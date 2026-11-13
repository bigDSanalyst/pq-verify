"""
pq_verify.contained -- audit a shared library through pq-verify's contained
worker (`--audit-contained`).

The library audits (--audit-kem and the rest) score their results in the
process that has loaded the library, so a library that corrupts memory, or is
written to deceive the audit, can change its own verdict. Here the library
runs somewhere else, and the audit is the harness audit's
(pq_verify.harness_audit):

  * pq-verify copies the file, from one open descriptor, into a sealed memory
    file, hashing it as it goes. What was hashed is what runs, whatever
    happens to the file on disk afterwards.
  * The worker (harness/contained/pqv_worker.c, compiled here with the
    system's C compiler) is a Crucible-protocol harness. It is sent inputs
    and returns what the library wrote. No expected answer is sent to it;
    the scoring is done in pq-verify's own process, which for the length of
    the audit is not readable by the worker (not dumpable).
  * Before the library is mapped, the worker gives up its capabilities, sets
    no_new_privs and installs a seccomp filter. pq-verify confirms all three
    from /proc, and that the library is not mapped yet, before it tells the
    worker to load it.
  * NIST's answers are published, and shipped in this package where the
    worker can read them. So the audit also asks fresh questions, from a
    seed drawn for the run (pq_verify.fresh), scored against answers
    pq-verify's reference computes. The seed is reported, once the worker is
    gone.
  * When the audit ends, every process the worker's tree left behind is
    stopped: those still under the worker, and those that became pq-verify's
    own children because the worker died first (pq-verify is a child
    subreaper for the length of the audit). Any such process is a finding.

What this is not is in LIMITS.md and SECURITY.md. In short: the worker can
read any file the user can, so it is no sandbox; and a library that computes
correctly while it is being audited and differently when it is not passes
here as it passes anywhere.
"""

import atexit
import ctypes
import fcntl
import hashlib
import os
import platform
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time

from .display import shown
from .harness_audit import DEFAULT_CALL_TIMEOUT, Harness, HarnessDied

FRESH_DEFAULT = 8                   # fresh tests per group
MAX_LIBRARY = 1 << 30
_SOURCE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "harness", "contained", "pqv_worker.c")

_F_ADD_SEALS, _F_GET_SEALS = 1033, 1034
_SEALS = 0x1 | 0x2 | 0x4 | 0x8     # SEAL, SHRINK, GROW, WRITE
_MFD_CLOEXEC, _MFD_ALLOW_SEALING = 0x1, 0x2
_MFD_EXEC = 0x10                    # Linux 6.3: say outright that it will be executed
_SYS_MEMFD_CREATE = 319             # x86-64, the one machine the worker runs on
_PR_GET_DUMPABLE, _PR_SET_DUMPABLE = 3, 4
_PR_SET_CHILD_SUBREAPER, _PR_GET_CHILD_SUBREAPER = 36, 37

_RUN_LOCK = threading.Lock()        # the hardening below is the whole process's


class ContainedError(Exception):
    """The contained audit cannot be set up."""


def _cc():
    for name in ("cc", "gcc", "clang"):
        path = shutil.which(name)
        if path:
            return path
    return None


def available():
    """None, or why a contained audit cannot run here."""
    if not sys.platform.startswith("linux"):
        return ("the contained worker needs Linux (seccomp, memfd, /proc); this is "
                + sys.platform)
    if platform.machine() != "x86_64":
        # The worker's source has the AArch64 system calls too, but nothing
        # has run it there, and an untested filter is not one to rely on.
        return ("the contained worker is tested on x86-64 Linux only; this is "
                + platform.machine())
    if not os.path.exists("/proc/self/status"):
        return "/proc is not mounted"
    if _cc() is None:
        return "a C compiler (cc, gcc or clang) is needed to build the worker"
    return None


# ----------------------------------------------------------------------
# the worker
# ----------------------------------------------------------------------

_WORKER = None
_WORKER_LOCK = threading.Lock()


def _sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def worker():
    """(path, description) of the compiled worker, built once per process."""
    global _WORKER
    with _WORKER_LOCK:
        if _WORKER and os.path.exists(_WORKER[0]):
            return _WORKER
        cc = _cc()
        if cc is None:
            raise ContainedError("no C compiler to build the worker with")
        work = tempfile.mkdtemp(prefix="pqv-worker-")
        atexit.register(shutil.rmtree, work, True)
        exe = os.path.join(work, "pqv_worker")
        p = subprocess.run([cc, "-std=gnu11", "-O2", "-o", exe, _SOURCE, "-ldl", "-lpthread"],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if p.returncode != 0:
            raise ContainedError("the worker did not compile: "
                                 + p.stdout.decode("utf-8", "replace")[:400])
        v = subprocess.run([cc, "--version"], stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL)
        version = v.stdout.decode("utf-8", "replace").splitlines()
        _WORKER = (exe, {"source_sha256": _sha256_file(_SOURCE),
                         "binary_sha256": _sha256_file(exe),
                         "compiler": version[0] if version else cc})
        return _WORKER


def policy():
    """The worker's filter, as the worker itself lists it: the system calls
    it refuses outright, those it refuses for some arguments, and the rules
    for those in words. {'denied': {name: number}, 'conditional': {name:
    number}, 'rules': [text]}."""
    exe, _ = worker()
    out = subprocess.run([exe, "--policy"], stdout=subprocess.PIPE, check=True).stdout
    denied, conditional, rules = {}, {}, []
    for line in out.decode().splitlines():
        kind, _, rest = line.partition(" ")
        if kind in ("deny", "conditional"):
            name, nr = rest.split()
            (denied if kind == "deny" else conditional)[name] = int(nr)
        elif kind == "rule":
            rules.append(" ".join(rest.split()))
    return {"denied": denied, "conditional": conditional, "rules": rules}


# ----------------------------------------------------------------------
# the sealed copy
# ----------------------------------------------------------------------

def _identity(st):
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


class Pinned:
    """A sealed in-memory copy of a library file."""

    def __init__(self, path, fd, sha256, size, disk):
        self.path, self.fd, self.sha256, self.size = path, fd, sha256, size
        self.disk = disk                       # the file's identity when it was read
        st = os.fstat(fd)
        self.inode = st.st_ino

    def rehash(self):
        h, off = hashlib.sha256(), 0
        while True:
            chunk = os.pread(self.fd, 1 << 20, off)
            if not chunk:
                return h.hexdigest()
            h.update(chunk)
            off += len(chunk)

    def sealed(self):
        return fcntl.fcntl(self.fd, _F_GET_SEALS) & _SEALS == _SEALS

    def disk_changed(self):
        try:
            return _identity(os.stat(self.path)) != self.disk
        except OSError:
            return True

    def close(self):
        if self.fd is not None:
            try:
                os.close(self.fd)
            except OSError:
                pass
            self.fd = None


def _memfd_create(name, flags):
    if hasattr(os, "memfd_create"):
        return os.memfd_create(name, flags)
    # A Python built where the C library had no memfd_create: ask the kernel.
    libc = ctypes.CDLL(None, use_errno=True)
    fd = libc.syscall(ctypes.c_long(_SYS_MEMFD_CREATE), ctypes.c_char_p(name.encode()),
                      ctypes.c_uint(flags))
    if fd < 0:
        err = ctypes.get_errno()
        raise OSError(err, os.strerror(err))
    return fd


def _memfd():
    flags = _MFD_CLOEXEC | _MFD_ALLOW_SEALING
    try:
        return _memfd_create("pqv-library", flags | _MFD_EXEC)
    except OSError:
        return _memfd_create("pqv-library", flags)       # before Linux 6.3


def pin(path):
    """Copy `path` into a sealed memory file, hashing it on the way. One open
    of the file serves both, so there is no moment between the hash and the
    load at which the file can be swapped."""
    real = os.path.realpath(path)
    src = os.open(real, os.O_RDONLY | os.O_CLOEXEC)
    try:
        st0 = os.fstat(src)
        if not stat.S_ISREG(st0.st_mode):
            raise ContainedError(f"{real} is not a regular file")
        if st0.st_size > MAX_LIBRARY:
            raise ContainedError(f"{real} is larger than {MAX_LIBRARY} bytes")
        fd = _memfd()
        try:
            h, total = hashlib.sha256(), 0
            while True:
                chunk = os.read(src, 1 << 20)
                if not chunk:
                    break
                h.update(chunk)
                total += len(chunk)
                view = memoryview(chunk)
                while view:
                    view = view[os.write(fd, view):]
            if _identity(os.fstat(src)) != _identity(st0) or total != st0.st_size:
                raise ContainedError("the library changed while it was being read")
            fcntl.fcntl(fd, _F_ADD_SEALS, _SEALS)
            pinned = Pinned(real, fd, h.hexdigest(), total, _identity(st0))
            if not pinned.sealed():
                raise ContainedError("the memory file could not be sealed")
            return pinned
        except BaseException:
            os.close(fd)
            raise
    finally:
        os.close(src)


def exported_functions(fd):
    """The functions the ELF file open on `fd` exports: the defined, global
    or weak entries of its dynamic symbol table that are functions. That is
    what `nm -D --defined-only` lists as T, i and W, and what the other
    audits ask nm for. Here pq-verify reads the table itself, so that no
    other program is run on a file it does not trust outside the worker.
    Anything that is not a 64-bit little-endian ELF with section headers
    gives an empty list, and the audit then says it found no entry points."""
    import struct

    def at(offset, n):
        data = os.pread(fd, n, offset)
        if len(data) != n:
            raise ValueError("short read")
        return data

    try:
        head = at(0, 64)
        if head[:6] != b"\x7fELF\x02\x01":            # ELF, 64-bit, little-endian
            return []
        shoff, = struct.unpack_from("<Q", head, 0x28)
        shentsize, shnum = struct.unpack_from("<HH", head, 0x3A)
        if shentsize != 64 or shnum == 0:
            return []
        table = at(shoff, 64 * shnum)
        sections = [struct.unpack_from("<IIQQQQIIQQ", table, 64 * i) for i in range(shnum)]
        names = []
        for _name, kind, _flags, _addr, offset, size, link, _info, _align, entsize in sections:
            if kind != 11 or entsize != 24 or link >= shnum:        # SHT_DYNSYM
                continue
            stroff, strsize = sections[link][4], sections[link][5]
            if size > 1 << 28 or strsize > 1 << 28:
                return []
            strings, symbols = at(stroff, strsize), at(offset, size - size % 24)
            for i in range(0, len(symbols), 24):
                st_name, info, _other, shndx = struct.unpack_from("<IBBH", symbols, i)
                bind, typ = info >> 4, info & 15
                if shndx == 0 or shndx >= 0xFF00 or bind not in (1, 2):   # defined; global, weak
                    continue
                code = shndx < shnum and sections[shndx][2] & 0x4          # SHF_EXECINSTR
                if not (typ in (2, 10) or (typ == 0 and code)):            # FUNC, GNU_IFUNC
                    continue
                end = strings.find(b"\0", st_name)
                if 0 <= st_name < end:
                    names.append(strings[st_name:end].decode("ascii", "replace"))
        return names
    except (OSError, OverflowError, ValueError, struct.error):
        return []                   # a header that points nowhere, a short file


# ----------------------------------------------------------------------
# pq-verify's own process, for the length of the audit
# ----------------------------------------------------------------------

_PRCTL = None


def _prctl(*args):
    global _PRCTL
    if _PRCTL is None:
        fn = ctypes.CDLL(None, use_errno=True).prctl
        fn.argtypes = [ctypes.c_int] + [ctypes.c_ulong] * 4
        fn.restype = ctypes.c_int
        _PRCTL = fn
    return _PRCTL(*(list(args) + [0] * (5 - len(args))))


class _Hardened:
    """Not dumpable, so the worker cannot read this process's memory or open
    its descriptors through /proc; and a child subreaper, so a process the
    worker's tree orphans becomes a child of this one, where it can be found
    and stopped. Both are put back afterwards."""

    def __enter__(self):
        self.was_dumpable = _prctl(_PR_GET_DUMPABLE)
        was = ctypes.c_int(0)
        self.was_subreaper = (was.value if _prctl(_PR_GET_CHILD_SUBREAPER,
                                                  ctypes.addressof(was)) == 0 else 0)
        self.non_dumpable = _prctl(_PR_SET_DUMPABLE, 0) == 0
        self.subreaper = _prctl(_PR_SET_CHILD_SUBREAPER, 1) == 0
        return self

    def __exit__(self, *exc):
        if self.subreaper:
            _prctl(_PR_SET_CHILD_SUBREAPER, self.was_subreaper)
        if self.non_dumpable and self.was_dumpable == 1:
            _prctl(_PR_SET_DUMPABLE, 1)
        return False


# ----------------------------------------------------------------------
# /proc
# ----------------------------------------------------------------------

def _table():
    """{pid: (parent, state, name)} of every process /proc shows."""
    table = {}
    try:
        names = os.listdir("/proc")
    except OSError:
        return table
    for name in names:
        if not name.isdigit():
            continue
        try:
            with open(f"/proc/{name}/stat", "rb") as fh:
                data = fh.read().decode("ascii", "replace")
        except OSError:
            continue
        lp, rp = data.find("("), data.rfind(")")
        fields = data[rp + 2:].split()
        try:
            table[int(name)] = (int(fields[1]), fields[0], data[lp + 1:rp])
        except (IndexError, ValueError):
            continue
    return table


def _children(pid, table=None):
    table = _table() if table is None else table
    return {p for p, (parent, _s, _n) in table.items() if parent == pid}


def _descendants(pid):
    table = _table()
    out, todo = [], [pid]
    while todo:
        for child in _children(todo.pop(), table):
            out.append(child)
            todo.append(child)
    return out


def _status(pid):
    out = {}
    with open(f"/proc/{pid}/status", errors="replace") as fh:
        for line in fh:
            key, _, value = line.partition(":")
            out[key.strip()] = value.strip()
    return out


def _maps(pid):
    """{inode: path} of the files mapped into `pid`."""
    files = {}
    with open(f"/proc/{pid}/maps", errors="replace") as fh:
        for line in fh:
            parts = line.split(None, 5)
            if len(parts) < 6 or parts[4] == "0":
                continue
            files.setdefault(int(parts[4]), parts[5].rstrip("\n"))
    return files


def _reap(pid, seconds=3.0):
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        try:
            if os.waitpid(pid, os.WNOHANG)[0]:
                return
        except ChildProcessError:
            return
        time.sleep(0.01)


def _kill(pid):
    try:
        os.kill(pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


# ----------------------------------------------------------------------
# the harness
# ----------------------------------------------------------------------

class ContainedHarness(Harness):
    """pq-verify's worker with a library loaded from a sealed copy."""

    fixed_buffers = True            # the C API takes buffers of fixed sizes

    def __init__(self, pinned, exe, symbols, sizes, timeout=DEFAULT_CALL_TIMEOUT,
                 use_filter=True, keep=None):
        if keep is not None:
            keep.append(self)       # reachable even if starting it fails
        self.pinned = pinned
        self.use_filter = use_filter
        self.containment = {}
        self.outside = []           # calls after which a guard had changed
        self.loaded = []            # what the load, and anything after it, mapped
        self.escapees = []          # processes the worker's tree left behind
        self.killed_by_us = False
        self._closed = False
        self._before = None
        self._mine = _children(os.getpid())
        argv = [exe, str(pinned.fd), *symbols, *(str(n) for n in sizes)]
        Harness.__init__(self, argv + ([] if use_filter else ["nofilter"]), timeout=timeout)
        self._record_loaded()

    def _spawn(self):
        # An environment of its own: no LD_PRELOAD, no LD_LIBRARY_PATH. The
        # pipes are buffered on this side: a reply is thousands of hex digits,
        # and an unbuffered readline asks the kernel for each one.
        return subprocess.Popen(
            self.argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, start_new_session=True,
            close_fds=True, pass_fds=(self.pinned.fd,), cwd="/",
            env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"})

    def _before_handshake(self):
        """The worker says it is contained; /proc is asked whether that is so,
        and only then is the worker told to map the library."""
        first = self._read("the worker's start")
        if not isinstance(first, dict) or first.get("stage") != "contained":
            raise HarnessDied("the worker did not reach its contained stage: "
                              + str(first)[:160])
        pid = self.proc.pid
        try:
            st, before = _status(pid), _maps(pid)
        except OSError as exc:
            raise HarnessDied(f"the worker's state could not be read from /proc: {exc}") from None
        c = self.containment
        c["seccomp"] = {"0": "off", "1": "strict", "2": "filter"}.get(
            st.get("Seccomp"), st.get("Seccomp"))
        c["no_new_privs"] = st.get("NoNewPrivs") == "1"
        try:
            caps = [int(st[k], 16) for k in ("CapInh", "CapPrm", "CapEff")]
        except (KeyError, ValueError):
            caps = [1]
        c["capabilities"] = "none" if not any(caps) else "some"
        c["library_mapped_before_asked"] = self.pinned.inode in before
        wrong = []
        if self.use_filter and c["seccomp"] != "filter":
            wrong.append("no seccomp filter is in force in the worker")
        if not c["no_new_privs"]:
            wrong.append("no_new_privs is not set in the worker")
        if any(caps):
            wrong.append("the worker still holds capabilities")
        if c["library_mapped_before_asked"]:
            wrong.append("the library was mapped before pq-verify asked for it")
        c["confirmed_before_load"] = bool(self.use_filter and not wrong)
        if wrong:
            raise HarnessDied("containment could not be confirmed: " + "; ".join(wrong))
        self._before = before
        try:
            self.proc.stdin.write(b'{"load": true}\n')
            self.proc.stdin.flush()
        except OSError:
            raise HarnessDied("the worker closed its input before the library "
                              "was loaded") from None

    def _read(self, what):
        r = Harness._read(self, what)
        if isinstance(r, dict):
            if "fatal" in r:
                raise HarnessDied(f"the worker stopped: {str(r['fatal'])[:300]}")
            if r.get("outside"):
                self.outside.append(str(r["outside"])[:200])
        return r

    def _record_loaded(self):
        """Every file mapped since the worker was told to load: the sealed
        copy, and what the loader pulled in with it or after it."""
        if self._before is None or self.proc.poll() is not None:
            return
        try:
            now = _maps(self.proc.pid)
        except OSError:
            return
        seen = {o["inode"] for o in self.loaded}
        for inode, path in now.items():
            if inode in self._before or inode in seen:
                continue
            if inode == self.pinned.inode:
                self.loaded.append({"path": path, "inode": inode,
                                    "sha256": self.pinned.sha256,
                                    "sealed_copy_of": self.pinned.path})
                continue
            digest = None
            try:
                with open(path, "rb") as fh:
                    if os.fstat(fh.fileno()).st_ino == inode:
                        h = hashlib.sha256()
                        for chunk in iter(lambda: fh.read(1 << 20), b""):
                            h.update(chunk)
                        digest = h.hexdigest()
            except OSError:
                pass
            self.loaded.append({"path": path, "inode": inode, "sha256": digest})

    def close(self):
        """Stop the worker and everything its tree started, wherever that
        has ended up, and remember what was found."""
        if self._closed:
            return
        self._closed = True
        pid, me = self.proc.pid, os.getpid()
        self._record_loaded()
        found = {}
        table = _table()
        for p in _descendants(pid):                 # still under the worker
            found[p] = table.get(p, (0, "?", "?"))[2]
        try:
            self.proc.stdin.close()                 # the worker leaves at end of input
        except OSError:
            pass
        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.killed_by_us = True
        for p in found:
            _kill(p)
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        self.proc.kill()
        self.proc.wait()
        # pq-verify is a child subreaper during the audit: what the worker's
        # tree orphaned, before the worker died or because it did, is now a
        # child of this process. Whatever pq-verify did not have before the
        # audit and did not start itself is such a process.
        for _ in range(50):
            table = _table()
            new = _children(me, table) - self._mine - {pid}
            if not new:
                break
            for p in new:
                found.setdefault(p, table[p][2])
                _kill(p)
            for p in new:
                _reap(p)
        for p in found:
            _reap(p, 0.2)
        self.escapees = [{"pid": p, "name": name} for p, name in sorted(found.items())]

    def ended(self):
        """How the worker ended, for the report."""
        rc = self.proc.returncode
        if self.killed_by_us:
            return "stopped by pq-verify when the audit ended"
        if rc is None:
            return "unknown"
        if rc < 0:
            try:
                return f"killed by {signal.Signals(-rc).name}"
            except ValueError:
                return f"killed by signal {-rc}"
        return f"exited with status {rc}"

    def violated(self):
        """The kernel killed the worker for a system call on the filter's
        list (SIGSYS), which nothing of pq-verify's own makes: the worker
        does what it will need to do once before any vendor code is mapped."""
        return (not self.killed_by_us and self.proc.returncode == -signal.SIGSYS
                and self._before is not None)


# ----------------------------------------------------------------------
# the audit
# ----------------------------------------------------------------------

SECCOMP_VIOLATION = "ISO-SECCOMP-VIOLATION"
ESCAPEE = "ISO-ESCAPEE"


def _cannot(base, reason, verbose):
    if verbose:
        print(f"  CANNOT VERIFY: {shown(reason, 400)}")
    return dict(base, verified=False, status="CANNOT VERIFY", reason=reason,
                passed=0, total=0, detail={}, not_applicable={},
                not_applicable_total=0, failures=[])


def pqverify_audit_contained(so_path, param_set, keypair=None, encaps=None, decaps=None,
                             prefix=None, timeout=DEFAULT_CALL_TIMEOUT, verbose=True,
                             edge=True, accumulated=10_000, fresh=FRESH_DEFAULT,
                             fresh_seed=None, use_filter=True):
    """Audit an ML-KEM shared library through the contained worker.

    The checks are the harness audit's: NIST's keyGen, encapsulation,
    decapsulation and key-check vectors, the edge cases, the accumulated
    vectors, and `fresh` tests per group on inputs drawn for this run. Added
    to them: `containment` (the filter was confirmed before the library was
    mapped, the library made no system call on its list, and no process was
    left behind) and `bounds` (no call wrote outside a buffer it was given).

    use_filter=False starts the worker without its filter. It exists for
    pq-verify's own tests of what happens when a library does start a process;
    such a run is never VERIFIED.

    Returns the harness audit's result dict with 'library', 'artifact' and
    'containment' added.
    """
    from .core import _KEM_SIZES, _resolve_kem_symbols
    if param_set not in _KEM_SIZES:
        raise ValueError(f"unknown parameter set {param_set}")
    path = os.path.abspath(os.path.expanduser(so_path))
    base = {"library": path, "parameter_set": param_set, "command": None}
    why = available()
    if why:
        return _cannot(base, why, verbose)
    try:
        pinned = pin(path)
    except (OSError, ContainedError) as exc:
        return _cannot(base, f"the library could not be read: {exc}", verbose)
    try:
        base["artifact"] = {"bound": True, "sha256": pinned.sha256, "path": pinned.path,
                            "summary": f"sha256 {pinned.sha256}",
                            "detail": ("The audited computation was performed by a sealed "
                                       "in-memory copy of this file, hashed as it was "
                                       "copied."),
                            "isolation": "contained worker"}
        if verbose:
            print(f"  artifact: {base['artifact']['summary']}  (the sealed copy that runs)")
        # Names come from the sealed copy, and pq-verify reads them itself:
        # nm is not run on the file, nor on whatever the path holds by now.
        exported = exported_functions(pinned.fd)
        found, ambiguous = _resolve_kem_symbols(
            exported, param_set, {"keypair": keypair, "encaps": encaps, "decaps": decaps},
            prefix=prefix)
        if ambiguous:
            role, cands = next(iter(ambiguous.items()))
            return _cannot(base, f"more than one symbol could be {role} "
                                 f"({', '.join(cands[:4])}); name it with --kem-{role} "
                                 f"or narrow the choice with --symbol-prefix", verbose)
        missing = [r for r in ("keypair", "encaps", "decaps") if not found.get(r)]
        if missing:
            return _cannot(base, "no derandomised entry point for " + ", ".join(missing)
                           + " (keypair_derand, enc_derand, dec): NIST's vectors are "
                             "seeded, and a library with only randomised entry points "
                             "can be checked for self-consistency alone, which is not "
                             "verification. Name them with --kem-keypair, --kem-encaps "
                             "and --kem-decaps if they are called something else",
                           verbose)
        try:
            exe, built = worker()
        except (OSError, ContainedError) as exc:
            return _cannot(base, str(exc), verbose)
        symbols = [found["keypair"], found["encaps"], found["decaps"]]
        base["symbols"] = dict(zip(("keypair", "encaps", "decaps"), symbols))
        sizes = _KEM_SIZES[param_set][:3]
        keep = []

        def start(_argv, timeout):
            return ContainedHarness(pinned, exe, symbols, sizes, timeout=timeout,
                                    use_filter=use_filter, keep=keep)

        def banner():
            c = keep[0].containment if keep else {}
            return [f"library : {shown(pinned.path, 300)}",
                    f"worker  : seccomp {c.get('seccomp')}, no_new_privs "
                    f"{'set' if c.get('no_new_privs') else 'NOT set'}, capabilities "
                    f"{c.get('capabilities')}; confirmed before the library was mapped"]

        with _RUN_LOCK, _Hardened() as hard:
            if not hard.non_dumpable or not hard.subreaper:
                return _cannot(base, "pq-verify could not protect its own process for the "
                                     "audit (prctl: not dumpable "
                                     f"{'set' if hard.non_dumpable else 'refused'}, child "
                                     f"subreaper {'set' if hard.subreaper else 'refused'})",
                               verbose)

            def finish(result, _h):
                return _finish(result, keep[0] if keep else None, pinned, built,
                               use_filter)

            from .harness_audit import pqverify_audit_harness
            result = pqverify_audit_harness(
                [exe], param_set, timeout=timeout, verbose=verbose, edge=edge,
                accumulated=accumulated, fresh=fresh, fresh_seed=fresh_seed,
                start=start, finish=finish,
                describe={"title": "CONTAINED AUDIT (pq-verify's worker, Crucible protocol)",
                          "banner": banner,
                          "closing": ("Audited: this file, run from a sealed copy in "
                                      "pq-verify's contained worker and",
                                      "scored in pq-verify's own process. The worker is not "
                                      "a sandbox: SECURITY.md.")})
        result.update({k: v for k, v in base.items() if k not in ("command",)})
        result["command"] = None
        return result
    finally:
        pinned.close()


def _finish(result, h, pinned, built, use_filter):
    """Add to the harness audit's result what only the contained audit knows:
    how the worker ended, what it left behind, what it mapped, and whether
    the sealed copy is still what was hashed."""
    if h is not None:
        h.close()                   # a worker that never finished starting, too
    detail = dict(result.get("detail") or {})
    failures = list(result.get("failures") or [])
    c = dict(h.containment) if h is not None else {}
    c["worker"] = dict(built)
    c["filter"] = "on" if use_filter else "OFF (pq-verify's own tests only)"
    notes = list(result.get("harness_notes") or [])
    findings = []
    if h is not None:
        c["worker_ended"] = h.ended()
        c["escapees"] = h.escapees
        if h.violated():
            findings.append({"stage": "containment", "case": SECCOMP_VIOLATION,
                             "detail": ("the kernel stopped the worker for a system call "
                                        "on the filter's list (starting a process, exec, a "
                                        "socket, opening a file for writing or changing "
                                        "one, signalling or tracing another process; "
                                        "`pqv_worker --policy` lists them), made while the "
                                        "library was being loaded or run")})
        if h.escapees:
            who = ", ".join(f"{e['pid']} ({e['name']})" for e in h.escapees[:8])
            findings.append({"stage": "containment", "case": ESCAPEE,
                             "detail": (f"the library left {len(h.escapees)} process(es) "
                                        f"behind: {who}. All were stopped")})
        if h.outside:
            findings.append({"stage": "bounds", "case": h.outside[0],
                             "detail": (f"the library wrote outside a buffer it was given "
                                        f"in {len(h.outside)} call(s): memory corruption "
                                        f"in the worker, so its other answers may be "
                                        f"affected too")})
        artifact_objects = h.loaded
    else:
        artifact_objects = []
    try:
        c["sealed_copy_unchanged"] = pinned.rehash() == pinned.sha256 and pinned.sealed()
    except OSError:
        c["sealed_copy_unchanged"] = False
    c["file_on_disk_changed_during_audit"] = pinned.disk_changed()
    if c["file_on_disk_changed_during_audit"]:
        notes.append("the file on disk changed during the audit; what ran, and what this "
                     f"result is bound to, is the sealed copy (sha256 {pinned.sha256})")

    died = result["status"] == "CANNOT VERIFY" and not result.get("total")
    reason = result.get("reason")
    if died and h is not None and not h.killed_by_us and (h.proc.returncode or 0) < 0:
        # "the harness exited (status -11)" is the harness audit's wording
        reason = f"the worker was {h.ended()}: {reason}"
        if h.proc.returncode == -signal.SIGSYS and not h.violated():
            reason = ("the worker was stopped by its own filter before any library was "
                      "mapped: the filter does not suit this system's C library, and no "
                      "contained audit can run here")
    fr = result.get("fresh")
    if fr and fr.get("seed_source") != "drawn for this run":
        notes.append("the fresh questions were derived from a seed supplied to this run. "
                     "A supplied seed is on the command line, where the worker can read "
                     "it: this reproduces an earlier result, it does not ask anything new")
    ran = h is not None and h.containment.get("confirmed_before_load")
    if ran and not died:
        detail["containment"] = (0 if any(f["stage"] == "containment" for f in findings) else 1, 1)
        detail["bounds"] = (0 if h.outside else 1, 1)
    else:
        for stage in {f["stage"] for f in findings}:
            detail[stage] = (0, 1)
    failures = findings + failures
    passed = sum(p for p, _ in detail.values())
    total = sum(t for _, t in detail.values())
    out = dict(result, detail=detail, failures=failures, passed=passed, total=total,
               harness_notes=notes, containment=c)
    out["loaded_objects"] = artifact_objects
    if died:
        out["reason"] = reason
    if findings:
        out.update(status="FINDINGS PRESENT", verified=False)
    elif not c["sealed_copy_unchanged"]:
        out.update(status="CANNOT VERIFY", verified=False,
                   reason="the sealed copy of the library is no longer what was hashed")
    elif died:
        out.update(status="CANNOT VERIFY", verified=False)
    elif not use_filter:
        out.update(status="CANNOT VERIFY", verified=False,
                   reason="the worker ran without its filter; such a run is never VERIFIED")
    else:
        verified = passed == total and total > 0
        out.update(verified=verified,
                   status="VERIFIED" if verified else
                   ("FINDINGS PRESENT" if total else "CANNOT VERIFY"))
    return out
