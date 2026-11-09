"""
pq_verify.isolate — run a vendor audit in a child process.

Every --audit-* path loads the vendor's library and calls into it. Done in
pq-verify's own process, two things go wrong:

  * a crash (SIGSEGV on an edge-case vector, an abort in an assertion) kills
    pq-verify with it, so no report is written and CI sees a bare signal;
  * a hang never ends, and CI times out with nothing to say why.

Here the audit runs in a fresh interpreter (multiprocessing "spawn": no state
inherited from the parent beyond what is passed). Its printed output is relayed
line by line, so progress still streams. A crash or a timeout becomes a
reported outcome -- with the signal, or the limit that was hit -- rather than
a missing report.

The child leads a process group of its own, so the audit ends as one unit:
at the deadline, after a crash, and after it reports, the parent SIGKILLs the
group -- the child and every process the library started that is still in
it (one that leaves, as a daemon does, is out of reach). The deadline holds
whatever the child does: its messages are read on a thread of their own, and
its exit is watched directly (a pidfd where Linux has one), not through a pipe
a forked helper could hold open.

This is not a sandbox. The child runs the whole audit, scoring included, in
the same process as the library, and the parent takes the result the child
sends back. So a library that corrupts memory, or is built to deceive the
audit, can change its own verdict, and it runs with the user's privileges.
SECURITY.md says to audit a binary you do not trust in a container or a VM.

The child also records which shared objects the audit mapped into the process
(/proc/self/maps, before and after the call), hashed, so the report binds the
code that actually ran: the vendor library AND whatever it pulled in (a
libcrypto, a dependency found through LD_LIBRARY_PATH), not just the one path
pq-verify was given.

Set PQV_IN_PROCESS=1 to run audits in-process (debugging only; the report
says so).
"""

import hashlib
import importlib
import io
import multiprocessing
import os
import queue
import selectors
import signal
import subprocess
import sys
import tempfile
import threading
import time

DEFAULT_TIMEOUT = 3600            # seconds; --audit-timeout overrides
_GRACE = 2.0         # seconds for the rest of a dead child's messages to arrive
_TICK = 0.1          # how often to look for the child's exit where no pidfd says so
_EXIT_WAIT = 10.0    # seconds a child that has reported gets to exit by itself


class IsolatedFailure(Exception):
    """The audit did not return: it crashed, hung, or raised."""

    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind              # 'crash' | 'timeout' | 'exception'


def in_process():
    return os.environ.get("PQV_IN_PROCESS") == "1"


def _mapped_objects():
    """{path: inode} for every file-backed object mapped right now that holds
    code, whatever its name.

    A maps line ends in the path, which may contain spaces, so it is split at
    most five times. A file removed or replaced after it was mapped keeps the
    kernel's " (deleted)" suffix: it cannot be hashed, and the report says so.
    """
    if sys.platform == "darwin":
        return _dyld_images()
    out = {}
    try:
        with open("/proc/self/maps") as fh:
            for line in fh:
                parts = line.rstrip("\n").split(None, 5)
                if len(parts) < 6 or not parts[5].startswith("/"):
                    continue
                path = parts[5]
                if "x" in parts[1] or ".so" in os.path.basename(path):
                    out[path] = int(parts[4])
    except OSError:
        return None                   # not Linux: nothing to report
    return out


def _dyld_images():
    """macOS: every image dyld has loaded (there is no /proc), by path."""
    import ctypes
    try:
        libc = ctypes.CDLL(None)
        libc._dyld_image_count.restype = ctypes.c_uint32
        libc._dyld_get_image_name.restype = ctypes.c_char_p
        libc._dyld_get_image_name.argtypes = [ctypes.c_uint32]
        out = {}
        for i in range(libc._dyld_image_count()):
            name = libc._dyld_get_image_name(i)
            if not name:
                continue
            path = os.fsdecode(name)
            try:
                out[path] = os.stat(path).st_ino
            except OSError:
                out[path] = 0          # in the shared cache, not on disk
        return out
    except (OSError, AttributeError):
        return None


def _sha256(path):
    h = hashlib.sha256()
    try:
        with open(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
    except OSError:
        return None
    return h.hexdigest()


def loaded_since(before):
    """Shared objects mapped since `before`, each with its inode and sha256."""
    after = _mapped_objects()
    if after is None or before is None:
        return None
    return [{"path": p, "inode": after[p], "sha256": _sha256(p)}
            for p in sorted(after) if p not in before]


def environment():
    """The loader settings that decide which code a dlopen maps."""
    return {k: os.environ[k] for k in ("LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT")
            if os.environ.get(k)}


class _Relay(io.TextIOBase):
    """sys.stdout in the child: each write goes to the parent as it happens."""

    def __init__(self, conn):
        self.conn = conn

    def write(self, s):
        if s:
            self.conn.send(("out", s))
        return len(s)

    def flush(self):
        pass


# ───────────────────────────── the child ─────────────────────────────

def _wait_readable(fd, timeout=None):
    """Block until `fd` is readable, or `timeout` seconds pass."""
    with selectors.DefaultSelector() as sel:
        sel.register(fd, selectors.EVENT_READ)
        sel.select(timeout)


def _die_with_parent(parent_pid):
    """Run in a thread of the child: when the parent goes away, SIGKILL this
    process group, so neither the audit nor anything the library started in
    it outlives pq-verify."""
    fd = None
    if hasattr(os, "pidfd_open"):
        try:
            fd = os.pidfd_open(parent_pid)        # Linux 5.3+: readable at exit
        except OSError:
            fd = None
    if fd is not None and os.getppid() == parent_pid:
        _wait_readable(fd)
    else:
        while os.getppid() == parent_pid:
            time.sleep(0.5)
    os.killpg(0, signal.SIGKILL)


def _lead_own_group(parent_pid):
    """Make the child the leader of a process group of its own before any
    library is loaded, so one signal stops the audit and everything the
    library started. A terminal's Ctrl-C and a kill of pq-verify no longer
    reach the group, so the child watches the parent and ends the group when
    the parent goes away."""
    if not hasattr(os, "setsid"):
        return
    try:
        os.setsid()
    except OSError:
        return
    if parent_pid:
        threading.Thread(target=_die_with_parent, args=(parent_pid,),
                         name="pqv-parent-watch", daemon=True).start()


def _child(conn, module, func, args, kwargs, parent_pid=None):
    _lead_own_group(parent_pid)
    sys.stdout = _Relay(conn)
    try:
        before = _mapped_objects()
        fn = getattr(importlib.import_module(module), func)
        result = fn(*args, **kwargs)
        from .core import DEGRADED
        conn.send(("ok", result, {k: list(v) for k, v in DEGRADED.items()},
                   loaded_since(before)))
    except BaseException as exc:                      # noqa: BLE001 -- relayed
        conn.send(("raised", type(exc).__name__,
                   [c.__name__ for c in type(exc).__mro__], str(exc)))
    finally:
        conn.close()


# ───────────────────────────── the parent ─────────────────────────────

class _Inbox:
    """The child's messages, read on a thread of their own.

    Connection.recv() returns only once a whole message has arrived, so a
    child that sent part of one held a parent reading in its main thread past
    every deadline. Here the reading thread blocks instead, and wakes the
    main thread through a pipe for each message it queues. The thread owns
    the connection and closes it when it is done.
    """

    def __init__(self, conn):
        self.messages = queue.Queue()
        self.wake, self._wake_w = os.pipe()
        os.set_blocking(self.wake, False)
        threading.Thread(target=self._pump, args=(conn,), name="pqv-inbox",
                         daemon=True).start()

    def _pump(self, conn):
        try:
            while True:
                self._put(("message", conn.recv()))
        except EOFError:
            self._put(("closed", None))
        except BaseException as exc:                  # noqa: BLE001 -- e.g. a message that will not unpickle
            self._put(("closed", exc))
        finally:
            conn.close()
            os.close(self._wake_w)

    def _put(self, item):
        self.messages.put(item)
        try:
            os.write(self._wake_w, b"\0")
        except OSError:
            pass

    def take(self):
        """Every message queued so far, in order."""
        try:
            while os.read(self.wake, 4096):
                pass
        except (BlockingIOError, OSError):
            pass
        out = []
        while True:
            try:
                out.append(self.messages.get_nowait())
            except queue.Empty:
                return out


def _exit_fd(pid):
    """A descriptor that becomes readable when `pid` exits (Linux 5.3+), or
    None. No process the child starts can hold it open, unlike the pipes the
    child inherits."""
    if not hasattr(os, "pidfd_open"):
        return None
    try:
        return os.pidfd_open(pid)
    except OSError:
        return None


def _has_exited(proc):
    """Whether the child has exited. Where the platform can tell without
    reaping it, it is not reaped, so its process group keeps its id until
    _stop has signalled the group."""
    if hasattr(os, "waitid") and hasattr(os, "WNOWAIT"):
        try:
            return os.waitid(os.P_PID, proc.pid,
                             os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None
        except ChildProcessError:
            return True
    return proc.exitcode is not None


def _await(proc, inbox, exit_fd, timeout):
    """Relay the child's output until it reports, goes, or runs out of time.

    Returns (outcome, message, exited): outcome is "final" (message is the
    child's report), "gone" (it died or closed its end without reporting) or
    "timeout"; exited says whether the child had exited by itself.
    """
    deadline = None if not timeout else time.monotonic() + timeout
    sel = selectors.DefaultSelector()
    sel.register(inbox.wake, selectors.EVENT_READ)
    if exit_fd is not None:
        sel.register(exit_fd, selectors.EVENT_READ)
    closed = exited = False
    grace_end = None
    try:
        while True:
            for kind, msg in inbox.take():
                if kind == "closed":
                    closed = True
                    sel.unregister(inbox.wake)        # its writer is gone: always readable
                elif msg[0] == "out":
                    sys.stdout.write(msg[1])
                else:
                    return "final", msg, False
            if not exited and _has_exited(proc):
                exited = True
                if exit_fd is not None:
                    sel.unregister(exit_fd)
            now = time.monotonic()
            if closed and exited:
                return "gone", None, True             # nothing more can arrive
            if closed or exited:
                # One end has gone. What the child sent before it went is
                # already in the pipe, unless a helper it started holds the
                # pipe open or a message stopped half-way: wait briefly.
                if grace_end is None:
                    grace_end = now + _GRACE
                if now >= grace_end:
                    return "gone", None, exited
            if deadline is not None and now >= deadline:
                return "timeout", None, exited
            waits = [t - now for t in (grace_end, deadline) if t is not None]
            if exit_fd is None or exited:
                waits.append(_TICK)                   # look for the exit by polling
            sel.select(max(0.0, min(waits)) if waits else None)
    finally:
        sel.close()


def _stop(proc, exit_fd, wait=0.0):
    """End the audit. A child that has reported gets `wait` seconds to exit by
    itself (it removes its temporary files on the way out); then its whole
    process group -- the child and whatever the library started that is
    still in it -- is SIGKILLed, and the child is reaped."""
    if wait:
        end = time.monotonic() + wait
        while not _has_exited(proc) and time.monotonic() < end:
            if exit_fd is not None:
                _wait_readable(exit_fd, max(0.0, end - time.monotonic()))
            else:
                time.sleep(_TICK)
    if proc.pid is not None and hasattr(os, "killpg"):
        try:
            # Until the child is reaped its pid cannot be reused, and no
            # other group can carry it as an id: this reaches only the child's.
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    proc.kill()                   # a child stopped before it led a group of its own
    proc.join(5)


def _signal_name(code):
    try:
        return signal.Signals(-code).name
    except (ValueError, TypeError):
        return f"signal {-code}"


# ─────────────────────── a program that runs vendor code ───────────────────────

def _killpg(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError, AttributeError):
        pass


def _text(fh):
    """The output as text=True gave it, every line ending made "\\n"; decoded
    as UTF-8, with a byte that is not UTF-8 replaced rather than an error."""
    fh.seek(0)
    return (fh.read().decode("utf-8", "replace")
            .replace("\r\n", "\n").replace("\r", "\n"))


def run_group(cmd, timeout=None, env=None):
    """subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
    env=env), for a program that runs vendor code: a driver under Valgrind, an
    exhaustive test built from vendor source.

    Captured through pipes, its output kept the run open for as long as any
    process the vendor code started held them: a run that had finished was
    reported as a timeout, and the process lived on. Here the program leads a
    process group of its own and writes to temporary files, and the group is
    SIGKILLed once the program exits or runs out of time.
    """
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                env=env, start_new_session=True)
        try:
            proc.wait(timeout=timeout)
        except BaseException as exc:                   # the deadline, or Ctrl-C
            _killpg(proc.pid)
            proc.wait()
            if isinstance(exc, subprocess.TimeoutExpired):
                raise subprocess.TimeoutExpired(cmd, timeout, _text(out),
                                                _text(err)) from None
            raise
        _killpg(proc.pid)                              # what the program left behind
        return subprocess.CompletedProcess(cmd, proc.returncode, _text(out), _text(err))


def run(module, func, args=(), kwargs=None, timeout=DEFAULT_TIMEOUT):
    """Call module.func(*args, **kwargs) in a child; return (result, loaded).

    Raises IsolatedFailure on a crash, a timeout, or an exception in the
    child. An exception whose class is an OSError keeps that meaning: it is
    re-raised as OSError so "the linker could not load it" stays CANNOT VERIFY.
    """
    kwargs = kwargs or {}
    if in_process():
        before = _mapped_objects()
        result = getattr(importlib.import_module(module), func)(*args, **kwargs)
        return result, loaded_since(before)

    ctx = multiprocessing.get_context("spawn")
    parent, child = ctx.Pipe(duplex=False)
    proc = ctx.Process(target=_child,
                       args=(child, module, func, args, kwargs, os.getpid()),
                       daemon=True)
    proc.start()
    child.close()
    inbox = _Inbox(parent)
    exit_fd = _exit_fd(proc.pid)
    outcome = None
    try:
        outcome, msg, exited = _await(proc, inbox, exit_fd, timeout)
    finally:
        _stop(proc, exit_fd, _EXIT_WAIT if outcome == "final" else 0.0)
        os.close(inbox.wake)
        if exit_fd is not None:
            os.close(exit_fd)
    if outcome == "timeout":
        raise IsolatedFailure(
            "timeout", f"the audit did not finish within {timeout} s "
                       f"(--audit-timeout); the library may hang on an input")
    if outcome == "gone":
        code = proc.exitcode
        if not exited:
            raise IsolatedFailure(
                "crash", "the audit process closed its result channel before reporting")
        if code is not None and code < 0:
            raise IsolatedFailure(
                "crash", f"the library crashed the audit process "
                         f"({_signal_name(code)}) -- a vendor library that "
                         f"crashes on a test vector is not verified")
        raise IsolatedFailure(
            "crash", f"the audit process exited with status {code} "
                     f"before reporting")
    if msg[0] == "ok":
        _, result, degraded, loaded = msg
        from .core import DEGRADED
        for k, v in degraded.items():
            DEGRADED.setdefault(k, []).extend(x for x in v if x not in DEGRADED.get(k, []))
        return result, loaded
    _, name, mro, text = msg
    if "OSError" in mro:
        raise OSError(text)
    if name == "AdapterError":
        from .hbs_audit import AdapterError
        raise AdapterError(text)
    raise IsolatedFailure("exception", f"{name}: {text}")
