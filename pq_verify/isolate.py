"""
pq_verify.isolate — run a vendor audit in a child process.

Every --audit-* path loads the vendor's library and calls into it. Done in
pq-verify's own process, three things go wrong:

  * a crash (SIGSEGV on an edge-case vector, an abort in an assertion) kills
    pq-verify with it, so no report is written and CI sees a bare signal;
  * a hang never ends, and CI times out with nothing to say why;
  * the library shares memory with the code that decides its verdict.

Here the audit runs in a fresh interpreter (multiprocessing "spawn": no state
inherited from the parent beyond what is passed). Its printed output is relayed
line by line, so progress still streams. The parent keeps the verdict logic;
the child only computes and sends its result back. A crash or a timeout becomes
a reported outcome -- with the signal, or the limit that was hit -- rather than
a missing report.

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
import signal
import sys
import time

DEFAULT_TIMEOUT = 3600            # seconds; --audit-timeout overrides


class IsolatedFailure(Exception):
    """The audit did not return: it crashed, hung, or raised."""

    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind              # 'crash' | 'timeout' | 'exception'


def in_process():
    return os.environ.get("PQV_IN_PROCESS") == "1"


def _mapped_objects():
    """{path: inode} for every file-backed shared object mapped right now."""
    if sys.platform == "darwin":
        return _dyld_images()
    out = {}
    try:
        with open("/proc/self/maps") as fh:
            for line in fh:
                parts = line.split()
                if len(parts) >= 6 and parts[5].startswith("/"):
                    path = parts[5]
                    base = os.path.basename(path)
                    if ".so" in base:
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


def _child(conn, module, func, args, kwargs):
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


def _signal_name(code):
    try:
        return signal.Signals(-code).name
    except (ValueError, TypeError):
        return f"signal {-code}"


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
    proc = ctx.Process(target=_child, args=(child, module, func, args, kwargs),
                       daemon=True)
    proc.start()
    child.close()
    deadline = None if not timeout else time.monotonic() + timeout
    try:
        while True:
            remaining = None if deadline is None else max(0.0, deadline - time.monotonic())
            if not parent.poll(remaining):
                proc.kill()
                proc.join()
                raise IsolatedFailure(
                    "timeout", f"the audit did not finish within {timeout} s "
                               f"(--audit-timeout); the library may hang on an input")
            try:
                msg = parent.recv()
            except EOFError:
                proc.join()
                code = proc.exitcode
                if code is not None and code < 0:
                    raise IsolatedFailure(
                        "crash", f"the library crashed the audit process "
                                 f"({_signal_name(code)}) -- a vendor library that "
                                 f"crashes on a test vector is not verified") from None
                raise IsolatedFailure(
                    "crash", f"the audit process exited with status {code} "
                             f"before reporting") from None
            if msg[0] == "out":
                sys.stdout.write(msg[1])
                continue
            break
    finally:
        parent.close()
    proc.join()
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
