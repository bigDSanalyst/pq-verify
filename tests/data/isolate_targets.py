"""Stand-ins for a misbehaving library, run in pq_verify.isolate's child.

The tests put tests/data on sys.path, which the spawned child inherits, and
call these through isolate.run. Each writes the pids it creates to `pidfile`
("child helper"), so a test can check that nothing outlived the audit.
"""
import ctypes
import gc
import os
import signal
import struct
import time


def _helper(pidfile, seconds=600):
    """Fork a helper process, as a library might, and record both pids."""
    pid = os.fork()
    if pid == 0:                     # the helper: inherits every descriptor, then idles
        try:
            time.sleep(seconds)
        finally:
            os._exit(0)
    with open(pidfile, "w") as fh:
        fh.write(f"{os.getpid()} {pid}")


def fork_then_hang(pidfile):
    _helper(pidfile)
    time.sleep(3600)


def fork_then_crash(pidfile):
    _helper(pidfile)
    os.kill(os.getpid(), signal.SIGABRT)


def fork_then_return(pidfile):
    _helper(pidfile)
    return "returned"


def hang(pidfile):
    with open(pidfile, "w") as fh:
        fh.write(f"{os.getpid()}")
    time.sleep(3600)


def stall_mid_message():
    """Write the header of a message into the result pipe, then stall."""
    from multiprocessing.connection import Connection
    for obj in gc.get_objects():
        if isinstance(obj, Connection) and not obj.closed and obj.writable:
            os.write(obj.fileno(), struct.pack("!i", 1000))
    time.sleep(3600)


def load(path):
    """Load a library, as an audit does."""
    ctypes.CDLL(path)
    return path
