"""
pq_verify.bounds -- catch a vendor function writing outside its buffers.

The audits hand a library buffers of the sizes the standard gives. A library
that writes past one corrupts memory in the audit's own process: it may
crash, which the child process reports, or it may not, and then nothing said
it had happened. The HQC audit has always surrounded its buffers with guard
bytes and checked them (hqc_audit._Buf); Guarded does the same for the
ML-KEM, ML-DSA and SLH-DSA audits.

Guarded wraps a vendor function. On each call every buffer argument (a ctypes
array) is copied into the middle of a larger buffer whose GUARD bytes on
either side hold a known pattern; the function gets that copy. Afterwards the
pattern is checked and the contents are copied back, so callers see what they
always saw. A pattern that changed means the function wrote outside a buffer
it was given: the audit reports it and does not verify the library.

This catches the common case, an overflow or underflow of up to GUARD bytes.
A write that skips past the guard, or lands elsewhere in memory, is not
caught; memory errors in general are what a sanitizer or Valgrind finds.
"""

import ctypes as _ct

GUARD = 64
FILL = 0xA5
_PATTERN = bytes([FILL]) * GUARD
_KEEP = 8                    # out-of-bounds writes described in a report


class Guarded:
    """A vendor function whose every call is checked for writes outside the
    buffers it is given. restype, argtypes and the like pass through to the
    function itself."""

    def __init__(self, fn, name):
        object.__setattr__(self, "_fn", fn)
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "calls", 0)
        object.__setattr__(self, "outside", [])       # the first _KEEP, described
        object.__setattr__(self, "outside_total", 0)

    def __getattr__(self, attr):
        return getattr(self._fn, attr)

    def __setattr__(self, attr, value):
        if attr in ("calls", "outside_total"):
            object.__setattr__(self, attr, value)
        else:
            setattr(self._fn, attr, value)

    def __call__(self, *args):
        moved, copies, call = [], {}, []
        for i, a in enumerate(args):
            if isinstance(a, _ct.Array):
                if id(a) not in copies:            # one copy if a buffer is passed twice
                    n = _ct.sizeof(a)
                    raw = (_ct.c_ubyte * (n + 2 * GUARD))()
                    _ct.memset(raw, FILL, n + 2 * GUARD)
                    _ct.memmove(_ct.addressof(raw) + GUARD, a, n)
                    copies[id(a)] = type(a).from_buffer(raw, GUARD)
                    moved.append((i, a, raw, n))
                call.append(copies[id(a)])
            else:
                call.append(a)
        try:
            return self._fn(*call)
        finally:
            self.calls += 1
            for i, a, raw, n in moved:
                base = _ct.addressof(raw)
                before = _ct.string_at(base, GUARD) != _PATTERN
                after = _ct.string_at(base + GUARD + n, GUARD) != _PATTERN
                if before or after:
                    self.outside_total += 1
                    if len(self.outside) < _KEEP:
                        self.outside.append({
                            "function": self.name, "argument": i + 1, "bytes": n,
                            "where": ("before the start and after the end" if before and after
                                      else "before the start" if before else "after the end")})
                _ct.memmove(a, base + GUARD, n)


def outside_writes(*fns):
    """What the Guarded functions among `fns` saw, for a result dict."""
    gs = [f for f in fns if isinstance(f, Guarded)]
    seen = [o for g in gs for o in g.outside][:_KEEP]
    return {"calls": sum(g.calls for g in gs),
            "outside_total": sum(g.outside_total for g in gs),
            "outside": seen, "guard_bytes": GUARD}


def finding(b):
    """The finding for a result whose bounds stage failed."""
    first = b["outside"][0] if b.get("outside") else {}
    return (f"stage bounds: the library wrote outside a buffer pq-verify gave it, in "
            f"{b['outside_total']} of {b['calls']} calls (first: {first.get('function')} "
            f"argument {first.get('argument')}, a {first.get('bytes')}-byte buffer, "
            f"{first.get('where')}). That is memory corruption in the audit's own "
            f"process, so the other results may be affected too")


def print_line(b):
    """An audit's console line for its bounds check."""
    if not b["outside_total"]:
        print(f"  PASS  bounds   {b['calls']} calls, none wrote outside its buffers "
              f"({b['guard_bytes']} guard bytes each side)")
        return
    print(f"  FAIL  bounds   wrote outside a buffer in {b['outside_total']} of "
          f"{b['calls']} calls: memory corruption")
    for o in b["outside"][:3]:
        print(f"        \u2717 {o['function']} argument {o['argument']} "
              f"({o['bytes']} bytes): {o['where']}")
