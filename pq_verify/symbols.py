"""
pq_verify.symbols — the functions a shared library exports, per platform.

Every --audit-* path finds the vendor's entry points by name. The listing is
the one platform-specific step:

  Linux (ELF)     nm -D --defined-only: T (function), i (GNU IFUNC: CPU-
                  dispatched, common in optimised crypto) and W (weak)
  macOS (Mach-O)  nm -gU: defined globals; Mach-O prefixes C symbols with
                  an underscore, which is removed so names match ctypes

No nm at all yields an empty list: the audit then binds nothing and reports
CANNOT VERIFY, never a pass.
"""
import subprocess
import sys


def _nm(args):
    try:
        return subprocess.run(["nm", *args], capture_output=True, text=True).stdout
    except (OSError, ValueError):
        return ""


def exported_functions(path):
    """Names of the functions `path` exports, as ctypes would look them up."""
    if sys.platform == "darwin":
        out = []
        for line in _nm(["-gU", path]).splitlines():
            p = line.split()
            if len(p) == 3 and p[1] in ("T", "W"):
                name = p[2]
                out.append(name[1:] if name.startswith("_") else name)
        return out
    return [p[2] for p in (l.split() for l in _nm(["-D", "--defined-only", path]).splitlines())
            if len(p) == 3 and p[1] in ("T", "i", "W")]
