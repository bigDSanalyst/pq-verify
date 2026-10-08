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


def with_prefix(exported, prefix):
    """The symbols starting with `prefix` (case-sensitive), or all of them.

    A library can export several implementations of one algorithm -- liboqs
    exports its public OQS_* API and the backends behind it (mlkem-native's
    portable C and x86-64 code, both). --symbol-prefix names the one to
    audit; within it, an ambiguous role is still refused, never guessed."""
    return [e for e in exported if e.startswith(prefix)] if prefix else list(exported)


def implementation_prefixes(ambiguous, patterns):
    """The implementations behind an ambiguity, as --symbol-prefix values:
    each candidate with its role suffix (the matched pattern) removed."""
    import re
    out = set()
    for role, cands in ambiguous.items():
        pat = patterns.get(role)
        for c in cands:
            m = re.search(pat, c.lower()) if pat else None
            if m and m.start() > 0:
                p = c[:m.start()]
                out.add(p if p.endswith("_") else p + "_")
    return sorted(out)


def ambiguity_message(path, ambiguous, patterns, flag):
    """The refusal printed for an ambiguous binding: the candidates, the
    implementations to choose between, and how."""
    lines = [f"  Cannot audit {path}: more than one candidate for"]
    for role, cands in ambiguous.items():
        lines.append(f"    {role}: {', '.join(cands)}")
    prefixes = implementation_prefixes(ambiguous, patterns)
    if len(prefixes) > 1:
        lines.append("    The library exports more than one implementation. Choose one with")
        lines.extend(f"      --symbol-prefix {p}" for p in prefixes)
        lines.append(f"    or name each symbol ({flag}); pq-verify does not guess.")
    else:
        lines.append(f"    Name the symbol explicitly ({flag}) rather than let pq-verify guess.")
    return "\n".join(lines)
