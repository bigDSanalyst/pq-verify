"""Source audit: CBMC and exhaustive checks of ML-KEM and ML-DSA C source.

    pq-verify --audit-source DIR

DIR holds the library's arithmetic in the layout of the reference code, as
in PQClean's crypto_kem/ml-kem-*/clean (params.h, poly.c, ntt.c, reduce.c,
verify.c and their headers) or crypto_sign/ml-dsa-*/clean (params.h, poly.c,
ntt.c, reduce.c, rounding.c and their headers); the scheme is read off
params.h. Nothing in it is annotated or edited: every harness states only
what FIPS 203 or 204 fixes, and pq-verify reads the prefix the library's names
carry off its own headers. A library that names a function some other way is
given the name with --source-symbol ROLE=NAME (SCHEMES' roles). Its data must
still be the reference code's: a `poly` of N coefficients, and params.h with
the standard's values (harness/source/pqv_fips203.h, mldsa/pqv_fips204.h).
C, not C++.

What runs, and what it means:

  CBMC, undefined behaviour   each scheme's jobs, on every input the standard
                              gives them: the NTT (and ML-DSA's inverse), the
                              NTT-domain multiplication and the polynomial
                              reduction, each with its output bound; ML-KEM's
                              poly_frommsg, with FIPS 203's bit order; ML-DSA's
                              montgomery_reduce itself, whose int64 domain is
                              too large to enumerate, and poly_chknorm, its
                              undefined behaviour only. Every loop has a fixed
                              bound and is unrolled completely, so a pass
                              covers every such input, not a sample.
  CBMC, overflow              the same functions, for values stored in a type
                              they do not fit (implementation-defined in C).
  reachability                a false assertion at each harness's end must
                              fail, or the harness's assumptions contradict
                              each other and its passes are vacuous.
  exhaustive                  what can be enumerated, compiled from the
                              library's own files: ML-KEM's barrett_reduce and
                              montgomery_reduce and its zeta table; ML-DSA's
                              montgomery_reduce on every low word, reduce32,
                              caddq and freeze on all 2^32 inputs,
                              its zeta table, and power2round, decompose and
                              use_hint against FIPS 204's algorithms on every
                              r in [0, q).

The NTTs and the NTT-domain multiplications are checked with
montgomery_reduce (and ML-KEM's barrett_reduce) replaced by contracts (each
scheme's stubs.c). The exhaustive test proves ML-KEM's of the compiled
functions; CBMC proves ML-DSA's montgomery_reduce contract of its C. CBMC's
own self-test (harness/source/selftest.c) and each exhaustive check's control
must catch a planted defect first: a check that cannot fail would say nothing.

Two things C leaves to the compiler, and the reductions rely on: a right
shift of a negative value, and a narrowing conversion that does not fit.
CBMC models the first as filling with the sign and the second as wrapping,
as GCC and Clang do. The self-test pins that model (selftest_model) and the
exhaustive test checks the compiler in use does the same; either failing is
CANNOT VERIFY, since the proofs hold only for such a compiler.

Each CBMC run is limited to --audit-timeout seconds and MEMORY_GB of address
space, its solver capped the same; one that runs out of either decided
nothing.

What would make a pass vacuous is refused: a call to a function with no body
in the files compiled, which CBMC takes to do nothing, and source that could
change what a harness means (screen(): CBMC directives, the harnesses'
names, inline assembly with an instruction in it).

Verdicts: VERIFIED, FINDINGS PRESENT, or CANNOT VERIFY when a tool is
missing, the layout is not one pq-verify knows, a pass would be vacuous as
above, a self-test or control did not catch its defect, a harness end was
not reached, or a check did not finish. Not checked: any other function,
functional equality of the NTTs and the NTT-domain multiplications with the
standard (the ACVP vectors' job), poly_chknorm's accept/reject decision,
strict aliasing, constant time, and the binary beyond the exhaustive test.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

try:
    import resource
except ImportError:          # not on Windows; the memory cap is then not set
    resource = None

# The shared harness files (pqv_ns.h, selftest.c) and ML-KEM's; ML-DSA's are
# in mldsa/.
HARNESS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "harness", "source")

# Undefined behaviour in C, and the unrolling being complete.
UB = ["--bounds-check", "--pointer-check", "--pointer-primitive-check",
      "--signed-overflow-check", "--undefined-shift-check",
      "--pointer-overflow-check", "--div-by-zero-check",
      "--unwinding-assertions"]
# A value stored in a type it does not fit: implementation-defined for a
# signed type, defined (it wraps) for an unsigned one.
CONV = ["--conversion-check"]

PROFILES = ("ub", "conv", "reach")

# What pq-verify knows of each scheme's reference layout, as in PQClean's
# crypto_kem/ml-kem-*/clean and crypto_sign/ml-dsa-*/clean:
#   files       what the harnesses compile or include
#   headers     where the prefix the library's names carry is read
#   roles       what the harnesses call: each the prefix and the role, or what
#               --source-symbol ROLE=NAME gives (pqv_ns.h's PQV_SYM_<role>)
#   defaults    a role's name when it is not prefixed
#   jobs        function: (harness, library files, montgomery_reduce as its
#               contract?, solver, memory budget in GB, split?). The NTTs and
#               the pointwise multiplication run with Kissat: on the NTTs'
#               formulas it took half CaDiCaL's time in all, in less than half
#               its memory (SOURCE-AUDIT.md). The others run with
#               CBMC's built-in MiniSat. ML-DSA's montgomery_reduce runs with
#               Z3, which decides its shift property in seconds; Kissat takes
#               about 12 s, and MiniSat and CaDiCaL had not after ten minutes.
#               The budget is a run's measured peak, CBMC and its solver
#               together, with a margin; the scheduler keeps the runs at once
#               within the machine's memory. A split job's properties are
#               checked in groups (GROUPS, below).
#   requires    the solvers the scheme's audit cannot run without. Where one
#               a job names is missing and not required, the job runs with
#               MiniSat instead, to the same verdict more slowly, and its
#               result says which solver ran
#   exhaustive  the library files the exhaustive test is linked with
#   checks      each exhaustive check, and the file a wrong result is in
#   sets        the params.h constant naming the parameter set, and its values
SCHEMES = {
    "ML-KEM": {
        "standard": "FIPS 203",
        "dir": HARNESS,
        "files": ("params.h", "poly.h", "ntt.h", "reduce.h", "poly.c", "ntt.c", "reduce.c",
                  "verify.c"),
        "headers": ("reduce.h", "ntt.h", "poly.h"),
        "roles": ("montgomery_reduce", "barrett_reduce", "zetas", "ntt", "poly_reduce",
                  "poly_basemul_montgomery", "poly_frommsg"),
        "defaults": {},
        "requires": (),
        "jobs": {
            "poly_reduce": ("h_poly_reduce.c", ("poly.c", "reduce.c"), False, "minisat", 1.0, False),
            "ntt": ("h_ntt.c", ("ntt.c",), True, "kissat", 2.0, False),
            "poly_basemul_montgomery": ("h_basemul.c", ("poly.c", "ntt.c"), True, "minisat", 2.0, False),
            "poly_frommsg": ("h_frommsg.c", ("poly.c", "verify.c"), False, "minisat", 0.5, False),
        },
        "exhaustive": ("reduce.c", "ntt.c"),
        "checks": {"barrett_reduce": "reduce.c", "montgomery_reduce": "reduce.c",
                   "zetas": "ntt.c"},
        "sets": ("KYBER_K", {"2": "ML-KEM-512", "3": "ML-KEM-768", "4": "ML-KEM-1024"}),
        "scope": ("poly_reduce, ntt, poly_basemul_montgomery and poly_frommsg, by CBMC on "
                  "every input FIPS 203 allows them; barrett_reduce, montgomery_reduce and "
                  "the zeta table exhaustively. No other function, no functional equality "
                  "of the NTT or the NTT-domain multiplication with FIPS 203, no strict "
                  "aliasing, no timing (SOURCE-AUDIT.md)"),
    },
    "ML-DSA": {
        "standard": "FIPS 204",
        "dir": os.path.join(HARNESS, "mldsa"),
        "files": ("params.h", "poly.h", "ntt.h", "reduce.h", "rounding.h", "poly.c", "ntt.c",
                  "reduce.c", "rounding.c"),
        "headers": ("reduce.h", "ntt.h", "poly.h", "rounding.h"),
        "roles": ("montgomery_reduce", "reduce32", "caddq", "freeze", "zetas", "ntt",
                  "invntt_tomont", "poly_pointwise_montgomery", "poly_reduce", "poly_chknorm",
                  "power2round", "decompose", "use_hint"),
        # the reference keeps its zeta table static in ntt.c, and unprefixed;
        # the exhaustive test includes ntt.c to read it
        "defaults": {"zetas": "zetas"},
        "requires": ("kissat", "z3"),
        "jobs": {
            "montgomery_reduce": ("h_montgomery.c", ("reduce.c",), False, "z3", 0.5, False),
            "ntt": ("h_ntt.c", ("ntt.c",), True, "kissat", 8.0, True),
            "invntt_tomont": ("h_invntt.c", ("ntt.c",), True, "kissat", 8.0, True),
            "poly_pointwise_montgomery": ("h_pointwise.c", ("poly.c",), True, "kissat", 4.0, True),
            "poly_reduce": ("h_poly_reduce.c", ("poly.c", "reduce.c"), False, "minisat", 1.0, False),
            "poly_chknorm": ("h_chknorm.c", ("poly.c",), False, "minisat", 1.0, False),
        },
        "exhaustive": ("reduce.c", "rounding.c"),
        "checks": {"montgomery_reduce": "reduce.c", "reduce32": "reduce.c",
                   "caddq": "reduce.c", "freeze": "reduce.c",
                   "zetas": "ntt.c", "power2round": "rounding.c", "decompose": "rounding.c",
                   "use_hint": "rounding.c"},
        "sets": ("K", {"4": "ML-DSA-44", "6": "ML-DSA-65", "8": "ML-DSA-87"}),
        "scope": ("montgomery_reduce, ntt, invntt_tomont, poly_pointwise_montgomery, "
                  "poly_reduce and poly_chknorm, by CBMC on every input FIPS 204 gives "
                  "them; reduce32, caddq, freeze, the zeta table, power2round, decompose "
                  "and use_hint exhaustively, the rounding against FIPS 204's algorithms. "
                  "No other function, no functional equality of the NTTs or the pointwise "
                  "multiplication with FIPS 204, not poly_chknorm's decision itself, no "
                  "strict aliasing, no timing (SOURCE-AUDIT.md)"),
    },
}
# Every role either scheme has, for checking --source-symbol before the
# scheme is known.
ROLES = tuple(dict.fromkeys(r for sc in SCHEMES.values() for r in sc["roles"]))

# CBMC's own controls: (function, checks, the class it must report). None:
# nothing may be reported -- selftest_model pins CBMC's model of the
# implementation-defined behaviour the proofs rely on.
SELFTEST = (("selftest_bounds", UB, "undefined behaviour"),
            ("selftest_signed_overflow", UB, "undefined behaviour"),
            ("selftest_narrowing", UB + CONV, "implementation-defined"),
            ("selftest_model", UB, None),
            ("selftest_no_body", UB, "no body"))
# The same out-of-bounds write and model, through each solver other than
# MiniSat that a job runs with. A solver that could not answer SAT, or that
# answered UNSAT wrongly, would pass every proof it ran.
SOLVER_FLAGS = {"kissat": ["--external-sat-solver", "kissat"], "z3": ["--z3"]}
SOLVER_SELFTEST = (("selftest_bounds", UB, "undefined behaviour"),
                   ("selftest_model", UB, None))

# Address space for CBMC and, separately, for its solver, each run. The
# largest run, ML-DSA's inverse NTT, needs a few GB; a runaway run stops here
# instead of taking the machine.
MEMORY_GB = 8

_PROPERTY = re.compile(r"^\[(?P<id>[^\]]+)\] (?:line (?P<line>\d+) )?(?P<desc>.*): "
                       r"(?P<res>SUCCESS|FAILURE)$")
# "<file> function <name>" heads each file's properties; a warning such as
# "no body for function nondet_int16" must not be taken for one.
_GROUP = re.compile(r"^(?P<file>\S.*\.[ch]) function (?P<fn>\S+)$")
_VIOLATED_AT = re.compile(r"file (?P<file>.+?) function (?P<fn>\S+) line (?P<line>\d+)")
# CBMC takes a call to a function it has no body for to return any value and
# do nothing else, so a proof through one is vacuous: an NTT with no body
# keeps every bound its input had. Only the harnesses' own inputs, the
# nondet_ functions they declare, may have none.
_NO_BODY = re.compile(r"no body for function (\S+)")
_NONDET = frozenset(
    n for d, _, names in sorted(os.walk(HARNESS)) for f in sorted(names)
    if f.endswith((".c", ".h"))
    for n in re.findall(r"\b(nondet_\w+)\s*\(",
                        open(os.path.join(d, f), encoding="utf-8").read()))


class Unavailable(Exception):
    """The audit cannot decide: CANNOT VERIFY, with the reason."""


def _scheme(src):
    """Which scheme's reference layout src is in, read off its params.h."""
    path = os.path.join(src, "params.h")
    if not os.path.isfile(path):
        raise Unavailable("no params.h: not a source layout pq-verify knows (the reference "
                          "code's, as in PQClean's crypto_kem/ml-kem-*/clean and "
                          "crypto_sign/ml-dsa-*/clean)")
    text = open(path, encoding="utf-8", errors="replace").read()
    if re.search(r"#define\s+KYBER_\w+", text):
        return "ML-KEM"
    if re.search(r"#define\s+GAMMA2\b", text):
        return "ML-DSA"
    raise Unavailable("params.h defines neither ML-KEM's KYBER_ constants nor ML-DSA's "
                      "GAMMA2: not a source layout pq-verify knows")


def detect(src, includes=(), symbols=None):
    """The library's layout: its scheme and parameter set, the prefix its names
    carry, and the names given for roles it calls something else (symbols,
    from --source-symbol, over the scheme's defaults). Raises Unavailable for
    a layout pq-verify does not know."""
    if not os.path.isdir(src):
        raise Unavailable(f"{src} is not a directory")
    name = _scheme(src)
    sc = SCHEMES[name]
    missing = [f for f in sc["files"] if not os.path.isfile(os.path.join(src, f))]
    if missing:
        raise Unavailable(f"not an {name} source layout pq-verify knows (the reference "
                          f"code's, as in PQClean): missing {', '.join(missing)}")
    text = {f: open(os.path.join(src, f), encoding="utf-8", errors="replace").read()
            for f in sc["files"]}
    given = dict(symbols or {})
    unknown = sorted(set(given) - set(sc["roles"]))
    if unknown:
        raise Unavailable(f"--source-symbol: {name} has no role {', '.join(unknown)}; its "
                          "roles are " + ", ".join(sc["roles"]))
    symbols = dict(sc["defaults"], **given)
    blob = "\n".join(text.values())
    # The prefix, from the first role the library declares under its usual name.
    headers = "".join(text[h] for h in sc["headers"])
    prefix = None
    for role in (r for r in sc["roles"] if r not in symbols):
        m = re.search(r"\b(\w*?)" + role + (r"\s*\[" if role == "zetas" else r"\s*\("),
                      headers)
        if m:
            prefix = m.group(1)
            break
    if prefix is None:
        if len(symbols) != len(sc["roles"]):
            raise Unavailable("the headers declare none of " + ", ".join(
                r for r in sc["roles"] if r not in symbols) + " (name each with "
                "--source-symbol ROLE=NAME)")
        prefix = ""

    def present(role):
        if role in symbols:
            return re.search(r"\b" + re.escape(symbols[role]) + r"\b", blob)
        return (re.search(r"\b" + re.escape(prefix + role) + r"\b", blob)
                or re.search(r"#define\s+" + role + r"\b", blob))
    absent = [r for r in sc["roles"] if not present(r)]
    if absent:
        raise Unavailable(f"names not found with prefix {prefix!r}: {', '.join(absent)} "
                          "(name each with --source-symbol ROLE=NAME)")
    constant, sets = sc["sets"]
    k = re.search(r"#define\s+" + constant + r"\s+(\d)\b", text["params.h"])
    inc = [os.path.abspath(i) for i in includes]
    # PQClean keeps fips202.h and randombytes.h three levels up, in common/.
    common = os.path.normpath(os.path.join(src, "..", "..", "..", "common"))
    if os.path.isdir(common) and common not in inc:
        inc.append(common)
    return {"scheme": name, "prefix": prefix, "k": int(k.group(1)) if k else None,
            "parameter_set": sets.get(k.group(1)) if k else None, "includes": inc,
            "symbols": symbols}


def _includes(src, layout):
    """-I flags: the harnesses' own directories first, so that no file of the
    library can stand in for one of theirs, then the library's."""
    out = ["-I", SCHEMES[layout["scheme"]]["dir"], "-I", HARNESS, "-I", src]
    for inc in layout["includes"]:
        out += ["-I", inc]
    return out


def _defines(layout):
    """-D flags for the library's names."""
    out = [f"-DPQV_PREFIX={layout['prefix']}"]
    out += [f"-DPQV_SYM_{role}={name}" for role, name in sorted(layout["symbols"].items())]
    return out


# What the source under audit may not hold outside its comments, since each
# could change what a harness means while CBMC still says VERIFIED: CBMC's own
# directives and pragmas (an assumption can drop inputs, a pragma can turn a
# check off, a macro can redefine an assertion), the harnesses' reserved
# names, and inline assembly, which CBMC skips without a warning. An empty
# template, asm("" : "+r"(b)), is allowed: it is a compiler barrier with no
# instruction (PQClean's compat.h has one), so skipping it is exact.
_FORBIDDEN = (
    (re.compile(r"CPROVER"), "a CBMC directive, which could assume inputs away or "
                             "turn a check off"),
    (re.compile(r"\b(?:nondet_\w*|PQV_\w*)"), "a name the harnesses reserve"),
    (re.compile(r"\b(?:asm|__asm|__asm__)\b"), "inline assembly, which CBMC skips "
                                              "without a warning"),
)
_EMPTY_ASM = re.compile(r"(?:\s*\b(?:volatile|__volatile__|__volatile|inline|goto)\b)*"
                        r"\s*\(\s*\"\"\s*[:)]")


def _code(text):
    """C source without its comments, each line where it was."""
    text = re.sub(r"/\*.*?\*/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def screen(src, layout, cc):
    """Every file of the library the checks compile, and every header those
    include outside the system's: none may hold what _FORBIDDEN lists.
    Raises Unavailable, naming the file and line."""
    files = SCHEMES[layout["scheme"]]["files"]
    cfiles = [os.path.join(src, f) for f in files if f.endswith(".c")]
    cmd = [cc, "-MM", *_defines(layout), *_includes(src, layout)]
    try:
        p = subprocess.run(cmd + cfiles, capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise Unavailable(f"could not list the headers the source includes: {e}")
    if p.returncode:
        raise Unavailable("could not list the headers the source includes: "
                          + p.stderr.strip()[-300:])
    deps = re.findall(r"(?:\\ |[^\s\\])+", p.stdout.replace("\\\n", " "))
    files = {os.path.abspath(os.path.join(src, f)) for f in files}
    files |= {os.path.abspath(d.replace("\\ ", " ")) for d in deps if not d.endswith(":")}
    mine = os.path.abspath(HARNESS) + os.sep
    for path in sorted(f for f in files if not f.startswith(mine)):
        text = _code(open(path, encoding="utf-8", errors="replace").read())
        for pattern, why in _FORBIDDEN:
            for m in pattern.finditer(text):
                if "asm" in m.group(0) and _EMPTY_ASM.match(text, m.end()):
                    continue
                line = text.count("\n", 0, m.start()) + 1
                raise Unavailable(f"{path}:{line} holds {m.group(0)!r}: {why}")


def artifact(src):
    """The audited source, bound by the SHA-256 of each file and of the list."""
    files = {}
    for name in sorted(os.listdir(src)):
        path = os.path.join(src, name)
        if os.path.isfile(path):
            with open(path, "rb") as fh:
                files[name] = hashlib.sha256(fh.read()).hexdigest()
    manifest = "".join(f"{h}  {n}\n" for n, h in files.items())
    digest = hashlib.sha256(manifest.encode()).hexdigest()
    return {"bound": True, "sha256": digest, "path": os.path.abspath(src),
            "files": files,
            "summary": f"sha256 {digest} (manifest of {len(files)} source files)",
            "detail": ("The audited source: the SHA-256 of the manifest that lists "
                       "each file in the directory with its own SHA-256.")}


def tools():
    """Versions of what the audit runs, or Unavailable."""
    cbmc = shutil.which("cbmc")
    if not cbmc:
        raise Unavailable("cbmc not in PATH (apt install cbmc)")
    cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
    if not cc:
        raise Unavailable("no C compiler in PATH")

    def first_line(cmd):
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            return (out.stdout or out.stderr).strip().splitlines()[0]
        except (OSError, subprocess.TimeoutExpired, IndexError):
            return "unknown"
    return {"cbmc": first_line([cbmc, "--version"]), "cc": first_line([cc, "--version"]),
            "cc_path": cc,
            "kissat": first_line(["kissat", "--version"]) if shutil.which("kissat") else None,
            "z3": first_line(["z3", "--version"]) if shutil.which("z3") else None}


def classify(failure):
    """What C says about a failed check."""
    if "unsigned type conversion" in failure:
        return "defined: wraps to an unsigned type"
    if "signed type conversion" in failure:
        return "implementation-defined: value does not fit the signed type"
    if "reach:" in failure:
        return "reach"
    return "undefined behaviour or a false property"


def parse(out):
    """CBMC's verdict and each failed property, with file and line."""
    failed, here = [], None
    lines = out.splitlines()
    for i, ln in enumerate(lines):
        g = _GROUP.match(ln.strip())
        if g:
            here = g.group("file")
            continue
        p = _PROPERTY.match(ln)
        if p and p.group("res") == "FAILURE":
            failed.append({"file": here, "line": int(p.group("line")) if p.group("line") else None,
                           "property": p.group("id"), "text": p.group("desc")})
        if ln.strip() == "Violated property:" and i + 2 < len(lines):
            at = _VIOLATED_AT.search(lines[i + 1])
            failed.append({"file": at.group("file") if at else None,
                           "line": int(at.group("line")) if at else None,
                           "property": None, "text": lines[i + 2].strip()})
    for f in failed:
        f["class"] = classify(f["text"])
    verdict = ("VERIFIED" if "VERIFICATION SUCCESSFUL" in out else
               "FAILED" if "VERIFICATION FAILED" in out else "ERROR")
    properties = sum(1 for ln in lines if _PROPERTY.match(ln))
    return verdict, properties, failed


def _limit(gb):
    """A preexec_fn capping the address space of CBMC and its solver."""
    if not (resource and gb):
        return None

    def cap():
        try:
            n = int(gb * (1 << 30))
            resource.setrlimit(resource.RLIMIT_AS, (n, n))
        except (ValueError, OSError):
            pass                 # a platform that does not enforce it
    return cap


def _cbmc(args, timeout, memory_gb=MEMORY_GB):
    t0 = time.monotonic()
    try:
        p = subprocess.run(["cbmc", *args], capture_output=True, text=True,
                           timeout=timeout or None, preexec_fn=_limit(memory_gb))
    except subprocess.TimeoutExpired:
        return {"result": "TIMEOUT", "properties": 0, "failed": [], "no_body": [],
                "seconds": round(time.monotonic() - t0, 1), "error": f"over {timeout} s"}
    out = p.stdout + p.stderr
    verdict, props, failed = parse(out)
    error = None
    no_body = sorted({n for n in _NO_BODY.findall(out) if n not in _NONDET})
    if no_body and verdict != "ERROR":
        verdict, error = "ERROR", (
            f"no body for {', '.join(no_body)}: its definition is in none of the files "
            "compiled, and CBMC takes a call to it to do nothing, so nothing through it "
            "is proved")
    elif verdict == "ERROR":
        if re.search(r"out of memory|bad_alloc|Cannot allocate memory", out, re.I):
            error = f"out of memory under the {memory_gb} GB limit"
        elif p.returncode < 0:
            error = f"killed by signal {-p.returncode}"
        else:
            error = out.strip()[-500:]
    return {"result": verdict, "properties": props, "failed": failed, "no_body": no_body,
            "seconds": round(time.monotonic() - t0, 1), "error": error}


def selftest(timeout=600, solvers=()):
    """CBMC must report each planted defect of selftest.c, and nothing in
    selftest_model, which pins its model of what C leaves to the compiler; and
    pq-verify must see selftest_no_body's call to a function with no body.
    solvers: the others the jobs run with (SOLVER_FLAGS), each of which must
    do the same on SOLVER_SELFTEST."""
    rows = []
    runs = [(fn, checks, want, None) for fn, checks, want in SELFTEST]
    runs += [(fn, checks, want, name) for name in solvers
             for fn, checks, want in SOLVER_SELFTEST]
    for fn, checks, want, name in runs:
        r = _cbmc([os.path.join(HARNESS, "selftest.c"), "--function", fn, *checks,
                   *SOLVER_FLAGS.get(name, [])], timeout)
        if want is None:
            ok = r["result"] == "VERIFIED"
        elif want == "no body":
            ok = r["result"] == "ERROR" and r["no_body"] == ["pqv_selftest_undefined"]
        else:
            ok = r["result"] == "FAILED" and any(f["class"].startswith(want)
                                                 for f in r["failed"])
        rows.append({"control": f"{fn} ({name})" if name else fn, "ok": ok,
                     "result": r["result"]})
    return rows


def _available_gb():
    """The memory free now, from /proc/meminfo, in GB; None where it cannot be read."""
    try:
        with open("/proc/meminfo") as fh:
            for line in fh:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / (1 << 20)
    except (OSError, ValueError, IndexError):
        pass
    return None


def _schedule(tasks, run, workers, cost, budget):
    """Run each task, at most `workers` at once and the sum of their cost (GB)
    within `budget`, the heaviest started first. One that alone exceeds the
    budget runs by itself. Results come back in the tasks' order."""
    lock = threading.Condition()
    used = [0.0]
    out = [None] * len(tasks)

    def go(i):
        c = cost(tasks[i])
        with lock:
            while used[0] > 0 and used[0] + c > budget:
                lock.wait()
            used[0] += c
        try:
            out[i] = run(tasks[i])
        finally:
            with lock:
                used[0] -= c
                lock.notify_all()
    with ThreadPoolExecutor(max_workers=workers) as pool:
        list(pool.map(go, sorted(range(len(tasks)), key=lambda i: -cost(tasks[i]))))
    return out


# A split job's properties are checked in groups, each its own CBMC run with
# the formula sliced to it. ML-DSA's NTT makes 1,024 64-bit products, and as
# one formula it is 42 million clauses; split this way, its largest part is
# 21 million. Every property is in exactly one group, checked against CBMC's
# own list of them, so splitting can drop nothing:
#   contract  montgomery_reduce's precondition (stubs.c), which needs the products
#   products  a multiplication's overflow, which needs them too
#   rest      everything else, built without the precondition
#             (-DPQV_NO_PRECONDITION), so no product is left in its formula
GROUPS = (("rest", ["-DPQV_NO_PRECONDITION"]), ("contract", []),
          ("products", ["-DPQV_NO_PRECONDITION"]))


def _group(description):
    if description.startswith("montgomery_reduce contract"):
        return "contract"
    if description.startswith("arithmetic overflow on signed *"):
        return "products"
    return "rest"


def _cbmc_json(args, what, timeout):
    """CBMC's JSON for --show-properties or --show-goto-functions, or an error string."""
    try:
        p = subprocess.run(["cbmc", *args, what, "--json-ui"], capture_output=True,
                           text=True, timeout=timeout or None, preexec_fn=_limit(MEMORY_GB))
        return json.loads(p.stdout)
    except (OSError, subprocess.TimeoutExpired, ValueError) as e:
        return f"could not run cbmc {what}: {e}"


def _properties(args, timeout):
    """The properties a run checks: {name: (description, file, line)}, or an
    error string."""
    doc = _cbmc_json(args, "--show-properties", timeout)
    if isinstance(doc, str):
        return doc
    found = {prop["name"]: (prop.get("description", ""),
                            os.path.basename(prop.get("sourceLocation", {}).get("file", "")),
                            str(prop.get("sourceLocation", {}).get("line", "")))
             for item in doc if isinstance(item, dict)
             for prop in item.get("properties", [])}
    return found or "CBMC listed no properties"


def _signed_width(t):
    """The width of signed integer type that holds every value of irep type t
    (an unsigned type needs one bit more); None for any other type."""
    try:
        w = int(t["namedSub"]["width"]["id"])
    except (KeyError, TypeError, ValueError):
        return None
    return {"signedbv": w, "unsignedbv": w + 1}.get(t.get("id"))


def _bounded_product(guard):
    """Whether an assertion's guard is not(overflow-*(cast a, cast b)) with a and
    b each widened from types narrow enough that no product can overflow:
    signed widths wa + wb <= W bound |a * b| by 2^(W-2)."""
    try:
        if guard["id"] != "not":
            return False
        (ovf,) = guard["sub"]
        if ovf["id"] != "overflow-*" or len(ovf["sub"]) != 2:
            return False
        widths, result = [], set()
        for op in ovf["sub"]:
            if op["id"] != "typecast" or op["namedSub"]["type"].get("id") != "signedbv":
                return False
            result.add(int(op["namedSub"]["type"]["namedSub"]["width"]["id"]))
            (inner,) = op["sub"]
            widths.append(_signed_width(inner["namedSub"]["type"]))
        (wide,) = result
        return None not in widths and max(widths) < wide and sum(widths) <= wide
    except (KeyError, TypeError, ValueError):
        return False


_ASSERT_AT = re.compile(r"// \d+ file (?P<file>.+?) line (?P<line>\d+) function \S+\n"
                        r".*ASSERT .* // (?P<desc>.+?)\n?$", re.S)


def _type_bounded(args, timeout):
    """{(file, line, description)} of the multiplication overflow checks their
    operands' types alone decide: CBMC's own typed program, read structurally.
    One that any matching instruction does not show stays a check."""
    doc = _cbmc_json(args, "--show-goto-functions", timeout)
    if isinstance(doc, str):
        return set()
    safe, other = set(), set()
    for item in doc:
        for fn in (item.get("functions", []) if isinstance(item, dict) else []):
            for ins in fn.get("instructions", []):
                if ins.get("instructionId") != "ASSERT":
                    continue
                m = _ASSERT_AT.search(ins.get("instruction", ""))
                if m:
                    key = (os.path.basename(m.group("file")), m.group("line"),
                           m.group("desc").strip())
                    (safe if _bounded_product(ins.get("guard")) else other).add(key)
    return safe - other


def _split(args, timeout, memory_gb, profile="ub"):
    """One profile of a split job: a CBMC run per group, then one result. The
    conv profile adds only conversion checks, which fall in the rest group;
    the contract and products groups are the ub profile's, verdict for
    verdict, so it does not run them again."""
    full = _properties(args, timeout)
    lean = _properties(args + ["-DPQV_NO_PRECONDITION"], timeout)
    for listing in (full, lean):
        if isinstance(listing, str):
            return {"result": "ERROR", "properties": 0, "failed": [], "no_body": [],
                    "seconds": 0.0, "error": listing}
    groups = {g: sorted(n for n, (d, _, _) in (full if g == "contract" else lean).items()
                        if _group(d) == g) for g, _ in GROUPS}
    # A product whose operands' types bound it cannot overflow: decided here,
    # not by the solver (an int32 by an int32 in int64 is under 2^62).
    bounded = _type_bounded(args + ["-DPQV_NO_PRECONDITION"], timeout)
    by_types = [n for n in groups["products"] if (lean[n][1], lean[n][2], lean[n][0]) in bounded]
    groups["products"] = [n for n in groups["products"] if n not in by_types]
    covered = [n for g in groups.values() for n in g] + by_types
    # Each name taken from the lean build must be the same property in the
    # full one: same description, file and line.
    renamed = [n for g, names in groups.items() if g != "contract"
               for n in names + (by_types if g == "products" else [])
               if full.get(n) != lean[n]]
    if sorted(covered) != sorted(full) or renamed:
        return {"result": "ERROR", "properties": 0, "failed": [], "no_body": [],
                "seconds": 0.0, "error": "the property groups do not cover every property "
                "exactly once, so a split run could miss one"}
    runs = []
    for g, extra in GROUPS:
        if profile == "conv" and g != "rest":
            continue
        if groups[g]:
            chosen = [a for n in groups[g] for a in ("--property", n)]
            r = _cbmc(args + extra + chosen + ["--slice-formula"], timeout, memory_gb)
            runs.append((g, r))
    out = {"result": "VERIFIED", "properties": sum(r["properties"] for _, r in runs),
           "failed": [f for _, r in runs for f in r["failed"]],
           "no_body": sorted({n for _, r in runs for n in r["no_body"]}),
           "seconds": round(sum(r["seconds"] for _, r in runs), 1), "error": None,
           "groups": {g: {"result": r["result"], "properties": r["properties"],
                          "seconds": r["seconds"]} for g, r in runs},
           "by_types": by_types}
    bad = [(g, r) for g, r in runs if r["result"] in ("ERROR", "TIMEOUT")]
    if bad:
        g, r = bad[0]
        out["result"], out["error"] = r["result"], f"{g} group: {r['error']}"
    elif any(r["result"] == "FAILED" for _, r in runs):
        out["result"] = "FAILED"
    return out


# Where to get each solver a job can name, for the message when it is missing.
# MiniSat is CBMC's own.
GET = {"kissat": "build it from github.com/arminbiere/kissat, as SOURCE-AUDIT.md says",
       "z3": "apt install z3"}


def check(src, layout, job, profile, timeout=3600, kissat=None, memory_gb=MEMORY_GB,
          z3=None):
    """One CBMC run: a function's harness under one profile. kissat and z3:
    whether each is installed, None to look in PATH. The result names the
    solver that ran."""
    sc = SCHEMES[layout["scheme"]]
    here = sc["dir"]
    harness, files, stubbed, solver, _, split = sc["jobs"][job]
    have = {"minisat": True,
            "kissat": kissat if kissat is not None else bool(shutil.which("kissat")),
            "z3": z3 if z3 is not None else bool(shutil.which("z3"))}
    if not have[solver]:
        if solver in sc["requires"]:
            return {"result": "ERROR", "properties": 0, "failed": [], "no_body": [],
                    "seconds": 0.0, "function": job, "profile": profile, "contracts": stubbed,
                    "solver": None,
                    "error": f"{solver} not in PATH ({GET[solver]}): {job}'s proof needs it"}
        solver = "minisat"          # the same verdict, more slowly; the result says so
    args = [os.path.join(here, harness)] + [os.path.join(src, f) for f in files]
    if stubbed:
        args.append(os.path.join(here, "stubs.c"))
    args += [*_includes(src, layout), *_defines(layout),
             "--function", "harness", "--drop-unused-functions"]
    if profile == "reach":
        args += ["-DPQV_REACH", "--stop-on-fail"]
    else:
        args += UB + (CONV if profile == "conv" else [])
    if solver == "kissat":
        args += ["--external-sat-solver", "kissat"]
    elif solver == "z3":
        args += ["--z3"]
    if split and profile == "reach":
        # Only the reach assertion. An assertion does not restrict what is
        # reachable, so the precondition is left out, and with it the products.
        args += ["-DPQV_NO_PRECONDITION"]
        reach = _properties(args, timeout)
        if isinstance(reach, str):
            r = {"result": "ERROR", "properties": 0, "failed": [], "no_body": [],
                 "seconds": 0.0, "error": reach}
        else:
            chosen = [a for n, (d, _, _) in reach.items() if d.startswith("reach:")
                      for a in ("--property", n)]
            r = (_cbmc(args + chosen + ["--slice-formula"], timeout, memory_gb) if chosen
                 else {"result": "ERROR", "properties": 0, "failed": [], "no_body": [],
                       "seconds": 0.0, "error": "the harness has no reach assertion"})
    elif split:
        r = _split(args, timeout, memory_gb, profile)
    else:
        r = _cbmc(args, timeout, memory_gb)
    r.update(function=job, profile=profile, contracts=stubbed, solver=solver)
    return r


def exhaustive(src, layout, cc, timeout=1200):
    """Build and run the scheme's exhaustive.c against the library."""
    sc = SCHEMES[layout["scheme"]]
    work = tempfile.mkdtemp(prefix="pqv-source-")
    exe = os.path.join(work, "exhaustive")
    base = [cc, "-O2", *_defines(layout), *_includes(src, layout)]
    srcs = [os.path.join(sc["dir"], "exhaustive.c")] + [os.path.join(src, f)
                                                         for f in sc["exhaustive"]]
    ubsan = True
    build = subprocess.run(base + ["-fsanitize=undefined", "-fno-sanitize-recover=all",
                                   "-o", exe] + srcs, capture_output=True, text=True)
    if build.returncode:
        ubsan = False
        build = subprocess.run(base + ["-o", exe] + srcs, capture_output=True, text=True)
    try:
        if build.returncode:
            return {"error": "the exhaustive test does not build against this source: "
                             + build.stderr.strip()[-400:]}
        t0 = time.monotonic()
        try:
            p = subprocess.run([exe], capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return {"error": f"the exhaustive test ran over {timeout} s"}
        res = {"seconds": round(time.monotonic() - t0, 1), "exit": p.returncode,
               "ubsan": ubsan, "ubsan_report": p.stderr.strip()[-400:] or None,
               "checks": {}, "controls": {}, "model": {}}
        for line in p.stdout.splitlines():
            m = re.match(r"(\w+) (\d+) (?:inputs|entries) (\d+) wrong(?: first (-?\d+))?$", line)
            if m:
                res["checks"][m.group(1)] = {"cases": int(m.group(2)), "wrong": int(m.group(3)),
                                             "first": int(m.group(4)) if m.group(4) else None}
            c = re.match(r"control (\w+) (ok|FAILED)$", line)
            if c:
                res["controls"][c.group(1)] = c.group(2) == "ok"
            d = re.match(r"model (\w+) (ok|DIFFERENT)$", line)
            if d:
                res["model"][d.group(1)] = d.group(2) == "ok"
        return res
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _where(f):
    name = os.path.basename(f["file"]) if f.get("file") else "?"
    return f"{name}:{f['line']}" if f.get("line") else name


def judge(src, checks, ex, scheme="ML-KEM"):
    """(findings, notes, cannot): what the runs show about the library."""
    findings, notes, cannot = [], [], []
    expected = SCHEMES[scheme]["checks"]
    for r in checks:
        tag = f"{r['function']} ({r['profile']})"
        if r["result"] in ("ERROR", "TIMEOUT"):
            cannot.append(f"{tag}: CBMC {r['result'].lower()}: {(r.get('error') or '')[:200]}")
            continue
        if r["profile"] == "reach":
            # Nothing violated means the false assertion at the end held: no
            # input reaches it. Another property violated first is a failure
            # the other profiles report.
            if r["result"] == "VERIFIED":
                cannot.append(f"{r['function']}: no input reaches the harness's end, so its "
                              "assumptions contradict each other and its passes are vacuous")
            continue
        for f in r["failed"]:
            where = _where(f)
            if f["class"].startswith("undefined"):
                findings.append(f"source: {where}: undefined behaviour or a broken bound in "
                                f"{r['function']}: {f['text']}")
            elif r["contracts"]:
                # with the reductions as contracts, a value that does not fit is
                # the function's own arithmetic overflowing a coefficient
                findings.append(f"source: {where}: a value does not fit its type in "
                                f"{r['function']}: {f['text']}")
            elif f["class"].startswith("defined"):
                notes.append(f"{where}: {f['class']}, in {r['function']}'s path: {f['text']}")
            else:
                notes.append(f"{where}: {f['class']}, in {r['function']}'s path: {f['text']}. "
                             "Its results were checked with the value wrapped, as GCC and "
                             "Clang do")
    if "error" in ex:
        cannot.append(ex["error"])
    else:
        if set(ex["controls"]) != set(expected) or not all(ex["controls"].values()):
            cannot.append("an exhaustive check's control was not caught, so the check "
                          "could not have failed")
        if set(ex["checks"]) != set(expected):
            cannot.append("not every exhaustive check ran")
        model = ex.get("model") or {}
        if set(model) != {"arithmetic_shift", "narrowing_wraps"} or not all(model.values()):
            cannot.append("this compiler does not do what CBMC's model assumes "
                          f"({', '.join(k for k, v in model.items() if not v) or 'not checked'}): "
                          "a right shift of a negative value filling with its sign, and a "
                          "narrowing conversion wrapping. The proofs hold only for one that does")
        if ex.get("ubsan_report"):
            at = re.search(r"([\w.-]+\.[ch]):(\d+):\d+: runtime error", ex["ubsan_report"])
            findings.append(f"source: {at.group(1) + ':' + at.group(2) if at else 'the library'}"
                            ": UBSan reported undefined behaviour in the exhaustive run: "
                            f"{ex['ubsan_report'][:200]}")
        for name, c in ex["checks"].items():
            if c["wrong"]:
                findings.append(f"source: {expected.get(name, 'the library')}: "
                                f"{name}: {c['wrong']} of {c['cases']} wrong, first at "
                                f"{c['first']}")
    return findings, notes, cannot


def pqverify_audit_source(src, includes=(), symbols=None, jobs=None, timeout=3600,
                          memory_gb=MEMORY_GB, verbose=True):
    """Audit src. Returns the result dict the report is built from."""
    src = os.path.abspath(src)
    def say(*a):
        if verbose:
            print(*a, flush=True)
    result = {"source": src, "status": "CANNOT VERIFY", "verified": False,
              "findings": [], "notes": [], "checks": [], "exhaustive": None,
              "selftest": None, "layout": None, "tools": None, "reason": None,
              "artifact": artifact(src) if os.path.isdir(src) else None,
              "limits": {"timeout_s": timeout, "memory_gb": memory_gb},
              "scheme": None, "scope": None}
    try:
        result["tools"] = tools()
        result["layout"] = layout = detect(src, includes, symbols)
        screen(src, layout, result["tools"]["cc_path"])
    except Unavailable as e:
        result["reason"] = str(e)
        say(f"  source audit: CANNOT VERIFY -- {e}")
        return result
    sc = SCHEMES[layout["scheme"]]
    result["scheme"], result["scope"] = layout["scheme"], sc["scope"]
    missing = [n for n in sc["requires"] if not result["tools"][n]]
    if missing:
        result["reason"] = (f"{layout['scheme']}'s proofs need " + " and ".join(
            f"{n} ({GET[n]})" for n in missing) + " in PATH")
        say(f"  source audit: CANNOT VERIFY -- {result['reason']}")
        return result
    say(f"  source audit of {src}")
    say(f"  {layout['parameter_set'] or layout['scheme']}, names prefixed "
        f"{layout['prefix'] or '(none)'}; {result['tools']['cbmc']}")
    used = sorted({j[3] for j in sc["jobs"].values()} & set(SOLVER_FLAGS))
    st = result["selftest"] = selftest(solvers=[n for n in used if result["tools"][n]])
    if not all(r["ok"] for r in st):
        missed = ", ".join(r["control"] for r in st if not r["ok"])
        result["reason"] = (f"CBMC's self-test failed: {missed} (a planted defect not "
                            "reported, or its model is not the one the proofs assume)")
        say(f"  source audit: CANNOT VERIFY -- {result['reason']}")
        return result
    say("  CBMC self-test: each planted defect reported, and its model is the one assumed")
    ex = result["exhaustive"] = exhaustive(src, layout, result["tools"]["cc_path"])
    for name, c in (ex.get("checks") or {}).items():
        say(f"  exhaustive {name:18} {c['cases']:>10} cases {c['wrong']:>6} wrong")
    todo = [(job, profile) for job in sc["jobs"] for profile in PROFILES]

    def one(task):
        r = check(src, layout, *task, timeout=timeout, kissat=bool(result["tools"]["kissat"]),
                  memory_gb=memory_gb, z3=bool(result["tools"]["z3"]))
        say(f"  cbmc {r['function']:24} {r['profile']:5} {r['result']:9} "
            f"{r['properties']:>4} properties {len(r['failed']):>3} failed {r['seconds']:7.1f} s"
            f"  {r['solver'] or ''}")
        return r
    # Several CBMC runs at once, as many as the machine's memory holds: each
    # job's peak, solver included, is budgeted in its scheme's table. ML-DSA's
    # NTTs are budgeted at 8 GB each, so on a 16 GB machine no two run at once.
    free = _available_gb()
    budget = 0.8 * free if free else 12.0
    result["limits"]["parallel_gb"] = round(budget, 1)
    result["checks"] = _schedule(todo, one, jobs or min(3, os.cpu_count() or 1),
                                 lambda task: sc["jobs"][task[0]][4], budget)
    findings, notes, cannot = judge(src, result["checks"], ex, layout["scheme"])
    result["findings"], result["notes"] = findings, notes
    # A finding stands on a check whose controls passed; what could not be
    # decided is still said, beside it.
    result["reason"] = "; ".join(cannot) or None
    result["status"] = ("FINDINGS PRESENT" if findings else
                        "CANNOT VERIFY" if cannot else "VERIFIED")
    result["verified"] = result["status"] == "VERIFIED"
    for f in findings:
        say(f"  FINDING: {f}")
    for n in notes:
        say(f"  note: {n}")
    say(f"  source audit: {result['status']}"
        + (f" -- {result['reason']}" if result["reason"] else ""))
    return result
