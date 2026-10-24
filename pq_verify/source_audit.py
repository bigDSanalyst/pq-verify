"""Source audit: CBMC and exhaustive checks of an ML-KEM library's C source.

    pq-verify --audit-source DIR

DIR holds the library's ML-KEM arithmetic in the layout of the reference
code (params.h, poly.c, ntt.c, reduce.c, verify.c and their headers), as in
PQClean's crypto_kem/ml-kem-*/clean. Nothing in it is annotated or edited:
every harness states only what FIPS 203 fixes, and pq-verify reads the
prefix the library's names carry off its own reduce.h. A library that names a
function some other way is given the name with --source-symbol ROLE=NAME
(ROLES below); its data must still be the reference code's: a `poly` of
int16_t coeffs[256], and KYBER_N, KYBER_Q in params.h with FIPS 203's values
(harness/source/pqv_fips203.h). C, not C++.

What runs, and what it means:

  CBMC, undefined behaviour   poly_reduce, ntt, poly_basemul_montgomery and
                              poly_frommsg, on every input FIPS 203 allows
                              them. Every loop has a fixed bound and is
                              unrolled completely, so a pass covers every
                              such input, not a sample.
  CBMC, int16 overflow        the same functions, for values stored in a type
                              they do not fit (implementation-defined in C).
  reachability                a false assertion at each harness's end must
                              fail, or the harness's assumptions contradict
                              each other and its passes are vacuous.
  exhaustive                  barrett_reduce on every int16, montgomery_reduce
                              on every input its contract admits, and the
                              zeta table against FIPS 203, compiled from the
                              library's own reduce.c and ntt.c.

ntt and poly_basemul_montgomery are checked with the two reductions replaced
by their contracts (harness/source/stubs.c), which the exhaustive test proves
of the compiled functions. CBMC's own self-test (harness/source/selftest.c)
and each exhaustive check's control must catch a planted defect first: a
check that cannot fail would say nothing.

Two things C leaves to the compiler, and the reductions rely on: a right
shift of a negative value, and a narrowing conversion that does not fit.
CBMC models the first as filling with the sign and the second as wrapping,
as GCC and Clang do. The self-test pins that model (selftest_model) and the
exhaustive test checks the compiler in use does the same; either failing is
CANNOT VERIFY, since the proofs hold only for such a compiler.

Each CBMC run is limited to --audit-timeout seconds and MEMORY_GB of address
space, solver included; one that runs out of either decided nothing.

What would make a pass vacuous is refused: a call to a function with no body
in the files compiled, which CBMC takes to do nothing, and source that could
change what a harness means (screen(): CBMC directives, the harnesses'
names, inline assembly with an instruction in it).

Verdicts: VERIFIED, FINDINGS PRESENT, or CANNOT VERIFY when a tool is
missing, the layout is not one pq-verify knows, a pass would be vacuous as
above, a self-test or control did not catch its defect, a harness end was
not reached, or a check did not finish. Not checked: any other function, functional equality with FIPS 203
(the ACVP vectors' job), strict aliasing, constant time, and the binary.
"""
import hashlib
import os
import re
import shutil
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

try:
    import resource
except ImportError:          # not on Windows; the memory cap is then not set
    resource = None

HARNESS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "harness", "source")
STUBS = os.path.join(HARNESS, "stubs.c")

# Undefined behaviour in C, and the unrolling being complete.
UB = ["--bounds-check", "--pointer-check", "--pointer-primitive-check",
      "--signed-overflow-check", "--undefined-shift-check",
      "--pointer-overflow-check", "--div-by-zero-check",
      "--unwinding-assertions"]
# A value stored in a type it does not fit: implementation-defined for a
# signed type, defined (it wraps) for an unsigned one.
CONV = ["--conversion-check"]

# function: (harness, library files, reductions as contracts?, prefer CaDiCaL?)
# CaDiCaL halves the NTT's solve time; on the others CBMC's built-in MiniSat
# is faster.
JOBS = {
    "poly_reduce": ("h_poly_reduce.c", ("poly.c", "reduce.c"), False, False),
    "ntt": ("h_ntt.c", ("ntt.c",), True, True),
    "poly_basemul_montgomery": ("h_basemul.c", ("poly.c", "ntt.c"), True, False),
    "poly_frommsg": ("h_frommsg.c", ("poly.c", "verify.c"), False, False),
}
PROFILES = ("ub", "conv", "reach")

# The files the harnesses compile or include, and the roles they call: each
# role's name is the library's prefix and the role, or what --source-symbol
# ROLE=NAME gives (pqv_ns.h's PQV_SYM_<role>).
FILES = ("params.h", "poly.h", "ntt.h", "reduce.h", "poly.c", "ntt.c", "reduce.c", "verify.c")
ROLES = ("montgomery_reduce", "barrett_reduce", "zetas", "ntt", "poly_reduce",
         "poly_basemul_montgomery", "poly_frommsg")
SETS = {"2": "ML-KEM-512", "3": "ML-KEM-768", "4": "ML-KEM-1024"}

# CBMC's own controls: (function, checks, the class it must report). None:
# nothing may be reported -- selftest_model pins CBMC's model of the
# implementation-defined behaviour the proofs rely on.
SELFTEST = (("selftest_bounds", UB, "undefined behaviour"),
            ("selftest_signed_overflow", UB, "undefined behaviour"),
            ("selftest_narrowing", UB + CONV, "implementation-defined"),
            ("selftest_model", UB, None),
            ("selftest_no_body", UB, "no body"))

# Address space for each CBMC run, solver included. The NTT, the largest,
# needs about 1.5 GB; a runaway run stops here instead of taking the machine.
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
    n for f in sorted(os.listdir(HARNESS)) if f.endswith((".c", ".h"))
    for n in re.findall(r"\b(nondet_\w+)\s*\(",
                        open(os.path.join(HARNESS, f), encoding="utf-8").read()))


class Unavailable(Exception):
    """The audit cannot decide: CANNOT VERIFY, with the reason."""


def detect(src, includes=(), symbols=None):
    """The library's layout: its parameter set, the prefix its names carry,
    and the names given for roles it calls something else (symbols, from
    --source-symbol). Raises Unavailable for a layout pq-verify does not know."""
    if not os.path.isdir(src):
        raise Unavailable(f"{src} is not a directory")
    missing = [f for f in FILES if not os.path.isfile(os.path.join(src, f))]
    if missing:
        raise Unavailable("not an ML-KEM source layout pq-verify knows (the reference "
                          f"code's, as in PQClean): missing {', '.join(missing)}")
    text = {f: open(os.path.join(src, f), encoding="utf-8", errors="replace").read()
            for f in FILES}
    symbols = dict(symbols or {})
    unknown = sorted(set(symbols) - set(ROLES))
    if unknown:
        raise Unavailable(f"--source-symbol: no role {', '.join(unknown)}; the roles are "
                          + ", ".join(ROLES))
    blob = "\n".join(text.values())
    # The prefix, from the first role the library declares under its usual name.
    headers = text["reduce.h"] + text["ntt.h"] + text["poly.h"]
    prefix = None
    for role in (r for r in ROLES if r not in symbols):
        m = re.search(r"\b(\w*?)" + role + (r"\s*\[" if role == "zetas" else r"\s*\("), headers)
        if m:
            prefix = m.group(1)
            break
    if prefix is None:
        if len(symbols) != len(ROLES):
            raise Unavailable("the headers declare none of " + ", ".join(
                r for r in ROLES if r not in symbols) + " (name each with --source-symbol "
                "ROLE=NAME)")
        prefix = ""

    def present(role):
        if role in symbols:
            return re.search(r"\b" + re.escape(symbols[role]) + r"\b", blob)
        return (re.search(r"\b" + re.escape(prefix + role) + r"\b", blob)
                or re.search(r"#define\s+" + role + r"\b", blob))
    absent = [r for r in ROLES if not present(r)]
    if absent:
        raise Unavailable(f"names not found with prefix {prefix!r}: {', '.join(absent)} "
                          "(name each with --source-symbol ROLE=NAME)")
    k = re.search(r"#define\s+KYBER_K\s+(\d)", text["params.h"])
    inc = [os.path.abspath(i) for i in includes]
    # PQClean keeps fips202.h and randombytes.h three levels up, in common/.
    common = os.path.normpath(os.path.join(src, "..", "..", "..", "common"))
    if os.path.isdir(common) and common not in inc:
        inc.append(common)
    return {"prefix": prefix, "k": int(k.group(1)) if k else None,
            "parameter_set": SETS.get(k.group(1)) if k else None, "includes": inc,
            "symbols": symbols}


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
    cfiles = [os.path.join(src, f) for f in FILES if f.endswith(".c")]
    cmd = [cc, "-MM", *_defines(layout), "-I", src, "-I", HARNESS]
    for inc in layout["includes"]:
        cmd += ["-I", inc]
    try:
        p = subprocess.run(cmd + cfiles, capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise Unavailable(f"could not list the headers the source includes: {e}")
    if p.returncode:
        raise Unavailable("could not list the headers the source includes: "
                          + p.stderr.strip()[-300:])
    deps = re.findall(r"(?:\\ |[^\s\\])+", p.stdout.replace("\\\n", " "))
    files = {os.path.abspath(os.path.join(src, f)) for f in FILES}
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
            "cc_path": cc, "cadical": bool(shutil.which("cadical"))}


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


def selftest(timeout=600):
    """CBMC must report each planted defect of selftest.c, and nothing in
    selftest_model, which pins its model of what C leaves to the compiler; and
    pq-verify must see selftest_no_body's call to a function with no body."""
    rows = []
    for fn, checks, want in SELFTEST:
        r = _cbmc([os.path.join(HARNESS, "selftest.c"), "--function", fn, *checks], timeout)
        if want is None:
            ok = r["result"] == "VERIFIED"
        elif want == "no body":
            ok = r["result"] == "ERROR" and r["no_body"] == ["pqv_selftest_undefined"]
        else:
            ok = r["result"] == "FAILED" and any(f["class"].startswith(want)
                                                 for f in r["failed"])
        rows.append({"control": fn, "ok": ok, "result": r["result"]})
    return rows


def check(src, layout, job, profile, timeout=3600, cadical=False, memory_gb=MEMORY_GB):
    """One CBMC run: a function's harness under one profile."""
    harness, files, stubbed, prefer_cadical = JOBS[job]
    args = [os.path.join(HARNESS, harness)] + [os.path.join(src, f) for f in files]
    if stubbed:
        args.append(STUBS)
    args += ["-I", src, "-I", HARNESS, *_defines(layout),
             "--function", "harness", "--drop-unused-functions"]
    for inc in layout["includes"]:
        args += ["-I", inc]
    if profile == "reach":
        args += ["-DPQV_REACH", "--stop-on-fail"]
    else:
        args += UB + (CONV if profile == "conv" else [])
        if prefer_cadical and cadical:
            args += ["--external-sat-solver", "cadical"]
    r = _cbmc(args, timeout, memory_gb)
    r.update(function=job, profile=profile, contracts=stubbed)
    return r


def exhaustive(src, layout, cc, timeout=1200):
    """Build and run harness/source/exhaustive.c against the library."""
    work = tempfile.mkdtemp(prefix="pqv-source-")
    exe = os.path.join(work, "exhaustive")
    base = [cc, "-O2", *_defines(layout), "-I", HARNESS, "-I", src]
    for inc in layout["includes"]:
        base += ["-I", inc]
    srcs = [os.path.join(HARNESS, "exhaustive.c"), os.path.join(src, "reduce.c"),
            os.path.join(src, "ntt.c")]
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


def judge(src, checks, ex):
    """(findings, notes, cannot): what the runs show about the library."""
    findings, notes, cannot = [], [], []
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
        if set(ex["controls"]) != {"barrett_reduce", "montgomery_reduce", "zetas"} \
                or not all(ex["controls"].values()):
            cannot.append("an exhaustive check's control was not caught, so the check "
                          "could not have failed")
        if len(ex["checks"]) != 3:
            cannot.append("not every exhaustive check ran")
        model = ex.get("model") or {}
        if set(model) != {"arithmetic_shift", "narrowing_wraps"} or not all(model.values()):
            cannot.append("this compiler does not do what CBMC's model assumes "
                          f"({', '.join(k for k, v in model.items() if not v) or 'not checked'}): "
                          "a right shift of a negative value filling with its sign, and a "
                          "narrowing conversion wrapping. The proofs hold only for one that does")
        if ex.get("ubsan_report"):
            findings.append("source: reduce.c: UBSan reported undefined behaviour in the "
                            f"exhaustive run: {ex['ubsan_report'][:200]}")
        for name, c in ex["checks"].items():
            if c["wrong"]:
                findings.append(f"source: {'ntt.c' if name == 'zetas' else 'reduce.c'}: "
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
              "limits": {"timeout_s": timeout, "memory_gb": memory_gb}}
    try:
        result["tools"] = tools()
        result["layout"] = layout = detect(src, includes, symbols)
        screen(src, layout, result["tools"]["cc_path"])
    except Unavailable as e:
        result["reason"] = str(e)
        say(f"  source audit: CANNOT VERIFY -- {e}")
        return result
    say(f"  source audit of {src}")
    say(f"  {layout['parameter_set'] or 'ML-KEM'}, names prefixed {layout['prefix'] or '(none)'}; "
        f"{result['tools']['cbmc']}")
    st = result["selftest"] = selftest()
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
    todo = [(job, profile) for job in JOBS for profile in PROFILES]

    def one(task):
        r = check(src, layout, *task, timeout=timeout, cadical=result["tools"]["cadical"],
                  memory_gb=memory_gb)
        say(f"  cbmc {r['function']:24} {r['profile']:5} {r['result']:9} "
            f"{r['properties']:>4} properties {len(r['failed']):>3} failed {r['seconds']:7.1f} s")
        return r
    with ThreadPoolExecutor(max_workers=jobs or min(3, os.cpu_count() or 1)) as pool:
        result["checks"] = list(pool.map(one, todo))
    findings, notes, cannot = judge(src, result["checks"], ex)
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
