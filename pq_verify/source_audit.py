"""Source audit: CBMC and exhaustive checks of an ML-KEM library's C source.

    pq-verify --audit-source DIR

DIR holds the library's ML-KEM arithmetic in the layout of the reference
code (params.h, poly.c, ntt.c, reduce.c, verify.c and their headers), as in
PQClean's crypto_kem/ml-kem-*/clean. Nothing in it is annotated or edited:
every harness states only what FIPS 203 fixes, and pq-verify reads the
prefix the library's names carry off its own reduce.h.

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

Verdicts: VERIFIED, FINDINGS PRESENT, or CANNOT VERIFY when a tool is
missing, the layout is not one pq-verify knows, a self-test or control did
not catch its defect, a harness end was not reached, or a check did not
finish. Not checked: any other function, functional equality with FIPS 203
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

# The files the harnesses compile or include, and the names they call.
FILES = ("params.h", "poly.h", "ntt.h", "reduce.h", "poly.c", "ntt.c", "reduce.c", "verify.c")
NAMES = ("montgomery_reduce", "barrett_reduce", "ntt", "poly_reduce",
         "poly_basemul_montgomery", "poly_frommsg", "zetas", "cmov_int16")
SETS = {"2": "ML-KEM-512", "3": "ML-KEM-768", "4": "ML-KEM-1024"}

# CBMC's own controls: (function, checks, the class it must report)
SELFTEST = (("selftest_bounds", UB, "undefined behaviour"),
            ("selftest_signed_overflow", UB, "undefined behaviour"),
            ("selftest_narrowing", UB + CONV, "implementation-defined"))

_PROPERTY = re.compile(r"^\[(?P<id>[^\]]+)\] (?:line (?P<line>\d+) )?(?P<desc>.*): "
                       r"(?P<res>SUCCESS|FAILURE)$")
# "<file> function <name>" heads each file's properties; a warning such as
# "no body for function nondet_int16" must not be taken for one.
_GROUP = re.compile(r"^(?P<file>\S.*\.[ch]) function (?P<fn>\S+)$")
_VIOLATED_AT = re.compile(r"file (?P<file>.+?) function (?P<fn>\S+) line (?P<line>\d+)")


class Unavailable(Exception):
    """The audit cannot decide: CANNOT VERIFY, with the reason."""


def detect(src, includes=()):
    """The library's layout: its parameter set and the prefix its names carry.
    Raises Unavailable for a layout pq-verify does not know."""
    if not os.path.isdir(src):
        raise Unavailable(f"{src} is not a directory")
    missing = [f for f in FILES if not os.path.isfile(os.path.join(src, f))]
    if missing:
        raise Unavailable("not an ML-KEM source layout pq-verify knows (the reference "
                          f"code's, as in PQClean): missing {', '.join(missing)}")
    text = {f: open(os.path.join(src, f), encoding="utf-8", errors="replace").read()
            for f in FILES}
    m = re.search(r"int16_t\s+(\w*?)montgomery_reduce\s*\(", text["reduce.h"])
    if not m:
        raise Unavailable("reduce.h declares no montgomery_reduce(int32_t)")
    prefix = m.group(1)
    blob = "\n".join(text.values())
    absent = [n for n in NAMES
              if not re.search(r"\b" + re.escape(prefix + n) + r"\b", blob)
              and not re.search(r"#define\s+" + n + r"\b", blob)]
    if absent:
        raise Unavailable(f"names not found with prefix {prefix!r}: {', '.join(absent)}")
    k = re.search(r"#define\s+KYBER_K\s+(\d)", text["params.h"])
    inc = [os.path.abspath(i) for i in includes]
    # PQClean keeps fips202.h and randombytes.h three levels up, in common/.
    common = os.path.normpath(os.path.join(src, "..", "..", "..", "common"))
    if os.path.isdir(common) and common not in inc:
        inc.append(common)
    return {"prefix": prefix, "k": int(k.group(1)) if k else None,
            "parameter_set": SETS.get(k.group(1)) if k else None, "includes": inc}


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


def _cbmc(args, timeout):
    t0 = time.monotonic()
    try:
        p = subprocess.run(["cbmc", *args], capture_output=True, text=True,
                           timeout=timeout or None)
    except subprocess.TimeoutExpired:
        return {"result": "TIMEOUT", "properties": 0, "failed": [],
                "seconds": round(time.monotonic() - t0, 1), "error": f"over {timeout} s"}
    out = p.stdout + p.stderr
    verdict, props, failed = parse(out)
    return {"result": verdict, "properties": props, "failed": failed,
            "seconds": round(time.monotonic() - t0, 1),
            "error": None if verdict != "ERROR" else out.strip()[-500:]}


def selftest(timeout=600):
    """CBMC must report each planted defect of selftest.c."""
    rows = []
    for fn, checks, want in SELFTEST:
        r = _cbmc([os.path.join(HARNESS, "selftest.c"), "--function", fn, *checks], timeout)
        caught = r["result"] == "FAILED" and any(f["class"].startswith(want) for f in r["failed"])
        rows.append({"control": fn, "caught": caught, "result": r["result"]})
    return rows


def check(src, layout, job, profile, timeout=3600, cadical=False):
    """One CBMC run: a function's harness under one profile."""
    harness, files, stubbed, prefer_cadical = JOBS[job]
    args = [os.path.join(HARNESS, harness)] + [os.path.join(src, f) for f in files]
    if stubbed:
        args.append(STUBS)
    args += ["-I", src, "-I", HARNESS, f"-DPQV_PREFIX={layout['prefix']}",
             "--function", "harness", "--drop-unused-functions"]
    for inc in layout["includes"]:
        args += ["-I", inc]
    if profile == "reach":
        args += ["-DPQV_REACH", "--stop-on-fail"]
    else:
        args += UB + (CONV if profile == "conv" else [])
        if prefer_cadical and cadical:
            args += ["--external-sat-solver", "cadical"]
    r = _cbmc(args, timeout)
    r.update(function=job, profile=profile, contracts=stubbed)
    return r


def exhaustive(src, layout, cc, timeout=1200):
    """Build and run harness/source/exhaustive.c against the library."""
    work = tempfile.mkdtemp(prefix="pqv-source-")
    exe = os.path.join(work, "exhaustive")
    base = [cc, "-O2", f"-DPQV_PREFIX={layout['prefix']}", "-I", HARNESS, "-I", src]
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
               "checks": {}, "controls": {}}
        for line in p.stdout.splitlines():
            m = re.match(r"(\w+) (\d+) (?:inputs|entries) (\d+) wrong(?: first (-?\d+))?$", line)
            if m:
                res["checks"][m.group(1)] = {"cases": int(m.group(2)), "wrong": int(m.group(3)),
                                             "first": int(m.group(4)) if m.group(4) else None}
            c = re.match(r"control (\w+) (ok|FAILED)$", line)
            if c:
                res["controls"][c.group(1)] = c.group(2) == "ok"
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
        if ex.get("ubsan_report"):
            findings.append("source: reduce.c: UBSan reported undefined behaviour in the "
                            f"exhaustive run: {ex['ubsan_report'][:200]}")
        for name, c in ex["checks"].items():
            if c["wrong"]:
                findings.append(f"source: {'ntt.c' if name == 'zetas' else 'reduce.c'}: "
                                f"{name}: {c['wrong']} of {c['cases']} wrong, first at "
                                f"{c['first']}")
    return findings, notes, cannot


def pqverify_audit_source(src, includes=(), jobs=None, timeout=3600, verbose=True):
    """Audit src. Returns the result dict the report is built from."""
    src = os.path.abspath(src)
    def say(*a):
        if verbose:
            print(*a, flush=True)
    result = {"source": src, "status": "CANNOT VERIFY", "verified": False,
              "findings": [], "notes": [], "checks": [], "exhaustive": None,
              "selftest": None, "layout": None, "tools": None, "reason": None,
              "artifact": artifact(src) if os.path.isdir(src) else None}
    try:
        result["tools"] = tools()
        result["layout"] = layout = detect(src, includes)
    except Unavailable as e:
        result["reason"] = str(e)
        say(f"  source audit: CANNOT VERIFY -- {e}")
        return result
    say(f"  source audit of {src}")
    say(f"  {layout['parameter_set'] or 'ML-KEM'}, names prefixed {layout['prefix'] or '(none)'}; "
        f"{result['tools']['cbmc']}")
    st = result["selftest"] = selftest()
    if not all(r["caught"] for r in st):
        missed = ", ".join(r["control"] for r in st if not r["caught"])
        result["reason"] = f"CBMC's self-test missed {missed}"
        say(f"  source audit: CANNOT VERIFY -- {result['reason']}")
        return result
    say("  CBMC self-test: each planted defect reported")
    ex = result["exhaustive"] = exhaustive(src, layout, result["tools"]["cc_path"])
    for name, c in (ex.get("checks") or {}).items():
        say(f"  exhaustive {name:18} {c['cases']:>10} cases {c['wrong']:>6} wrong")
    todo = [(job, profile) for job in JOBS for profile in PROFILES]

    def one(task):
        r = check(src, layout, *task, timeout=timeout, cadical=result["tools"]["cadical"])
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
