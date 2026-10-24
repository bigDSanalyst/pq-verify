"""CBMC and exhaustive checks of PQClean's ML-KEM-768 (clean) arithmetic.

Proof of concept for a vendor-agnostic source audit. Nothing in the
library's source is annotated or edited: each harness states only what
FIPS 203 fixes (a polynomial is 256 coefficients; the representatives the
library may hold), and the library's names live in one header.

  python3 -I run_poc.py SRC_DIR OUT_DIR

SRC_DIR is crypto_kem/ml-kem-768/clean of a PQClean checkout. Every check
runs on the code as it is, then on each mutant (one deliberate bug), which
must fail the check named for it.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.join(HERE, "harness")
EXHAUSTIVE = os.path.join(HERE, "exhaustive", "exhaustive.c")
STUBS = os.path.join(HARNESS, "stubs.c")

# Undefined behaviour in C, and the unrolling being complete. Every check here
# is UB: a program that does it has no meaning.
UB = ["--bounds-check", "--pointer-check", "--pointer-primitive-check",
      "--signed-overflow-check", "--undefined-shift-check",
      "--pointer-overflow-check", "--div-by-zero-check",
      "--unwinding-assertions"]
# A value that does not fit the integer type it is stored in. For a signed
# type the result is implementation-defined, not undefined: GCC and Clang
# wrap, the standard does not promise it.
CONV = ["--conversion-check"]

# CaDiCaL halves the NTT's solve time (486 s against MiniSat's 896 s); on the
# others CBMC's built-in MiniSat is faster, so it is used there.
CADICAL = ["--external-sat-solver", "cadical"] if shutil.which("cadical") else []

# name: (harness, library files, the reductions as contracts?, solver)
JOBS = {
    "poly_reduce": ("h_poly_reduce.c", ["poly.c", "reduce.c"], False, []),
    "ntt": ("h_ntt.c", ["ntt.c"], True, CADICAL),
    "basemul": ("h_basemul.c", ["poly.c", "ntt.c"], True, []),
    "frommsg": ("h_frommsg.c", ["poly.c", "verify.c"], False, []),
}

# One deliberate bug each, as an exact edit of the library's source, and the
# check that must catch it.
MUTANTS = [
    {"name": "frommsg reads and writes past its arrays",
     "file": "poly.c",
     "find": "    for (i = 0; i < KYBER_N / 8; i++) {\n        for (j = 0; j < 8; j++) {\n"
             "            r->coeffs[8 * i + j] = 0;",
     "replace": "    for (i = 0; i <= KYBER_N / 8; i++) {\n        for (j = 0; j < 8; j++) {\n"
                "            r->coeffs[8 * i + j] = 0;",
     "caught_by": ("frommsg", "ub")},
    {"name": "ntt butterfly without its Montgomery reduction (int16 overflow)",
     "file": "ntt.c",
     "find": "                t = fqmul(zeta, r[j + len]);",
     "replace": "                t = zeta * r[j + len];",
     "caught_by": ("ntt", "conv")},
    {"name": "basemul multiplies three factors before reducing (int32 overflow, UB)",
     "file": "ntt.c",
     "find": "    r[0]  = fqmul(a[1], b[1]);\n    r[0]  = fqmul(r[0], zeta);",
     "replace": "    r[0]  = PQCLEAN_MLKEM768_CLEAN_montgomery_reduce((int32_t)a[1] * b[1] * zeta);",
     "caught_by": ("basemul", "ub")},
    {"name": "montgomery_reduce truncates t*q to 16 bits",
     "file": "reduce.c",
     "find": "    t = (a - (int32_t)t * KYBER_Q) >> 16;",
     "replace": "    t = (a - (int16_t)(t * KYBER_Q)) >> 16;",
     "caught_by": ("exhaustive", "montgomery_reduce")},
    {"name": "one zeta off by one",
     "file": "ntt.c",
     "find": "    -1044,  -758,  -359, -1517,",
     "replace": "    -1044,  -757,  -359, -1517,",
     "caught_by": ("exhaustive", "zetas")},
]

LINE = re.compile(r"^\[(?P<id>[^\]]+)\] (?P<desc>.*): (?P<res>SUCCESS|FAILURE)$")

# PQClean's shared headers (fips202.h, randombytes.h), set by main().
INCLUDES = []


def cbmc(src, job, profile, timeout=3600):
    harness, files, stubbed, solver = JOBS[job]
    args = ["cbmc", os.path.join(HARNESS, harness)]
    args += [os.path.join(src, f) for f in files]
    if stubbed:
        args.append(STUBS)
    args += ["-I", src, "-I", HARNESS, "--function", "harness",
             "--drop-unused-functions"]
    for inc in INCLUDES:
        args += ["-I", inc]
    if profile == "reach":
        # Only the harness's own assertions and a false one at its end, which
        # must fail: it shows the end is reachable, so the assumptions do not
        # contradict each other and no "SUCCESS" above was vacuous.
        args += ["-DPQV_REACH", "--stop-on-fail"]
    else:
        args += UB + (CONV if profile == "conv" else []) + solver
    t0 = time.monotonic()
    try:
        p = subprocess.run(args, capture_output=True, text=True, timeout=timeout)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return {"job": job, "profile": profile, "result": "TIMEOUT",
                "seconds": round(time.monotonic() - t0, 1)}
    props = [m.groupdict() for m in map(LINE.match, out.splitlines()) if m]
    failed = [f"{f['id']}: {f['desc']}" for f in props if f["res"] == "FAILURE"]
    # --stop-on-fail prints the one violated property instead of a list
    lines = out.splitlines()
    for i, ln in enumerate(lines):
        if ln.strip() == "Violated property:" and i + 2 < len(lines):
            failed.append(f"{lines[i + 1].strip()}: {lines[i + 2].strip()}")
    verdict = ("VERIFIED" if "VERIFICATION SUCCESSFUL" in out else
               "FAILED" if "VERIFICATION FAILED" in out else "ERROR")
    return {"job": job, "profile": profile, "result": verdict,
            "properties": len(props), "failed": failed,
            "classes": sorted({classify(f) for f in failed}),
            "seconds": round(time.monotonic() - t0, 1),
            "error": None if verdict != "ERROR" else out[-600:]}


def classify(failure):
    """What C says about a failed check. A conversion to an unsigned type is
    defined (it wraps), one to a signed type that does not fit is
    implementation-defined, and every other check here is undefined
    behaviour or a broken harness property."""
    if "unsigned type conversion" in failure:
        return "defined: wraps to an unsigned type"
    if "signed type conversion" in failure:
        return "implementation-defined: value does not fit the signed type"
    if "reach:" in failure:
        return "reach"
    return "undefined behaviour or a false property"


def exhaustive(src, bindir):
    exe = os.path.join(bindir, "exhaustive")
    os.makedirs(bindir, exist_ok=True)
    build = subprocess.run(["gcc", "-O2", "-fsanitize=undefined", "-fno-sanitize-recover=all",
                            "-I", src, "-o", exe, EXHAUSTIVE,
                            os.path.join(src, "reduce.c"), os.path.join(src, "ntt.c")],
                           capture_output=True, text=True)
    if build.returncode:
        return {"error": build.stderr[-600:]}
    t0 = time.monotonic()
    p = subprocess.run([exe], capture_output=True, text=True, timeout=600)
    res = {"seconds": round(time.monotonic() - t0, 1), "exit": p.returncode,
           "ubsan": p.stderr.strip()[-400:] or None, "checks": {}}
    for line in p.stdout.splitlines():
        m = re.match(r"(\w+) (\d+) (?:inputs|entries) (\d+) wrong(.*)", line)
        if m:
            res["checks"][m.group(1)] = {"cases": int(m.group(2)), "wrong": int(m.group(3)),
                                         "first": m.group(4).strip() or None}
    return res


def apply_mutant(clean, dst, mutant):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(clean, dst)
    path = os.path.join(dst, mutant["file"])
    text = open(path).read()
    n = text.count(mutant["find"])
    if n != 1:
        raise SystemExit(f"mutant {mutant['name']!r}: its find text occurs {n} times")
    open(path, "w").write(text.replace(mutant["find"], mutant["replace"]))


def run_all(src, out, label, only=None):
    """Every check, or with only=(job, profile) that check alone (a mutant's)."""
    from concurrent.futures import ThreadPoolExecutor
    res = {"cbmc": [], "exhaustive": exhaustive(src, os.path.join(out, "bin"))}
    todo = [(job, profile) for job in JOBS for profile in ("ub", "conv", "reach")
            if not only or only == (job, profile)]

    def one(task):
        r = cbmc(src, *task)
        print(f"  [{label}] {r['job']:12} {r['profile']:5} {r['result']:9} "
              f"{r.get('properties', '-'):>4} props {len(r.get('failed', [])):>3} failed "
              f"{r['seconds']:7.1f}s", flush=True)
        return r
    with ThreadPoolExecutor(max_workers=3) as pool:
        res["cbmc"] = list(pool.map(one, todo))
    ex = res["exhaustive"]
    for name, c in ex.get("checks", {}).items():
        print(f"  [{label}] exhaustive {name:18} {c['cases']:>10} cases {c['wrong']:>6} wrong",
              flush=True)
    return res


def judge_clean(res):
    """What the unmutated library must show."""
    problems = []
    for r in res["cbmc"]:
        # A check that did not finish decided nothing, whatever its profile.
        if r["result"] in ("ERROR", "TIMEOUT"):
            problems.append(f"{r['job']} {r['profile']}: {r['result']}")
            continue
        if r["profile"] == "ub" and r["result"] != "VERIFIED":
            problems.append(f"{r['job']} ub: {r['result']}")
        if r["profile"] == "reach" and (r["result"] != "FAILED" or r["classes"] != ["reach"]):
            problems.append(f"{r['job']} reach: the harness end is not shown reachable")
        # With the reductions as contracts, any value that does not fit is the
        # caller's own arithmetic overflowing a coefficient.
        if r["profile"] == "conv" and JOBS[r["job"]][2] and r["result"] != "VERIFIED":
            problems.append(f"{r['job']} conv: {r['result']} {r['failed'][:2]}")
    for name, c in res["exhaustive"].get("checks", {}).items():
        if c["wrong"]:
            problems.append(f"exhaustive {name}: {c['wrong']} wrong")
    if len(res["exhaustive"].get("checks", {})) != 3:
        problems.append("exhaustive: not all three checks ran")
    return problems


def caught(res, mutant):
    kind, what = mutant["caught_by"]
    if kind == "exhaustive":
        c = res["exhaustive"].get("checks", {}).get(what)
        return c is not None and c["wrong"] > 0, (
            f"exhaustive {what}: {c['wrong']} wrong, {c['first']}" if c else "did not run")
    r = next(r for r in res["cbmc"] if r["job"] == kind and r["profile"] == what)
    want = ("undefined behaviour or a false property" if what == "ub" else
            "implementation-defined: value does not fit the signed type")
    return r["result"] == "FAILED" and want in r.get("classes", []), (
        f"cbmc {kind} {what}: {r['result']}, " +
        ("; ".join(r["failed"][:2]) if r.get("failed") else "nothing failed"))


def main():
    src, out = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    os.makedirs(out, exist_ok=True)
    common = os.path.normpath(os.path.join(src, "..", "..", "..", "common"))
    if os.path.isdir(common):
        INCLUDES.append(common)
    def version(cmd):
        return subprocess.run(cmd, capture_output=True, text=True).stdout.strip()
    report = {"cbmc": version(["cbmc", "--version"]),
              "gcc": version(["gcc", "-dumpfullversion"]),
              "solvers": {j: (v[3][-1] if v[3] else "minisat (built in)")
                          for j, v in JOBS.items()},
              "source": src}
    print("clean library:", flush=True)
    report["clean"] = run_all(src, os.path.join(out, "clean"), "clean")
    report["clean_problems"] = judge_clean(report["clean"])
    report["mutants"] = []
    for i, m in enumerate(MUTANTS, 1):
        dst = os.path.join(out, f"mutant{i}", "src")
        apply_mutant(src, dst, m)
        print(f"mutant {i}: {m['name']}", flush=True)
        only = m["caught_by"] if m["caught_by"][0] != "exhaustive" else ("-", "-")
        res = run_all(dst, os.path.join(out, f"mutant{i}"), f"m{i}", only=only)
        ok, why = caught(res, m)
        report["mutants"].append({"name": m["name"], "caught_by": m["caught_by"],
                                  "caught": ok, "evidence": why, "results": res})
        print(f"  -> {'CAUGHT' if ok else 'MISSED'}: {why}", flush=True)
    with open(os.path.join(out, "report.json"), "w") as fh:
        json.dump(report, fh, indent=1)
    good = not report["clean_problems"] and all(m["caught"] for m in report["mutants"])
    print("RESULT", "OK" if good else "PROBLEMS", report["clean_problems"])
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
