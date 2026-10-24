"""Re-run --audit-source on PQClean's ML-KEM, and require each mutant to be caught.

    python3 tools/source_audit.py [--sets 512,768,1024] [--src DIR] [--no-mutants]

CI runs this (vendor-audits.yml). PQClean is fetched at the commit
tools/vendor_audits.json pins for the vendor audits, so the source is the
same every run and a change in a verdict is a change in pq-verify. Each set
must come out VERIFIED. Then each mutant, one planted bug applied as an exact
edit to a copy of ML-KEM-768, must fail the check named for it: one that
passes is a bug class the source audit cannot see. The last hides the NTT's
body, which CBMC would take to do nothing, and must be refused. Exit status
0 only if all of this holds.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The installed package when there is one, so CI checks the harness files
# ship with it; otherwise the checkout this script is in.
try:
    from pq_verify import source_audit as sa
except ImportError:
    sys.path.insert(0, ROOT)
    from pq_verify import source_audit as sa

# One deliberate bug each, as an exact edit of PQClean's ML-KEM-768 source,
# and the check that must catch it: (function, profile) of a CBMC run, or
# ("exhaustive", check).
MUTANTS = [
    {"name": "poly_frommsg reads and writes past its arrays",
     "file": "poly.c",
     "find": "    for (i = 0; i < KYBER_N / 8; i++) {\n        for (j = 0; j < 8; j++) {\n"
             "            r->coeffs[8 * i + j] = 0;",
     "replace": "    for (i = 0; i <= KYBER_N / 8; i++) {\n        for (j = 0; j < 8; j++) {\n"
                "            r->coeffs[8 * i + j] = 0;",
     "caught_by": ("poly_frommsg", "ub")},
    {"name": "the NTT butterfly without its Montgomery reduction (int16 overflow)",
     "file": "ntt.c",
     "find": "                t = fqmul(zeta, r[j + len]);",
     "replace": "                t = zeta * r[j + len];",
     "caught_by": ("ntt", "conv")},
    {"name": "basemul multiplies three factors before reducing (int32 overflow, UB)",
     "file": "ntt.c",
     "find": "    r[0]  = fqmul(a[1], b[1]);\n    r[0]  = fqmul(r[0], zeta);",
     "replace": "    r[0]  = PQCLEAN_MLKEM768_CLEAN_montgomery_reduce((int32_t)a[1] * b[1] * zeta);",
     "caught_by": ("poly_basemul_montgomery", "ub")},
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
    # Bounds and safety all hold here: only FIPS 203's bit order is wrong, so
    # only the harness's postcondition, coefficient 8i+j from bit j of byte i,
    # can see it.
    {"name": "poly_frommsg reads each byte's bits in the reverse order",
     "file": "poly.c",
     "find": "(msg[i] >> j) & 1);",
     "replace": "(msg[i] >> (7 - j)) & 1);",
     "caught_by": ("poly_frommsg", "ub")},
    # Not a bug in the arithmetic: the name the harness calls has no body in
    # the files compiled. CBMC would take the call to do nothing, and every
    # bound the input had would still hold, a vacuous pass. The run must
    # refuse it instead.
    {"name": "ntt's definition is in none of the files compiled",
     "file": "ntt.c",
     "find": "void PQCLEAN_MLKEM768_CLEAN_ntt(int16_t r[256]) {",
     "replace": "void PQCLEAN_MLKEM768_CLEAN_ntt_elsewhere(int16_t r[256]) {",
     "caught_by": ("ntt", "ub"), "refused": True},
]


def pin():
    """PQClean's url and commit, as the vendor audits pin them."""
    rows = json.load(open(os.path.join(ROOT, "tools", "vendor_audits.json")))["audits"]
    row = next(r for r in rows if r.get("build") == "pqclean")
    return row["url"], row["commit"]


def fetch(dest):
    url, commit = pin()
    subprocess.run(["git", "init", "-q", dest], check=True)
    subprocess.run(["git", "-C", dest, "fetch", "-q", "--depth", "1", url, commit], check=True)
    subprocess.run(["git", "-C", dest, "-c", "advice.detachedHead=false", "checkout", "-q",
                    "FETCH_HEAD"], check=True)
    return commit


def caught(src, mutant, includes):
    """Whether the mutant fails the check named for it, and the evidence."""
    layout = sa.detect(src, includes)
    kind, what = mutant["caught_by"]
    if kind == "exhaustive":
        ex = sa.exhaustive(src, layout, sa.tools()["cc_path"])
        c = (ex.get("checks") or {}).get(what)
        return bool(c and c["wrong"]), (f"exhaustive {what}: {c['wrong']} of {c['cases']} "
                                        f"wrong, first at {c['first']}" if c else
                                        ex.get("error", "did not run"))
    r = sa.check(src, layout, kind, what, cadical=sa.tools()["cadical"])
    if mutant.get("refused"):
        return r["result"] == "ERROR" and bool(r["no_body"]), (
            f"cbmc {kind} {what}: {r['result']}: {(r['error'] or '')[:160]}")
    want = "undefined" if what == "ub" else "implementation-defined"
    hit = [f for f in r["failed"] if f["class"].startswith(want)]
    return r["result"] == "FAILED" and bool(hit), (
        f"cbmc {kind} {what}: {r['result']}"
        + (f", {os.path.basename(hit[0]['file'] or '?')}:{hit[0]['line']} {hit[0]['text']}"
           if hit else ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--sets", default="512,768,1024")
    ap.add_argument("--src", help="a PQClean checkout to use instead of fetching the pin")
    ap.add_argument("--no-mutants", action="store_true")
    a = ap.parse_args()
    work = tempfile.mkdtemp(prefix="pqv-source-audit-")
    ok = True
    try:
        root = a.src or os.path.join(work, "pqclean")
        if not a.src:
            print(f"PQClean at {fetch(root)}", flush=True)
        for n in a.sets.split(","):
            src = os.path.join(root, "crypto_kem", f"ml-kem-{n}", "clean")
            print(f"\n== ML-KEM-{n}: {src}", flush=True)
            r = sa.pqverify_audit_source(src)
            if r["status"] != "VERIFIED":
                print(f"   ML-KEM-{n}: expected VERIFIED, got {r['status']}")
                ok = False
        if not a.no_mutants:
            clean = os.path.join(root, "crypto_kem", "ml-kem-768", "clean")
            for i, m in enumerate(MUTANTS, 1):
                dst = os.path.join(work, f"mutant{i}")
                shutil.copytree(clean, dst)
                path = os.path.join(dst, m["file"])
                text = open(path).read()
                if text.count(m["find"]) != 1:
                    print(f"mutant {i}: its edit does not apply once to {m['file']}")
                    ok = False
                    continue
                open(path, "w").write(text.replace(m["find"], m["replace"]))
                # the copy is outside PQClean's tree, so name its common/ headers
                hit, why = caught(dst, m, [os.path.join(root, "common")])
                print(f"mutant {i} ({m['name']}): {'CAUGHT' if hit else 'MISSED'}: {why}",
                      flush=True)
                ok = ok and hit
    finally:
        shutil.rmtree(work, ignore_errors=True)
    print("\nRESULT", "OK" if ok else "PROBLEMS")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
