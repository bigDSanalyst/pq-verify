#!/usr/bin/env python3
"""Rebuild each pinned third-party ML-KEM library and re-run --audit-kem on it.

  python3 tools/vendor_audit.py              build every row, check its result
  python3 tools/vendor_audit.py --markdown   print the AUDITS.md table (offline)

Every input is pinned: the library to an exact commit (tools/vendor_audits.json),
the NIST vectors to the bundle pq-verify ships, the reference implementations
to constraints-reference.txt. So when a row's result differs from what the
table records, the only thing that changed is pq-verify -- a regression, or a
deliberate change that must update the table in the same PR.

This is the check that would have caught the symbol-resolution bug fixed in
2.8.1: pq-verify bound mlkem-native's internal indcpa_keypair_derand and
reported a correct library as 35/60. Its unit tests use stub libraries and
could not see it; a real, pinned library does.

EXIT  0 every row reproduces   1 a row differs   2 a library could not be built
"""
import argparse
import contextlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TABLE = REPO / "tools" / "vendor_audits.json"
STAGES = ("keyGen", "encaps", "decaps", "ekCheck", "dkCheck")
BEGIN, END = "<!-- vendor-audits:begin -->", "<!-- vendor-audits:end -->"

_RANDOMBYTES = (b"#include <stdint.h>\n#include <stddef.h>\n"
                b"int randombytes(uint8_t *o, size_t n)"
                b"{ for (size_t i = 0; i < n; i++) o[i] = (uint8_t)i; return 0; }\n")


def load_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh)["audits"]


# ─────────────────────────────── build ───────────────────────────────

def fetch(url, commit, dest):
    """Exactly `commit`, nothing newer: fetch that object and check it out."""
    run = lambda *a: subprocess.run(a, cwd=dest, check=True, capture_output=True)
    os.makedirs(dest, exist_ok=True)
    run("git", "init", "-q")
    run("git", "fetch", "-q", "--depth", "1", url, commit)
    run("git", "checkout", "-q", "FETCH_HEAD")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=dest, check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != commit:
        raise RuntimeError(f"fetched {head}, pinned {commit}")


def build(recipe, src, param_set, out_dir):
    """Compile one parameter set of a library to a shared object."""
    level = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{level}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared"]
    if recipe == "mlkem-native":
        rb = Path(out_dir) / "randombytes.c"
        rb.write_bytes(_RANDOMBYTES)
        cmd = cc + [f"-DMLK_CONFIG_PARAMETER_SET={level}", "-I", f"{src}/mlkem",
                    "-o", str(so), f"{src}/mlkem/mlkem_native.c", str(rb)]
    elif recipe == "pqclean":
        d = Path(src) / "crypto_kem" / f"ml-kem-{level}" / "clean"
        common = Path(src) / "common"
        cmd = cc + ["-I", str(common), "-o", str(so),
                    *sorted(str(p) for p in d.glob("*.c")),
                    str(common / "fips202.c"), str(common / "randombytes.c")]
    else:
        raise ValueError(f"unknown build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


# ─────────────────────────────── audit ───────────────────────────────

def audit(so, param_set):
    sys.path.insert(0, str(REPO))
    from pq_verify.core import pqverify_audit_kem
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_kem(so, param_set, verbose=False)
    if r is None:
        return None
    return {k: list(v) for k, v in r["detail"].items()}


def total(stages):
    return (sum(v[0] for v in stages.values()), sum(v[1] for v in stages.values()))


def check_all(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        want = {k: list(v) for k, v in row["expected"].items()}
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit(so, ps)
            if got == want:
                p, t = total(got)
                print(f"  ok     {label}: {p}/{t}, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in STAGES:
                if got.get(s) != want.get(s):
                    print(f"         {s:8s} recorded {want.get(s)}  now {got.get(s)}")
    if failures:
        print(f"\n  {failures} row(s) differ. pq-verify's behaviour changed against a "
              f"pinned library and pinned vectors: fix the regression, or, if the "
              f"change is intended, update tools/vendor_audits.json and AUDITS.md "
              f"in the same PR and say why.")
        return 1
    return 0


# ─────────────────────────────── table ───────────────────────────────

def markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen | encaps | decaps | ekCheck "
             "| dkCheck | Result |",
             "|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        e = row["expected"]
        p, t = total(e)
        verdict = f"**{p}/{t} VERIFIED**" if p == t else f"{p}/{t}, findings"
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        cells = [f"{e[s][0]}/{e[s][1]}" for s in STAGES]
        lines.append(f"| {row['library']} | [`{row['commit'][:7]}`]"
                     f"({row['url']}/commit/{row['commit']}) ({row['date']}) "
                     f"| {sets} | " + " | ".join(cells) + f" | {verdict} |")
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--markdown", action="store_true",
                    help="print the AUDITS.md table from the pinned rows; no build")
    ap.add_argument("--workdir", help="where to fetch and build (default: a "
                                      "temporary directory, removed afterwards)")
    a = ap.parse_args(argv)
    rows = load_table()
    if a.markdown:
        print(markdown(rows))
        return 0
    if a.workdir:
        return check_all(rows, a.workdir)
    work = tempfile.mkdtemp(prefix="pqv-vendor-")
    try:
        return check_all(rows, work)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
