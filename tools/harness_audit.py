#!/usr/bin/env python3
"""Rebuild Crucible's harnesses at a pinned commit and re-audit through them.

  python3 tools/harness_audit.py              build every harness, check results
  python3 tools/harness_audit.py --markdown   print the AUDITS.md table (offline)

Each harness in tools/harness_audits.json is built unmodified from Crucible's
pinned commit with the pinned Go toolchain (GOTOOLCHAIN), and audited with
`--audit-harness` for every parameter set its row records. The status, every
stage count and the not-applicable count must match. Inputs are pinned
(Crucible's commit, Go's version, each harness's go.sum, pq-verify's
vectors), so a difference means pq-verify's behaviour changed.

EXIT  0 every result reproduces   1 a result differs   2 a harness could not be built
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
TABLE = REPO / "tools" / "harness_audits.json"
BEGIN, END = "<!-- harness-audits:begin -->", "<!-- harness-audits:end -->"
sys.path.insert(0, str(REPO / "tools"))
from vendor_audit import fetch                                     # noqa: E402


def load(path=TABLE):
    with open(path) as fh:
        return json.load(fh)


def build(src, row, go, out):
    exe = Path(out) / f"harness-{row['name']}"
    env = dict(os.environ, GOTOOLCHAIN=f"go{go}", GOFLAGS="-mod=readonly")
    subprocess.run(["go", "build", "-o", str(exe), "."], cwd=Path(src) / row["dir"],
                   env=env, check=True, capture_output=True)
    return str(exe)


def audit(exe, ps):
    sys.path.insert(0, str(REPO))
    from pq_verify.harness_audit import pqverify_audit_harness
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_harness([exe], ps, verbose=False)
    return {"status": r["status"], "stages": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"]}


def check(table, work):
    src = Path(work) / "crucible"
    c = table["crucible"]
    try:
        if not (src / ".git").exists():
            fetch(c["url"], c["commit"], src)
    except Exception as e:
        print(f"  ERROR  Crucible @ {c['commit'][:7]}: fetch failed: {e}")
        return 2
    failures = 0
    for row in table["harnesses"]:
        try:
            exe = build(src, row, table["go"], work)
        except subprocess.CalledProcessError as e:
            print(f"  ERROR  {row['name']}: build failed\n{e.stderr.decode()[-2000:]}")
            return 2
        for ps, want in row["results"].items():
            got = audit(exe, ps)
            label = f"{row['implementation']} {ps}"
            if got == want:
                p = sum(v[0] for v in got["stages"].values())
                t = sum(v[1] for v in got["stages"].values())
                print(f"  ok     {label}: {got['status']} {p}/{t}, "
                      f"{got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}: recorded {want['status']}, now {got['status']}")
            for s in sorted(set(got["stages"]) | set(want["stages"])):
                if got["stages"].get(s) != want["stages"].get(s):
                    print(f"         {s:16s} recorded {want['stages'].get(s)}  "
                          f"now {got['stages'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
    if failures:
        print(f"\n  {failures} harness result(s) differ. Fix the regression, or, if "
              f"intended, update tools/harness_audits.json and AUDITS.md in the "
              f"same PR and say why.")
        return 1
    return 0


def markdown(table):
    lines = ["| Implementation (harness) | Parameter set | Result | Checks | Not applicable |",
             "|---|---|---|---|---|"]
    for row in table["harnesses"]:
        for ps, r in row["results"].items():
            p = sum(v[0] for v in r["stages"].values())
            t = sum(v[1] for v in r["stages"].values())
            status = f"**{r['status']}**" if r["status"] == "VERIFIED" else r["status"]
            lines.append(f"| {row['implementation']} (`{row['dir']}`) | {ps} | {status} "
                         f"| {p:,}/{t:,} | {r['not_applicable']:,} |")
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--markdown", action="store_true",
                    help="print the AUDITS.md table from the pinned rows; no build")
    ap.add_argument("--workdir", help="where to fetch and build (default: temporary)")
    a = ap.parse_args(argv)
    table = load()
    if a.markdown:
        print(markdown(table))
        return 0
    if a.workdir:
        return check(table, a.workdir)
    work = tempfile.mkdtemp(prefix="pqv-harness-")
    try:
        return check(table, work)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
