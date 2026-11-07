#!/usr/bin/env python3
"""Rebuild the pinned harnesses and re-audit through them.

  python3 tools/harness_audit.py              build every harness, check results
  python3 tools/harness_audit.py --markdown   print the AUDITS.md table (offline)

tools/harness_audits.json holds two kinds of row:
  go     one of Crucible's harnesses, built unmodified from Crucible's pinned
         commit with the pinned Go toolchain (GOTOOLCHAIN); the library behind
         it is pinned by the harness's go.sum
  java   one of pq-verify's own harnesses (pq_verify/harness/...), run with
         Java's source launcher against a library jar fetched from its pinned
         URL and checked against its pinned sha256. JAVA names the java
         executable (default: java on PATH); javac is taken from beside it.

Each is audited with `--audit-harness` for every parameter set its row
records. The status, every stage count and the not-applicable count must
match. Inputs are pinned (Crucible's commit, Go's version, each go.sum, each
jar's sha256, pq-verify's vectors), so a difference means pq-verify's
behaviour changed.

A java row's mutants each plant one bug in the library itself: one class is
recompiled from the row's pinned sources jar with the mutant's find/replace,
into a copy of the pinned jar without its signature files (a signed jar
refuses a class it did not sign). The audit must fail each mutant in the
stages it lists.

EXIT  0 every result reproduces   1 a result differs   2 a harness could not be built
"""
import argparse
import contextlib
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
import zipfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TABLE = REPO / "tools" / "harness_audits.json"
BEGIN, END = "<!-- harness-audits:begin -->", "<!-- harness-audits:end -->"
sys.path.insert(0, str(REPO / "tools"))
from vendor_audit import fetch                                     # noqa: E402


def load(path=TABLE):
    with open(path) as fh:
        return json.load(fh)


def kind(row):
    return row.get("kind", "go")


def build(src, row, go, out):
    exe = Path(out) / f"harness-{row['name']}"
    env = dict(os.environ, GOTOOLCHAIN=f"go{go}", GOFLAGS="-mod=readonly")
    subprocess.run(["go", "build", "-o", str(exe), "."], cwd=Path(src) / row["dir"],
                   env=env, check=True, capture_output=True)
    return str(exe)


# ───────────────────────────── java rows ─────────────────────────────

def java():
    j = os.environ.get("JAVA") or shutil.which("java")
    if not j:
        raise RuntimeError("no java executable: install a JDK or set JAVA")
    return j


def javac():
    beside = os.path.join(os.path.dirname(java()), "javac")
    return beside if os.path.exists(beside) else (shutil.which("javac") or beside)


def pinned(spec, work):
    """The file at spec["url"], fetched once into work and checked against
    spec["sha256"] every time it is used."""
    dest = Path(work) / "downloads" / spec["url"].rsplit("/", 1)[1]
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        for attempt in range(4):
            try:
                with urllib.request.urlopen(spec["url"], timeout=120) as r:
                    data = r.read()
                break
            except urllib.error.HTTPError as e:      # retry only rate limits and outages
                if attempt == 3 or (e.code != 429 and e.code < 500):
                    raise
            except urllib.error.URLError:
                if attempt == 3:
                    raise
            time.sleep(5 * 2 ** attempt)
        part = dest.with_name(dest.name + ".part")
        part.write_bytes(data)
        part.rename(dest)
    got = hashlib.sha256(dest.read_bytes()).hexdigest()
    if got != spec["sha256"]:
        raise RuntimeError(f"{dest.name}: sha256 {got}, pinned {spec['sha256']}")
    return dest


def java_command(row, jar):
    return [java(), "-cp", str(jar), str(REPO / row["harness"])]


def mutant_jar(jar, classes, out):
    """A copy of `jar` with the class files under `classes` in place of its
    own, and of any versioned copy of them (META-INF/versions/N/), and
    without its signature files."""
    classes = Path(classes)
    rebuilt = {p.relative_to(classes).as_posix(): p for p in classes.rglob("*.class")}
    signature = re.compile(r"META-INF/[^/]+\.(SF|RSA|DSA|EC)$")
    with zipfile.ZipFile(jar) as zin, zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as zout:
        for info in zin.infolist():
            base = re.sub(r"^META-INF/versions/\d+/", "", info.filename)
            if signature.match(info.filename) or base in rebuilt:
                continue
            zout.writestr(info, zin.read(info.filename))
        for name, path in sorted(rebuilt.items()):
            zout.write(path, name)
    return out


def java_mutant(row, m, i, work):
    """The harness command over a copy of the pinned jar with one class
    rebuilt from the pinned sources jar, with the mutant's bug planted."""
    jar, sources = pinned(row["jar"], work), pinned(row["sources"], work)
    d = Path(work) / "java-mutants" / f"{row['name']}-{i}"
    if d.exists():
        shutil.rmtree(d)
    src = d / "src" / m["file"]
    src.parent.mkdir(parents=True)
    (d / "classes").mkdir()
    with zipfile.ZipFile(sources) as z:
        text = z.read(m["file"]).decode("utf-8")
    n = text.count(m["find"])
    if n != 1:
        raise RuntimeError(f"mutant {m['name']!r}: pattern found {n} times in {m['file']}, "
                           f"expected once")
    src.write_text(text.replace(m["find"], m["replace"]), encoding="utf-8")
    subprocess.run([javac(), "-proc:none", "-nowarn", "-encoding", "UTF-8", "-cp", str(jar),
                    "-d", str(d / "classes"), str(src)], check=True, capture_output=True)
    return java_command(row, mutant_jar(jar, d / "classes", d / f"mutant-{jar.name}"))


# ───────────────────────────── the check ─────────────────────────────

def audit(cmd, ps, **kw):
    sys.path.insert(0, str(REPO))
    from pq_verify.harness_audit import pqverify_audit_harness
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_harness(list(cmd), ps, verbose=False, **kw)
    return {"status": r["status"], "stages": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"]}


def _error(label, e):
    detail = e.stderr.decode(errors="replace")[-2000:] if getattr(e, "stderr", None) else str(e)
    print(f"  ERROR  {label}: {detail}")
    return 2


def check(table, work):
    src = Path(work) / "crucible"
    c = table["crucible"]
    if any(kind(row) == "go" for row in table["harnesses"]):
        try:
            if not (src / ".git").exists():
                fetch(c["url"], c["commit"], src)
        except Exception as e:
            print(f"  ERROR  Crucible @ {c['commit'][:7]}: fetch failed: {e}")
            return 2
    if any(kind(row) == "java" for row in table["harnesses"]):
        try:
            v = subprocess.run([java(), "-version"], capture_output=True, text=True)
            lines = (v.stderr or v.stdout).splitlines()     # JAVA_TOOL_OPTIONS adds a line
            print(f"  java   {next((x for x in lines if 'version' in x), lines[0])}")
        except (RuntimeError, OSError, IndexError) as e:
            return _error("java", e)
    failures = 0
    for row in table["harnesses"]:
        try:
            cmd = ([build(src, row, table["go"], work)] if kind(row) == "go" else
                   java_command(row, pinned(row["jar"], work)))
        except (subprocess.CalledProcessError, RuntimeError, OSError) as e:
            return _error(f"{row['name']}: build failed", e)
        for ps, want in row["results"].items():
            got = audit(cmd, ps)
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
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['implementation']} mutant {m['name']!r} ({m['set']})"
            try:
                mcmd = java_mutant(row, m, i, work)
            except (subprocess.CalledProcessError, RuntimeError, OSError, KeyError) as e:
                return _error(label, e)
            got = audit(mcmd, m["set"], accumulated=0)
            missed = [f"{s} {p}/{t}" for s in m["fails"]
                      for p, t in [got["stages"].get(s, (0, 0))] if not (t and p < t)]
            if not missed:
                bad = sorted(s for s, (p, t) in got["stages"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad)}")
                continue
            failures += 1
            print(f"  MISSED {label}: {got['status']}; the audit did not fail "
                  f"{', '.join(missed)}. pq-verify cannot see this bug class through "
                  f"the harness.")
    if failures:
        print(f"\n  {failures} harness result(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/harness_audits.json and AUDITS.md in the "
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
