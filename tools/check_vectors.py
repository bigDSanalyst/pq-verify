#!/usr/bin/env python3
"""
check_vectors.py — NIST ACVP vector drift watcher for pq-verify.

Fetches the current NIST ACVP-Server vector files, fingerprints them
(sha256 + a structural summary: per-group function / keyFormat / test count /
field names), and compares against tools/vector_state/baseline.json.

Exit codes:
  0  no change since baseline
  1  a change was detected (sha256 and/or structure differs)
  2  fetch/parse error

On change, prints a human-readable diff AND rewrites baseline.json to the new
state, so the next run compares against the latest. In CI this is wired to open
an issue (see .github/workflows/watch-nist-vectors.yml).

Why this exists: NIST edits these files periodically and the ML-KEM encapDecap
schema has oscillated between 'seed'/'expanded' keyFormats and a single 'dk'
form. pq-verify ships FROZEN vectors for determinism; this watcher tells the
maintainer WHEN upstream has changed so a new pinned snapshot can be cut
deliberately (and only once upstream has settled), rather than chasing live
edits at runtime.
"""
import urllib.request, json, hashlib, os, sys

BASE = "https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files/"
TARGETS = {
    "ML-KEM-encapDecap-FIPS203": "prompt.json",
    "ML-KEM-keyGen-FIPS203":     "prompt.json",
    "ML-DSA-sigGen-FIPS204":     "prompt.json",
    "ML-DSA-keyGen-FIPS204":     "prompt.json",
    "ML-DSA-sigVer-FIPS204":     "prompt.json",
}
STATE = os.path.join(os.path.dirname(__file__), "vector_state", "baseline.json")


def fingerprint(raw: bytes) -> dict:
    j = json.loads(raw)
    struct = []
    for g in j.get("testGroups", []):
        t0 = g["tests"][0] if g.get("tests") else {}
        struct.append({
            "function":  g.get("function"),
            "keyFormat": g.get("keyFormat"),
            "paramSet":  g.get("parameterSet"),
            "n":         len(g.get("tests", [])),
            "fields":    sorted(t0.keys()),
        })
    return {
        "sha256":      hashlib.sha256(raw).hexdigest(),
        "bytes":       len(raw),
        "total_tests": sum(len(g.get("tests", [])) for g in j.get("testGroups", [])),
        "structure":   struct,
    }


def fetch_current() -> dict:
    out = {}
    for d, f in TARGETS.items():
        raw = urllib.request.urlopen(BASE + d + "/" + f, timeout=60).read()
        out[d] = fingerprint(raw)
    return out


def describe_change(name, old, new) -> list:
    lines = []
    if old is None:
        lines.append(f"  [{name}] NEW file now tracked ({new['total_tests']} tests)")
        return lines
    if old["sha256"] == new["sha256"]:
        return lines
    lines.append(f"  [{name}] CHANGED")
    lines.append(f"      sha256 {old['sha256'][:12]} -> {new['sha256'][:12]}")
    lines.append(f"      bytes  {old['bytes']} -> {new['bytes']}")
    lines.append(f"      tests  {old['total_tests']} -> {new['total_tests']}")
    # structural delta: compare (function, keyFormat, paramSet) -> (n, fields)
    def key(s): return (s["function"], s["keyFormat"], s["paramSet"])
    o = {key(s): s for s in old["structure"]}
    n = {key(s): s for s in new["structure"]}
    for k in sorted(set(o) | set(n), key=lambda x: tuple(str(v) for v in x)):
        if k not in o:
            lines.append(f"      + group added: {k} n={n[k]['n']} fields={n[k]['fields']}")
        elif k not in n:
            lines.append(f"      - group removed: {k} n={o[k]['n']} fields={o[k]['fields']}")
        elif o[k]["fields"] != n[k]["fields"] or o[k]["n"] != n[k]["n"]:
            lines.append(f"      ~ group {k}: n {o[k]['n']}->{n[k]['n']} "
                         f"fields {o[k]['fields']} -> {n[k]['fields']}")
    return lines


def main():
    try:
        current = fetch_current()
    except Exception as e:
        print(f"ERROR fetching vectors: {type(e).__name__}: {e}")
        return 2

    baseline = {}
    if os.path.exists(STATE):
        baseline = json.load(open(STATE))

    changed = False
    report = []
    for name in TARGETS:
        delta = describe_change(name, baseline.get(name), current.get(name))
        if delta:
            changed = True
            report.extend(delta)

    if not changed:
        n = len(current)
        print(f"No change. {n} NIST vector files match baseline.")
        for name, fp in current.items():
            print(f"  {name}: sha={fp['sha256'][:12]} tests={fp['total_tests']}")
        return 0

    print("=" * 68)
    print("  NIST ACVP VECTORS CHANGED UPSTREAM")
    print("=" * 68)
    print("\n".join(report))
    print("=" * 68)
    print("ACTION: upstream has moved. Do NOT auto-update the shipped bundle.")
    print("Wait until the fingerprint is stable across several runs, then cut a")
    print("new pinned snapshot deliberately and re-verify offline before release.")

    # advance baseline so the next run diffs against the latest
    os.makedirs(os.path.dirname(STATE), exist_ok=True)
    json.dump(current, open(STATE, "w"), indent=2, sort_keys=True)
    return 1


if __name__ == "__main__":
    sys.exit(main())
