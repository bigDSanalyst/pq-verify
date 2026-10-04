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

Why this exists: pq-verify ships a FROZEN snapshot of these vectors so results
are deterministic and offline. This watcher tells the maintainer WHEN upstream
has changed, so re-pinning is a deliberate, reviewed act rather than a live
runtime dependency. It never modifies the shipped bundle.

Three things it tracks that a naive page-watcher would miss:

1. expectedResults.json, not just prompt.json.
   prompt.json is the inputs and schema; expectedResults.json is the ground
   truth pq-verify validates AGAINST. NIST can correct an expected value
   without touching the prompt schema — in which case a prompt-only watcher
   reports "no change" while the correct answers have moved underneath the
   frozen bundle. That is precisely the failure this tool exists to prevent.

2. Oscillation vs. progress.
   ML-KEM encapDecap has flipped between 'seed'/'expanded' keyFormats and a
   single 'dk' form and back, twice within one day. Storing only the latest
   fingerprint makes a revert indistinguishable from forward movement. Since
   the policy is "wait until stable across several runs", that distinction is
   the whole decision. A per-file history of seen digests is kept, and a
   return to a known digest is reported as REVERTED with the date last seen.

3. Transient network failure.
   A single failed fetch previously returned exit 2, which in CI opens a
   spurious issue. Now retried with backoff.

State is written BEFORE the report is printed, so a broken pipe or a crash
mid-print cannot lose the baseline and cause everything to re-report.
"""
import hashlib
import json
import os
import sys
import time
import urllib.request
from datetime import datetime, timezone

BASE = ("https://raw.githubusercontent.com/usnistgov/ACVP-Server/"
        "master/gen-val/json-files/")

# directory -> files tracked within it
# Every file that is PINNED INTO THE SHIPPED BUNDLE must be watched here.
# If the bundle carries a file the watcher does not track, upstream can move
# underneath the frozen copy without anyone being told -- which is precisely
# the failure this tool exists to prevent.
#   pq_verify/vectors/acvp_vectors.json.gz and slhdsa_sig_vectors.json.gz
#   <-- keep this list in sync with them
TARGETS = {
    "ML-KEM-encapDecap-FIPS203": ["prompt.json", "expectedResults.json",
                                  "internalProjection.json"],
    "ML-KEM-keyGen-FIPS203":     ["prompt.json", "expectedResults.json",
                                  "internalProjection.json"],
    "ML-DSA-sigGen-FIPS204":     ["prompt.json", "expectedResults.json"],
    "ML-DSA-keyGen-FIPS204":     ["prompt.json", "expectedResults.json"],
    "ML-DSA-sigVer-FIPS204":     ["prompt.json", "expectedResults.json"],
    "SLH-DSA-keyGen-FIPS205":    ["prompt.json", "expectedResults.json"],
    # Pinned in pq_verify/vectors/slhdsa_sig_vectors.json.gz, verbatim.
    "SLH-DSA-sigGen-FIPS205":    ["prompt.json", "expectedResults.json"],
    "SLH-DSA-sigVer-FIPS205":    ["prompt.json", "expectedResults.json"],
    "LMS-keyGen-1.0":            ["prompt.json", "expectedResults.json"],
    "LMS-sigGen-1.0":            ["prompt.json", "expectedResults.json"],
    "LMS-sigGen-SP800-208":      ["prompt.json", "expectedResults.json"],
    "LMS-sigVer-1.0":            ["prompt.json", "expectedResults.json"],
    "LMS-sigVer-SP800-208":      ["prompt.json", "expectedResults.json"],
}

_HERE = os.path.dirname(os.path.abspath(__file__))
STATE = os.path.join(_HERE, "vector_state", "baseline.json")
HISTORY = os.path.join(_HERE, "vector_state", "history.json")
MANIFEST = os.path.join(_HERE, os.pardir, "pq_verify", "vectors",
                        "MANIFEST.json")


def _fetch(url, tries=4, delay=5.0):
    """GET with backoff. Raises only if every attempt fails."""
    last = None
    for attempt in range(tries):
        try:
            req = urllib.request.Request(
                url, headers={"User-Agent": "pq-verify-vector-watcher/2.0"})
            with urllib.request.urlopen(req, timeout=90) as r:
                return r.read()
        except Exception as exc:
            last = exc
            if attempt < tries - 1:
                time.sleep(delay * (attempt + 1))
    raise last


def fingerprint(raw):
    fp = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
    try:
        j = json.loads(raw)
    except json.JSONDecodeError:
        fp["total_tests"] = None
        fp["structure"] = []
        return fp
    struct = []
    for g in j.get("testGroups", []):
        t0 = g["tests"][0] if g.get("tests") else {}
        entry = {
            "function":  g.get("function"),
            "keyFormat": g.get("keyFormat"),
            "paramSet":  g.get("parameterSet"),
            "n":         len(g.get("tests", [])),
            "fields":    sorted(t0.keys()),
        }
        # Signature suites have several groups per parameter set, told apart
        # only by interface; without it a change report merges them.
        variant = [str(g[k]) for k in ("signatureInterface", "preHash",
                                       "deterministic") if k in g]
        if variant:
            entry["variant"] = "/".join(variant)
        struct.append(entry)
    fp["total_tests"] = sum(len(g.get("tests", []))
                            for g in j.get("testGroups", []))
    fp["structure"] = struct
    return fp


def fetch_current():
    out = {}
    for d, files in TARGETS.items():
        for f in files:
            raw = _fetch(BASE + d + "/" + f)
            out[f"{d}/{f}"] = fingerprint(raw)
            del raw                       # release before the next fetch
    return out


def describe_change(name, old, new, hist):
    lines = []
    if old is None:
        lines.append(f"  [{name}] NEW file now tracked "
                     f"({new['total_tests']} tests)")
        return lines
    if old["sha256"] == new["sha256"]:
        return lines

    seen = hist.get(name, {}).get(new["sha256"])
    if seen:
        lines.append(f"  [{name}] REVERTED to a previously-seen state")
        lines.append(f"      this sha256 was last seen {seen.get('last_seen')} "
                     f"({seen.get('count')}x before)")
        lines.append("      upstream is oscillating, not advancing "
                     "-- do NOT cut a snapshot yet")
    else:
        lines.append(f"  [{name}] CHANGED")
    lines.append(f"      sha256 {old['sha256'][:12]} -> {new['sha256'][:12]}")
    lines.append(f"      bytes  {old['bytes']} -> {new['bytes']}")
    lines.append(f"      tests  {old['total_tests']} -> {new['total_tests']}")

    def key(s):
        return (s["function"], s["keyFormat"], s["paramSet"], s.get("variant"))
    o = {key(s): s for s in old.get("structure", [])}
    n = {key(s): s for s in new.get("structure", [])}
    for k in sorted(set(o) | set(n), key=lambda x: tuple(str(v) for v in x)):
        if k not in o:
            lines.append(f"      + group added: {k} n={n[k]['n']} "
                         f"fields={n[k]['fields']}")
        elif k not in n:
            lines.append(f"      - group removed: {k} n={o[k]['n']} "
                         f"fields={o[k]['fields']}")
        elif o[k]["fields"] != n[k]["fields"] or o[k]["n"] != n[k]["n"]:
            lines.append(f"      ~ group {k}: n {o[k]['n']}->{n[k]['n']} "
                         f"fields {o[k]['fields']} -> {n[k]['fields']}")
    return lines


def bundle_behind(current, history, manifest_path=MANIFEST):
    """Compare upstream against what pq-verify actually SHIPS.

    The baseline records what the watcher last saw upstream; it says nothing
    about the bundle. If the baseline is advanced without the bundle being
    re-cut, every later run compares upstream to baseline, finds them equal,
    and reports "no change" while users run stale vectors. That happened with
    NIST's ad33b3d fix to the ML-KEM encapsulationKeyCheck vectors: the
    shipped "invalid" keys were over-length, so they were rejected on length
    alone and the FIPS 203 §7.2 modulus check was never exercised.
    """
    manifest = (json.load(open(manifest_path))
                if os.path.exists(manifest_path) else {})
    lines = []
    for name, fp in current.items():
        pinned = manifest.get(name)
        if pinned is None:
            lines.append(f"  [{name}] shipped in the bundle but missing from "
                         f"MANIFEST.json -- cannot be checked")
            continue
        if pinned["sha256"] == fp["sha256"]:
            continue
        since = history.get(name, {}).get(fp["sha256"], {}).get("first_seen")
        lines.append(f"  [{name}] BUNDLE BEHIND UPSTREAM")
        lines.append(f"      shipped  sha256 {pinned['sha256'][:12]}")
        lines.append(f"      upstream sha256 {fp['sha256'][:12]}"
                     + (f" (first seen {since})" if since else ""))
    return lines


def main():
    try:
        current = fetch_current()
    except Exception as e:
        print(f"ERROR fetching vectors: {type(e).__name__}: {e}")
        return 2

    baseline = json.load(open(STATE)) if os.path.exists(STATE) else {}
    history = json.load(open(HISTORY)) if os.path.exists(HISTORY) else {}

    changed, report = False, []
    for name in current:
        delta = describe_change(name, baseline.get(name), current[name], history)
        if delta:
            changed = True
            report.extend(delta)

    # ---- persist state BEFORE printing, so a broken pipe can't lose it ----
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    for name, fp in current.items():
        h = history.setdefault(name, {})
        rec = h.setdefault(fp["sha256"], {"first_seen": now, "count": 0})
        rec["last_seen"] = now
        rec["count"] += 1
    os.makedirs(os.path.dirname(HISTORY), exist_ok=True)
    json.dump(history, open(HISTORY, "w"), indent=2, sort_keys=True)
    if changed:
        json.dump(current, open(STATE, "w"), indent=2, sort_keys=True)

    behind = bundle_behind(current, history)

    if not changed and not behind:
        print(f"No change. {len(current)} NIST vector files match baseline "
              f"and the shipped bundle.")
        for name, fp in current.items():
            print(f"  {name}: sha={fp['sha256'][:12]} "
                  f"tests={fp['total_tests']}")
        return 0

    if not changed:
        print("=" * 68)
        print("  SHIPPED BUNDLE IS BEHIND NIST")
        print("=" * 68)
        print("\n".join(behind))
        print("=" * 68)
        print("ACTION: upstream has not moved since the last run, but the pinned")
        print("snapshot in pq_verify/vectors was never re-cut to match it. Re-pin")
        print("the files above, update MANIFEST.json, and re-verify offline.")
        return 1

    print("=" * 68)
    print("  NIST ACVP VECTORS CHANGED UPSTREAM")
    print("=" * 68)
    print("\n".join(report))
    print("=" * 68)
    print("ACTION: upstream has moved. Do NOT auto-update the shipped bundle.")
    print("Wait until the fingerprint is stable across several runs, then cut")
    print("a new pinned snapshot deliberately and re-verify offline first.")
    print("If any line above says REVERTED, upstream is still oscillating")
    print("and is not ready to pin.")
    if behind:
        print("=" * 68)
        print("  SHIPPED BUNDLE vs NIST")
        print("\n".join(behind))
    return 1


if __name__ == "__main__":
    sys.exit(main())
