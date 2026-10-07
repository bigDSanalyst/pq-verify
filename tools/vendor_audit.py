#!/usr/bin/env python3
"""Rebuild each pinned third-party ML-KEM / ML-DSA library and re-audit it.

  python3 tools/vendor_audit.py              build every row, check its result
  python3 tools/vendor_audit.py --markdown   print the AUDITS.md tables (offline)
  python3 tools/vendor_audit.py --only ML-DSA   just one scheme (ML-KEM, ML-DSA, LMS/XMSS,
                                                FN-DSA)

ML-KEM rows are re-run with --audit-kem, ML-DSA rows with --audit-dsa. ML-DSA
libraries are linked with pq-verify's randomness harness
(pq_verify/harness/pqv_randombytes.c), so their randomised keypair() and
signature() APIs are audited byte-exactly, not only the seed-taking ones.

Mutants. An audit that passes correct libraries has shown half of what it
must. Each ML-DSA row also lists mutants: a one-line source change that plants
a known bug class (a verifier that skips the challenge comparison, a hint
decoder that accepts a repeated index, a signer that ignores rnd, ...). CI
builds every mutant and requires the audit to FAIL it in the stages the row
names. A mutant the audit passes is a hole in pq-verify, reported as such.

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
HARNESS = REPO / "pq_verify" / "harness" / "pqv_randombytes.c"
STAGES = ("keyGen", "encaps", "decaps", "ekCheck", "dkCheck")
# Wycheproof/CCTV edge cases (pq_verify/edge.py). Their counts differ per
# parameter set, so each row records them per set under "edge".
EDGE_STAGES = ("edgeValid", "edgeEk", "edgeDk")
BEGIN, END = "<!-- vendor-audits:begin -->", "<!-- vendor-audits:end -->"
DSA_BEGIN, DSA_END = "<!-- vendor-audits-dsa:begin -->", "<!-- vendor-audits-dsa:end -->"
DSA_STAGES = ("keyGen", "sigGenInternal", "sigGenPure", "sigGenPreHash", "sigGenMu",
              "sigVerInternal", "sigVerPure", "sigVerPreHash", "sigVerMu")
DSA_EDGE_STAGES = ("edge:sigVerify", "edge:sigGen", "edge:edgeLength")
DSA_BUILDS = ("mldsa-native", "pqcrystals-ref", "pqclean-mldsa")
HBS_BEGIN, HBS_END = "<!-- vendor-audits-hbs:begin -->", "<!-- vendor-audits-hbs:end -->"
HBS_BUILDS = ("hash-sigs", "xmss-reference")
HBS_ADAPTERS = REPO / "pq_verify" / "harness" / "hbs"
FNDSA_BEGIN, FNDSA_END = "<!-- vendor-audits-fndsa:begin -->", "<!-- vendor-audits-fndsa:end -->"
FNDSA_BUILDS = ("pqclean-falcon",)
FNDSA_STAGES = ("verify", "open", "reject", "keyGen", "sign")

_RANDOMBYTES = (b"#include <stdint.h>\n#include <stddef.h>\n"
                b"int randombytes(uint8_t *o, size_t n)"
                b"{ for (size_t i = 0; i < n; i++) o[i] = (uint8_t)i; return 0; }\n")


def load_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh)["audits"]


def load_dsa_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("dsa_audits", [])


def load_hbs_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("hbs_audits", [])


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


def build_dsa(recipe, src, param_set, out_dir, tag=""):
    """Compile one ML-DSA parameter set, linked with the randomness harness."""
    level = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{level}{tag}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared"]
    src = Path(src)
    if recipe == "mldsa-native":
        cmd = cc + [f"-DMLD_CONFIG_PARAMETER_SET={level}", "-I", str(src / "mldsa"),
                    "-o", str(so), str(src / "mldsa" / "mldsa_native.c"), str(HARNESS)]
    elif recipe == "pqcrystals-ref":
        mode = {"44": 2, "65": 3, "87": 5}[level]
        ref = src / "ref"
        files = ("sign.c", "packing.c", "polyvec.c", "poly.c", "ntt.c", "reduce.c",
                 "rounding.c", "fips202.c", "symmetric-shake.c")
        cmd = cc + [f"-DDILITHIUM_MODE={mode}", "-o", str(so),
                    *(str(ref / f) for f in files), str(HARNESS)]
    elif recipe == "pqclean-mldsa":
        d = src / "crypto_sign" / f"ml-dsa-{level}" / "clean"
        common = src / "common"
        cmd = cc + ["-I", str(common), "-o", str(so),
                    *sorted(str(p) for p in d.glob("*.c")),
                    str(common / "fips202.c"), str(HARNESS)]
    else:
        raise ValueError(f"unknown ML-DSA build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def build_hbs(recipe, src, out_dir, tag=""):
    """Compile an LMS/XMSS library with its pqv_hbs adapter. Both use OpenSSL
    for SHA-2, so -lcrypto."""
    so = Path(out_dir) / f"{recipe}{tag}.so"
    cc = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared", "-w",
          "-I", str(HBS_ADAPTERS), "-I", str(src)]
    src = Path(src)
    if recipe == "hash-sigs":
        files = ("hss hss_alloc hss_aux hss_common hss_compute hss_generate hss_keygen "
                 "hss_param hss_reserve hss_sign hss_sign_inc hss_thread_single hss_verify "
                 "hss_verify_inc hss_derive hss_zeroize lm_common lm_ots_common lm_ots_sign "
                 "lm_ots_verify lm_verify endian hash sha256").split()
        cmd = cc + ["-o", str(so), str(HBS_ADAPTERS / "adapter_hash_sigs.c"),
                    *(str(src / f"{f}.c") for f in files), "-lcrypto"]
    elif recipe == "xmss-reference":
        files = ("params hash fips202 hash_address wots xmss xmss_core xmss_commons "
                 "utils").split()
        cmd = cc + ["-o", str(so), str(HBS_ADAPTERS / "adapter_xmss_reference.c"),
                    *(str(src / f"{f}.c") for f in files), "-lcrypto"]
    else:
        raise ValueError(f"unknown LMS/XMSS build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


def mutate(src, mutant, dest):
    """A copy of the source tree with one planted bug. The change must apply
    exactly once: a pattern that no longer matches would test nothing."""
    dest = Path(dest)
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(src, dest, ignore=shutil.ignore_patterns(".git"))
    f = dest / mutant["file"]
    text = f.read_text()
    n = text.count(mutant["find"])
    if n != 1:
        raise RuntimeError(f"mutant {mutant['name']!r}: pattern found {n} times in "
                           f"{mutant['file']}, expected once")
    f.write_text(text.replace(mutant["find"], mutant["replace"]))
    return dest


def load_fndsa_table(path=TABLE):
    with open(path) as fh:
        return json.load(fh).get("fndsa_audits", [])


def build_fndsa(recipe, src, param_set, out_dir, tag=""):
    """Compile one FN-DSA (Falcon) parameter set. Signing draws its nonce
    and seeds from the system RNG: FN-DSA signing is audited for validity,
    not byte-for-byte, so no randomness harness is linked."""
    n = param_set.rsplit("-", 1)[1]
    so = Path(out_dir) / f"{recipe}{n}{tag}.so"
    src = Path(src)
    if recipe == "pqclean-falcon":
        d = src / "crypto_sign" / f"falcon-{n}" / "clean"
        common = src / "common"
        cmd = [os.environ.get("CC", "gcc"), "-O2", "-fPIC", "-shared", "-I", str(common),
               "-o", str(so), *sorted(str(p) for p in d.glob("*.c")),
               str(common / "fips202.c"), str(common / "randombytes.c")]
    else:
        raise ValueError(f"unknown FN-DSA build recipe {recipe!r}")
    subprocess.run(cmd, check=True, capture_output=True)
    return str(so)


# ─────────────────────────────── audit ───────────────────────────────

def audit_dsa(so, param_set):
    sys.path.insert(0, str(REPO))
    from pq_verify.dsa_audit import pqverify_audit_dsa
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_dsa(so, param_set, verbose=False)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"], "rng": r["rng"]}


def audit_hbs(so):
    sys.path.insert(0, str(REPO))
    from pq_verify.hbs_audit import pqverify_audit_hbs
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_hbs(so, verbose=False)
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"], "not_run": r["not_run_total"],
            # Which checks fail, by name: pinned for a library with known
            # defects, so a mutant is judged on what it ADDS (below).
            "failing": sorted(f"{f['stage']}: {f['case']}" for f in r["failures"])}


def audit_fndsa(so, param_set):
    sys.path.insert(0, str(REPO))
    from pq_verify.fndsa_audit import pqverify_audit_fndsa
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_fndsa(so, param_set, verbose=False)
    if r is None:
        return None
    return {"results": {k: list(v) for k, v in r["detail"].items()},
            "not_applicable": r["not_applicable_total"]}


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
        for ps in row["sets"]:
            want = {k: list(v) for k, v in row["expected"].items()}
            want.update({k: list(v) for k, v in row["edge"][ps].items()})
            if "accumulated" in row:
                want["accumulated"] = list(row["accumulated"][ps])
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
            for s in STAGES + EDGE_STAGES + ("accumulated",):
                if got.get(s) != want.get(s):
                    print(f"         {s:8s} recorded {want.get(s)}  now {got.get(s)}")
    if failures:
        print(f"\n  {failures} row(s) differ. pq-verify's behaviour changed against a "
              f"pinned library and pinned vectors: fix the regression, or, if the "
              f"change is intended, update tools/vendor_audits.json and AUDITS.md "
              f"in the same PR and say why.")
        return 1
    return 0


def check_dsa(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_dsa(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_dsa(so, ps)
            want = {"results": row["results"][ps],
                    "not_applicable": row["not_applicable"][ps], "rng": []}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:16s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
            for r in got["rng"][:3]:
                print(f"         randomness: {r}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                # A distinct file per mutant: the dynamic loader hands back an
                # already-loaded library for a path it has seen, so reusing a
                # name would audit the first mutant every time.
                so = build_dsa(row["build"], msrc, m["set"], workdir, tag=f"-mut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_dsa(so, m["set"])
            missed = []
            for stage in m["fails"]:
                if stage == "rng":
                    if not (got and got["rng"]):
                        missed.append("rng")
                    continue
                p, t = (got or {"results": {}})["results"].get(stage, (0, 0))
                if not (t and p < t):
                    missed.append(f"{stage} {p}/{t}")
            if got is not None and not missed:
                bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad + (['rng'] if got['rng'] else []))}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} ML-DSA row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def _check_mutants(row, src, workdir, build_fn, audit_fn):
    """Build each mutant of a row and require the audit to fail it in every
    listed stage. Returns the number missed (or 2 on a build error)."""
    missed_rows = 0
    for i, m in enumerate(row.get("mutants", [])):
        label = f"{row['library']} mutant {m['name']!r}"
        try:
            msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
            so = build_fn(msrc, i)
        except (RuntimeError, subprocess.CalledProcessError) as e:
            print(f"  ERROR  {label}: {e}")
            return None
        got = audit_fn(so)
        missed = []
        known = set(row.get("failing", []))
        for stage in m["fails"]:
            if stage == "rng":
                if not got.get("rng"):
                    missed.append("rng")
                continue
            p, t = got["results"].get(stage, (0, 0))
            if "failing" in got:
                # The library itself may already fail checks in this stage (an
                # upstream defect, pinned in the row): only a check that fails
                # for the mutant and NOT for the library shows the planted bug.
                if not any(x.startswith(stage + ": ") and x not in known
                           for x in got["failing"]):
                    missed.append(f"{stage} {p}/{t} (no check beyond the library's own)")
            elif not (t and p < t):
                missed.append(f"{stage} {p}/{t}")
        if not missed:
            bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
            print(f"  caught {label}: fails {', '.join(bad)}")
            continue
        missed_rows += 1
        print(f"  MISSED {label}: the audit did not fail {', '.join(missed)}. "
              f"pq-verify cannot see this bug class.")
    return missed_rows


def check_hbs(rows, workdir):
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        label = f"{row['library']} @ {row['commit'][:7]}"
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
            so = build_hbs(row["build"], src, workdir)
        except subprocess.CalledProcessError as e:
            print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
            return 2
        except Exception as e:
            print(f"  ERROR  {label}: fetch failed: {e}")
            return 2
        got = audit_hbs(so)
        want = {"results": row["results"], "not_applicable": row["not_applicable"],
                "not_run": row["not_run"], "failing": row.get("failing", [])}
        if got == want:
            p, t = total(got["results"])
            print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, "
                  f"{got['not_run']} not run, as recorded")
        else:
            failures += 1
            print(f"  DIFF   {label}")
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:32s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            for k in ("not_applicable", "not_run"):
                if got[k] != want[k]:
                    print(f"         {k} recorded {want[k]}  now {got[k]}")
            for x in sorted(set(got["failing"]) ^ set(want["failing"])):
                print(f"         {'now fails' if x in got['failing'] else 'now passes'}: {x}")
        missed = _check_mutants(
            row, src, workdir,
            lambda msrc, i, r=row: build_hbs(r["build"], msrc, workdir, tag=f"-mut{i}"),
            audit_hbs)
        if missed is None:
            return 2
        failures += missed
    if failures:
        print(f"\n  {failures} LMS/XMSS row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


def check_fndsa(rows, workdir):
    """FN-DSA (draft track): each row's sets as recorded, and every mutant
    failed in the stages it names."""
    failures = 0
    for row in rows:
        src = Path(workdir) / row["build"] / row["commit"][:12]
        try:
            if not (src / ".git").exists():
                fetch(row["url"], row["commit"], src)
        except Exception as e:
            print(f"  ERROR  {row['library']} @ {row['commit'][:7]}: fetch failed: {e}")
            return 2
        for ps in row["sets"]:
            label = f"{row['library']} @ {row['commit'][:7]} {ps}"
            try:
                so = build_fndsa(row["build"], src, ps, workdir)
            except subprocess.CalledProcessError as e:
                print(f"  ERROR  {label}: build failed\n{e.stderr.decode()[-2000:]}")
                return 2
            got = audit_fndsa(so, ps)
            want = {"results": row["results"][ps],
                    "not_applicable": row["not_applicable"][ps]}
            if got == want:
                p, t = total(got["results"])
                print(f"  ok     {label}: {p}/{t}, {got['not_applicable']} n/a, as recorded")
                continue
            failures += 1
            print(f"  DIFF   {label}")
            if got is None:
                print("         pq-verify could not audit it (entry points not resolved)")
                continue
            for s in sorted(set(got["results"]) | set(want["results"])):
                if got["results"].get(s) != want["results"].get(s):
                    print(f"         {s:8s} recorded {want['results'].get(s)}  "
                          f"now {got['results'].get(s)}")
            if got["not_applicable"] != want["not_applicable"]:
                print(f"         not applicable recorded {want['not_applicable']}  "
                      f"now {got['not_applicable']}")
        for i, m in enumerate(row.get("mutants", [])):
            label = f"{row['library']} mutant {m['name']!r} ({m['set']})"
            try:
                msrc = mutate(src, m, Path(workdir) / "mutants" / row["build"])
                so = build_fndsa(row["build"], msrc, m["set"], workdir, tag=f"-mut{i}")
            except (RuntimeError, subprocess.CalledProcessError) as e:
                print(f"  ERROR  {label}: {e}")
                return 2
            got = audit_fndsa(so, m["set"])
            missed = [f"{st} {p}/{t}" for st in m["fails"]
                      for p, t in [(got or {"results": {}})["results"].get(st, (0, 0))]
                      if not (t and p < t)]
            if got is not None and not missed:
                bad = sorted(s for s, (p, t) in got["results"].items() if p < t)
                print(f"  caught {label}: fails {', '.join(bad)}")
                continue
            failures += 1
            print(f"  MISSED {label}: the audit did not fail "
                  + (", ".join(missed) if got else "(could not audit it)")
                  + ". pq-verify cannot see this bug class.")
    if failures:
        print(f"\n  {failures} FN-DSA row(s) or mutant(s) differ. Fix the regression, "
              f"or, if intended, update tools/vendor_audits.json and AUDITS.md in "
              f"the same PR and say why.")
        return 1
    return 0


# ─────────────────────────────── table ───────────────────────────────

def edge_total(row):
    return tuple(sum(row["edge"][ps][s][i] for ps in row["sets"] for s in EDGE_STAGES)
                 for i in (0, 1))


def markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen | encaps | decaps | ekCheck "
             "| dkCheck | Edge cases | Accumulated | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        e = row["expected"]
        p, t = total(e)
        ep, et = edge_total(row)
        acc = row.get("accumulated", {})
        ap, at = (sum(acc[ps][i] for ps in acc) for i in (0, 1))
        ok = p == t and ep == et and ap == at
        verdict = "**VERIFIED**" if ok else "findings"
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        cells = [f"{e[s][0]}/{e[s][1]}" for s in STAGES]
        lines.append(f"| {row['library']} | [`{row['commit'][:7]}`]"
                     f"({row['url']}/commit/{row['commit']}) ({row['date']}) "
                     f"| {sets} | " + " | ".join(cells) +
                     f" | {ep:,}/{et:,} | {f'{ap}/{at}' if at else '—'} "
                     f"| {p}/{t} + {ep:,}/{et:,}{f' + {ap}/{at}' if at else ''} {verdict} |")
    return "\n".join(lines)


def dsa_markdown(rows):
    lines = ["| Library | Commit | Sets | keyGen | sigGen int / pure / pre-hash / μ "
             "| sigVer int / pure / pre-hash / μ | Wycheproof verify / sign / length "
             "| Accumulated | Not applicable | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stages):
            out = []
            for s in stages:
                p = sum(row["results"][ps].get(s, [0, 0])[0] for ps in row["sets"])
                t = sum(row["results"][ps].get(s, [0, 0])[1] for ps in row["sets"])
                out.append(f"{p}/{t}" if t else "n/a")
            return " / ".join(out)
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        na = sum(row["not_applicable"][ps] for ps in row["sets"])
        muts = row.get("mutants", [])
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            sets, cell(["keyGen"]),
            cell(["sigGenInternal", "sigGenPure", "sigGenPreHash", "sigGenMu"]),
            cell(["sigVerInternal", "sigVerPure", "sigVerPreHash", "sigVerMu"]),
            cell(list(DSA_EDGE_STAGES)), cell(["accumulated"]), f"{na:,}",
            f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def hbs_markdown(rows):
    lines = ["| Library | Commit | Schemes | Verify | keyGen | sigGen | Malformed rejected "
             "| Key state | Not applicable | Not run | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        r = row["results"]

        def cell(kind):
            ks = [k for k in r if k.split(" ")[1].startswith(kind)]
            if not ks:
                return "n/a"
            return f"{sum(r[k][0] for k in ks):,}/{sum(r[k][1] for k in ks):,}"
        p, t = total(r)
        muts = row.get("mutants", [])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            row["schemes"], cell("verify"), cell("keyGen"), cell("sigGen"),
            cell("malformed"), cell("state"), f"{row['not_applicable']:,}",
            f"{row['not_run']:,}",
            f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED**' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def fndsa_markdown(rows):
    lines = ["| Library | Commit | Sets | Verify (pinned) | Open (pinned) | Malformed rejected "
             "| keyGen | sign | Not applicable | Mutants caught | Result |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for row in rows:
        def cell(stage):
            p = sum(row["results"][ps].get(stage, [0, 0])[0] for ps in row["sets"])
            t = sum(row["results"][ps].get(stage, [0, 0])[1] for ps in row["sets"])
            return f"{p}/{t}" if t else "n/a"
        p, t = (sum(v[i] for ps in row["sets"] for v in row["results"][ps].values())
                for i in (0, 1))
        na = sum(row["not_applicable"][ps] for ps in row["sets"])
        muts = row.get("mutants", [])
        sets = " / ".join(s.rsplit("-", 1)[1] for s in row["sets"])
        lines.append(" | ".join([
            f"| {row['library']}",
            f"[`{row['commit'][:7]}`]({row['url']}/commit/{row['commit']}) ({row['date']})",
            sets, cell("verify"), cell("open"), cell("reject"), cell("keyGen"),
            cell("sign"), f"{na:,}", f"{len(muts)}/{len(muts)}" if muts else "—",
            f"{p:,}/{t:,} {'**VERIFIED** (draft)' if p == t else 'findings'} |"]))
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--markdown", action="store_true",
                    help="print the AUDITS.md table from the pinned rows; no build")
    ap.add_argument("--workdir", help="where to fetch and build (default: a "
                                      "temporary directory, removed afterwards)")
    ap.add_argument("--only", choices=("ML-KEM", "ML-DSA", "LMS/XMSS", "FN-DSA"),
                    help="re-audit one scheme's rows")
    a = ap.parse_args(argv)
    rows, dsa_rows, hbs_rows = load_table(), load_dsa_table(), load_hbs_table()
    fndsa_rows = load_fndsa_table()
    if a.markdown:
        print(markdown(rows))
        print()
        print(dsa_markdown(dsa_rows))
        print()
        print(hbs_markdown(hbs_rows))
        print()
        print(fndsa_markdown(fndsa_rows))
        return 0

    def run(work):
        code = 0
        if a.only in (None, "ML-KEM"):
            code = max(code, check_all(rows, work))
        if a.only in (None, "ML-DSA"):
            code = max(code, check_dsa(dsa_rows, work))
        if a.only in (None, "LMS/XMSS"):
            code = max(code, check_hbs(hbs_rows, work))
        if a.only in (None, "FN-DSA"):
            code = max(code, check_fndsa(fndsa_rows, work))
        return code
    if a.workdir:
        return run(a.workdir)
    work = tempfile.mkdtemp(prefix="pqv-vendor-")
    try:
        return run(work)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
