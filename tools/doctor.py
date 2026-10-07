#!/usr/bin/env python3
"""Is the pinned vector bundle sound, and is a NIST update safe to pin?

Run it when the watcher reports that NIST changed a vector file, and any time
you want to know the state of the pinned vectors. By default it reads and
writes nothing but a scratch directory; only `--apply` changes the repository.

  python3 tools/doctor.py                  the pinned bundle, offline
  python3 tools/doctor.py --candidate      fetch what NIST changed and test it
  python3 tools/doctor.py --candidate-dir D   the same, from files already on disk
  python3 tools/doctor.py --candidate --apply   re-pin, only if nothing BLOCKs

WHAT IT MAY AND MAY NOT DO
  It computes; it does not advise. Every line is derived from the bundle, the
  manifest, the watcher's state and the suites it runs, so a green check never
  asserts something it did not compute. An agent should run doctor and report
  what it returns (`--json`), not read the vector files and narrate them.

  Rules are imported, not restated: key sizes come from pq_verify.core, the
  tracked file list and fingerprints from tools/check_vectors.py. A rule stated
  twice is a rule that will disagree with itself.

WHY IT EXISTS
  pq-verify 2.8.0 shipped NIST vectors whose invalid ML-KEM keys were 416
  bytes over length, so every "invalid key" check passed on length alone. NIST
  had already fixed it; the bundle was never re-cut, and nothing ran the checks
  a re-pin needs. Each check below is one of those steps.

STATUSES
  ok      nothing owed
  DECIDE  a decision is owed, not a fault: typically "NIST moved; wait or pin"
  WARN    works, but something is unfinished or could not be confirmed
  BLOCK   wrong now: do not pin, or the pinned bundle itself is unsound

EXIT
  0  no BLOCK        1  at least one BLOCK        2  could not run
"""
import argparse
import contextlib
import datetime
import gzip
import hashlib
import io
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / "tools"))
import check_vectors as W                                     # noqa: E402
from pq_verify.core import _VECTOR_BUNDLES, _bundle_name      # noqa: E402

OK, DECIDE, WARN, BLOCK = "ok", "DECIDE", "WARN", "BLOCK"
PINNED_SIDE = ("manifest", "watched", "keycheck:pinned", "references", "upstream",
               "edge:manifest", "references:edge", "hbs:manifest",
               "fndsa:manifest")
STABLE_DAYS = 14          # NIST has reverted files within a day; wait this long
REFERENCES = ("kyber-py", "dilithium-py", "slh-dsa")
SUITES = {                # the runner for each vector directory prefix
    "ML-KEM": "pqverify_acvp",
    "ML-DSA": "pqverify_mldsa_acvp",
    "SLH-DSA": "pqverify_slhdsa_acvp",
    "LMS": "pqverify_lms_acvp",
}
SUITE_SIGGEN = {"SLH-DSA": "SLH-DSA-sigGen-"}   # opt-in groups a re-pin must run


class Check:
    """One computed finding. `fix` is a command or an act, never an opinion."""

    def __init__(self, key, status, headline, detail="", fix=""):
        self.key, self.status = key, status
        self.headline, self.detail, self.fix = headline, detail, fix

    def as_dict(self):
        return {"check": self.key, "status": self.status, "headline": self.headline,
                "detail": self.detail, "fix": self.fix}


# ─────────────────────────────── inputs ───────────────────────────────

def paths(repo):
    v = Path(repo) / "pq_verify" / "vectors"
    t = Path(repo) / "tools" / "vector_state"
    return {"bundle": v / "acvp_vectors.json.gz", "manifest": v / "MANIFEST.json",
            "bundles": {name: v / name for name in _VECTOR_BUNDLES},
            "baseline": t / "baseline.json", "history": t / "history.json"}


def load_json(p, default=None):
    try:
        with open(p) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


def load_bundle(p):
    """One archive, or every archive when given paths()["bundles"], merged:
    {"DIR/file.json": parsed JSON, or NIST's text verbatim}. A missing
    archive contributes nothing, so check_manifest names what it lacked."""
    if isinstance(p, dict):
        out = {}
        for q in p.values():
            if Path(q).exists():
                out.update(load_bundle(q))
        return out
    with gzip.open(p, "rt") as fh:
        return json.load(fh)


def raw_of(entry):
    """The bytes a bundle entry stands for: verbatim entries are NIST's file
    text; parsed ones are re-serialised (their sha256 is not NIST's)."""
    return entry.encode() if isinstance(entry, str) else json.dumps(entry).encode()


def doc_of(entry):
    return json.loads(entry) if isinstance(entry, str) else entry


def write_bundle(path, entries, verbatim):
    """Deterministic: the same entries give byte-identical archives."""
    with open(path, "wb") as fh:
        with gzip.GzipFile(filename=Path(path).name[:-3], mode="wb", fileobj=fh,
                           mtime=0, compresslevel=9) as g:
            g.write(json.dumps(entries, separators=(",", ":"),
                               sort_keys=verbatim).encode())


def tracked():
    return [f"{d}/{f}" for d, files in W.TARGETS.items() for f in files]


# ─────────────────────────────── checks ───────────────────────────────

def check_manifest(bundle, manifest):
    """The manifest is what the watcher and every report cite; it must cover
    the bundle exactly and say which NIST commit each file came from."""
    missing = sorted(set(bundle) - set(manifest))
    extra = sorted(set(manifest) - set(bundle))
    nocommit = sorted(k for k, v in manifest.items() if not v.get("nist_commit"))
    # Verbatim entries are NIST's bytes, so their digest is checkable offline.
    altered = sorted(k for k, v in bundle.items() if isinstance(v, str) and k in manifest
                     and (hashlib.sha256(v.encode()).hexdigest() != manifest[k]["sha256"]
                          or len(v.encode()) != manifest[k]["bytes"]))
    if not (missing or extra or nocommit or altered):
        verbatim = sum(isinstance(v, str) for v in bundle.values())
        return Check("manifest", OK,
                     f"MANIFEST.json covers all {len(bundle)} bundled files, "
                     f"each with its NIST commit"
                     + (f"; {verbatim} verbatim file(s) match their sha256"
                        if verbatim else ""))
    parts = []
    if missing:
        parts.append(f"bundled but not in the manifest: {', '.join(missing)}")
    if extra:
        parts.append(f"in the manifest but not bundled: {', '.join(extra)}")
    if nocommit:
        parts.append(f"no nist_commit recorded: {', '.join(nocommit)}")
    if altered:
        parts.append(f"content differs from its pinned sha256: {', '.join(altered)}")
    return Check("manifest", BLOCK, "MANIFEST.json does not describe the bundle",
                 "; ".join(parts) + ". Reports cite the manifest as the vector "
                 "revision, so they would name vectors that were not used.",
                 "for each file listed, record its NIST commit (find it with "
                 "git -C ACVP-Server log -1 -- gen-val/json-files/<file>); "
                 "--apply fills the manifest only for files it re-pins")


def check_watched(bundle):
    unwatched = sorted(set(bundle) - set(tracked()))
    if not unwatched:
        return Check("watched", OK, "every bundled file is tracked by the watcher")
    return Check("watched", BLOCK,
                 f"{len(unwatched)} bundled file(s) the watcher never checks",
                 ", ".join(unwatched) + " can change upstream with nobody told.",
                 "add them to TARGETS in tools/check_vectors.py")


def keycheck_problems(files):
    """Every key-check key must have its parameter set's exact FIPS 203 length.
    An over-length 'invalid' key is rejected on length alone, so it does not
    exercise the modulus or hash check it is labelled as testing."""
    from pq_verify.core import _KEM_SIZES
    out = []
    for name, doc in files.items():
        if not name.startswith("ML-KEM-encapDecap") or not isinstance(doc, dict):
            continue
        for g in doc.get("testGroups", []):
            fn, ps = g.get("function"), g.get("parameterSet")
            if fn not in ("encapsulationKeyCheck", "decapsulationKeyCheck"):
                continue
            if ps not in _KEM_SIZES:
                out.append(f"{name}: unknown parameter set {ps!r}")
                continue
            ek_n, dk_n = _KEM_SIZES[ps][0], _KEM_SIZES[ps][1]
            for t in g.get("tests", []):
                for field, want in (("ek", ek_n), ("dk", dk_n)):
                    if field in t and len(t[field]) // 2 != want:
                        out.append(f"{name} tcId {t.get('tcId')} ({ps}, {fn}): "
                                   f"{field} is {len(t[field]) // 2} bytes, "
                                   f"FIPS 203 says {want}")
    return out


def check_keycheck(files, label):
    bad = keycheck_problems(files)
    if not bad:
        return Check(f"keycheck:{label}", OK,
                     f"{label}: every key-check key has its FIPS 203 length")
    return Check(f"keycheck:{label}", BLOCK,
                 f"{label}: {len(bad)} key-check key(s) have the wrong length",
                 "; ".join(bad[:5]) + (" …" if len(bad) > 5 else "") +
                 ". A wrong-length invalid key is rejected on length alone, so "
                 "the check it is labelled as testing never runs.",
                 "do not pin this revision; report it to NIST (usnistgov/ACVP-Server)")


def reference_pins(repo):
    """{dist: version} from constraints-reference.txt, the versions CI pins."""
    pins = {}
    try:
        for line in (Path(repo) / "constraints-reference.txt").read_text().splitlines():
            line = line.split("#", 1)[0].strip()
            if "==" in line:
                name, ver = line.split("==", 1)
                pins[name.strip().lower()] = ver.strip()
    except OSError:
        pass
    return pins


def check_references(repo=REPO):
    """The suites are only as good as the reference implementations that
    answer them. Name the versions, so a result says what produced it, and
    flag any that differ from the versions CI pins."""
    from importlib import metadata
    have, missing = {}, []
    for r in REFERENCES:
        try:
            have[r] = metadata.version(r)
        except metadata.PackageNotFoundError:
            missing.append(r)
    vers = ", ".join(f"{k} {v}" for k, v in have.items())
    pins = reference_pins(repo)
    drift = [f"{k} {v} (CI pins {pins[k]})" for k, v in have.items()
             if k in pins and pins[k] != v]
    if not missing and not drift:
        return Check("references", OK, f"reference implementations: {vers}"
                     + (" (as CI pins)" if pins else "")), have
    # Report every problem at once: a missing library must not hide that the
    # ones present differ from CI (it did, in the first version of this check).
    heads, why = [], []
    if drift:
        heads.append(f"reference implementation(s) differ from CI: {', '.join(drift)}")
        why.append("results here may differ from CI's, and a candidate shown to "
                   "pass here is not shown to pass there")
    if missing:
        heads.append(f"missing reference implementation(s): {', '.join(missing)}")
        why.append("suites that need them cannot run, so a candidate cannot be "
                   "shown to pass them")
    return Check("references", WARN, "; ".join(heads),
                 "; ".join(why) + (f". Present: {vers}" if vers else ""),
                 "pip install -c constraints-reference.txt "
                 + " ".join(REFERENCES)), have


def check_edge_manifest(repo=REPO):
    """The Wycheproof/CCTV bundle matches EDGE_MANIFEST.json, offline."""
    import pin_edge_vectors as E
    v = Path(repo) / "pq_verify" / "vectors"
    bundle, manifest = v / "edge_vectors.json.gz", v / "EDGE_MANIFEST.json"
    if not bundle.exists() or not manifest.exists():
        return Check("edge:manifest", BLOCK, "the edge-case bundle or its manifest is missing",
                     fix="python3 tools/pin_edge_vectors.py")
    problems = E.verify(bundle, manifest)
    if problems:
        return Check("edge:manifest", BLOCK,
                     f"{len(problems)} edge-case file(s) do not match EDGE_MANIFEST.json",
                     "\n".join(problems[:10]), "python3 tools/pin_edge_vectors.py")
    m = json.loads(manifest.read_text())
    src = ", ".join(f"{k} {s['commit'][:7]}" for k, s in sorted(m["sources"].items()))
    return Check("edge:manifest", OK, f"edge-case vectors: {len(m['files'])} files match "
                 f"EDGE_MANIFEST.json ({src})")


def check_hbs_manifest(repo=REPO):
    """The non-NIST LMS/XMSS bundle matches HBS_MANIFEST.json, offline."""
    import pin_hbs_vectors as P
    v = Path(repo) / "pq_verify" / "vectors"
    bundle, manifest = v / "hbs_vectors.json.gz", v / "HBS_MANIFEST.json"
    if not bundle.exists() or not manifest.exists():
        return Check("hbs:manifest", BLOCK, "the LMS/XMSS bundle or its manifest is missing",
                     fix="python3 tools/pin_hbs_vectors.py")
    problems = P.verify(bundle, manifest)
    if problems:
        return Check("hbs:manifest", BLOCK,
                     f"{len(problems)} LMS/XMSS file(s) do not match HBS_MANIFEST.json",
                     "\n".join(problems[:10]), "python3 tools/pin_hbs_vectors.py")
    m = json.loads(manifest.read_text())
    src = ", ".join(f"{k} {s['commit'][:7]}" for k, s in sorted(m["sources"].items()))
    return Check("hbs:manifest", OK, f"LMS/XMSS vectors: {len(m['files'])} files match "
                 f"HBS_MANIFEST.json ({src})")


def check_fndsa_manifest(repo=REPO):
    """The FN-DSA (draft track) bundle matches FNDSA_MANIFEST.json and the
    sha256 PQClean publishes for each file, offline."""
    import pin_fndsa_vectors as P
    v = Path(repo) / "pq_verify" / "vectors"
    bundle, manifest = v / "fndsa_vectors.json.gz", v / "FNDSA_MANIFEST.json"
    if not bundle.exists() or not manifest.exists():
        return Check("fndsa:manifest", BLOCK, "the FN-DSA bundle or its manifest is missing",
                     fix="python3 tools/pin_fndsa_vectors.py")
    problems = P.verify(bundle, manifest)
    if problems:
        return Check("fndsa:manifest", BLOCK,
                     f"{len(problems)} FN-DSA file(s) do not match their pinned sha256",
                     "\n".join(problems[:10]), "python3 tools/pin_fndsa_vectors.py")
    m = json.loads(manifest.read_text())
    return Check("fndsa:manifest", OK, f"FN-DSA vectors (draft track): {len(m['files'])} files "
                 f"match FNDSA_MANIFEST.json and PQClean "
                 f"{m['sources']['pqclean']['commit'][:7]}'s META.yml")


def check_reference_edges():
    """Run the edge-case vectors against the installed references and hold
    the result to KNOWN_REFERENCE_DEFECTS: a new disagreement BLOCKs, a known
    one WARNs until a release fixes it, a fixed one asks to be removed."""
    from pq_verify import edge as EG
    r = EG.reference_run()
    if r is None:
        return Check("references:edge", WARN, "edge-case vectors not run: no reference "
                     "implementation installed", fix='pip install "pq-verify[full]"')
    unknown, known = [], {}
    for ps, res in r["sets"].items():
        for f in res["failures"]:
            if f.get("known_defect"):
                known.setdefault(res["reference"], []).append(f"{ps} {f['case']}")
            else:
                unknown.append(f"{ps} [{res['reference']}] {f['stage']}: {f['case']} "
                               f"{f['flags']} -- {f['detail']}")
    stale = [f"{n} {v}" for (n, v) in EG.KNOWN_REFERENCE_DEFECTS
             if EG._reference_version(n) == v and n not in known
             and any(res["reference"] == n for res in r["sets"].values())]
    if unknown:
        return Check("references:edge", BLOCK,
                     f"a reference disagrees with Wycheproof/CCTV on {len(unknown)} "
                     f"case(s) not in KNOWN_REFERENCE_DEFECTS",
                     "\n".join(unknown[:10]),
                     "pq-verify --edge-cases; if the vector is right the reference is "
                     "wrong: record it in pq_verify/edge.py KNOWN_REFERENCE_DEFECTS "
                     "with the upstream fix")
    if stale:
        return Check("references:edge", WARN,
                     f"known defect no longer reproduces: {', '.join(stale)}",
                     fix="remove the entry from pq_verify/edge.py KNOWN_REFERENCE_DEFECTS")
    if known:
        lines = []
        for name, cases in known.items():
            d = EG.KNOWN_REFERENCE_DEFECTS[(name, EG._reference_version(name))]
            lines.append(f"{name} {EG._reference_version(name)}: {d['summary']} "
                         f"({len(cases)} vector(s)); {d['upstream']}")
        return Check("references:edge", WARN,
                     f"edge cases {r['passed']}/{r['total']}: only known reference "
                     f"defects fail", "\n".join(lines),
                     "when a release contains the upstream fix, bump "
                     "constraints-reference.txt and drop the KNOWN_REFERENCE_DEFECTS entry")
    return Check("references:edge", OK, f"edge cases {r['passed']}/{r['total']} against "
                 f"the installed references ({r['vectors']})")


def check_upstream_state(manifest, baseline, history):
    """Offline: has the watcher seen NIST move away from what is pinned?"""
    moved = sorted(k for k in manifest
                   if k in baseline and baseline[k]["sha256"] != manifest[k]["sha256"])
    if not baseline:
        return Check("upstream", WARN, "the watcher has no baseline yet",
                     "nothing records what NIST currently publishes",
                     "python3 tools/check_vectors.py"), moved
    if not moved:
        return Check("upstream", OK,
                     "the pinned bundle matches what the watcher last saw at NIST"), moved
    since = [history.get(k, {}).get(baseline[k]["sha256"], {}).get("first_seen")
             for k in moved]
    since = sorted(s for s in since if s)
    return Check("upstream", DECIDE,
                 f"NIST changed {len(moved)} pinned file(s) since the bundle was cut",
                 ", ".join(moved) + (f"; first seen {since[0]}" if since else ""),
                 "python3 tools/doctor.py --candidate"), moved


# ─────────────────────────── candidate review ───────────────────────────

def fetch_candidate(names, dest):
    """Download NIST's current copy of `names` into dest/<name>."""
    for n in names:
        raw = W._fetch(W.BASE + n)
        p = Path(dest) / n
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw)


def nist_commit(name):
    """The ACVP-Server commit that last changed `name`, or None. Uses the
    public GitHub API; offline or rate-limited, the caller reports WARN."""
    import urllib.request
    url = ("https://api.github.com/repos/usnistgov/ACVP-Server/commits?per_page=1"
           "&path=gen-val/json-files/" + name)
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "pq-verify-doctor"})
        with urllib.request.urlopen(req, timeout=30) as r:
            d = json.loads(r.read())
        c = d[0]
        return {"sha": c["sha"][:7], "date": c["commit"]["committer"]["date"][:10],
                "message": c["commit"]["message"].splitlines()[0]}
    except Exception:
        return None


def run_suites(vector_dir, prefixes, opts=None):
    """{prefix: (passed, total, {group: (p, t)})} for each suite, or an error
    string. Output is swallowed; the doctor reports, the suites do not."""
    from pq_verify import core
    out = {}
    for pre in prefixes:
        fn = getattr(core, SUITES[pre])
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                r = fn(vector_dir=str(vector_dir), **(opts or {}).get(pre, {}))
        except Exception as e:                       # a malformed file, typically
            out[pre] = f"{type(e).__name__}: {e}"
            continue
        if r is None:
            out[pre] = "could not run (reference implementation missing)"
            continue
        out[pre] = (r["passed"], r["total"],
                    {k: tuple(v) for k, v in (r.get("detail") or {}).items()})
    return out


def lengthonly_control(files):
    """Negative control: a checker that tests length and nothing else must be
    FOOLED by every invalid encapsulation key (each has the correct length and
    is invalid only by content). Any invalid key it rejects was rejected on
    length alone, so it tests nothing a length check does not -- exactly the
    defect of NIST c924096. Returns (rejected_on_length, invalid_total)."""
    from pq_verify.core import _KEM_SIZES
    by_length = total = 0
    for name, doc in files.items():
        if not name.endswith("encapDecap-FIPS203/internalProjection.json"):
            continue
        for g in doc.get("testGroups", []):
            if g.get("function") != "encapsulationKeyCheck":
                continue
            n = _KEM_SIZES[g["parameterSet"]][0]
            for t in g.get("tests", []):
                if not t["testPassed"]:
                    total += 1
                    by_length += len(t["ek"]) // 2 != n
    return by_length, total


def review_candidate(bundle, manifest, history, cand_dir, have_refs):
    """Checks for a candidate: NIST's current files layered over the bundle."""
    checks = []
    cand_dir = Path(cand_dir)
    changed = {}
    for name in sorted(manifest):
        p = cand_dir / name
        if not p.exists():
            continue
        raw = p.read_bytes()
        if hashlib.sha256(raw).hexdigest() != manifest[name]["sha256"]:
            changed[name] = raw
    if not changed:
        checks.append(Check("candidate", OK,
                            "NIST's files match the pinned bundle: nothing to pin"))
        return checks, {}, None

    # Structure: what changed, per file.
    lines = []
    for name, raw in changed.items():
        old = W.fingerprint(raw_of(bundle[name]))
        new = W.fingerprint(raw)
        old["sha256"] = manifest[name]["sha256"]
        lines += W.describe_change(name, old, new, {})
    checks.append(Check("candidate", DECIDE,
                        f"{len(changed)} file(s) differ from the pinned bundle",
                        " | ".join(l.strip() for l in lines)))

    # Two full trees in scratch: the pinned bundle as loose files, and the
    # same overlaid with NIST's changed files. Both run through --vector-dir,
    # so the only difference between the two results is the change.
    scratch = Path(tempfile.mkdtemp(prefix="pqv-doctor-"))
    pinned_tree, work = scratch / "pinned", scratch / "candidate"
    cand_files = {}
    try:
        for name, doc in bundle.items():
            q = pinned_tree / name
            q.parent.mkdir(parents=True, exist_ok=True)
            q.write_bytes(raw_of(doc))
            p = work / name
            p.parent.mkdir(parents=True, exist_ok=True)
            if name in changed:
                p.write_bytes(changed[name])
                try:
                    cand_files[name] = json.loads(changed[name])
                except ValueError as e:
                    checks.append(Check(f"parse:{name}", BLOCK,
                                        f"{name} is not valid JSON", str(e),
                                        "do not pin; NIST may be mid-publish"))
                    return checks, changed, None
            else:
                p.write_bytes(raw_of(doc))
                cand_files[name] = doc_of(doc)

        checks.append(check_keycheck(cand_files, "candidate"))

        by_length, total = lengthonly_control(cand_files)
        if total:
            checks.append(Check(
                "control", OK if by_length == 0 else BLOCK,
                f"negative control: a length-only checker is fooled by all "
                f"{total} invalid encapsulation keys, so they test content"
                if by_length == 0 else
                f"negative control: {by_length}/{total} invalid encapsulation "
                f"keys are rejected on length alone",
                "" if by_length == 0 else
                "those vectors cannot show whether an implementation performs "
                "the FIPS 203 §7.2 modulus check",
                "" if by_length == 0 else "do not pin this revision"))

        # Side by side: the pinned bundle and the candidate, same suites.
        prefixes = sorted({p for p in SUITES for n in changed if n.startswith(p + "-")})
        # A changed sigGen file is checked by signing it: ~30 min, but a re-pin
        # of answers nobody recomputed is what this review exists to stop.
        opts = {p: {"siggen": True} for p in SUITE_SIGGEN
                if any(n.startswith(SUITE_SIGGEN[p]) for n in changed)}
        pinned = run_suites(pinned_tree, prefixes, opts)
        cand = run_suites(work, prefixes, opts)
        for pre in prefixes:
            a, b = pinned.get(pre), cand.get(pre)
            key = f"suite:{pre}"
            if isinstance(b, str):
                st = WARN if "missing" in b else BLOCK
                checks.append(Check(key, st, f"{pre}: the candidate could not be run", b,
                                    'pip install "pq-verify[full]"' if st == WARN
                                    else "do not pin until it parses and runs"))
                continue
            p, t, groups = b
            was = f"{a[0]}/{a[1]}" if isinstance(a, tuple) else "n/a"
            if p == t:
                checks.append(Check(key, OK, f"{pre}: candidate {p}/{t} "
                                             f"(pinned {was})"))
            else:
                bad = [f"{g} {v[0]}/{v[1]}" for g, v in groups.items() if v[0] != v[1]]
                checks.append(Check(
                    key, BLOCK, f"{pre}: candidate {p}/{t} (pinned {was})",
                    "failing: " + ", ".join(bad) + ". Either the reference "
                    "implementation or NIST's new answers are wrong; pinning "
                    "would ship a red suite.",
                    "compare the failing tcIds against NIST's commit message "
                    "before deciding"))
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    # Stability: NIST has reverted these files within a day before.
    today = datetime.date.today()
    young = []
    for name, raw in changed.items():
        seen = history.get(name, {}).get(hashlib.sha256(raw).hexdigest(), {})
        first = seen.get("first_seen")
        age = (today - datetime.date.fromisoformat(first)).days if first else None
        if age is None or age < STABLE_DAYS:
            young.append(f"{name} ({'never seen by the watcher' if age is None else f'{age} days'})")
    if young:
        checks.append(Check("stable", DECIDE,
                            f"{len(young)} changed file(s) are younger than "
                            f"{STABLE_DAYS} days", "; ".join(young),
                            "wait and re-run; NIST has reverted these files before"))
    else:
        checks.append(Check("stable", OK, f"every change has held for "
                                          f"{STABLE_DAYS}+ days"))

    # Provenance: which NIST commit, so MANIFEST can cite it.
    commits = {}
    for name in changed:
        c = nist_commit(name)
        if c:
            commits[name] = c
    unknown = [n for n in changed if n not in commits]
    if unknown:
        checks.append(Check(
            "provenance", WARN,
            f"could not identify the NIST commit for {len(unknown)} file(s)",
            "the GitHub API was unreachable or rate-limited; MANIFEST.json "
            "must cite the commit each file came from",
            "git clone --filter=blob:none https://github.com/usnistgov/ACVP-Server "
            "&& git -C ACVP-Server log -1 --format='%h %cs %s' -- "
            "gen-val/json-files/<file>; then --apply --commit <file>=<sha>"))
    else:
        checks.append(Check("provenance", OK, "NIST commits: " + "; ".join(
            f"{n.split('/')[0]} {c['sha']} ({c['date']}) \"{c['message']}\""
            for n, c in commits.items())))
    return checks, changed, commits


# ─────────────────────────────── apply ───────────────────────────────

def apply_candidate(repo, bundle, manifest, changed, commits):
    """Re-cut the archives and manifest. Deterministic: the same inputs produce
    byte-identical files, so the diff a reviewer sees is only the change.
    Only the archives holding a changed file are rewritten; the SLH-DSA
    signature archive keeps NIST's text verbatim, the main one parsed JSON."""
    P = paths(repo)
    touched = set()
    for name, raw in changed.items():
        verbatim = isinstance(bundle.get(name), str) or bool(_VECTOR_BUNDLES[_bundle_name(name)])
        bundle[name] = raw.decode() if verbatim else json.loads(raw)
        manifest[name] = {"bytes": len(raw),
                          "sha256": hashlib.sha256(raw).hexdigest(),
                          "nist_commit": commits[name]["sha"]}
        touched.add(_bundle_name(name))
    for arc in sorted(touched):
        entries = {k: v for k, v in bundle.items() if _bundle_name(k) == arc}
        write_bundle(P["bundles"][arc], entries, verbatim=bool(_VECTOR_BUNDLES[arc]))
    with open(P["manifest"], "w") as fh:
        json.dump(dict(sorted(manifest.items())), fh, indent=2)
        fh.write("\n")


# ─────────────────────────────── driver ───────────────────────────────

def token(manifest, changed, checks):
    """What was examined and what was found, as one hash: two runs with the
    same token saw the same vectors and reached the same findings."""
    h = hashlib.sha256()
    for k in sorted(manifest):
        h.update(f"{k}={manifest[k]['sha256']};".encode())
    for k in sorted(changed):
        h.update(f"cand:{k}={hashlib.sha256(changed[k]).hexdigest()};".encode())
    for c in checks:
        h.update(f"{c.status}:{c.key}:{c.headline};".encode())
    return h.hexdigest()[:16]


def run(repo, candidate=False, candidate_dir=None, apply=False, commit_overrides=None,
        skip_edge=False):
    P = paths(repo)
    bundle = load_bundle(P["bundles"])
    manifest = load_json(P["manifest"], {})
    baseline = load_json(P["baseline"], {})
    history = load_json(P["history"], {})

    checks = [check_manifest(bundle, manifest), check_watched(bundle),
              check_keycheck(bundle, "pinned")]
    ref_check, refs = check_references(repo)
    checks.append(ref_check)
    checks.append(check_edge_manifest(repo))
    checks.append(check_hbs_manifest(repo))
    checks.append(check_fndsa_manifest(repo))
    if not skip_edge:
        checks.append(check_reference_edges())
    up, moved = check_upstream_state(manifest, baseline, history)
    checks.append(up)
    changed, commits = {}, None

    if candidate or candidate_dir:
        cdir = candidate_dir
        scratch = None
        if not cdir:
            scratch = tempfile.mkdtemp(prefix="pqv-nist-")
            try:
                fetch_candidate(tracked(), scratch)
            except Exception as e:
                shutil.rmtree(scratch, ignore_errors=True)
                checks.append(Check("fetch", BLOCK, "could not fetch NIST's files",
                                    f"{type(e).__name__}: {e}",
                                    "check network access to raw.githubusercontent.com"))
                return checks, {}, token(manifest, {}, checks)
            cdir = scratch
        try:
            more, changed, commits = review_candidate(bundle, manifest, history,
                                                      cdir, refs)
        finally:
            if scratch:
                shutil.rmtree(scratch, ignore_errors=True)
        checks += more
        commits = dict(commits or {})
        for name, sha in (commit_overrides or {}).items():
            commits[name] = {"sha": sha}
        if commits and all(n in commits for n in changed):
            checks = [c for c in checks if c.key != "provenance"] + [
                Check("provenance", OK, "NIST commit recorded for every changed file")]

    if apply:
        # Only the candidate can make a re-pin unsafe. A BLOCK on the pinned
        # side (a malformed bundle, an incomplete manifest) is what a re-pin
        # repairs, so it does not refuse; the result is re-checked below.
        blocked = [c for c in checks if c.status == BLOCK and c.key not in PINNED_SIDE]
        unproven = [c for c in checks if c.key == "provenance" and c.status != OK]
        waiting = [c for c in checks if c.key == "stable" and c.status != OK]
        if not changed:
            checks.append(Check("apply", WARN, "--apply: nothing to pin"))
        elif blocked or unproven or waiting:
            why = blocked or unproven or waiting
            checks.append(Check("apply", BLOCK, "--apply refused: " + why[0].headline,
                                "the bundle was not changed", why[0].fix))
        else:
            apply_candidate(repo, bundle, manifest, changed, commits)
            checks.append(Check(
                "apply", OK, f"re-pinned {len(changed)} file(s); bundle and "
                             f"MANIFEST.json rewritten",
                "", "add the revisions to pq_verify/vectors/PROVENANCE.md and an "
                    "entry to CHANGELOG.md, run pytest, then open a PR"))
            # Re-check what was written, from disk, not from memory.
            nb, nm = load_bundle(P["bundles"]), load_json(P["manifest"], {})
            for c in (check_manifest(nb, nm), check_keycheck(nb, "re-pinned")):
                c.key = "after:" + c.key
                checks.append(c)
    return checks, changed, token(manifest, changed, checks)


def render(checks, tok):
    print("pq-verify doctor — pinned NIST vectors")
    print()
    for c in checks:
        print("  %-7s %s" % (c.status, c.headline))
        if c.status != OK:
            if c.detail:
                print("          " + c.detail)
            if c.fix:
                print("          next: " + c.fix)
            print()
    blocks = [c for c in checks if c.status == BLOCK]
    decides = [c for c in checks if c.status == DECIDE]
    print()
    if blocks:
        print("  Start here: " + blocks[0].headline)
        if blocks[0].fix:
            print("    " + blocks[0].fix)
        print()
    if decides:
        print("  Decisions owed (not faults):")
        for c in decides:
            print("    - " + c.headline)
        print()
    print("  %d blocked, %d decision(s) owed, %d warning(s).   token %s"
          % (len(blocks), len(decides),
             len([c for c in checks if c.status == WARN]), tok))
    return 1 if blocks else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=str(REPO), help="repository root")
    ap.add_argument("--candidate", action="store_true",
                    help="fetch NIST's current files and test them against the bundle")
    ap.add_argument("--candidate-dir", metavar="DIR",
                    help="test NIST files already on disk (DIR/<suite>/<file>.json)")
    ap.add_argument("--apply", action="store_true",
                    help="re-pin the candidate; refused while anything BLOCKs, a "
                         "change is younger than %d days, or its NIST commit is "
                         "unknown" % STABLE_DAYS)
    ap.add_argument("--commit", action="append", default=[], metavar="FILE=SHA",
                    help="NIST commit for a changed file, when the API is unreachable")
    ap.add_argument("--fast", action="store_true",
                    help="skip running the edge-case vectors against the references "
                         "(about 45 s); the edge bundle's digests are still checked")
    ap.add_argument("--json", action="store_true",
                    help="machine-readable; what an agent should read")
    a = ap.parse_args(argv)
    overrides = dict(x.split("=", 1) for x in a.commit)
    try:
        checks, changed, tok = run(a.repo, a.candidate, a.candidate_dir, a.apply,
                                   overrides, skip_edge=a.fast)
    except Exception as e:
        print(f"doctor could not run: {type(e).__name__}: {e}", file=sys.stderr)
        return 2
    if a.json:
        blocked = [c for c in checks if c.status == BLOCK]
        print(json.dumps({
            "token": tok,
            "blocked": len(blocked),
            "decisions_owed": len([c for c in checks if c.status == DECIDE]),
            "changed": sorted(changed),
            "next": blocked[0].as_dict() if blocked else None,
            "checks": [c.as_dict() for c in checks],
        }, indent=2))
        return 1 if blocked else 0
    return render(checks, tok)


if __name__ == "__main__":
    sys.exit(main())
