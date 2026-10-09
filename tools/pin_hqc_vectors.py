#!/usr/bin/env python3
"""Pin the submitters' HQC code layer: generator polynomials and decoder answers.

For each code profile pq_verify.hqc knows, the submitters' reference
implementation is fetched at a pinned commit and built per parameter set. The
self-check's inputs (pq_verify.hqc.self_suite: built from a fixed seed, the
same on every Python) are run through ITS encoders and decoders, and a sha256
per category of (input, its answer) is recorded. `pq-verify --hqc` recomputes
every answer with pq-verify's own reference and must reproduce each digest --
so the reference agrees with the submitters' code on every codeword, tie,
between-two-codewords block, Hankel-built error pattern and whole received
word in the suite. The generator polynomials are copied from each
parameters.h (RS_POLY_COEFS) and the reference must compute them.

PQClean's clean code (the 2023-04-30 submission) is run on the same inputs as
a cross-check of the v5 profile: its digests must equal v5.0.0's.

    python tools/pin_hqc_vectors.py           # fetch, build, pin
    python tools/pin_hqc_vectors.py --check   # verify the manifest, no network
"""
import argparse
import json
import pathlib
import re
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / "tools"))

MANIFEST = REPO / "pq_verify" / "vectors" / "HQC_MANIFEST.json"
UPSTREAM = "https://gitlab.com/pqc-hqc/hqc.git"
SOURCES = {
    "v5": {"repo": UPSTREAM, "commit": "f46e54222ffb76706678a9ec8a43cd2188a12ab1",
           "date": "2025-08-22", "what": "HQC v5.0.0 (tag v5.0.0), src/ref"},
    "next": {"repo": UPSTREAM, "commit": "71090d4679837a0de1e6946284818184994d952a",
             "date": "2026-08-05", "what": "next-release branch (unreleased), src/ref"},
}
CROSS = {"v5": {"repo": "https://github.com/PQClean/PQClean",
                "commit": "0586a824fc0d49df0b6b6e9179d8d15d06d0974f", "date": "2026-08-04",
                "what": "PQClean clean (2023-04-30 submission)", "recipe": "pqclean-hqc"}}


def published_generator(src, param_set):
    from vendor_audit import HQC_DIRS
    text = (pathlib.Path(src) / "src" / "ref" / HQC_DIRS[param_set][1] / "parameters.h").read_text()
    m = re.search(r"#define\s+RS_POLY_COEFS\s*((?:[\s\\]*\d+\s*,?)+)", text)
    return [int(x) for x in re.findall(r"\d+", m.group(1))]


def answers(so, name, profile):
    """The library's own answers on the self-check inputs, as suite_digest
    reads them."""
    from pq_verify import hqc as H
    from pq_verify.hqc_audit import VendorHQC
    v = VendorHQC(so, name)
    C, cases = H.self_suite(name, profile)
    out = {}
    out["rs_encode"] = [(m, v.call("rs_encode", m, C.n1)[0]) for m, _ in cases["rs_encode"]]
    out["rm_encode"] = [(x, v.call("rm_encode", x, C.word_bytes)[0]) for x, _ in cases["rm_encode"]]
    out["code_encode"] = [(m, v.call("code_encode", m, C.word_bytes)[0])
                          for m, _ in cases["code_encode"]]
    out["rm_decode"] = [(w, labs, v.call("rm_decode", w, C.n1)[0])
                        for w, labs, _ in cases["rm_decode"]]
    out["rs_decode"] = [(lab, w, v.call("rs_decode", w, C.k)[0]) for lab, w, _ in cases["rs_decode"]]
    out["code_decode"] = [(lab, w, v.call("code_decode", w, C.k)[0])
                          for lab, w, _ in cases["code_decode"]]
    return H.suite_digest(out)


def build_all(work):
    from pq_verify import hqc as H
    from vendor_audit import fetch, build_hqc
    work = pathlib.Path(work)
    manifest = {"sources": SOURCES, "cross_checks": {}, "published_generator": {},
                "decoder_outputs": {},
                "note": "decoder_outputs: sha256 per category over (input, the submitters' "
                        "answer) on pq_verify.hqc.self_suite; pq-verify --hqc must reproduce "
                        "each with its own reference"}
    for profile, s in SOURCES.items():
        src = work / f"hqc-{s['commit'][:12]}"
        fetch(s["repo"], s["commit"], src)
        manifest["published_generator"][profile] = {}
        manifest["decoder_outputs"][profile] = {}
        for name in H.SETS:
            manifest["published_generator"][profile][name] = published_generator(src, name)
            so = build_hqc("hqc-ref", src, name, work, tag=f"-{profile}")
            manifest["decoder_outputs"][profile][name] = answers(so, name, profile)
            print(f"  {profile} {name}: pinned from {s['what']} {s['commit'][:7]}")
    for profile, c in CROSS.items():
        src = work / f"cross-{c['commit'][:12]}"
        fetch(c["repo"], c["commit"], src)
        for name in H.SETS:
            so = build_hqc(c["recipe"], src, name, work, tag=f"-cross-{profile}")
            got = answers(so, name, profile)
            if got != manifest["decoder_outputs"][profile][name]:
                raise SystemExit(f"{c['what']} {name} answers differently from "
                                 f"{SOURCES[profile]['what']}: the {profile} profile is not "
                                 f"one code layer")
            print(f"  {profile} {name}: {c['what']} answers identically")
        manifest["cross_checks"][profile] = {k: v for k, v in c.items() if k != "recipe"}
    return manifest


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="verify the manifest offline")
    ap.add_argument("--workdir", help="where to fetch and build (default: temporary)")
    a = ap.parse_args(argv)
    if not a.check:
        if a.workdir:
            manifest = build_all(a.workdir)
        else:
            with tempfile.TemporaryDirectory() as tmp:
                manifest = build_all(tmp)
        MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    from pq_verify import hqc as H
    problems = H.manifest_problems()
    for p in problems:
        print(f"BLOCK  {p}")
    if problems:
        return 1
    print("HQC code layer pinned: generator polynomials and the submitters' decoder "
          "answers for every profile and set")
    return 0


if __name__ == "__main__":
    sys.exit(main())
