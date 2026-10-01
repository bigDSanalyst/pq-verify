#!/usr/bin/env python3
"""Pin Wycheproof and CCTV edge-case vectors into pq_verify/vectors/.

NIST's ACVP vectors are mostly well-formed inputs. The bugs that ship in real
ML-KEM / ML-DSA code sit at the edges: an encapsulation key with one
coefficient >= q, a ciphertext whose re-encryption differs only after a zero
byte (strcmp), a seed that forces unusually many XOF reads, a signature whose
hint encoding is out of order. C2SP's Wycheproof and CCTV projects collect
exactly those, each with the bug class it targets.

This tool fetches the files below from ONE commit of each repository and
writes, deterministically:

    pq_verify/vectors/edge_vectors.json.gz   {bundle key: upstream text}
    pq_verify/vectors/EDGE_MANIFEST.json     sources, commits, sha256 per file

Upstream text is stored verbatim, so sha256 of a stored entry equals sha256
of the file at that commit (for CCTV's .txt.gz files, of the decompressed
text; the gzip's own digest is kept as `upstream_sha256`). tools/doctor.py
re-checks every digest offline.

    python tools/pin_edge_vectors.py            # fetch the pinned commits
    python tools/pin_edge_vectors.py --check    # verify the bundle, no network
"""
import argparse
import gzip
import hashlib
import io
import json
import pathlib
import sys
import urllib.request

REPO = pathlib.Path(__file__).resolve().parent.parent
VEC = REPO / "pq_verify" / "vectors"
BUNDLE = VEC / "edge_vectors.json.gz"
MANIFEST = VEC / "EDGE_MANIFEST.json"

SOURCES = {
    "wycheproof": {
        "repo": "https://github.com/C2SP/wycheproof",
        "raw": "https://raw.githubusercontent.com/C2SP/wycheproof",
        "commit": "3fa63dd0344abb611f1fb1d77e119938603ea230",
        "date": "2026-09-02",
    },
    "cctv": {
        "repo": "https://github.com/C2SP/CCTV",
        "raw": "https://raw.githubusercontent.com/C2SP/CCTV",
        "commit": "50a8ecf2a220f4c8bdc4f085789b8e85c26829e7",
        "date": "2026-09-25",
    },
}

_KEM = ("512", "768", "1024")
_DSA = ("44", "65", "87")

# Left out on purpose: Wycheproof mlkem_*_keygen_seed (plain KATs, covered by
# NIST keyGen) and mldsa_*_sign_noseed (the sign_seed files carry the same
# cases with the seed, which pq-verify can use to rebuild the key).
FILES = (
    [("wycheproof", f"testvectors_v1/mlkem_{p}_test.json") for p in _KEM]
    + [("wycheproof", f"testvectors_v1/mlkem_{p}_encaps_test.json") for p in _KEM]
    + [("wycheproof", f"testvectors_v1/mlkem_{p}_semi_expanded_decaps_test.json") for p in _KEM]
    + [("wycheproof", f"testvectors_v1/mldsa_{p}_verify_test.json") for p in _DSA]
    + [("wycheproof", f"testvectors_v1/mldsa_{p}_sign_seed_test.json") for p in _DSA]
    + [("cctv", f"ML-KEM/strcmp/ML-KEM-{p}.txt") for p in _KEM]
    + [("cctv", f"ML-KEM/unluckysample/ML-KEM-{p}.txt") for p in _KEM]
    + [("cctv", f"ML-KEM/modulus/ML-KEM-{p}.txt.gz") for p in _KEM]
)


def bundle_key(source, path):
    return f"{source}/{path[:-3] if path.endswith('.gz') else path}"


def _sha(b):
    return hashlib.sha256(b).hexdigest()


def fetch(source, path):
    s = SOURCES[source]
    url = f"{s['raw']}/{s['commit']}/{path}"
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()


def build(fetcher=fetch):
    bundle, files = {}, {}
    for source, path in FILES:
        raw = fetcher(source, path)
        entry = {"source": source, "path": path}
        if path.endswith(".gz"):
            entry["upstream_sha256"] = _sha(raw)
            raw = gzip.decompress(raw)
        text = raw.decode("utf-8")
        key = bundle_key(source, path)
        bundle[key] = text
        entry.update(bytes=len(raw), sha256=_sha(raw))
        files[key] = entry
    manifest = {"sources": SOURCES, "files": files}
    return bundle, manifest


def write(bundle, manifest):
    payload = json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode()
    buf = io.BytesIO()
    # mtime=0 and a fixed name: the same inputs give the same bytes.
    with gzip.GzipFile(filename="edge_vectors.json", mode="wb", fileobj=buf,
                       mtime=0, compresslevel=9) as fh:
        fh.write(payload)
    BUNDLE.write_bytes(buf.getvalue())
    MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def verify(bundle_path=BUNDLE, manifest_path=MANIFEST):
    """Offline: every stored entry hashes to its manifest digest. Returns
    a list of problems (empty when sound)."""
    with gzip.open(bundle_path, "rt", encoding="utf-8") as fh:
        bundle = json.load(fh)
    manifest = json.loads(pathlib.Path(manifest_path).read_text())
    files = manifest["files"]
    problems = []
    for key in sorted(set(files) - set(bundle)):
        problems.append(f"{key}: in EDGE_MANIFEST.json, missing from the bundle")
    for key in sorted(set(bundle) - set(files)):
        problems.append(f"{key}: in the bundle, not described by EDGE_MANIFEST.json")
    for key in sorted(set(files) & set(bundle)):
        raw = bundle[key].encode("utf-8")
        if _sha(raw) != files[key]["sha256"] or len(raw) != files[key]["bytes"]:
            problems.append(f"{key}: content does not match its pinned sha256")
        src = files[key].get("source")
        if src not in manifest.get("sources", {}) or \
                len(manifest["sources"][src].get("commit", "")) != 40:
            problems.append(f"{key}: source {src!r} has no full pinned commit")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="verify the pinned bundle against its manifest, offline")
    a = ap.parse_args(argv)
    if a.check:
        problems = verify()
        for p in problems:
            print(f"BLOCK  {p}")
        print("edge vectors sound" if not problems else f"{len(problems)} problem(s)")
        return 1 if problems else 0
    bundle, manifest = build()
    write(bundle, manifest)
    problems = verify()
    if problems:
        for p in problems:
            print(f"BLOCK  {p}")
        return 1
    print(f"pinned {len(bundle)} files -> {BUNDLE.relative_to(REPO)} "
          f"({BUNDLE.stat().st_size // 1024} KiB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
