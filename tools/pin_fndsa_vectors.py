#!/usr/bin/env python3
"""Pin the FN-DSA (Falcon) vectors: DRAFT TRACK, ahead of FIPS 206.

NIST publishes no ACVP vectors for FN-DSA yet. The vectors pinned here are
the outputs of PQClean's own KAT generators for Falcon-512 and Falcon-1024,
run on PQClean's reference code at a pinned commit:

  nistkat      NIST's KAT harness and AES-CTR DRBG, first record (NIST's
               standard first seed)
  testvectors  PQClean's deterministic generator: a fresh key per message,
               messages of 0, 1, 4, 16, 64, 256 and 1024 bytes, each with a
               NIST-API signed message and a detached signature

They are anchored independently of this tool: PQClean publishes the sha256
of each output in the scheme's META.yml (nistkat-sha256,
testvectors-sha256), and every pinned file must hash to that value. The
manifest records those published hashes next to the files'; --check and
tools/doctor.py compare all three offline.

    python tools/pin_fndsa_vectors.py --pqclean DIR   # rebuild from a checkout
    python tools/pin_fndsa_vectors.py                 # sparse-clone, rebuild
    python tools/pin_fndsa_vectors.py --check         # verify, no network
"""
import argparse
import gzip
import hashlib
import io
import json
import pathlib
import re
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "tools"))
import pin_edge_vectors as _E                                  # noqa: E402

VEC = REPO / "pq_verify" / "vectors"
BUNDLE = VEC / "fndsa_vectors.json.gz"
MANIFEST = VEC / "FNDSA_MANIFEST.json"

SOURCE = {
    "repo": "https://github.com/PQClean/PQClean",
    "commit": "0586a824fc0d49df0b6b6e9179d8d15d06d0974f",
    "date": "2026-08-04",
}
SETS = {"FN-DSA-512": "falcon-512", "FN-DSA-1024": "falcon-1024"}
KINDS = {"nistkat": ("nistkat.c", "nistkatrng.c"),
         "testvectors": ("testvectors.c", "notrandombytes.c")}
LABEL = "PQClean Falcon reference (round 3), FIPS 206 draft track"


def _sha(b):
    return hashlib.sha256(b).hexdigest()


def _meta(pq, scheme):
    text = (pq / "crypto_sign" / scheme / "META.yml").read_text()
    return {k: re.search(rf"^{k}-sha256:\s*([0-9a-f]{{64}})", text, re.M).group(1)
            for k in KINDS}


def _clone(dest):
    subprocess.run(["git", "clone", "-q", "--filter=blob:none", "--sparse",
                    SOURCE["repo"], str(dest)], check=True)
    subprocess.run(["git", "-C", str(dest), "checkout", "-q", SOURCE["commit"]], check=True)
    subprocess.run(["git", "-C", str(dest), "sparse-checkout", "set", "common", "test",
                    *(f"crypto_sign/{s}" for s in SETS.values())], check=True)


def _generate(pq, scheme, kind, work):
    src, rng = KINDS[kind]
    impl = pq / "crypto_sign" / scheme / "clean"
    ns = "PQCLEAN_" + scheme.replace("-", "").upper() + "_CLEAN"
    exe = work / f"{kind}-{scheme}"
    common = [str(pq / "common" / f) for f in ("fips202.c", "aes.c", "sha2.c")]
    subprocess.run(["gcc", "-O2", "-w", f"-I{pq / 'common'}", f"-I{impl}",
                    f"-DPQCLEAN_NAMESPACE={ns}", str(pq / "test" / "crypto_sign" / src),
                    *common, str(pq / "test" / "common" / rng),
                    *map(str, sorted(impl.glob("*.c"))), "-o", str(exe), "-lm"], check=True)
    return subprocess.run([str(exe)], check=True, capture_output=True).stdout


def build(pq):
    pq = pathlib.Path(pq)
    head = subprocess.run(["git", "-C", str(pq), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()
    if head != SOURCE["commit"]:
        raise SystemExit(f"{pq} is at {head}, not the pinned {SOURCE['commit']}")
    source = dict(SOURCE, published={})
    bundle, files = {}, {}
    with tempfile.TemporaryDirectory() as work:
        for name, scheme in SETS.items():
            meta = _meta(pq, scheme)
            source["published"][name] = meta
            for kind in KINDS:
                raw = _generate(pq, scheme, kind, pathlib.Path(work))
                if _sha(raw) != meta[kind]:
                    raise SystemExit(f"{scheme} {kind}: output {_sha(raw)} does not match "
                                     f"META.yml {meta[kind]}")
                key = f"pqclean/{scheme}/{kind}"
                bundle[key] = raw.decode("ascii")
                files[key] = {"source": "pqclean", "set": name, "kind": kind,
                              "label": LABEL, "path": f"crypto_sign/{scheme}/META.yml "
                              f"({kind}-sha256)", "bytes": len(raw), "sha256": _sha(raw)}
    return bundle, {"sources": {"pqclean": source}, "files": files}


def write(bundle, manifest):
    payload = json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode()
    buf = io.BytesIO()
    with gzip.GzipFile(filename="fndsa_vectors.json", mode="wb", fileobj=buf,
                       mtime=0, compresslevel=9) as fh:
        fh.write(payload)
    BUNDLE.write_bytes(buf.getvalue())
    MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def verify(bundle_path=BUNDLE, manifest_path=MANIFEST):
    """Offline: each file hashes to its manifest digest AND to the digest
    PQClean publishes for it."""
    problems = _E.verify(bundle_path, manifest_path)
    manifest = json.loads(pathlib.Path(manifest_path).read_text())
    published = manifest["sources"]["pqclean"].get("published", {})
    for key, f in sorted(manifest["files"].items()):
        want = published.get(f.get("set"), {}).get(f.get("kind"))
        if want != f["sha256"]:
            problems.append(f"{key}: sha256 is not the one PQClean's META.yml publishes")
    if set(published) != set(SETS):
        problems.append(f"published hashes cover {sorted(published)}, not {sorted(SETS)}")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="verify the pinned bundle against its manifest, offline")
    ap.add_argument("--pqclean", help="a PQClean checkout at the pinned commit")
    a = ap.parse_args(argv)
    if not a.check:
        if a.pqclean:
            bundle, manifest = build(a.pqclean)
        else:
            with tempfile.TemporaryDirectory() as tmp:
                _clone(pathlib.Path(tmp) / "pqclean")
                bundle, manifest = build(pathlib.Path(tmp) / "pqclean")
        write(bundle, manifest)
    problems = verify()
    for p in problems:
        print(f"BLOCK  {p}")
    if problems:
        print(f"{len(problems)} problem(s)")
        return 1
    print(f"FN-DSA vectors sound: {len(json.loads(MANIFEST.read_text())['files'])} files "
          f"match FNDSA_MANIFEST.json and PQClean's published sha256")
    return 0


if __name__ == "__main__":
    sys.exit(main())
