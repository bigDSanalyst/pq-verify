#!/usr/bin/env python3
"""Pin the Classic McEliece KATs (round 4; not a FIPS standard).

For each of the ten parameter sets, PQClean's NIST KAT harness (NIST's
AES-CTR DRBG, first record) is built on PQClean's reference code at a pinned
commit, and its output must hash to the nistkat-sha256 PQClean publishes in
the scheme's META.yml.

The public keys are 0.26 to 1.36 MB, so they are not pinned: the bundle keeps
the seed, private key, ciphertext and shared secret, and the published hash.
pq-verify's own keygen must regenerate the public key from the private key's
seed so exactly that the rebuilt KAT hashes to PQClean's published value
(pq_verify.mceliece.self_check) -- the reference proves itself on a key it was
never given.

    python tools/pin_mceliece_vectors.py --pqclean DIR   # rebuild from a checkout
    python tools/pin_mceliece_vectors.py                 # sparse-clone, rebuild
    python tools/pin_mceliece_vectors.py --check         # verify, no network
"""
import argparse
import gzip
import hashlib
import io
import json
import pathlib
import re
import resource
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parent.parent
VEC = REPO / "pq_verify" / "vectors"
BUNDLE = VEC / "mceliece_kat.json.gz"
MANIFEST = VEC / "MCELIECE_MANIFEST.json"

SOURCE = {
    "repo": "https://github.com/PQClean/PQClean",
    "commit": "0586a824fc0d49df0b6b6e9179d8d15d06d0974f",
    "date": "2026-08-04",
    "implementation": "clean (SUPERCOP-20221025, round 4)",
}
SETS = ("mceliece348864", "mceliece348864f", "mceliece460896", "mceliece460896f",
        "mceliece6688128", "mceliece6688128f", "mceliece6960119", "mceliece6960119f",
        "mceliece8192128", "mceliece8192128f")


def _sha(b):
    return hashlib.sha256(b).hexdigest()


def _published(pq, scheme):
    text = (pq / "crypto_kem" / scheme / "META.yml").read_text()
    return re.search(r"^nistkat-sha256:\s*([0-9a-f]{64})", text, re.M).group(1)


def _clone(dest):
    subprocess.run(["git", "clone", "-q", "--filter=blob:none", "--sparse",
                    SOURCE["repo"], str(dest)], check=True)
    subprocess.run(["git", "-C", str(dest), "checkout", "-q", SOURCE["commit"]], check=True)
    subprocess.run(["git", "-C", str(dest), "sparse-checkout", "set", "common", "test",
                    *(f"crypto_kem/{s}" for s in SETS)], check=True)


def _big_stack():
    # the harness keeps a public key of up to 1.36 MB on the stack
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))


def _generate(pq, scheme, work):
    impl = pq / "crypto_kem" / scheme / "clean"
    ns = "PQCLEAN_" + scheme.upper() + "_CLEAN"
    exe = work / f"nistkat-{scheme}"
    common = [str(pq / "common" / f) for f in ("fips202.c", "aes.c", "sha2.c")]
    subprocess.run(["gcc", "-O2", "-w", f"-I{pq / 'common'}", f"-I{impl}",
                    f"-DPQCLEAN_NAMESPACE={ns}", str(pq / "test" / "crypto_kem" / "nistkat.c"),
                    *common, str(pq / "test" / "common" / "nistkatrng.c"),
                    *map(str, sorted(impl.glob("*.c"))), "-o", str(exe)], check=True)
    return subprocess.run([str(exe)], check=True, capture_output=True,
                          preexec_fn=_big_stack).stdout


def _fields(raw):
    out = {}
    for line in raw.decode("ascii").splitlines():
        k, _, v = line.partition(" = ")
        out[k] = v
    return out


def build(pq):
    pq = pathlib.Path(pq)
    head = subprocess.run(["git", "-C", str(pq), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()
    if head != SOURCE["commit"]:
        raise SystemExit(f"{pq} is at {head}, not the pinned {SOURCE['commit']}")
    bundle, published = {}, {}
    with tempfile.TemporaryDirectory() as work:
        for scheme in SETS:
            want = _published(pq, scheme)
            raw = _generate(pq, scheme, pathlib.Path(work))
            if _sha(raw) != want:
                raise SystemExit(f"{scheme}: KAT {_sha(raw)} does not match META.yml {want}")
            f = _fields(raw)
            bundle[scheme] = {"seed": f["seed"].lower(), "sk": f["sk"].lower(),
                              "ct": f["ct"].lower(), "ss": f["ss"].lower(),
                              "pk_sha256": _sha(bytes.fromhex(f["pk"]))}
            published[scheme] = want
            print(f"  {scheme}: KAT matches META.yml nistkat-sha256 {want[:16]}...")
    return bundle, {"source": SOURCE, "published_nistkat_sha256": published,
                    "note": "public keys are not pinned; pq-verify regenerates them and the "
                            "rebuilt KAT must hash to the published value"}


def write(bundle, manifest):
    payload = json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode()
    buf = io.BytesIO()
    with gzip.GzipFile(filename="mceliece_kat.json", mode="wb", fileobj=buf,
                       mtime=0, compresslevel=9) as fh:
        fh.write(payload)
    BUNDLE.write_bytes(buf.getvalue())
    manifest = dict(manifest, bundle_sha256=_sha(buf.getvalue()))
    MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def verify(bundle_path=BUNDLE, manifest_path=MANIFEST):
    """Offline structure check: the bundle is the one the manifest names, and
    every set has its published hash. (That the entries ARE the KATs is
    proved by pq-verify --mceliece, which rebuilds each one.)"""
    problems = []
    bundle_path, manifest_path = pathlib.Path(bundle_path), pathlib.Path(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    if _sha(bundle_path.read_bytes()) != manifest.get("bundle_sha256"):
        problems.append("mceliece_kat.json.gz does not match MCELIECE_MANIFEST.json")
    with gzip.open(bundle_path, "rt") as fh:
        bundle = json.load(fh)
    if set(bundle) != set(SETS) or set(manifest["published_nistkat_sha256"]) != set(SETS):
        problems.append(f"the bundle covers {sorted(bundle)}, not the ten sets")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="verify offline, no build")
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
        return 1
    print(f"Classic McEliece KATs pinned: {len(SETS)} sets, each matching PQClean's "
          f"published nistkat-sha256")
    return 0


if __name__ == "__main__":
    sys.exit(main())
