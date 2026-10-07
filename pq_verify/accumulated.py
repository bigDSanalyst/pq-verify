"""
pq_verify.accumulated — accumulated vectors for ML-KEM and ML-DSA.

A few thousand pinned vectors exercise the edge cases someone thought of.
Accumulated vectors exercise the ones nobody did: thousands of seeded random
cases, generated on the fly from one SHAKE-128 stream (empty input), with
every output absorbed into a second SHAKE-128 whose 32-byte digest must equal
a pinned value. The integers involved are small (q = 3329, 8380417), so
10 000 random cases reach values no hand-picked vector does -- the class of
arithmetic slip behind KyberSlash. Go and BoringSSL run these in CI;
pq-verify runs them against a vendor's own entry points.

ML-KEM -- Go's construction (crypto/mlkem TestAccumulated), per case:
    draw d || z (64), m (32), then ct (an invalid ciphertext)
    absorb ek, ct and K (Encaps ek, m), and K' = Decaps(dk, random ct)
    and Decaps(dk, ct) must equal K       (checked, not absorbed)
dk is not absorbed, so a library that keeps dk in seed form (FIPS 203 §7.1)
is checked the same way as one that expands it.

Why not CCTV's ML-KEM values. C2SP CCTV's README publishes accumulated
ML-KEM digests that also absorb dk, attributed to pq-crystals. They are the
FIPS 203 *draft*: with K-PKE.KeyGen's G(d) in place of the final G(d || k),
pq-verify reproduces CCTV's ML-KEM-512 value exactly, and no implementation
of final FIPS 203 can match any of them. pq-verify does not use them.

ML-DSA -- CCTV's construction (ML-DSA/accumulated/README.md), per case:
    draw seed (32); absorb pk (KeyGen seed) and the deterministic signature
    of the empty message with an empty context; the signature must verify.
These CCTV values are final FIPS 204: dilithium-py and PQClean reproduce them.

Every pinned digest records where it comes from (SOURCES). The ML-KEM-512 and
ML-KEM-1024 values are not published anywhere for final FIPS 203; they were
computed with Go's construction and pinned only because independent
implementations agree on them, which the source says.
"""
import hashlib

CCTV = {"repo": "https://github.com/C2SP/CCTV",
        "commit": "50a8ecf2a220f4c8bdc4f085789b8e85c26829e7", "date": "2026-09-25"}

_GO = "Go 1.26.1 crypto/mlkem TestAccumulated (published)"
_CCTV_DSA = "C2SP CCTV 50a8ecf ML-DSA/accumulated (published)"
_AGREED = ("computed: PQClean (C), kyber-py (Python) and {third} (Go) agree; "
           "no final-FIPS-203 value is published")

# digest, source -- by parameter set and number of cases
EXPECTED = {
    "ML-KEM-512": {
        100: ("86b1b4703b8ffef6f7f3290c6dbce4ad954498a0673ded401a94828e8c519a59",
              _AGREED.format(third="CIRCL")),
        10_000: ("e0112db334d4240ca6feed5b0beab1318925edd4ff7d840c2ebe6d61971fc14c",
                 _AGREED.format(third="CIRCL"))},
    "ML-KEM-768": {
        100: ("1114b1b6699ed191734fa339376afa7e285c9e6acf6ff0177d346696ce564415", _GO),
        10_000: ("8a518cc63da366322a8e7a818c7a0d63483cb3528d34a4cf42f35d5ad73f22fc", _GO)},
    "ML-KEM-1024": {
        100: ("800018fec3e2723f73f1d657fe239b4d5d8782efaade297e8cd448e54cc2ac00",
              _AGREED.format(third="Go crypto/mlkem and CIRCL")),
        10_000: ("f1a3925c9cf8538bb104c56efb2f5ecb74cc3df25087460b73f6c873e96bcb6a",
                 _AGREED.format(third="Go crypto/mlkem and CIRCL"))},
    "ML-DSA-44": {
        100: ("d51148e1f9f4fa1a723a6cf42e25f2a99eb5c1b378b3d2dbbd561b1203beeae4", _CCTV_DSA),
        10_000: ("e7fd21f6a59bcba60d65adc44404bb29a7c00e5d8d3ec06a732c00a306a7d143", _CCTV_DSA)},
    "ML-DSA-65": {
        100: ("8358a1843220194417cadbc2651295cd8fc65125b5a5c1a239a16dc8b57ca199", _CCTV_DSA),
        10_000: ("5ff5e196f0b830c3b10a9eb5358e7c98a3a20136cb677f3ae3b90175c3ace329", _CCTV_DSA)},
    "ML-DSA-87": {
        100: ("8c3ad714777622b8f21ce31bb35f71394f23bc0fcf3c78ace5d608990f3b061b", _CCTV_DSA),
        10_000: ("80a8cf39317f7d0be0e24972c51ac152bd2a3e09bc0c32ce29dd82c4e7385e60", _CCTV_DSA)},
}
DEFAULT = 10_000
_CT = {"ML-KEM-512": 768, "ML-KEM-768": 1088, "ML-KEM-1024": 1568}


def counts(param_set):
    return sorted(EXPECTED.get(param_set, {}))


class _Stream:
    """The input SHAKE-128 stream (empty input), read sequentially. hashlib
    has no incremental output, so the whole stream for n cases is drawn once:
    at most 16.6 MB for 10 000 ML-KEM-1024 cases. (So no 1 000 000-case run
    yet: that needs a streaming XOF.)"""

    def __init__(self, nbytes):
        self.buf, self.pos = hashlib.shake_128(b"").digest(nbytes), 0

    def read(self, n):
        out = self.buf[self.pos:self.pos + n]
        self.pos += n
        return out


def run_kem(backend, param_set, n=DEFAULT, seed_dk=False):
    """(ok, detail). backend: keygen(d, z) -> (ek, dk), encaps(ek, m) -> (c, K),
    decaps(dk, c) -> K. A refusal (any Exception) of a valid input fails;
    anything else (a dead harness) propagates."""
    want, source = EXPECTED[param_set][n]
    ct_n = _CT[param_set]
    rng = _Stream(n * (96 + ct_n))
    acc = hashlib.shake_128()
    for i in range(n):
        d, z, m, bad = rng.read(32), rng.read(32), rng.read(32), rng.read(ct_n)
        try:
            ek, dk = backend.keygen(d, z)
            c, K = backend.encaps(ek, m)
            K_back = backend.decaps(dk, c)
            K_bad = backend.decaps(dk, bad)
        except Exception as exc:
            return False, f"case {i}: refused a valid input ({type(exc).__name__}: {exc})"
        if K_back != K:
            return False, f"case {i}: Decaps(dk, Encaps(ek, m)) returned a different key"
        if seed_dk and dk != d + z:
            return False, f"case {i}: the seed-form dk is not d || z"
        for x in (ek, c, K, K_bad):
            acc.update(x)
    return _verdict(acc, n, want, source)


def _verdict(acc, n, want, source):
    got = acc.hexdigest(32)
    if got == want:
        return True, f"{n:,} cases: digest {got[:16]}… matches ({source})"
    return False, f"{n:,} cases: digest {got}, expected {want} ({source})"


def run_dsa(backend, param_set, n=DEFAULT):
    """(ok, detail). backend: keygen(seed) -> (pk, sk),
    sign_pure(m, ctx, rnd, sk) -> sig, verify_pure(m, ctx, sig, pk) -> bool.
    NotImplementedError (a case the API cannot express) propagates."""
    want, source = EXPECTED[param_set][n]
    rng = _Stream(32 * n)
    acc = hashlib.shake_128()
    for i in range(n):
        seed = rng.read(32)
        pk, sk = backend.keygen(seed)
        sig = backend.sign_pure(b"", b"", bytes(32), sk)
        if not backend.verify_pure(b"", b"", sig, pk):
            return False, f"case {i}: its own deterministic signature does not verify"
        acc.update(pk)
        acc.update(sig)
    return _verdict(acc, n, want, source)


def source(param_set, n):
    return EXPECTED[param_set][n][1]
