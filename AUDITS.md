# Independent audits

Results of pointing pq-verify at post-quantum implementations it did not write.

Every result below was produced by **pq-verify v2.6.4**
(`pq_verify/core.py`, sha `7b305da30a33`) on 2026-08-08, against the exact
upstream commits recorded in each section. Every audit is reproducible with the
commands given; nothing here is asserted from memory.

---

## Summary

| Implementation | Scheme | Method | Result |
|---|---|---|---|
| liboqs (`mlkem-native`) | ML-KEM-768 | symbol audit | **3/3 VERIFIED** |
| liboqs (`mldsa-native`) | ML-DSA-65 | symbol audit | **3/3 VERIFIED** |
| PQClean | ML-KEM-768 | symbol audit | **3/3 VERIFIED** |
| PQClean | ML-DSA-65 | symbol audit | **3/3 VERIFIED** |
| pq-crystals reference | Kyber-768 | symbol audit | **3/3 VERIFIED** |
| pq-crystals reference | Dilithium-3 | symbol audit | **3/3 VERIFIED** |
| BoringSSL | ML-KEM-768 | vector cross-check | **25/25 byte-exact** |
| BoringSSL | ML-KEM-1024 | vector cross-check | **25/25 byte-exact** |
| *(negative control)* | ML-KEM & ML-DSA | symbol audit | **correctly FAILS** |
| mlkem-native | ML-KEM-512/768/1024 | full scheme + invalid keys | **80/80 VERIFIED** |
| PQClean `clean` | ML-KEM-512/768/1024 | full scheme + invalid keys | 70/80 — accepts all 10 invalid keys |

No arithmetic discrepancies were found in any implementation. The one finding
is behavioural: PQClean's ML-KEM API accepts keys NIST marks invalid (see
[Full-scheme KEM audit](#full-scheme-kem-audit-including-invalid-keys)).

The arithmetic result is the expected one. These are mature, widely reviewed
implementations — `mlkem-native` and `mldsa-native` ship CBMC formal proofs.
The result is not "pq-verify found problems in liboqs"; it is **an independent
field-native check agrees with the formally-verified implementations,
byte-for-byte**.

---

## What each audit checks

Three checks per target, all against pq-verify's own FIPS 203/204 reference —
not against the implementation itself:

1. **Primitivity** — that ζ has the multiplicative order the scheme requires.
   ML-KEM: ζ²⁵⁶ ≡ 1, ζ¹²⁸ ≡ −1 (order n → incomplete transform, 7 layers).
   ML-DSA: ζ⁵¹² ≡ 1, ζ²⁵⁶ ≡ −1 (order 2n → complete transform, 8 layers).
2. **Full NTT** — 100 random polynomials, every coefficient compared against an
   independently computed reference. Byte-exact or it fails.
3. **Freivalds** — probabilistic verification of the linear map via
   `r·y == (NTTᵀ r)·x`, 100 polynomials × 5 rounds. Separate 16-bit and 32-bit
   engines; they are not interchangeable.

Montgomery-domain output is normalised before comparison. Standards libraries
commonly leave NTT output in Montgomery form, and a naive comparison would
report every one of them as broken.

---

## Negative control

A verifier that only ever passes is not verifying anything. Each scan was
repeated with a single output coefficient incremented by one:

```
corrupted ML-KEM:  Full NTT 100/100 mismatches   Freivalds 100 failures   FAIL
corrupted ML-DSA:  Full NTT 100/100 mismatches   Freivalds 100 failures   FAIL
```

Both classes of check reject the corruption. A self-consistent test that could
not fail is precisely what allowed a layer-count error to survive in pq-verify
itself from v2.4.1 until v2.6.3 — see `RELEASE_NOTES_v2.6.3.md`.

---

## liboqs — `mlkem-native` / `mldsa-native`

liboqs no longer vendors PQClean for ML-KEM/ML-DSA; it ships the
`pq-code-package` native implementations, which carry CBMC proofs.

- `mlkem-native` @ `d1b2fe7` (2026-08-07)
- `mldsa-native` @ `1731b44` (2026-08-07)

```
PQCP_MLKEM_NATIVE_MLKEM768_poly_ntt
  Primitivity  zeta^256=1, zeta^128=-1   [7-layer incomplete NTT]
  Full NTT     100 polynomials, 0 mismatches
  Freivalds    100 x 5 rounds, 0 failures        -> 3/3 VERIFIED

PQCP_MLDSA_NATIVE_MLDSA65_poly_ntt
  Primitivity  zeta^512=1, zeta^256=-1   [8-layer complete NTT]
  Full NTT     100 polynomials, 0 mismatches
  Freivalds    100 x 5 rounds, 0 failures        -> 3/3 VERIFIED
```

Reproduce:

```bash
git clone --depth 1 https://github.com/pq-code-package/mlkem-native.git
cd mlkem-native && make lib
mkdir ext && cd ext && ar x ../test/build/libmlkem768.a
# the library expects the caller to supply randombytes(); the NTT never calls it
printf '#include <stdint.h>\n#include <stddef.h>\nvoid randombytes(uint8_t*o,size_t n){for(size_t i=0;i<n;i++)o[i]=(uint8_t)i;}\n' > stub.c
gcc -c -fPIC stub.c -o stub.o && gcc -shared -o libmlkem768.so *.o
```

```python
ntt = pqverify_load_so('libmlkem768.so', 'PQCP_MLKEM_NATIVE_MLKEM768_poly_ntt')
pqverify_scan(ntt)
```

---

## PQClean

PQClean @ `0586a82` (2026-08-04).

```
PQCLEAN_MLKEM768_CLEAN_ntt   -> 3/3 VERIFIED   [7-layer incomplete]
PQCLEAN_MLDSA65_CLEAN_ntt    -> 3/3 VERIFIED   [8-layer complete]
```

```bash
K=PQClean/crypto_kem/ml-kem-768/clean
D=PQClean/crypto_sign/ml-dsa-65/clean
gcc -O3 -fPIC -shared -I$K -o libpqc_mlkem.so $K/ntt.c $K/reduce.c
gcc -O3 -fPIC -shared -I$D -o libpqc_mldsa.so $D/ntt.c $D/reduce.c
```

---

## pq-crystals reference

The specification reference implementations.

- kyber @ `3edd5af` (2026-08-02)
- dilithium @ `d35ba3f` (2026-06-03)

```
pqcrystals_kyber768_ref_ntt      -> 3/3 VERIFIED
pqcrystals_dilithium3_ref_ntt    -> 3/3 VERIFIED
```

```bash
gcc -O3 -fPIC -shared -DKYBER_K=3 -o libkyber.so kyber/ref/ntt.c kyber/ref/reduce.c
gcc -O3 -fPIC -shared -DDILITHIUM_MODE=3 -o libdili.so dilithium/ref/ntt.c dilithium/ref/reduce.c
```

---

## BoringSSL — vector cross-check

BoringSSL @ `922245a` (2026-08-07).

**BoringSSL cannot be audited by symbol.** Its NTT is declared `inline` inside
an anonymous namespace:

```cpp
namespace mlkem {
namespace {
  inline void scalar_ntt(scalar *s)
```

`inline` + anonymous namespace gives internal linkage — the symbol never
reaches the shared object. The same applies to their ML-DSA. This is a property
of how BoringSSL builds, not a limitation of pq-verify, and it is common in
production libraries that inline for performance.

BoringSSL does ship NIST-derived vectors in-tree, so the cross-check runs
against those instead:

```
crypto/mlkem/mlkem768_nist_keygen_tests.txt    25/25 byte-exact
crypto/mlkem/mlkem1024_nist_keygen_tests.txt   25/25 byte-exact
```

Each case supplies `(z, d)` and the expected `(ek, dk)`; pq-verify's FIPS 203
reference reproduces both exactly.

Incidentally, BoringSSL's own source comment corroborates the ML-KEM structure
the audits assume: *"transform leaves off the last iteration of the usual FFT
code, with the 128 relevant roots of unity being stored in kNTTRoots."*

---

## Full-scheme KEM audit, including invalid keys

`--audit-kem` drives a library's own `keypair_derand` / `enc_derand` / `dec`
with NIST's ACVP vectors (NIST ACVP-Server `15c0f3d`, `ad33b3d`). Besides the
byte-exact stages it feeds NIST's **invalid** keys and checks the library
refuses them (nonzero return) while accepting the valid ones:

- `ekCheck`: 5 encapsulation keys with a coefficient ≥ q (FIPS 203 §7.2)
- `dkCheck`: 5 decapsulation keys with a corrupted H(ek) (FIPS 203 §7.3)

It then runs the pinned C2SP edge-case vectors (Wycheproof `3fa63dd`, CCTV
`50a8ecf`; `pq_verify/vectors/EDGE_MANIFEST.json`), per parameter set:

- `edgeValid`: `strcmp`-trap ciphertexts, unlucky-sampling seeds, malleated
  ciphertexts that must take implicit rejection, and Wycheproof's other valid
  vectors, byte-exact
- `edgeEk`: every coefficient value q…4095 at every position of an
  encapsulation key (CCTV `modulus`) plus Wycheproof's unreduced keys, all
  of which must be refused
- `edgeDk`: decapsulation keys with a corrupted H(ek) or embedded ek

Wrong-length inputs are not applicable to a C entry point, which takes
fixed-size buffers; they are run against the Python references instead
(`pq-verify --edge-cases`).

This table is not a one-off snapshot. Each row pins a library to an exact
commit (`tools/vendor_audits.json`), and CI rebuilds every row and re-runs the
audit on every change to pq-verify and weekly
(`.github/workflows/vendor-audits.yml`). The library, the vectors and the
reference implementations are all pinned, so a row can only change if
pq-verify does. Rows are only ever added: a newer library commit becomes a new
row beside the old one, so the table records when a library's behaviour
changed. A test holds this table equal to the pinned file.

<!-- vendor-audits:begin -->
| Library | Commit | Sets | keyGen | encaps | decaps | ekCheck | dkCheck | Edge cases | Result |
|---|---|---|---|---|---|---|---|---|---|
| mlkem-native | [`fc269bc`](https://github.com/pq-code-package/mlkem-native/commit/fc269bc2d1068486625a3775310c2c1f28d74732) (2026-09-27) | 512 / 768 / 1024 | 25/25 | 25/25 | 10/10 | 10/10 | 10/10 | 4,320/4,320 | 80/80 + 4,320/4,320 **VERIFIED** |
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | 512 / 768 / 1024 | 25/25 | 25/25 | 10/10 | 5/10 | 5/10 | 1,383/4,320 | 70/80 + 1,383/4,320 findings |
<!-- vendor-audits:end -->

Reproduce every row: `python3 tools/vendor_audit.py`.

PQClean's outputs are byte-exact with NIST, but `crypto_kem_enc` and
`crypto_kem_dec` return 0 for every one of NIST's invalid keys: the API has no
rejection path. FIPS 203 lets the check run outside `Encaps`/`Decaps` (for
example once, when a key is received), so this is not by itself a
non-conformance. It does mean every caller of this API must perform the
§7.2/§7.3 check itself; a caller that relies on the library does not get one.
mlkem-native performs both checks inside `enc`/`dec` and rejects all ten.
The edge cases confirm it at scale: PQClean accepts all 2,931 invalid
encapsulation keys and all 6 invalid decapsulation keys, while every one of
its outputs on valid input is byte-exact; mlkem-native refuses every one.

Before this audit could be run, two resolver faults had to be fixed: it could
not find mlkem-native's `_dec`, and given that, it bound the internal
`indcpa_keypair_derand` instead of `keypair_derand` and reported a false
35/60 against a correct library. Symbols are now matched by exact suffix,
internal K-PKE routines are excluded, and an ambiguous match is refused rather
than guessed (`--kem-keypair` / `--kem-encaps` / `--kem-decaps` name them).

Reproduce (ML-KEM-768; substitute 512 or 1024):

```bash
git clone https://github.com/pq-code-package/mlkem-native.git   # fc269bc
printf '#include <stdint.h>\n#include <stddef.h>\nint randombytes(uint8_t*o,size_t n){for(size_t i=0;i<n;i++)o[i]=(uint8_t)i;return 0;}\n' > rb.c
gcc -O2 -fPIC -shared -DMLK_CONFIG_PARAMETER_SET=768 -Imlkem-native/mlkem \
    -o libmlkemnative768.so mlkem-native/mlkem/mlkem_native.c rb.c
pq-verify --audit-kem ./libmlkemnative768.so ML-KEM-768

git clone https://github.com/PQClean/PQClean.git                  # 0586a82
cd PQClean/crypto_kem/ml-kem-768/clean
gcc -O2 -fPIC -shared -I../../../common -o libpqclean768.so \
    *.c ../../../common/fips202.c ../../../common/randombytes.c
pq-verify --audit-kem ./libpqclean768.so ML-KEM-768
```

---

## Which implementations can be audited by symbol

| Linkage | Examples | Symbol audit |
|---|---|---|
| exported, namespaced | liboqs native, PQClean, pq-crystals | yes |
| `static` | wolfSSL (`static void mlkem_ntt`) | only via a source-level shim |
| `inline` in anonymous namespace | BoringSSL | no |
| C++ templates | Botan (`KyberPolyNTT`) | no |

Reference and portable implementations tend to export; production
implementations tend to hide internals for optimisation. Where symbols are
unavailable, vector cross-checking applies to any implementation that can
produce output — which is every one of them.

---

## Scope

These audits verify the **number-theoretic transform** against the FIPS 203/204
definitions. They do not:

- verify constant-time behaviour or side-channel resistance
- verify the full KEM/signature scheme end-to-end (that is what the ACVP
  suites do: 1479/1479 with FIPS 205 keyGen and sigVer, 2103/2103 with
  SLH-DSA sigGen)
- constitute a security review of the surrounding implementation

A passing NTT audit says the transform is arithmetically correct. It does not
say the library is free of defects elsewhere.
