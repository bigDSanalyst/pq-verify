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

No discrepancies were found in any implementation.

That is the expected and desirable outcome. These are mature, widely reviewed
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
  suites do: 855/855, or 975/975 including FIPS 205 key generation)
- constitute a security review of the surrounding implementation

A passing NTT audit says the transform is arithmetically correct. It does not
say the library is free of defects elsewhere.
