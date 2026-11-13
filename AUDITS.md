# Implementations pq-verify has audited

Results of pointing pq-verify at post-quantum implementations it did not write.

Every result below is pinned to the exact upstream commit its section
records, and each section gives the commands to reproduce it; nothing here is
asserted from memory.
- **The tables between `vendor-audits` markers** are written by
  `tools/vendor_audit.py`. CI's `vendor-audits.yml` rebuilds each of those
  libraries and re-audits it with the current pq-verify, on every change to
  the audit code and weekly, and fails if any row's result differs.
- **The symbol audits, the BoringSSL cross-check and the negative control**
  in the first sections were produced by pq-verify v2.6.4
  (`pq_verify/core.py`, sha `7b305da30a33`) on 2026-08-08. CI does not
  re-run them.

Each claim, with the command that reproduces it and the CI job that re-runs
it, is in [EVIDENCE.md](EVIDENCE.md).

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
| mlkem-native | ML-KEM-512/768/1024 | full scheme + invalid keys | **240/240 VERIFIED** |
| PQClean `clean` | ML-KEM-512/768/1024 | full scheme + invalid keys | 210/240 — accepts all 30 invalid keys, 10 per set |
| liboqs 0.16.0, `OQS_*` API and each backend | ML-KEM-512/768/1024 | full scheme + invalid keys + edge cases + constant time | **4,569/4,569 VERIFIED** per implementation |
| liboqs 0.16.0, `OQS_*` API | ML-DSA-44/65/87 | full scheme through the public API | **1,068/1,068 VERIFIED** |
| liboqs 0.16.0, mldsa-native C and x86-64 | ML-DSA-44/65/87 | full scheme | **1,548/1,548 VERIFIED** each |
| liboqs 0.16.0, `OQS_SIG_falcon_*` | FN-DSA-512/1024 (draft) | verify, reject, keyGen, sign | **227/227 VERIFIED** (padded and not) |
| slhdsa-c | SLH-DSA, all 12 sets | full scheme, three interfaces + refusals | **1,740/1,740 VERIFIED** |
| liboqs 0.16.0, `OQS_SIG_slh_dsa_*` | SLH-DSA, all 12 sets | full scheme through the public API + refusals | **2,088/2,088 VERIFIED** |
| Bouncy Castle 1.86 (Java), through pq-verify's harness | ML-KEM-512/768/1024 | full scheme + invalid keys + edge cases | **4,755/4,755 VERIFIED** |
| Bouncy Castle 1.86 (Java), through pq-verify's harness | ML-DSA-44/65/87 | full scheme (no external μ or 256-byte contexts) + every pre-hash verifier | **1,368/1,368 VERIFIED** |

No arithmetic discrepancies were found in the implementations in this table.
Its one finding is behavioural: PQClean's ML-KEM API accepts keys NIST marks
invalid (see [Full-scheme KEM audit](#full-scheme-kem-audit-including-invalid-keys)).
The audits further down add two more: two key-state defects in
xmss-reference ([LMS/HSS and XMSS](#lmshss-and-xmss-library-audit-with-mutants)),
and two defects in the HQC submitters' AVX2 Reed–Muller decoder
([HQC](#hqc-decoder-audit--standard-not-final-with-mutants)).

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

## liboqs 0.16.0 — full scheme, per implementation

The symbol audit above checks one NTT. This one drives liboqs end to end, as
distributions ship it: [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183)
(the 0.16.0 release, 2026-07-09), built with CMake, `OQS_DIST_BUILD=ON` (every
backend compiled in, one chosen at run time by CPU), `BUILD_SHARED_LIBS=ON`,
`OQS_USE_OPENSSL=OFF`, and only ML-KEM, ML-DSA and Falcon enabled.

**One library, several implementations.** That build exports liboqs's public
API and, beside it, each backend it dispatches to:

| Scheme | Public API | Backends exported |
|---|---|---|
| ML-KEM | `OQS_KEM_ml_kem_{512,768,1024}_*` | mlkem-native C and x86-64 (`PQCP_MLKEM_NATIVE_MLKEM768_{C,X86_64}_*`) |
| ML-DSA | `OQS_SIG_ml_dsa_{44,65,87}_*` | mldsa-native C and x86-64, with its full internal API |
| Falcon | `OQS_SIG_falcon{,_padded}_{512,1024}_*` | none (PQClean's code is not exported) |
| Classic McEliece (not FIPS) | `OQS_KEM_classic_mceliece_*` | none (only the AVX2 backend's assembly helpers are); audited in two builds of its own, [below](#classic-mceliece-library-audit--not-a-fips-standard-with-mutants) |

pq-verify refuses to choose between them and lists them;
`--symbol-prefix` names one. Each is audited separately, because the public
API runs only the backend the CPU selects: on a machine with AVX2 the C
backend is never exercised through it, and on one without, the x86-64 one
never is.

**What can be checked through each:**

- *ML-KEM*, all three: every NIST vector, the FIPS 203 key checks, the
  Wycheproof/CCTV edge cases and 10 000 accumulated cases per set, and the
  constant-time check on the public API and the C backend.
- *ML-DSA through `OQS_SIG_ml_dsa_*`*: its verify takes the message first,
  and its context variants are `*_sign_with_ctx_str` / `*_verify_with_ctx_str`;
  pq-verify calls them in that order (the `oqs` convention). Its randomness
  comes through liboqs's own documented hook,
  `OQS_randombytes_custom_algorithm`, so keyGen and pure sigGen are byte-exact
  against NIST with no special build, and a call drawing more or fewer bytes
  than FIPS 204 specifies is a finding. The API has no internal, pre-hash or
  external-μ entry points: those vectors, and the pre-hash round trips, are
  not applicable (504 across the three sets), never passed.
- *ML-DSA through each mldsa-native backend*: the full scheme, internal,
  pure, pre-hash and external μ, and every pre-hash function's verifier.
- *Falcon*: as for PQClean, except the signed-message `open` API and
  wrong-length keys, which liboqs's API cannot express.

**Mutants**, nine, one planted bug each, every one caught in CI. In liboqs's
own wrapper layer: ML-KEM's wrapper reporting success when Encaps refuses an
invalid key (fails ekCheck); ML-DSA's `sign_with_ctx_str` and
`verify_with_ctx_str` dropping the context (fail pure sigGen and sigVer);
Falcon's verify wrappers, padded and not, reporting success whatever the
verifier returns (fail reject). In each backend, through its own binding:
the C backend skipping FIPS 203's hash check on dk (fails dkCheck), the
x86-64 one skipping the modulus check on ek (fails ekCheck), and either
mldsa-native backend accepting a repeated hint index (fails Wycheproof's
verify vectors) -- the last proving the audit sees bugs through the v1
calling convention, not only that it runs. The wrapper mutants sit on the
x86-64 path, which CI's runner (AVX2) takes.

**What auditing liboqs found in pq-verify** (all fixed with this audit; no
defect was found in liboqs):

- The mldsa-native that liboqs vendors predates mldsa-native 2.0.0 and passes
  signature lengths (`size_t *siglen`), where 2.0.0 made them fixed-size. pq-
  verify knew only the 2.0.0 convention, so the backends crashed the audit
  (reported CANNOT VERIFY, never passed). It now tells them apart by the
  signed-message API (`_sign`, `_open`) that 2.0.0 removed.
- Naming `OQS_SIG_ml_dsa_*` entry points explicitly would have bound them
  with mldsa-native's argument order. The convention now follows the
  symbols actually bound, and a binding mixing liboqs's API with a backend's
  is refused.
- An explicitly named `verify` or `sign` was silently replaced when a
  context-taking variant was also found. An explicit binding now always
  stands.
- Used from Python in one process, the ML-DSA audit left liboqs's RNG hook
  installed, so liboqs used afterwards drew zeros (Falcon signing in the same
  process repeated its nonce, which the sign stage caught). The hook is now
  installed only while seeds are queued and handed back (liboqs's `system`
  RNG) when the audit ends. The command line was never affected: each audit
  runs in a child process.

---

## PQClean

PQClean @ `0586a82` (2026-08-04), its last commit: PQClean is retired and
archived read-only. Its README's retirement notice points to maintained
implementations; this file audits all but two of them:

| Named in the notice | Scheme | Audited here |
|---|---|---|
| mlkem-native | ML-KEM | [full scheme](#full-scheme-kem-audit-including-invalid-keys) |
| mldsa-native | ML-DSA | [full scheme](#full-scheme-ml-dsa-audit-with-mutants) |
| slhdsa-c | SLH-DSA | [full scheme](#slh-dsa-library-audit-with-mutants) |
| liboqs | ML-KEM, ML-DSA, SLH-DSA, FN-DSA, Classic McEliece | [per implementation](#liboqs-0160--full-scheme-per-implementation) |
| the HQC submitters' code | HQC | [code layer](#hqc-decoder-audit--standard-not-final-with-mutants) |
| Thomas Pornin's FN-DSA | FN-DSA | not yet; PQClean's and liboqs's Falcon are |
| libmceliece | Classic McEliece | not yet; PQClean's and liboqs's are |

PQClean's own rows stay: they record what its final code does.

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
refuses them (nonzero return) while accepting the valid ones. In each
parameter set:

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
| Library | Commit | Sets | keyGen | encaps | decaps | ekCheck | dkCheck | Edge cases | Accumulated | Constant time | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| mlkem-native | [`fc269bc`](https://github.com/pq-code-package/mlkem-native/commit/fc269bc2d1068486625a3775310c2c1f28d74732) (2026-09-27) | 512 / 768 / 1024 | 75/75 | 75/75 | 30/30 | 30/30 | 30/30 | 4,320/4,320 | 3/3 | 6/6 | — | 240/240 + 4,320/4,320 + 3/3 **VERIFIED** |
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | 512 / 768 / 1024 | 75/75 | 75/75 | 30/30 | 15/30 | 15/30 | 1,383/4,320 | 3/3 | 6/6 | 3/3 | 210/240 + 1,383/4,320 + 3/3 findings |
| liboqs 0.16.0 — OQS API | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 512 / 768 / 1024 | 75/75 | 75/75 | 30/30 | 30/30 | 30/30 | 4,320/4,320 | 3/3 | 6/6 | 1/1 | 240/240 + 4,320/4,320 + 3/3 **VERIFIED** |
| liboqs 0.16.0 — mlkem-native C backend | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 512 / 768 / 1024 | 75/75 | 75/75 | 30/30 | 30/30 | 30/30 | 4,320/4,320 | 3/3 | 6/6 | 1/1 | 240/240 + 4,320/4,320 + 3/3 **VERIFIED** |
| liboqs 0.16.0 — mlkem-native x86-64 backend | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 512 / 768 / 1024 | 75/75 | 75/75 | 30/30 | 30/30 | 30/30 | 4,320/4,320 | 3/3 | 6/6 | 1/1 | 240/240 + 4,320/4,320 + 3/3 **VERIFIED** |
<!-- vendor-audits:end -->

Each count is over all three parameter sets. **Result** adds the NIST
vectors, the edge cases and the accumulated check. The constant-time checks
are not in it, but a row is **VERIFIED** only if they pass too, and CI
requires each mutant to be caught.

Reproduce every row: `python3 tools/vendor_audit.py`.

PQClean's outputs are byte-exact with NIST, but `crypto_kem_enc` and
`crypto_kem_dec` return 0 for every one of NIST's invalid keys: the API has no
rejection path. FIPS 203 lets the check run outside `Encaps`/`Decaps` (for
example once, when a key is received), so this is not by itself a
non-conformance. It does mean every caller of this API must perform the
§7.2/§7.3 check itself; a caller that relies on the library does not get one.
mlkem-native performs both checks inside `enc`/`dec` and rejects all ten in
each set.
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

## Full-scheme ML-DSA audit, with mutants

`--audit-dsa` drives a library's own ML-DSA key generation, signing and
verification with every NIST ACVP ML-DSA vector for a parameter set (NIST
ACVP-Server `2972def`, `a7f283c`: 25 keyGen, 120 sigGen, 60 sigVer), and
with Wycheproof's ML-DSA verify and sign vectors (`3fa63dd`), which add
malleated hint encodings, out-of-range norms, wrong lengths and contexts
over 255 bytes.

Every FIPS 204 interface is a separate stage: **internal** (Algorithms 7/8),
**pure** (2/3), **pre-hash** HashML-DSA over all twelve approved hashes (4/5)
and **external μ**. Each NIST case goes through the most public entry point
the library has for it (the one its users call), and the report names that
symbol per stage. A case no entry point can express (no external-μ API, a
fixed-size signature argument given a wrong-length signature) is counted as
**not applicable**, with the reason, and never as a pass.

**NIST's verification vectors miss nine of the twelve pre-hash functions.**
In every parameter set they hold a valid HashML-DSA signature for only three
of the twelve, and five (SHA2-256, SHA2-512, SHA2-512/224, SHA3-384 and
SHA3-512) have none in any set. A verifier that encodes any of the other
nine wrongly passes every NIST sigVer vector: it is never shown a valid
signature it must accept. Signing is covered for all twelve, so a signer
that encodes wrongly fails NIST's sigGen vectors. So where the library has
its own HashML-DSA verifier, for each pre-hash function it must accept a
signature the library made with it (the "every pre-hash verifies" column).
Where pre-hash verification is reached only through `verify_internal`, pq-verify
builds M′ itself, NIST's vectors already check that encoding, and the check
is not applicable. A mutant shows the gap: mldsa-native verifying SHA3-512
pre-hashes under SHA2-512's OID passes every NIST and Wycheproof vector, and
only this check fails.

NIST's vectors are seeded, so an API that draws its own randomness can only
be checked byte-exactly if pq-verify controls that randomness. The libraries
below are linked with `pq_verify/harness/pqv_randombytes.c`, which serves
NIST's seed and `rnd` to `randombytes()` and records any call that draws
more or less than FIPS 204 calls for. That is how the randomised
`keypair()` and `signature()` the libraries' users call are audited, not
only the seed-taking internal functions.

<!-- vendor-audits-dsa:begin -->
| Library | Commit | Sets | keyGen | sigGen int / pure / pre-hash / μ | sigVer int / pure / pre-hash / μ | Every pre-hash verifies | Wycheproof verify / sign / length | Accumulated | Constant time | Not applicable | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| mldsa-native | [`159509d`](https://github.com/pq-code-package/mldsa-native/commit/159509d78063316bf090bbcd0aa50af5bb03cf70) (2026-10-01) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / 90/90 | 45/45 / 45/45 / 45/45 / 45/45 | 36/36 | 610/610 / 278/278 / n/a | 3/3 | 6/6 | 30 | 10/10 | 1,542/1,542 **VERIFIED** |
| pq-crystals dilithium ref | [`d35ba3f`](https://github.com/pq-crystals/dilithium/commit/d35ba3fe5449bee3e6d43e1f296c3ca818bd36be) (2026-06-03) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / n/a | 45/45 / 45/45 / 45/45 / n/a | n/a | 610/610 / 236/236 / 9/9 | 3/3 | cannot verify | 234 | 6/6 | 1,338/1,338 **VERIFIED** |
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | 44 / 65 / 87 | 75/75 | n/a / 90/90 / n/a / n/a | n/a / 45/45 / n/a / n/a | n/a | 610/610 / 236/236 / 9/9 | 3/3 | cannot verify | 504 | 1/1 | 1,068/1,068 **VERIFIED** |
| liboqs 0.16.0 — OQS API | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 44 / 65 / 87 | 75/75 | n/a / 90/90 / n/a / n/a | n/a / 45/45 / n/a / n/a | n/a | 610/610 / 236/236 / 9/9 | 3/3 | cannot verify | 504 | 2/2 | 1,068/1,068 **VERIFIED** |
| liboqs 0.16.0 — mldsa-native C backend | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / 90/90 | 45/45 / 45/45 / 45/45 / 45/45 | 36/36 | 610/610 / 275/275 / 9/9 | 3/3 | cannot verify | 24 | 1/1 | 1,548/1,548 **VERIFIED** |
| liboqs 0.16.0 — mldsa-native x86-64 backend | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / 90/90 | 45/45 / 45/45 / 45/45 / 45/45 | 36/36 | 610/610 / 275/275 / 9/9 | 3/3 | cannot verify | 24 | 1/1 | 1,548/1,548 **VERIFIED** |
<!-- vendor-audits-dsa:end -->

All three are byte-exact on every interface they expose. They differ in
what they expose: mldsa-native implements every interface, including
external μ and a native HashML-DSA API; pq-crystals ref has no external-μ
API; PQClean has pure ML-DSA only. The "not applicable" column counts
what each one's API cannot be asked. "Constant time" is
`--audit-dsa ... --constant-time` ([below](#constant-time---constant-time)):
only mldsa-native, built with its annotations and pq-verify's shim, can be
judged; every other build records CANNOT VERIFY, never a pass. Each count is
over all three parameter sets. **Result** counts the conformance checks; the
constant-time checks are not in it, but a row is **VERIFIED** only if they
pass too, where they can be judged.

**Mutants.** An audit that passes correct libraries has shown half of what
it must. Each row also carries mutants: a one-line change to the pinned
source that plants a known bug class. CI builds every one and requires the
audit to fail it in the listed stages (`tools/vendor_audits.json`). All eleven
are caught:

| Library | Planted bug | Caught by |
|---|---|---|
| pq-crystals ref | verify skips the challenge comparison | sigVer (all interfaces), Wycheproof verify |
| pq-crystals ref | hint decoder accepts a repeated index | Wycheproof verify only |
| pq-crystals ref | verify skips the ‖z‖ bound | Wycheproof verify only |
| pq-crystals ref | signing ignores `rnd` | sigGen, randomised half |
| pq-crystals ref | signing omits the context length | sigGen pure |
| pq-crystals ref | keypair draws 16 extra random bytes | keyGen, randomness finding |
| mldsa-native | hint decoder accepts a repeated index | Wycheproof verify only |
| mldsa-native | verify skips the ‖z‖ bound | Wycheproof verify only |
| mldsa-native | HashML-DSA encoded as pure ML-DSA | sigGen and sigVer pre-hash |
| mldsa-native | HashML-DSA verification encodes SHA3-512's OID as SHA2-512's | every pre-hash verifies only |
| PQClean | verify skips the challenge comparison | sigVer pure, Wycheproof verify |

Three of these bug classes are invisible to NIST's vectors. A verifier that
accepts a repeated hint index (the defect dilithium-py 1.4.0 ships, which
makes signatures malleable) and one that skips the ‖z‖∞ < γ₁ − β check both
pass every NIST sigVer vector. Only Wycheproof's verify vectors catch them,
which is why `--audit-dsa` runs both. A HashML-DSA verifier that encodes one
hash function's OID wrongly passes Wycheproof's vectors too; only the
pre-hash round trip catches it.

Reproduce every row and mutant: `python3 tools/vendor_audit.py --only ML-DSA`
(about 30 s). One library by hand (ML-DSA-65):

```bash
git clone https://github.com/pq-code-package/mldsa-native.git   # 159509d
H=$(python3 -c "import pq_verify, os; print(os.path.join(os.path.dirname(pq_verify.__file__), 'harness', 'pqv_randombytes.c'))")
gcc -O2 -fPIC -shared -DMLD_CONFIG_PARAMETER_SET=65 -Imldsa-native/mldsa \
    -o libmldsanative65.so mldsa-native/mldsa/mldsa_native.c "$H"
pq-verify --audit-dsa ./libmldsanative65.so ML-DSA-65
```

Without the harness, randomised APIs are reported not applicable and the
seed-taking ones (`keypair_internal`, `signature_internal`) are audited.
Never link the harness into a production build: it is deterministic by
design.

---

## SLH-DSA library audit, with mutants

`--audit-slhdsa PATH SET` audits an SLH-DSA library (FIPS 205) through its
own entry points, with every NIST ACVP SLH-DSA vector for the parameter set
(ACVP-Server `112690e`: 10 keyGen, 52 sigGen and 42 sigVer cases per set,
1,248 over the twelve).

Each FIPS 205 interface is a separate stage, and each case goes through the
library's entry point for it: **internal** (Algorithms 19 and 20), **pure**
(22 and 24, with a context) and **pre-hash** HashSLH-DSA (23 and 25, over all
twelve approved hashes). For NIST's cases pq-verify builds no M′, so its
vectors check the library's own encoding of the domain separator, the context
length and the hash's OID.

Key generation is checked twice: seeded (NIST's SK.seed, SK.prf and PK.seed
passed to `slh_keygen_internal`), and randomised, with the same seeds served
as one stream through the random-bit-generator callback `slh_keygen` takes.
The randomised key must be NIST's, and exactly 3n bytes must be drawn,
however the requests are split. FIPS 205 passes its randomness as arguments,
so no randomness harness or special build is needed.

**NIST's verification vectors miss ten of the twelve pre-hash functions.**
In every parameter set they hold a valid HashSLH-DSA signature for only two
of the twelve, so a verifier that hashes wrongly for any of the other ten
passes every NIST sigVer vector: it is never shown a valid signature to
reject. Signing is covered for all twelve. So for each pre-hash function the
library's verifier must accept a signature its own signer made with it (the
"every pre-hash verifies" column); a signer hashing wrongly fails NIST's
sigGen vectors first. A mutant shows the gap: slhdsa-c verifying SHA3-512
messages with SHA3-384 passes every NIST vector, and only this check fails.

Beyond NIST's vectors, the library must refuse:

- a 256-byte context (FIPS 205 allows 255), signing and verifying, pure and
  pre-hash;
- a hash function it does not know (`MD5`, and the empty name), signing and
  verifying;
- to return a key when its random bit generator fails (Algorithm 21).

Its size functions, where it has them, must give FIPS 205's sizes (Table 2).

A refused verification shows nothing if the call would have failed anyway.
So each one is offered a signature that one way of losing the check would
accept, after the library has accepted that signature where it belongs:

| Verifying with | A verifier that | Accepts |
|---|---|---|
| a 256-byte context | ignores the context | a signature made with an empty context |
| | keeps the length in one byte (256 → 0) | a pure signature over ctx ‖ M with an empty context; an internal signature over 1 ‖ 0 ‖ ctx ‖ OID ‖ SHA-256(M) |
| | reads 256 as "no context" | an internal signature over M |
| an unknown hash name | uses a default hash | a SHA2-256 signature |
| | formats M′ with no OID or digest | an internal signature over 1 ‖ 0 |
| | ignores the error | an internal signature over the empty message |

The "no context" row comes from slhdsa-c itself: it marks its internal calls
with a context length of 256 (`SLH_CTX_SZ_NO_CONTEXT`), so a pure verifier
without the length check would treat a 256-byte context as none. The mutant
that removes that check is caught by the internal signature and by nothing
else.

slhdsa-c is pinned at `4745143` (2026-11-04), the commit that makes
`slh_keygen` check its random bit generator's return value. It is work in
progress with no release yet, and its README does not yet recommend it for
production use or sensitive data.

**liboqs** (0.16.0, the release the other liboqs rows pin) ships SLH-DSA as
slhdsa-c behind its own wrappers: per parameter set a pure algorithm,
`OQS_SIG_slh_dsa_pure_<set>_*`, and one HashSLH-DSA algorithm per approved
hash, `OQS_SIG_slh_dsa_<hash>_prehash_<set>_*`, 156 in all. Its row audits
them the way liboqs's users call them:

- NIST's cases with an empty context go through the plain `sign` and
  `verify`, the rest through `sign_with_ctx_str` and `verify_with_ctx_str`,
  so both entry points are checked.
- Randomness reaches key generation and signing through liboqs's own hook,
  `OQS_randombytes_custom_algorithm`: NIST's seeds, and NIST's addrnd. liboqs
  signs hedged only, so a deterministic case is served PK.seed as addrnd, which
  is FIPS 205's deterministic variant. Each signature must draw exactly n
  bytes.
- Every algorithm's keypair is checked, NIST's first key through each
  HashSLH-DSA one, and every algorithm's sizes as `OQS_SIG_new` reports them.
- The internal interface goes through `slh_sign_internal` and
  `slh_verify_internal`, which liboqs exports from the same slhdsa-c copy its
  wrappers call (`src/sig/slh_dsa/patches/internal_api.patch`).
- Not applicable, with the reason, never passes: seeded key generation
  (liboqs does not export it), an unknown hash name (each algorithm fixes its
  hash) and a failing random bit generator (the hook returns void).

liboqs vendors slhdsa-c at `a0fc1ff` (2025-07-22), not the commit the
slhdsa-c row pins, so its result is its own. Build it with every algorithm
and the audit picks liboqs's API on its own:

```bash
git clone https://github.com/open-quantum-safe/liboqs.git
git -C liboqs checkout 5a1a854b0dc9f2141bdc771c555ee60c37950183
cmake -S liboqs -B liboqs/build -DBUILD_SHARED_LIBS=ON -DOQS_BUILD_ONLY_LIB=ON -DOQS_USE_OPENSSL=OFF
cmake --build liboqs/build -j
pq-verify --audit-slhdsa liboqs/build/lib/liboqs.so SLH-DSA-SHA2-128f
```

<!-- vendor-audits-slhdsa:begin -->
| Library | Commit | Sets | keyGen | keyGen, own RBG | sigGen (internal, pure, pre-hash) | sigVer (internal, pure, pre-hash) | Every pre-hash verifies | Refused (256-byte context, unknown pre-hash, failed RBG) | Sizes | Not applicable | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slhdsa-c | [`4745143`](https://github.com/pq-code-package/slhdsa-c/commit/47451432bb04faf8217ffe8a961a75b542bf88e8) (2026-11-04) | all 12 | 120/120 | 120/120 | 168/168, 168/168, 288/288 | 168/168, 168/168, 168/168 | 144/144 | 84/84, 96/96, 12/12 | 36/36 | 0 | 13/13 | 1,740/1,740 **VERIFIED** |
| liboqs 0.16.0 — SLH-DSA, OQS API | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | all 12 | n/a | 264/264 | 168/168, 168/168, 288/288 | 168/168, 168/168, 168/168 | 144/144 | 84/84, n/a, n/a | 468/468 | 228 | 8/8 | 2,088/2,088 **VERIFIED** |
<!-- vendor-audits-slhdsa:end -->

Every mutant plants one bug in its row's source; CI requires the audit to
fail it in the stages the mutant names. In slhdsa-c:

- verification that skips the hypertree root comparison (every
  verification stage), and a WOTS+ checksum left unshifted (every signing
  and verification stage);
- signing that ignores `addrnd`, and pure signing that drops the context;
- HashSLH-DSA writing SHA-384's OID for SHA-256;
- HashSLH-DSA verification hashing SHA3-512 messages with SHA3-384, which
  passes every NIST vector;
- seeded key generation building PK.root on the wrong layer;
- pure signing, pure verification and HashSLH-DSA each accepting a context
  over 255 bytes;
- HashSLH-DSA verification ignoring an unknown hash name, and an unknown
  name formatting M′ with no OID or digest;
- key generation ignoring a failed random draw, as `slh_keygen` did before
  the pinned commit.

In liboqs's wrappers, each for SLH-DSA-SHA2-128f:

- the pure `sign_with_ctx_str` dropping the context, and the plain `sign`
  signing with one;
- the pure `sign_with_ctx_str` drawing 15 bytes of addrnd, not 16;
- the SHA3-512 HashSLH-DSA algorithm verifying as SHA3-384;
- the pure keypair drawing no randomness;
- `OQS_SIG_new` reporting a pure signature one byte short;
- the plain pure `verify` accepting any signature;
- and, in liboqs's copy of slhdsa-c, verification skipping the hypertree
  root comparison.

Reproduce every set and mutant of both rows:
`python3 tools/vendor_audit.py --only SLH-DSA` (about 20 minutes). One
parameter set of slhdsa-c by hand:

```bash
git clone https://github.com/pq-code-package/slhdsa-c.git
git -C slhdsa-c checkout 47451432bb04faf8217ffe8a961a75b542bf88e8
gcc -O2 -fPIC -shared -std=c99 -o libslhdsa.so slhdsa-c/*.c
pq-verify --audit-slhdsa ./libslhdsa.so SLH-DSA-SHA2-128f
```

A pass says the library computes FIPS 205 exactly on NIST's inputs and
refuses the inputs above. It is not a side-channel review.

---

## LMS/HSS and XMSS library audit, with mutants

`--audit-hbs` audits a stateful hash-based signature library (SP 800-208,
the schemes CNSA 2.0 requires for firmware signing). LMS and XMSS libraries
share no C API, so each is loaded through a **pqv_hbs adapter**: five C
functions (`supports`, `verify`, `keygen`, `sign`, plus a name and ABI
version) that map the library onto one encoding (`pq_verify/harness/hbs/
pqv_hbs.h`). Adapters for cisco/hash-sigs and xmss-reference ship with
pq-verify; another library needs one small C file.

The audit drives the library with:

- **verify**: every pinned verification vector (NIST's LMS sigVer and sigGen
  signatures, post-quantum-cryptography/KAT's LMS and XMSS, liboqs's XMSS,
  XMSS^MT and HSS, RFC 8554 Appendix F), verdict exact
- **keyGen** and **sigGen**: seed → public key and seed + leaf → signature,
  byte-exact, where the library exposes them; LMS uses the ACVP derivation
  (child seeds and the randomizer C from the parent SEED and I)
- **malformed**: from the first valid signature of each parameter set,
  signatures wrong in exactly one field — the leaf index (out of range, or
  another leaf), the typecodes, the randomizer, the first and last chain
  values, the first and last authentication nodes, one byte short or long,
  another message, another key. pq-verify's own verifier confirms each is
  invalid; the library must reject it.
- **key state** — what no vector can show, because every vector names its
  leaf. Through the adapter's optional state functions the library manages
  its own key, and for each sampled parameter set (the cheapest key of each
  distinct tree height first):
  - the key it creates is the one `pqv_hbs_keygen` makes;
  - every signature it issues verifies (pq-verify's verifier);
  - no leaf index is issued twice;
  - after each signature, a restart from the stored key never reissues a
    released leaf — the state was advanced on disk before the signature left;
  - it signs its last leaf and then refuses. The audit skips ahead to the
    end of the key, so a 2^40-leaf XMSS^MT key is checked too.

  Restoring an old copy of a key file (a backup, a VM snapshot) makes any
  file-backed implementation reissue leaves; that is a deployment property,
  and the report says so.

Parameter sets the library does not implement are **not applicable**, with
the reason. Key generation and signing build whole trees, so by default they
run within a hash budget and for two cases per parameter set; the rest are
**not run** (`--audit-hbs-full` runs every case up to height 16). Neither is
ever counted as a pass.

<!-- vendor-audits-hbs:begin -->
| Library | Commit | Schemes | Verify | keyGen | sigGen | Malformed rejected | Key state | Not applicable | Not run | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|
| cisco/hash-sigs | [`44e6c7d`](https://github.com/cisco/hash-sigs/commit/44e6c7de934c05942bf17cc819a81e765cfe67d7) (2026-09-04) | LMS/HSS | 340/340 | 18/18 | 18/18 | 300/300 | 10/10 | 2,788 | 478 | 5/5 | 686/686 **VERIFIED** |
| XMSS/xmss-reference | [`171ccbd`](https://github.com/XMSS/xmss-reference/commit/171ccbd26f098542a67eb5d2b128281c80bd71a6) (2021-03-16) | XMSS, XMSS^MT | 141/141 | 8/8 | 8/8 | 407/407 | 15/20 | 3,371 | 169 | 6/6 | 579/584 findings |
<!-- vendor-audits-hbs:end -->

hash-sigs is correct on everything it implements, key state included: it
writes the advanced count through its `update_private_key` callback before it
signs, and on its last signature overwrites the stored key so it cannot load
again. It implements RFC 8554's SHA-256 sets only, so SP 800-208's 192-bit
and SHAKE LMS sets are not applicable to it; built in its ACVP mode
(`SECRET_METHOD 2`), its key generation and signatures are byte-exact.

xmss-reference implements every RFC 8391 and SP 800-208 XMSS and XMSS^MT set
with SP 800-208's `PRF_keygen`, and every vector passes. Its key-state
handling has **two defects**, both in `xmssmt_core_sign` at the pinned commit,
which is upstream `master`:

1. **The last leaf of every key yields an invalid signature, reported as
   success.** At `idx == 2^h - 1` the function wipes the secret key *before*
   signing: the index field is set to all-ones and the seeds to zero, then the
   signature is computed from the zeroed seeds and returns 0. The caller gets
   a signature that does not verify, carrying index `0xFF…`. Nothing leaks —
   a zero seed protects nothing — but the last one-time key of every key pair
   is lost, and the API says it succeeded.
2. **XMSS^MT keys whose index field is exactly full (h = 40, 5-byte index)
   never refuse.** The exhausted marker (all-ones) equals the last valid
   index, so the `idx > max` test never fires; the next index overflows to 0,
   and the key keeps returning success with invalid signatures from the
   wiped seeds. A deployment that rotates keys on the library's refusal never
   rotates. The same fail-open was reported in RustCrypto's XMSS port
   ([RustCrypto/signatures#1453](https://github.com/RustCrypto/signatures/issues/1453)).

Neither reissues a leaf with live key material: indices stay unique.
xmss-reference itself advances the index only in memory (its source says
production code must persist it); the adapter writes the key to disk before
returning each signature, which is what a deployment must do, and the
durable-state check confirms that holds. The defects are pinned in
`tools/vendor_audits.json` (`failing`), so CI holds the row to exactly these
five failing checks. The reference signer rebuilds the tree for every
signature, so its signing is sampled.

**Mutants** (CI requires the audit to fail each):

| Library | Planted bug | Caught by |
|---|---|---|
| hash-sigs | LMS verify skips the root comparison | verify (invalid vectors), malformed |
| hash-sigs | LM-OTS typecode in the signature not checked | **malformed only** |
| hash-sigs | verify drops the LM-OTS checksum | verify |
| hash-sigs | signing drops the LM-OTS checksum | sigGen |
| xmss-reference | verify skips the root comparison | verify (invalid vectors), malformed |
| xmss-reference | WOTS+ checksum not shifted | verify, sigGen |
| xmss-reference | randomizer r from the wrong leaf index | sigGen |
| xmss-reference | `PRF_keygen` uses PRF's domain separator | keyGen, sigGen |
| hash-sigs | the advanced count is never written back | **key state only** (no leaf twice, durable state) |
| xmss-reference | the index in the secret key is not advanced | **key state only** (no leaf twice, durable state) |
| xmss-reference | no check that the key is exhausted | **key state only** (refuses once exhausted) |

A mutant on a library with pinned defects counts as caught only when it fails
a check the library itself passes.

A verifier that ignores the LM-OTS typecode in the signature passes every
published vector; only the malformed stage catches it. Two further candidate
mutants were discarded as **equivalent** (they change no verdict, so no
vector can see them): removing hash-sigs' HSS level check, which an earlier
line repeats, and removing its leaf-index range check, after which an
out-of-range index is still rejected by the root comparison (the defect is
a one-node out-of-bounds read, which needs a memory sanitizer, not a
conformance audit). A third, removing hash-sigs' expiry test in
`hss_advance_count`, is equivalent too: its last signature also overwrites
the stored key, and loading refuses a count past the end, so the key still
refuses. Defence in depth, verified.

Reproduce every row and mutant: `python3 tools/vendor_audit.py --only LMS/XMSS`
(about 20 minutes, most of it xmss-reference signing). By hand:

```bash
git clone https://github.com/cisco/hash-sigs.git                 # 44e6c7d
A=$(python3 -c "import pq_verify, os; print(os.path.join(os.path.dirname(pq_verify.__file__), 'harness', 'hbs'))")
gcc -O2 -fPIC -shared -I"$A" -Ihash-sigs -o libhashsigs.so "$A/adapter_hash_sigs.c" \
    hash-sigs/{hss,hss_alloc,hss_aux,hss_common,hss_compute,hss_generate,hss_keygen,hss_param,hss_reserve,hss_sign,hss_sign_inc,hss_thread_single,hss_verify,hss_verify_inc,hss_derive,hss_zeroize,lm_common,lm_ots_common,lm_ots_sign,lm_ots_verify,lm_verify,endian,hash,sha256}.c -lcrypto
pq-verify --audit-hbs ./libhashsigs.so
```

---

## FN-DSA (Falcon) library audit — draft track, with mutants

`--audit-fndsa PATH FN-DSA-512|FN-DSA-1024` audits a vendor's FN-DSA library
ahead of the final FIPS 206. Every report says `track: "draft"`: a VERIFIED
here is against Falcon round 3, the scheme FIPS 206 standardises, never a
final FIPS 206, and it is not part of any FIPS 203/204/205 result.

- **Verify:** the pinned PQClean signatures (`pq-verify --fndsa`) are accepted.
- **Open:** the pinned NIST-API signed messages are opened to their message.
- **Malformed rejected:** for each pinned signature, the inputs a verifier
  must refuse. The non-canonical encodings are built so that only the
  decoder can refuse them: `-0` decodes to 0, and a public-key coefficient
  re-encoded as `w + q` is the same key mod q. A verifier missing either
  check accepts the signature, where a looser test would have been refused
  by the norm check and hidden the gap.
- **keyGen:** the library's public keys are canonical and belong to their
  secret keys (`h·f = g mod q`), and every secret key is a valid Falcon key,
  checked exactly in integers and rationals, never floating point: G is
  recomputed as `g·F/f mod q` and `f·G − g·F = q` must hold in
  ℤ[x]/(xⁿ+1) with every coefficient of G within ±127; and both
  Gram–Schmidt norms are below 1.17²·q (the reference's 16822.4121):
  `‖(g, −f)‖²`, and `‖(q·f*/D, q·g*/D)‖² = q²·[1/D]₀` with `D = f·f* + g·g*`,
  whose constant coefficient is computed as an exact rational through the
  field-norm tower. A key with a wrong F, or one whose basis is too long for
  the sampler's bounds, fails here even when its public key is right.
- **sign:** the library's signatures verify under pq-verify's verifier and
  its own, are in range and canonically encoded, and never reuse a nonce.
  Signing is randomised, so it is checked for validity, not byte-for-byte.
- **Signature statistics (`sampler`):** 1,000 more signatures of distinct
  messages under one key from the library's own keypair
  (`pq_verify/fndsa_stats.py`). For each, s1 is recomputed exactly; the
  2n coefficients of all of them must be centred on 0 (a chi-square on the
  2n means), of variance σ² and symmetric, each within 6 standard
  deviations of what an exact sampler gives. A biased sampler still signs
  validly: this is the stage that sees one. On PQClean's Falcon, 29 keys
  stayed within 3.3 standard deviations. A defect that keeps these moments
  passes: a base sampler with its table's tail cut does (measured).
- **Emulated arithmetic (`fpr_*`):** where the library exports Falcon's
  emulation of binary64 (`pq_verify/fndsa_fpr.py`), each function is asked
  1,214 to 10,006 questions from Falcon's domain, from a seed the report
  records, and every answer is compared with an exact reference. The
  reference is checked first against this machine's own floating point.
  - `fpr_scaled`, `fpr_add`, `fpr_mul`, `fpr_div`, `fpr_sqrt`: the exact
    result rounded to nearest, ties to even. The questions include sums and
    products built to land exactly halfway between two doubles, and
    operands within three binades of each other.
  - `fpr_expm_p63`: the reference's ApproxExp bit for bit, its 13
    coefficients and its integer arithmetic. Most questions are near
    x = ln 2 and ccs = 1, where a changed coefficient shows most often.

A wrong-length public key is **not applicable**: neither the NIST API nor
liboqs takes a key length, so the library would read past the buffer. So are
the arithmetic stages for liboqs, one line each: the audit binds its
`OQS_SIG_falcon_*` API, and on a CPU with AVX2 liboqs runs PQClean's AVX2
Falcon, which computes on the CPU's floating point and exports no `fpr_*`.

<!-- vendor-audits-fndsa:begin -->
| Library | Commit | Sets | Verify (pinned) | Open (pinned) | Malformed rejected | keyGen | sign | Signature statistics | Emulated arithmetic (fpr_*) | Not applicable | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | 512 / 1024 | 14/14 | 16/16 | 135/135 | 30/30 | 48/48 | 8/8 | 38,692/38,692 | 14 | 13/13 | 38,943/38,943 **VERIFIED** (draft) |
| liboqs 0.16.0 — Falcon | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 512 / 1024 | 14/14 | n/a | 135/135 | 30/30 | 48/48 | 8/8 | n/a | 42 | 1/1 | 235/235 **VERIFIED** (draft) |
| liboqs 0.16.0 — Falcon (padded) | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | 512 / 1024 | 14/14 | n/a | 135/135 | 30/30 | 48/48 | 8/8 | n/a | 42 | 1/1 | 235/235 **VERIFIED** (draft) |
<!-- vendor-audits-fndsa:end -->

Every mutant plants one bug class in PQClean's source; CI requires the audit
to fail it: a verifier that accepts `-0`, ignores nonzero padding bits,
accepts a public-key coefficient ≥ q, ignores the public-key header or skips
the norm bound; a signer that reuses one nonce or writes the wrong header;
a key generator that stores an F that does not solve the NTRU equation
(caught by keyGen, and by sign when the library then refuses its own key).
The Gram–Schmidt bound has no mutant: a generator that skips it emits an
over-long basis only now and then, so no planted bug fails it on every run;
the test suite checks it on constructed keys instead.
The first version of the audit missed the range-check mutant (its test key
changed value mod q, so the norm check refused it); the mutant is why the
`w + q` case exists.

Three more mutants change Falcon's arithmetic and nothing else:
- the emulation rounds a tie away from zero instead of to even (one constant
  in `fpr.h`);
- it truncates instead of rounding;
- one of ApproxExp's 13 coefficients is one unit off (`fpr.c`).

None of them is visible to PQClean's own known-answer tests. Built with each
one, PQClean's NIST KAT generator (100 key pairs and signatures) and its
deterministic test vectors give outputs whose SHA-256 equals the
`nistkat-sha256` and `testvectors-sha256` in Falcon-512's `META.yml`, exactly
as the unmodified code's do. A last-bit change almost never moves a sampled
integer. Every other stage of the audit passes them too. CI checks all of
this:
- each mutant must fail the arithmetic stages it names and nothing else
  (`"only"` in `tools/vendor_audits.json`);
- both generators are rebuilt from the mutated tree and their output hashed
  (`"kat_unchanged"`). A generator that stops with an error, as the test
  vectors do on a signature they cannot verify, counts as having seen the
  bug.

The coefficient mutant stays within 2^-50 of the true value, so only the
bit-for-bit comparison catches it.

Two more change the sampler, and fail the signature statistics and nothing
else (`"only"`); their signatures all verify:
- the sampler's sign bit is 1 with probability 136/256, not 1/2: the
  coefficient means drift by 53 to 60 standard deviations (6 keys);
- the signer draws with a σ 2% low: the variance sits 25 to 27 below
  (5 keys).

These do change PQClean's known-answer output. They stand for what the KAT
cannot reach: a library whose signing randomness pq-verify does not control,
or whose KATs were generated from its own sampler.

## Classic McEliece library audit — not a FIPS standard, with mutants

Classic McEliece (round 4) was a NIST round-4 candidate that NIST did not
select (it chose HQC); it is on an ISO track (ISO/IEC 18033-2). These results
are on a track of their own and are never part of a FIPS 203/204/205 verdict,
and they establish correctness, not the scheme's security.

**The reference.** `pq_verify/mceliece.py` is pq-verify's own implementation
of what an audit needs: seeded key generation, encoding with a chosen error
vector, the Goppa decoder (syndromes with g², Berlekamp–Massey, roots over the
support, success only at weight exactly t with a matching syndrome) and
decapsulation with implicit rejection. It is held to the official KATs
(`pq-verify --mceliece`): PQClean's NIST KAT harness, first record, for all
ten sets, each matching the `nistkat-sha256` PQClean publishes. The 0.26–1.36
MB public keys are not pinned; pq-verify regenerates each from the private
key's seed and the rebuilt KAT must hash to the published value, so the
reference proves itself on a key it was never given. Every step of key
generation is unique given the seed (the minimal polynomial, the sorted
support, the reduced echelon form [I | T] and, for the f variants, the first
32 pivot columns in [mt − 32, mt + 32)), which is why a correct library
reproduces it byte for byte.

**The audit** (`--audit-mceliece`), per library and parameter set, on two of
its own key pairs:

- **keyGen:** the private key stores the seed of the attempt that succeeded,
  so the whole key pair is regenerated from it in one attempt: public key,
  pivots `c`, Goppa polynomial `g` and rejection string `s` byte-exact; the
  Beneš control bits applied to the identity must give the regenerated
  permutation (control bits for a permutation are not unique, so their bytes
  are not compared). An f-variant key whose pivots are trivial (about 29% of
  keys) stores the same `c` as a library that never records pivots. So when
  the first key's pivots are trivial, the second key is redrawn until its are
  not (at most 24 more). A key passed over is still checked, and kept if a
  check fails. If none turns up, or the library repeats a key, the pivots
  record is not applicable.
- **encaps:** three ciphertexts per key decode under pq-verify's decoder to an
  error vector of weight t, the key is SHAKE256(1 ‖ e ‖ C), the library's own
  Decap returns it, and no error vector repeats.
- **decaps:** twelve ciphertexts per key built against that key, each
  answered by pq-verify's decoder: weight t at random positions (2), in the
  first t positions (the identity part of H), in the last t (the T part) and
  through the support's zero element → SHAKE256(1 ‖ e ‖ C); weight t − 1 (the
  decoder can correct it, the specification's weight check must reject it),
  again through the zero element, t + 1, C = 0, random C (2), and a valid
  ciphertext for the library's other key → SHAKE256(0 ‖ s ‖ C). An error at
  the zero element drops the error locator's degree, the classic place for a
  decoder to slip. A key's support lacks 0 with probability 1 − n/2^m (15% of
  mceliece348864 keys and 44% of mceliece460896's; none of mceliece8192128's,
  where n = 2^m). Such a key has its two zero-element cases built on another
  of the library's keys whose support has it: the audit's other key, or one
  more drawn from the library (at most 24), regenerated from its seed as
  keyGen does before it is used. If no key has it, those two cases are not
  applicable. They are never built on another element.
- **padding** (mceliece6960119 and 6960119f, where mt = 1547 and k = 5413 end
  mid-byte): a valid ciphertext with a padding bit set, and a public key with
  one, must be refused (nonzero return). The rule is taken from the
  submitters' reference implementation (SUPERCOP-20221025), which refuses
  both.

<!-- vendor-audits-mceliece:begin -->
| Library | Commit | Sets | keyGen (regenerated) | encaps | decaps (crafted) | padding | Constant time | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | all 10 | 100/100 | 60/60 | 240/240 | 4/4 | 20/20 | 12/12 | 404/404 **VERIFIED** |
| liboqs 0.16.0 — Classic McEliece, OQS API (distribution build) | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | all 10 | 100/100 | 60/60 | 240/240 | 4/4 | 20/20 | 8/8 | 404/404 **VERIFIED** |
| liboqs 0.16.0 — Classic McEliece, OQS API (portable build) | [`5a1a854`](https://github.com/open-quantum-safe/liboqs/commit/5a1a854b0dc9f2141bdc771c555ee60c37950183) (2026-07-09) | all 10 | 100/100 | 60/60 | 240/240 | 4/4 | 20/20 | 4/4 | 404/404 **VERIFIED** |
<!-- vendor-audits-mceliece:end -->

**liboqs 0.16.0** is audited through its public API, `OQS_KEM_classic_mceliece_*`,
in a build with only the ten Classic McEliece sets. Its backends' C entry
points are not exported, so the API is the only way in, and it runs one
backend: on a CPU with AVX2 and POPCNT the distribution build
(`OQS_DIST_BUILD=ON`) dispatches to the AVX2 code, while the portable build
(`OQS_OPT_TARGET=generic`) compiles the clean code alone. Both are pinned
rows, so each backend is audited, on all ten sets. Its `keypair_derand` and
`encaps_derand` exports are stubs that return an error, and the audit does
not bind them: key pairs are regenerated from the seed in the private key,
so no control over liboqs's randomness is needed.

Each mutant plants one bug in the source and CI requires the audit to fail
it in the stage named. In PQClean: a decoder that accepts any weight whose syndrome
matches (caught by the t − 1 and C = 0 cases; the first version of this audit
missed it on most keys, because the reference's fixed-degree locator gives a
spurious root at the zero element that the syndrome check then rejects, which
is why the through-zero cases exist), implicit rejection hashing the
decoder's output instead of s, or with prefix 1; a key generator storing a
zero s, or (f variant) no pivots (seen only on a key whose pivots are not
trivial; while both keys could have trivial ones, CI missed this mutant on
about 8% of runs); encapsulation hashing with prefix 0; and,
for 6960119, decapsulation and encapsulation ignoring padding bits. In
liboqs, on the AVX2 path: the AVX2 decoder's weight check passing any weight
(seen only through the support's zero element: that decoder finds the
locator's roots on the whole field, so any other weight t − 1 error gains a
spurious root at 0 and is rejected anyway; while a key lacking 0 had those
cases moved to its smallest support element, CI missed this mutant on about
2% of runs), implicit rejection hashing the decoder's output, encapsulation
hashing with prefix 0, the f variant recording no pivots, decapsulation
ignoring the ciphertext's padding bits, and liboqs's own wrapper turning the
backend's refusal into success (a 6960119 ciphertext with a padding bit set is
then accepted); on the clean path: the decoder accepting any weight, the same
wrapper bug for 6960119f, and encapsulation ignoring the public key's padding
bits. That the AVX2 mutants fail the distribution build and the clean ones
the portable build shows each row runs the backend it names.

**Constant time** (`--audit-mceliece ... --constant-time`), every row and set:
Decaps with the whole private key secret, on a valid and on a random
ciphertext, and Encaps with its randomness secret, under Valgrind memcheck;
see [Constant time](#constant-time---constant-time). All 30 are clean, and
seven planted leaks are caught (the CT mutants counted in the table).

Not covered: the distribution of encapsulation's error vectors (only their
weight, validity and repetition), and constant-time key generation.

## HQC decoder audit — standard not final, with mutants

HQC was selected by NIST in March 2025; its standard is not final. These
results are on a track of their own, never part of a FIPS 203/204/205 verdict,
and they cover HQC's error-correcting code, not the KEM: the Reed–Solomon code
over GF(2⁸) (outer) concatenated with a duplicated Reed–Muller RM(1,7)
(inner) that decryption decodes.

**Why the decoder on its own.** Honest decryptions almost never put more than
two errors in front of the outer decoder, and decapsulation re-encrypts, so a
ciphertext built to reach a corner of the decoder is rejected whatever the
decoder did. A decoder bug that only bites on rare error patterns passes
PQClean's known-answer test (one honest vector) and every round trip. So the audit calls the encoder and decoder functions directly.

**The reference.** `pq_verify/hqc.py`: GF(2⁸) by tables on a generator it
checks has order 255; the Reed–Solomon generator polynomial
(x − α)(x − α²)…(x − α^2δ), systematic encoding and a Berlekamp–Massey /
Forney decoder; the Reed–Muller encoder and an exact maximum-likelihood
decoder (the Walsh–Hadamard transform of the summed copies, ties to the lowest
index). Two code profiles: **v5** (HQC v5.0.0, whose code layer is the
2023-04-30 submission's) and **next** (the submitters' unreleased
next-release branch: GF(2⁸) modulo x⁸+x⁴+x³+x+1 with generator x + 1, since x
has order 51 there, and each Reed–Muller byte stored most-significant bit
first). `pq-verify --hqc` holds it to the generator polynomials published in
the submitters' `parameters.h`, and to their own reference decoders' answers
on every input of a fixed-seed suite, pinned as digests
(`pq_verify/vectors/HQC_MANIFEST.json`, `tools/pin_hqc_vectors.py`):
61/61. PQClean's 2023 code answers identically to v5.0.0 on the whole suite.

**The audit** (`--audit-hqc`), per library and parameter set, on vectors
built fresh each run (the seed is reported; the rows below use a fixed one):

- **encode:** the Reed–Solomon, Reed–Muller and concatenated encoders, byte
  for byte. An encoder that matches the other profile says so.
- **rm-decode:** every codeword (256); one block per position with noise up
  to the radius (32 × copies − 1 flips); blocks between two codewords at
  distances 32 × copies − 1, 32 × copies − 8, 24, 16 and 8 × copies from the
  nearer, half of them with the nearer codeword's index the higher; 12 ties
  (equidistant blocks, including indices 0 and 127) and the GF(2⁷) inversion
  word Tr(j⁻¹), at distance 54 from 14 codewords at once; one exact copy
  outvoting noisy ones, in each copy position; random blocks. Each answer
  exact. A wrong answer is reported as either not maximum likelihood (a
  nearer codeword exists) or a tie broken differently.
- **rm-symmetry:** the inner decoder against itself, with no reference
  decoder. Each of those blocks is moved by eight random symmetries of the
  code: an affine map of the seven position bits (which renumbers the
  codewords), a codeword added, the copies permuted. Each image must decode
  to the image of the block's own answer. A maximum-likelihood decoder always
  does, so an answer that depends on how positions or codewords are numbered
  fails. Blocks with two nearest codewords are skipped: there the
  lowest-index rule picks by numbering, as it should. It certifies that the
  decoder is symmetric, not that it is right: a defect that is itself
  symmetric passes it, and rm-decode catches that (see the mutants). The idea
  is Lemma 5 of N. C. Maino, *Post-Selection Verification, Information
  Geometry, and Clifford Symmetries in Magic State Cultivation* (October
  2026), an audit of a matching decoder's soft output under the surface
  code's automorphisms, here for hard decisions.
- **rs-decode:** errors up to the radius δ (no errors; 1, 2, δ − 1 and δ at
  random positions; δ all in the parity part; δ all in the message part), and
  error patterns whose m-th leading Hankel minor vanishes, for every m below
  δ and for 2 and 3 errors. That minor is affine in each error value
  (Cauchy–Binet), so one value is solved for. Past the radius no answer is
  specified and only the bounds are checked.
- **code-decode:** whole received words within both radii: clean, inner
  noise in every block, δ symbol errors through the inner code (random and
  Hankel-built), and every block one flip inside the inner radius, aimed at
  another codeword.
- **bounds:** every call writes only its output (guard bytes on both sides
  of 64-byte-aligned buffers).

<!-- vendor-audits-hqc:begin -->
| Library | Commit | Profile | Sets | encode | rm-decode | rm-symmetry | rs-decode | code-decode | bounds | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|---|---|
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | v5 | HQC-1, HQC-3, HQC-5 | 50/50 | 1402/1402 | 1313/1313 | 99/99 | 27/27 | 389/389 | 10/10 | 3,280/3,280 **VERIFIED** |
| HQC reference | [`f46e542`](https://gitlab.com/pqc-hqc/hqc/-/commit/f46e54222ffb76706678a9ec8a43cd2188a12ab1) (2025-08-22) | v5 | HQC-1, HQC-3, HQC-5 | 50/50 | 1402/1402 | 1313/1313 | 99/99 | 27/27 | 389/389 | — | 3,280/3,280 **VERIFIED** |
| HQC optimized (AVX2) | [`f46e542`](https://gitlab.com/pqc-hqc/hqc/-/commit/f46e54222ffb76706678a9ec8a43cd2188a12ab1) (2025-08-22) | v5 | HQC-1, HQC-3, HQC-5 | 50/50 | **1388/1402** | **1285/1313** | 99/99 | **21/27** | 389/389 | — | 3,232/3,280 **findings** |
| HQC reference | [`71090d4`](https://gitlab.com/pqc-hqc/hqc/-/commit/71090d4679837a0de1e6946284818184994d952a) (2026-08-05) | next | HQC-1, HQC-3, HQC-5 | 50/50 | 1402/1402 | 1309/1309 | 99/99 | 27/27 | 389/389 | — | 3,276/3,276 **VERIFIED** |
| HQC optimized (AVX2) | [`71090d4`](https://gitlab.com/pqc-hqc/hqc/-/commit/71090d4679837a0de1e6946284818184994d952a) (2026-08-05) | next | HQC-1, HQC-3, HQC-5 | 50/50 | **1388/1402** | **1281/1309** | 99/99 | **21/27** | 389/389 | — | 3,228/3,276 **findings** |
<!-- vendor-audits-hqc:end -->

**Two defects in the submitters' optimized (AVX2) Reed–Muller decoder**, in
the v5.0.0 release and still on next-release at `71090d4`, each reproduced on
all three parameter sets. The reference decoder (`src/ref`) has neither.

1. *Its peak search stops short.* `find_peaks` binary-searches for the
   largest |transform value| from a width of `1 << (5 + MULTIPLICITY / 2)`.
   Its comment gives 64, 128 and 256 for multiplicities 2, 4 and 6: half the
   largest possible value (64 × multiplicity), above which only one value can
   lie. HQC's multiplicities are 3 and 5, and integer division rounds down:
   the width is 64 and 128, while two values can reach 96 and 160 together
   (|t_a| + |t_b| ≤ 64 × multiplicity). With two above the width the decoder
   returns the lower index of the two, not the larger value. A block 95 flips
   from one codeword (inside HQC-1's unique-decoding radius of 95) and 97 from
   another comes back as the farther one whenever its index is lower: 6 of the
   414 blocks in an HQC-1 audit, 4 of 448 and 540 for HQC-3 and HQC-5, and 2 of
   9 whole received words within both codes' radii decode to the wrong
   message. In 40 800 blocks (HQC-1 and HQC-3; uniformly random words, and
   codewords with independent bit flips at rates 0.30, 0.35 and 0.40) it
   never differed from the reference: random testing, KATs and round trips
   do not see it. rm-symmetry, which uses no reference decoder, sees it too.
   Moving the same blocks through symmetries of the code renumbers their
   codewords, and the decoder's answer follows the numbering: 12, 8 and 8
   blocks for HQC-1, -3 and -5, against rm-decode's 6, 4 and 4, because a
   block it decodes right can come back wrong once its codewords are
   renumbered. Starting the search at
   `1 << (6 + MULTIPLICITY / 2)` fixes it (no differences on the same
   vectors). Its effect on HQC's decryption failure rate was not estimated.
2. *It reads a vector through a `uint16_t` pointer.* The sign lookup does
   `uint16_t *ptr = (uint16_t *)&tmp;` on an `__m256i`, which strict aliasing
   does not allow. GCC 13.3 at `-O2` then sets the sign bit of every block it
   decodes, so every block whose answer has it clear comes back wrong: half of
   the 256 codewords, 0x00 as 0x80. The KEM fails every round trip (0 of 50
   shared secrets agree). rm-symmetry fails all 392 blocks of an HQC-1 build
   with only this defect: a constant bit does not follow the symmetries. At `-O3`, the submitters' CMake
   default, at `-O2 -fno-strict-aliasing`, and with clang 18 it works; copying
   the vector out with `memcpy` fixes it under both compilers. The rows above
   build the submitters' code at `-O3`, as they do, so they record the first
   defect only.

*Disclosure.* Reported to the HQC team on 9 October 2026, with a patch for
both defects and a standalone reproduction that uses only
`reed_muller_encode` and `reed_muller_decode`; acknowledged on 13 October and
tracked upstream as [HQC issue #46](https://gitlab.com/pqc-hqc/hqc/-/issues/46),
with the patch under review.

**Mutants.** Ten one-line changes to PQClean's decoder, each caught in the
stages recorded: Berlekamp–Massey acting on a zero discrepancy, skipping its
length test, or moving the saved locator's degree on any nonzero discrepancy;
syndromes ignoring position 0; Forney's denominator dropping a factor;
Reed–Muller ties going to the highest index; one copy left out of the sum;
index 127 never a peak; the first transform entry corrected for one copy too
few; the sign test inverted, so that every answer is the complementary
codeword. rm-symmetry catches three of the five Reed–Muller ones with no
reference decoder: the copy left out, index 127 and the first transform
entry. The other two are its blind spots, and CI holds them as such (the
mutant's `passes`): ties are skipped by design, and the inverted sign is a
symmetric defect, which commutes with every symmetry. rm-decode catches
both.

The first three are why the Hankel-built patterns exist. Measured on HQC-1
(δ = 15), 20 000 random weight-15 patterns each: 1 078, 1 078 and 1 882 wrong
answers (5–9%), against 56/56, 56/56 and 51/56 on Hankel-built ones. Honest
decryptions, with at most a couple of outer errors, essentially never reach
them, and the suite's handful of random patterns may miss them; the built
patterns do not.

Not covered: the KEM (key generation, encryption, sampling, hashing), constant
time, and liboqs's binary, whose HQC functions have hidden visibility (its
sources are the submitters' 2025 reference, the v5 profile).

## Accumulated vectors

Every KEM, ML-DSA and harness audit also runs 10 000 seeded random cases
(`pq_verify/accumulated.py`) and compares a SHAKE-128 digest of every output
with a pinned value: the **Accumulated** column above. Fixed vectors cover
the cases someone chose; these reach the rest. A planted bug that returns a
wrong shared key on about 1 ciphertext in 8 192 passes every NIST, Wycheproof
and CCTV vector, and the accumulated run catches it. Coverage is
probabilistic: a bug rarer than about 1 in 10 000 operations may not be hit.

| Scheme | Construction | Pinned digests |
|---|---|---|
| ML-DSA | C2SP CCTV `ML-DSA/accumulated` | CCTV's, as published (final FIPS 204: dilithium-py, PQClean, mldsa-native, the pq-crystals reference and CIRCL all reproduce them) |
| ML-KEM-768 | Go's `crypto/mlkem` TestAccumulated | Go's, as published (100 and 10 000 cases) |
| ML-KEM-512, -1024 | the same | none is published for final FIPS 203; computed, and pinned because PQClean, kyber-py and CIRCL (and Go, for 1024) agree |

**CCTV's published ML-KEM accumulated digests are the FIPS 203 draft.** They
absorb dk as well, and are attributed to pq-crystals; with the draft's
K-PKE.KeyGen hash G(d) in place of final FIPS 203's G(d ‖ k), pq-verify
reproduces CCTV's ML-KEM-512 value exactly. No implementation of the final
standard can match them -- every correct library would fail -- so pq-verify
does not use them.

## Constant time (`--constant-time`)

ML-KEM Encaps (m secret) and Decaps (the K-PKE secret key and z secret, on a
valid and on a random ciphertext) run under Valgrind memcheck with the secret
bytes marked; any branch or memory address that depends on them fails the
stage and names the function. A self-test must first see a deliberate secret
branch and a deliberate secret-indexed read whose value is discarded, or
nothing is trusted. The second needs memcheck to keep every load: by default
Valgrind's translator deletes a load whose value is never used before memcheck
sees it, though the processor still performs it. Every run commits each
instruction's result (`--vex-iropt-register-updates=allregs-at-each-insn`),
and every row below reproduced unchanged with it.

| Library | Sets | ct:encaps | ct:decaps | Integer divisions |
|---|---|---|---|---|
| mlkem-native `fc269bc` | 512 / 768 / 1024 | 3/3 | 3/3 | none |
| PQClean clean `0586a82` | 512 / 768 / 1024 | 3/3 | 3/3 | none |

Leaks planted in PQClean ML-KEM-768, each leaving every output correct -- they
pass every NIST, Wycheproof, CCTV and accumulated stage -- and caught here:

| Planted leak | Caught in |
|---|---|
| a branch on a secret message bit (`poly_frommsg`; the Clangover class) | ct:encaps, ct:decaps |
| a lookup table indexed by a secret coefficient (`poly_tomsg`) | ct:decaps |
| `memcmp` in the FO re-encryption check (`crypto_kem_dec`) | ct:decaps |

Not checked, and said so in every report: instruction timing (KyberSlash's
secret division is invisible to memcheck; the library's integer divisions
are listed instead), key generation, and anything physical.

**Classic McEliece** (not FIPS; `--audit-mceliece ... --constant-time`). The
NIST API takes no coins, so the driver supplies the randomness: it defines
`randombytes()` and `PQCLEAN_randombytes()`, which take precedence over the
library's own, and installs itself through liboqs's
`OQS_randombytes_custom_algorithm`. An Encaps that draws nothing through it is
refused, not reported clean. Key pairs and valid ciphertexts come from the
library itself, outside Valgrind, so each set takes seconds. Key generation
retries when an attempt fails (an irreducibility check, repeated support
elements, a non-systematic matrix): the submitters declassify those
comparisons, a black-box check cannot tell them from a leak, and it is not
checked.

Encaps has one exception, made by rule rather than by name: reports inside the
library function that drew the random bytes they depend on are listed, not
judged. That function is the error-vector sampler (`gen_e`). Its range and
repetition checks are rejection sampling, declassified by the submitters
(`crypto_declassify`, a no-op in these builds). Memcheck does not follow
branches, so it also taints what the sampler computes afterwards. In
liboqs's AVX2 code GCC reuses the register holding the rejection flag,
provably zero once the loop exits, as a later loop's counter, and memcheck
reports a "secret" branch (mceliece348864) and a "secret" address
(mceliece6960119). Both were traced to the instruction and are false
positives. The cost: a real leak in the sampler's own construction of the
error vector would land in the same list. Every report outside it fails.

| Library | Sets | ct:encaps | ct:decaps |
|---|---|---|---|
| PQClean clean `0586a82` | all 10 | 10/10 | 10/10 |
| liboqs 0.16.0, distribution build (AVX2) `5a1a854` | all 10 | 10/10 | 10/10 |
| liboqs 0.16.0, portable build (clean) `5a1a854` | all 10 | 10/10 | 10/10 |

| Planted leak | Caught in |
|---|---|
| the Beneš network branching on its control bits (PQClean; liboqs clean) | ct:decaps |
| decryption returning early on a wrong weight (PQClean; liboqs AVX2) | ct:decaps |
| implicit rejection picking `s` or `e` by pointer (PQClean; liboqs AVX2) | ct:decaps |
| the syndrome reading a parity table indexed by the error vector (PQClean) | ct:encaps, in `syndrome`, outside the sampler |

**ML-DSA** (`--audit-dsa ... --constant-time`; [CONSTANT-TIME.md](CONSTANT-TIME.md)
is the specification). Sign's rejection loop branches on secret-derived
values by design, so a driver outside the library cannot tell those branches
from a leak. pq-verify judges a hooked build: the library's own
declassifications compiled in (mldsa-native's `MLD_CONFIG_CT_TESTING_ENABLED`)
and pq-verify's shim header in front of `<valgrind/memcheck.h>`, which logs
each declassification with its call site and bytes. Every memcheck report
fails. Every declassification must be at a site in the table for the pinned
implementation, in its place in the attempt, and equal to the value the
public key and signature determine wherever they do (on the accepting
attempt: the challenge, `w0`, `w1` and the signature). Signing runs on
messages chosen to include an acceptance at the first attempt, rejections and
a hint-weight rejection. The policy judges every searched call outside
Valgrind, 128 to 896 per set, and memcheck replays the chosen ones. Any other
build is CANNOT VERIFY.

| Library | Sets | ct:keyGen | ct:sign | Integer divisions |
|---|---|---|---|---|
| mldsa-native `159509d`, hooked build | 44 / 65 / 87 | 3/3 | 3/3 | none |
| every other ML-DSA row above | 44 / 65 / 87 | CANNOT VERIFY | CANNOT VERIFY | — |

Controls planted in mldsa-native ML-DSA-65 (CONSTANT-TIME.md, section 4),
each leaving every output correct:

| Planted change | Result in CI |
|---|---|
| the norm check takes `abs()` with a branch on the coefficient's sign | ct:sign fails: branch on a secret in `mld_poly_chknorm_c` |
| `z` declassified before its norm check | ct:sign fails: an undocumented site, `mld_compute_pack_z (z)`. memcheck is silent: the early declassification is what blinds it |
| the signature declassified before the hint-weight check, on a message accepted at its first attempt | ct:sign fails on value alone: the bytes declassified are not the returned signature |
| the same build, on a message with a hint-weight rejection | ct:sign fails on position: the signature is declassified in an attempt that was rejected |
| a table read indexed by a secret coefficient, its value discarded | ct:sign fails: secret used as a memory address in `mld_poly_chknorm_c`. With Valgrind's default translation it passed |
| `mld_decompose` divides with a hardware division (identical signatures) | passes, as specified: memcheck cannot see timing; the division list names `poly_decompose` and `poly_use_hint` |

## The contained worker, on the same libraries

`--audit-contained` runs an ML-KEM library in pq-verify's contained worker
and scores it in pq-verify's own process
([README](README.md#what-a-result-is-bound-to)). It is a different route to
the same answers, so CI takes it too: for every library and parameter set in
the [full-scheme KEM table](#full-scheme-kem-audit-including-invalid-keys),
`tools/vendor_audit.py` audits the same file a second time through the worker
and fails unless

- every stage both audits run has the same count (keyGen, encaps, decaps,
  ekCheck, dkCheck, the three edge stages and the 10,000 accumulated cases);
- `containment` and `bounds` pass: the filter was confirmed before the
  library was mapped, the library made no system call on its list and left no
  process behind, and no call wrote outside a buffer;
- the 24 fresh keyGen, encapsulation and decapsulation cases all pass, and
  the 16 fresh key checks pass exactly where NIST's do. PQClean, which has no
  rejection path, fails the invalid half of both, on inputs drawn for the run
  as on NIST's.

So the worker, its filter and its fresh questions are exercised on real
libraries (mlkem-native, PQClean and three builds of liboqs), not only on the
small ML-KEM pq-verify's tests are written against.

## Any language, through Crucible-protocol harnesses

`--audit-harness COMMAND PARAM_SET` audits an ML-KEM or ML-DSA implementation
in any language through a harness that speaks
[Crucible](https://github.com/symbolicsoft/crucible)'s JSON-line protocol.
Crucible's harnesses cover Go's `crypto/mlkem`, CIRCL, Bouncy Castle, libcrux,
AWS-LC, wolfCrypt, liboqs, noble and the Zig standard library.

**What is taken from Crucible: the wire format only.** No Crucible test,
verdict or exit code is used. Every check is pq-verify's — NIST's ACVP
vectors, NIST's invalid keys, the Wycheproof/CCTV edge cases — scored by the
same code as `--audit-kem` / `--audit-dsa`. The harness is untrusted:

| Could have been assumed | What pq-verify does instead |
|---|---|
| The harness follows the protocol | It is checked. Crucible's protocol says `ML_DSA_Sign` takes FIPS 204's M′, but its CIRCL and liboqs harnesses sign M with an empty context. Which one a harness uses is settled against a NIST signature, and only what that convention can carry is sent. |
| The harness is deterministic | Each operation is asked twice with the same inputs. Byte-exact checks a harness cannot be held to are not applicable, never passed. |
| An error is the library refusing | Only once the harness has accepted its own fresh signature; otherwise CANNOT VERIFY, since none of its rejections can be scored. |
| A crash, a hang, a reply that is not the protocol's (unparseable or nested too deep, outputs that are not an object of hex strings, a line over 1 MiB), or "unsupported" for an advertised function is a refusal | Never: CANNOT VERIFY. Scored as a refusal it would have passed every invalid-input check. `tests/fuzz_readers.py` corrupts one reply of a real audit at a time to hold this. |
| The harness speaks for the library | Unprovable across a process boundary. The harness file is hashed; the library behind it is pinned only by the harness's own build (here, `go.sum`), and the report says a failure can be the harness's wiring. |

Seed-form decapsulation keys (d ‖ z, which FIPS 203 §7.1 permits, as Go's
`crypto/mlkem` does) are checked as such: keyGen requires the ek byte-exact
and dk = d ‖ z, and NIST's expanded-key decapsulation cases are not
applicable rather than failed.

**Every pre-hash function's verifier.** NIST's ML-DSA verification vectors
hold a valid HashML-DSA signature for only three of the twelve pre-hash
functions per parameter set ([above](#full-scheme-ml-dsa-audit-with-mutants)).
A harness may send a HashML-DSA M′ to its library's own pre-hash code, and
pq-verify cannot see whether it does. So through a harness that takes M′,
each of the twelve is signed and must verify (preHashVerify). Through one
that signs M with an empty context, no HashML-DSA message can be sent, and
the 12 checks are not applicable.

Re-audited in CI by `tools/harness_audit.py`: Crucible's harnesses at
[`0522518`](https://github.com/symbolicsoft/crucible/commit/0522518e19559ef39ed1ff23643f52d2ac606084),
built unmodified with Go 1.26.1, and pq-verify's own Bouncy Castle harness
([below](#bouncy-castle-java-through-pq-verifys-harness)), run on JDK 21
against the jar pinned by sha256:

<!-- harness-audits:begin -->
| Implementation (harness) | Parameter set | Result | Checks | Not applicable |
|---|---|---|---|---|
| Go standard library crypto/mlkem (Go 1.26.1) (`harnesses/go-stdlib`) | ML-KEM-512 | CANNOT VERIFY | 0/0 | 0 |
| Go standard library crypto/mlkem (Go 1.26.1) (`harnesses/go-stdlib`) | ML-KEM-768 | **VERIFIED** | 1,469/1,469 | 31 |
| Go standard library crypto/mlkem (Go 1.26.1) (`harnesses/go-stdlib`) | ML-KEM-1024 | **VERIFIED** | 1,735/1,735 | 31 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-KEM-512 | **VERIFIED** | 1,489/1,489 | 0 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-KEM-768 | **VERIFIED** | 1,500/1,500 | 0 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-KEM-1024 | **VERIFIED** | 1,766/1,766 | 0 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-DSA-44 | **VERIFIED** | 274/274 | 210 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-DSA-65 | **VERIFIED** | 313/313 | 220 |
| Cloudflare CIRCL v1.6.3 (pinned by the harness's go.sum) (`harnesses/circl`) | ML-DSA-87 | **VERIFIED** | 336/336 | 219 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-KEM-512 | **VERIFIED** | 1,489/1,489 | 0 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-KEM-768 | **VERIFIED** | 1,500/1,500 | 0 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-KEM-1024 | **VERIFIED** | 1,766/1,766 | 0 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-DSA-44 | **VERIFIED** | 422/422 | 62 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-DSA-65 | **VERIFIED** | 462/462 | 71 |
| Bouncy Castle bcprov-jdk18on 1.86 (Maven Central jar, pinned by sha256) (`pq_verify/harness/bouncycastle`) | ML-DSA-87 | **VERIFIED** | 484/484 | 71 |
<!-- harness-audits:end -->

Go's `crypto/mlkem` has no ML-KEM-512, so its harness refuses that set:
CANNOT VERIFY, not a finding. The CIRCL harness's ML-DSA cases that are not
applicable are the internal, pre-hash and non-empty-context ones its
convention cannot carry, and external μ, which the protocol cannot.

Four places where Crucible's protocol and its harnesses disagree, found on
the first runs:

1. `ML_DSA_Sign` / `ML_DSA_Verify` "message": M′ in the protocol and
   templates; M with an empty context in the CIRCL and liboqs harnesses.
2. The verify signature input: `signature` in the README; `sigma` in the
   test battery and the CIRCL harness. pq-verify sends both.
3. Determinism: the liboqs harness's `ML_DSA_KeyGen` ignores its seed, so
   byte-exact checks through it are not applicable.
4. `ML_DSA_Verify`'s `valid`: hex in the protocol; `true` / `false` in the
   Bouncy Castle harness, which pq-verify cannot score: CANNOT VERIFY.

### Bouncy Castle (Java), through pq-verify's harness

Bouncy Castle's Java provider, `bcprov-jdk18on` 1.86 (2026-09-11), audited
through its lightweight API: ML-KEM-512/768/1024 and ML-DSA-44/65/87.
Crucible ships a Bouncy Castle harness, but through it nothing byte-exact
can be checked and ML-DSA cannot be scored at all. It ignores the
protocol's randomness inputs: key generation and encapsulation draw from a
live `SecureRandom`, and signing always uses rnd = 0. It also answers
`valid` as `true` or `false` (item 4 above).

So pq-verify ships its own,
[`pq_verify/harness/bouncycastle/PqvBouncyCastle.java`](pq_verify/harness/bouncycastle/PqvBouncyCastle.java),
run with Java's source launcher so that the report binds to it:

- **Randomness through the API users call.** NIST's seeds and `rnd` go in
  through a `SecureRandom` that serves exactly the given bytes:
  `MLKEMKeyPairGenerator` draws d then z, `MLKEMGenerator` draws m,
  `MLDSAKeyPairGenerator` draws the seed, and the signers draw `rnd`. A draw
  of any other length is an error, which the audit counts against the
  library.
- **Keys through Bouncy Castle's own constructors,** which apply its checks:
  FIPS 203's modulus check on an encapsulation key and its hash check on a
  decapsulation key, and the encoding lengths.
- **ML-DSA's M′ through the entry point that can express it.**
  - A pure-ML-DSA message goes to `MLDSASigner` with its context.
  - A HashML-DSA message with SHA2-512, the only pre-hash Bouncy Castle
    implements, goes to `HashMLDSASigner`.
  - Anything else goes to `MLDSAEngine`'s internal functions.

  Each computes exactly FIPS 204's Sign_internal or Verify_internal over M′.

**The jar** is fetched from Maven Central and pinned by sha256
(`2af190b3…`), with the sources jar its mutants are rebuilt from. Both carry
a PGP signature from key `7B12 1B76 A7ED 6CE6 E60A D517 84E9 13A8 E3A7 48C0`,
"The Legion of the Bouncy Castle Inc. (Maven Repository Artifact Signer)".
Maven Central's signatures on the 1.76 (2023) and 1.80 (2025) jars name the
same key. Its fingerprint was not cross-checked on bouncycastle.org. The harness names the jar it loaded,
with its sha256, in its handshake, and the report carries it.

**Results** are in the table above.

- **ML-KEM:** nothing is not applicable.
- **ML-DSA:** the cases that are not applicable are external μ, which the
  protocol has no route for, and the edge cases with a 256-byte context or
  μ.
- **HashML-DSA:** Bouncy Castle's SHA2-512 verifier is one NIST's vectors
  never test with a valid signature (SHA2-512 is one of the five with none),
  so the pre-hash round trip is what checks it.

**Mutants.** Each recompiles one class from Bouncy Castle's own 1.86 sources
with one planted bug, into a copy of the jar without its signature files (a
signed jar refuses a class it did not sign). CI requires every one to fail:

| Planted bug in Bouncy Castle | Caught by |
|---|---|
| a decapsulation key is loaded without FIPS 203's hash check | dkCheck, Wycheproof/CCTV dk |
| an encapsulation key is loaded without FIPS 203's modulus check | ekCheck, Wycheproof/CCTV ek |
| HashML-DSA verification hashes zeros in place of the digest | every pre-hash verifies only |
| pure ML-DSA verification ignores the context | sigVer pure, Wycheproof verify |
| signing does not draw the caller's randomness | sigGen pure, Wycheproof sign |

The HashML-DSA one passes every NIST and Wycheproof vector.

**Not reached this way:**

- **SLH-DSA, LMS/HSS and XMSS:** the protocol carries ML-KEM and ML-DSA only,
  and pq-verify's audits of the others drive a C library's entry points.
- **Falcon:** Bouncy Castle's is round-3 Falcon, not FN-DSA.
- **Bouncy Castle's C# library:** it needs a harness of its own.
- **The FIPS module on Maven Central (`bc-fips` 2.1.3):** it has no ML-KEM,
  ML-DSA or SLH-DSA classes.

Audit your own Bouncy Castle jar the same way:

```bash
H=$(python3 -c "import pq_verify, os; print(os.path.join(os.path.dirname(pq_verify.__file__), 'harness', 'bouncycastle', 'PqvBouncyCastle.java'))")
pq-verify --audit-harness "java -cp bcprov-jdk18on-1.86.jar $H" ML-KEM-768
pq-verify --audit-harness "java -cp bcprov-jdk18on-1.86.jar $H" ML-DSA-65
```

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

The symbol audits verify the **number-theoretic transform** against the FIPS
203/204 definitions; `--audit-kem`, `--audit-dsa` and `--audit-hbs` verify a
library's whole scheme against the pinned vectors. None of them:

- verify side-channel resistance: `--constant-time` checks ML-KEM's and
  Classic McEliece's Encaps and Decaps, and ML-DSA's key generation and
  signing in a hooked build, for secret-dependent branches and addresses,
  within the scope in [Constant time](#constant-time---constant-time), and
  nothing else
- constitute a security review of the surrounding implementation

A passing NTT audit says the transform is arithmetically correct. It does not
say the library is free of defects elsewhere. Everything pq-verify does not
check is collected in [LIMITS.md](LIMITS.md).
