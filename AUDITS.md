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

NIST's vectors are seeded, so an API that draws its own randomness can only
be checked byte-exactly if pq-verify controls that randomness. The libraries
below are linked with `pq_verify/harness/pqv_randombytes.c`, which serves
NIST's seed and `rnd` to `randombytes()` and records any call that draws
more or less than FIPS 204 calls for. That is how the randomised
`keypair()` and `signature()` the libraries' users call are audited, not
only the seed-taking internal functions.

<!-- vendor-audits-dsa:begin -->
| Library | Commit | Sets | keyGen | sigGen int / pure / pre-hash / μ | sigVer int / pure / pre-hash / μ | Wycheproof verify / sign / length | Not applicable | Mutants caught | Result |
|---|---|---|---|---|---|---|---|---|---|
| mldsa-native | [`159509d`](https://github.com/pq-code-package/mldsa-native/commit/159509d78063316bf090bbcd0aa50af5bb03cf70) (2026-10-01) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / 90/90 | 45/45 / 45/45 / 45/45 / 45/45 | 610/610 / 278/278 / n/a | 30 | 3/3 | 1,503/1,503 **VERIFIED** |
| pq-crystals dilithium ref | [`d35ba3f`](https://github.com/pq-crystals/dilithium/commit/d35ba3fe5449bee3e6d43e1f296c3ca818bd36be) (2026-06-03) | 44 / 65 / 87 | 75/75 | 90/90 / 90/90 / 90/90 / n/a | 45/45 / 45/45 / 45/45 / n/a | 610/610 / 236/236 / 9/9 | 198 | 6/6 | 1,335/1,335 **VERIFIED** |
| PQClean clean | [`0586a82`](https://github.com/PQClean/PQClean/commit/0586a824fc0d49df0b6b6e9179d8d15d06d0974f) (2026-08-04) | 44 / 65 / 87 | 75/75 | n/a / 90/90 / n/a / n/a | n/a / 45/45 / n/a / n/a | 610/610 / 236/236 / 9/9 | 468 | 1/1 | 1,065/1,065 **VERIFIED** |
<!-- vendor-audits-dsa:end -->

All three are byte-exact on every interface they expose. They differ in
what they expose: mldsa-native implements every interface, including
external μ and a native HashML-DSA API; pq-crystals ref has no external-μ
API; PQClean has pure ML-DSA only. The "not applicable" column counts
what each one's API cannot be asked.

**Mutants.** An audit that passes correct libraries has shown half of what
it must. Each row also carries mutants: a one-line change to the pinned
source that plants a known bug class. CI builds every one and requires the
audit to fail it in the listed stages (`tools/vendor_audits.json`). All ten
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
| PQClean | verify skips the challenge comparison | sigVer pure, Wycheproof verify |

Two of these bug classes are invisible to NIST's vectors: a verifier that
accepts a repeated hint index (the defect dilithium-py 1.4.0 ships, which
makes signatures malleable) and one that skips the ‖z‖∞ < γ₁ − β check both
pass every NIST sigVer vector. Only Wycheproof's verify vectors catch them,
which is why `--audit-dsa` runs both.

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

- verify constant-time behaviour or side-channel resistance
- constitute a security review of the surrounding implementation

A passing NTT audit says the transform is arithmetically correct. It does not
say the library is free of defects elsewhere.
