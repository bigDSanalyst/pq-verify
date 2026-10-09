# Changelog

All notable changes to pq-verify. This project follows [semantic
versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added — HQC's error-correcting code (HQC's standard is not final)

- **`pq-verify --hqc`**: pq-verify's own reference for HQC's code layer
  (`pq_verify/hqc.py`: GF(2⁸), the Reed–Solomon code and a Berlekamp–Massey /
  Forney decoder, the duplicated Reed–Muller RM(1,7) code and an exact
  maximum-likelihood decoder with the submitters' lowest-index tie rule),
  held to the generator polynomials the submitters publish and to their own
  reference decoders' answers on a fixed-seed suite of built vectors, pinned
  as digests (`tools/pin_hqc_vectors.py`): 61/61 in about 2 s. Two code
  profiles: v5 (HQC v5.0.0, whose code layer PQClean's 2023 submission
  shares, verified on the same suite) and next (the submitters' unreleased
  next-release branch: a new field polynomial, generator x + 1, and
  Reed–Muller bytes stored most-significant bit first).
- **`pq-verify --audit-hqc PATH SET`** (with `--hqc-profile`, `--hqc-symbol`,
  `--hqc-seed`, `--symbol-prefix`): a library's own encoder and decoder
  functions, called directly, because decapsulation's re-encryption hides
  the decoder from any KEM-level test. Every codeword; blocks between two
  codewords at every distance up to the inner radius; ties (including the
  GF(2⁷) inversion word, tied 14 ways); one exact copy outvoting noisy ones;
  Reed–Solomon error patterns whose leading Hankel minors vanish (the
  Berlekamp–Massey branch random patterns rarely reach); whole received
  words; guard bytes around every output. Each answer exact.
- **PQClean's HQC and the submitters' reference (v5.0.0 and next-release)
  are pinned and re-audited in CI**, HQC-1/3/5: 5,349/5,349, and nine planted
  decoder bugs are all caught. Three of them fail on 5–9% of random
  full-weight error patterns and on every Hankel-built one.
- **Two defects in the submitters' AVX2 Reed–Muller decoder** (v5.0.0, and
  next-release at 71090d4), recorded as pinned rows: its peak search starts
  from a width too small for HQC's odd multiplicities, so blocks inside the
  unique-decoding radius between two codewords can decode to the farther one
  (40 800 random and noisy blocks never triggered it; whole received words
  within both radii then decode to the wrong message); and its sign lookup reads an `__m256i`
  through a `uint16_t` pointer, so under GCC 13 at `-O2` every block's sign is
  wrong and the KEM fails every round trip (fine at the submitters' `-O3`).
- Its own track everywhere (`track: "hqc"`), never part of a FIPS 203/204/205
  verdict; the KEM around the code is not covered.

### Added — Classic McEliece (round 4; not a FIPS standard)

- **`pq-verify --mceliece`**: pq-verify's own Classic McEliece reference
  (`pq_verify/mceliece.py`: seeded key generation, encoding, the Goppa decoder,
  implicit rejection) held to the official KATs for all ten parameter sets.
  The KATs come from PQClean's NIST harness and match the `nistkat-sha256`
  PQClean publishes (`tools/pin_mceliece_vectors.py`). Their 0.26–1.36 MB
  public keys are not pinned: each is regenerated from the private key's seed,
  and the rebuilt KAT must hash to the published value. All ten sets in about
  15 s.
- **`pq-verify --audit-mceliece PATH SET`** (and `--mceliece-symbol`,
  `--symbol-prefix`): a vendor library's keys regenerated from the seed in
  their own private key (public key, pivots, Goppa polynomial and rejection
  string byte-exact, control bits encoding the permutation); its ciphertexts
  decoded; ciphertexts built against its key (weight t, t−1, t+1, zero,
  random, another key's) decapsulated to the exact expected key -- including errors through the
  support's zero element, where the locator's degree drops; and, for
  6960119, padding bits refused as the submitters' reference does.
- **PQClean's Classic McEliece is pinned and re-audited in CI**, all ten sets:
  404/404, and eight planted bugs (a decoder accepting any weight, implicit
  rejection hashing the wrong string or prefix, a zero `s`, missing pivots,
  the wrong encapsulation prefix, padding ignored twice) are all caught.
- **liboqs 0.16.0's Classic McEliece is pinned too**, through its public API
  in two builds: the distribution build, whose API runs the AVX2 backend on
  CI's runner, and the portable one, which has only the clean backend (the
  backends' own entry points are not exported). 404/404 each, and nine planted
  bugs caught, two of them in liboqs's wrapper (it turns the backend's refusal
  of a padded ciphertext into success). `tools/vendor_audit.py` builds liboqs
  per configuration: the McEliece sets apart from the other rows, dist or
  generic.
- **`--audit-mceliece ... --constant-time`**: Decaps (the whole private key
  secret, a valid and a random ciphertext) and Encaps (its randomness secret)
  under Valgrind memcheck. The NIST API takes no coins, so the driver supplies
  the randomness (`randombytes()`, `PQCLEAN_randombytes()`, liboqs's custom
  RNG hook) and refuses an Encaps that draws none through it; keys and valid
  ciphertexts come from the library itself, outside Valgrind, so a set takes
  seconds. Reports inside the function that drew the randomness (the
  error-vector sampler, whose rejection checks the submitters declassify) are
  listed, not judged; everything else fails. PQClean and both liboqs builds:
  clean on all ten sets (60/60), and seven planted leaks are caught, among them
  a parity table indexed by the error vector in the syndrome, outside the
  sampler. Two reports inside liboqs's AVX2 sampler were traced to the
  instruction: GCC reuses the rejection flag's register as a loop counter,
  a memcheck false positive. Key generation is not checked (declassified
  retries, and minutes per key under memcheck).
- Its own track everywhere (`track: "classic-mceliece"`), never part of a FIPS
  203/204/205 verdict, and a check of correctness, not of the scheme's
  security (its cryptanalysis is active; deployment follows agency guidance).
  The native GF(2) engine is not used: it holds at most 2048 variables and
  returns solutions, not the reduced matrix a public key is.

### Changed — the README is for using pq-verify

- **README.md is cut from 851 to about 550 lines**, by moving what is not
  needed to run an audit into two new files; nothing was removed and no claim
  changed. **ARCHITECTURE.md**: the full "Proven" list, the engine tracks, the
  six field-native engines and the specification front-end, the pinned
  vectors, the Python API, the evidence model in depth (scope, fresh
  questions, LMS key reuse, coverage) and the side-channel report fields.
  **HYBRID.md**: RFC 10024 composition in full.
- "What a result is bound to" now follows the Quick start, so a reader meets
  what a result does and does not show before anything else.
- The documentation guards (documented flags exist, referenced files exist,
  links and anchors resolve, the 160-check and ACVP figures match what is
  measured, the RFC 10024 table matches the registry) cover both new files.
- **LIMITS.md**: everything pq-verify does not check, in one place — what a
  pass is bound to (an audit-aware library, the CPU's code path, the
  prompt/response path's `artifact: none`, hidden symbols), the schemes not
  covered, partial coverage within covered ones, constant-time scope (ML-KEM
  and Classic McEliece Encaps/Decaps only), parameter security, the verdict
  classes, and which paths are proved in Coq and which are only tested. Its
  estimator figures and its constant-time table are held to the code by tests.
- The README's estimator row asked "Are the parameters hard enough?"; it now
  asks what the estimator answers. ML-KEM's three sets report the
  lattice-estimator's pinned primal-uSVP values; the formula for custom
  parameters matches it at its calibration point (Kyber-512) and gives
  β = 624 and 874 on ML-KEM-768's and -1024's parameters, against 630 and 864.
  "Reproduces lattice-estimator exactly" is gone from README and
  ARCHITECTURE.md.
- ARCHITECTURE.md's package list names all 24 modules, `coq/`, `harness/`,
  `vectors/` and `tools/`; the `dist/` files it listed are release assets,
  not in the repository. AUDITS.md's scope no longer says no audit checks
  constant time.

### Added — liboqs, audited per implementation

- **liboqs 0.16.0 is pinned and re-audited in CI** (`5a1a854`, built as
  distributions ship it: CMake, `OQS_DIST_BUILD`). Its public `OQS_*` API and
  each backend behind it are audited separately, because the public API runs
  only the backend the CPU selects. ML-KEM: 4,569/4,569 per implementation,
  constant time included. ML-DSA: 1,068/1,068 through the public API,
  1,512/1,512 through each mldsa-native backend. Falcon (draft track):
  227/227, padded and not. Nine planted bugs, in liboqs's wrappers and in
  each backend, are all caught. No defect was found in liboqs.
- **`--symbol-prefix PREFIX`** (with `--audit-kem`, `--audit-dsa`,
  `--audit-fndsa`; `prefix=` in the Python API) audits one implementation of
  a library that exports several. An ambiguous binding is still refused, and
  the refusal now lists the implementations to choose between.
- **liboqs's ML-DSA API** (`--dsa-abi oqs`, detected from the symbols bound):
  message-first verify, the `*_with_ctx_str` variants, and randomness through
  liboqs's own `OQS_randombytes_custom_algorithm` hook, so keyGen and pure
  sigGen are byte-exact with no special build, and a call drawing the wrong
  amount of randomness is a finding.
- **mldsa-native before 2.0.0** (`--dsa-abi mldsa-native-v1`, as liboqs
  vendors it), which passes signature lengths; told apart from 2.0.0 by the
  signed-message API 2.0.0 removed.
- The ML-KEM vendor table gains Constant time and Mutants caught columns.

### Fixed — found by auditing liboqs

- **mldsa-native's v1 backends crashed the ML-DSA audit**: pq-verify knew
  only 2.0.0's fixed-size convention. Reported CANNOT VERIFY, never passed.
- **Explicitly named `OQS_SIG_ml_dsa_*` symbols would have been called with
  mldsa-native's argument order.** The convention now follows the symbols
  bound, and a binding mixing liboqs's API with a backend's is refused.
- **An explicitly named `sign` or `verify` entry point was silently
  replaced** when a context-taking variant was also found. An explicit
  binding now always stands.
- **The ML-DSA audit left liboqs's RNG hook installed** when called from
  Python, so liboqs used afterwards in the same process drew zeros. The hook
  is now installed only while seeds are queued and handed back when the audit
  ends. The command line was never affected (each audit runs in a child
  process).

## [2.11.0] — 2026-10-07

### Fixed — supersingular curves, and engine targets that overclaimed

- **Every j = 0 and j = 1728 curve was reported supersingular.** The rule is
  exact only with the prime: for p > 3, j = 0 is supersingular iff
  p ≡ 2 mod 3 and j = 1728 iff p ≡ 3 mod 4 (Deuring); any other j only when
  the trace is 0, which the exact point count now decides. Three of the four
  "supersingular" curves in the adversarial suite's B2 were ordinary
  (y² = x³ + 1 mod 97 has 84 points; y² = x³ + x mod 17 and mod 97 have 16
  and 80), so B2 passed by sharing the check's mistake. B2 now holds six
  supersingular curves (including j = 8 mod 17, found only by the count, and
  j = 1728 mod a prime above 10¹⁵, decided by the rule alone) and must leave
  four ordinary j = 0 / 1728 controls unflagged.
- **SafeCurves' "ordinary curve" control could not fail**: it passed at any
  severity of at least OK. An OK expectation is now exact.
- **Engine targets no longer claim what they do not do.** The curve engines
  were listed as heading toward "the ECDH half of hybrid KEMs"; X25519 is
  neither j = 0 nor j = 1728, and hybrids are checked by `--verify-hybrid`,
  which does not use these engines. Engine 6 was listed as heading toward
  "mod-p Hasse–Witt test vectors for SQIsign", a route that does not exist.
  Both now say they have no PQC target.

### Added — exact FN-DSA key checks (`--audit-fndsa`, draft track)

- **keyGen checks that every secret key is a valid Falcon key**: G is
  recomputed (`g·F/f mod q`, centred, |G| ≤ 127) and `f·G − g·F = q` must
  hold in ℤ[x]/(xⁿ+1); both Gram–Schmidt norms must be below 1.17²·q:
  `‖(g, −f)‖²` and `q²·[1/(f f* + g g*)]₀`, the latter an exact rational
  through the field-norm tower. No floating point. The third polynomial in
  the secret key, decoded and discarded until now, is F (it was named G).
- A mutant whose key generator stores an F that does not solve the NTRU
  equation is caught; PQClean passes at both sets (keyGen 30/30).
- A library that refuses to sign with its own key is now a sign failure,
  not a crash of the audit.

### Added — constant-time audit (`--constant-time`)

- **`--audit-kem PATH SET --constant-time`** runs the vendor's own Encaps
  (m secret) and Decaps (the K-PKE secret key and z secret, on a valid and on
  a random ciphertext) under Valgrind memcheck with the secret bytes marked,
  and fails on every secret-dependent branch or memory address, naming the
  function. Stages `ct:encaps`, `ct:decaps`; the report's `side_channel`
  gains `constant_time_checked` with the exact scope.
- A self-test first: a deliberate branch on a marked secret must be
  reported, or the check is unavailable -- memcheck's silence is never read
  as a pass. Asked for and unable to run (no valgrind) fails the audit.
- What it does not see, stated in every report: instruction timing (a secret
  division, as in KyberSlash -- division instructions are listed for review
  instead), key generation (rho is derived from the secret seed and
  rejection-sampled; libraries declassify it internally), and anything
  physical.
- mlkem-native and PQClean pass at all three sets. Three leaks planted in
  PQClean, each leaving every output correct (a secret branch in
  `poly_frommsg`, the Clangover class; a secret-indexed table in
  `poly_tomsg`; `memcmp` in the FO re-encryption check), pass every
  correctness stage including the accumulated cases and are caught here. CI
  installs valgrind and requires all of it (`tools/vendor_audit.py`).

### Added — accumulated vectors

- **10 000 seeded random cases per audit**, hashed into one digest and
  compared with a pinned value: ML-KEM (keyGen, encaps, decaps of the right
  and of a random ciphertext) and ML-DSA (keyGen, deterministic signing,
  verification), the way Go and BoringSSL test themselves. On by default for
  `--audit-kem`, `--audit-dsa` and `--audit-harness`; `--accumulated N`
  chooses 100 or 10 000, `0` skips. A stage of its own (`accumulated`) in
  every report, with where its digest comes from.
- They reach what no fixed vector set does. A planted bug that returns a
  wrong shared key on about 1 ciphertext in 8 192 passes every NIST,
  Wycheproof and CCTV vector and is caught by the accumulated run (ML-KEM-512
  and -768; at 1024 its trigger never came up in 10 000 cases -- coverage is
  probabilistic, and the docs say so).
- **C2SP CCTV's published ML-KEM accumulated digests are the FIPS 203
  draft.** With the draft's K-PKE.KeyGen G(d) instead of the final
  G(d || k), pq-verify reproduces CCTV's ML-KEM-512 value exactly; no
  final-FIPS-203 implementation can match them, so every correct library
  would have failed. pq-verify uses Go's construction and Go's published
  ML-KEM-768 digests instead, and pins ML-KEM-512/1024 digests computed only
  where independent implementations agree (PQClean, kyber-py, CIRCL, Go),
  labelled as computed, not published. CCTV's ML-DSA digests are final FIPS
  204 and are used as published.
- Every pinned library passes: mlkem-native, PQClean (ML-KEM and ML-DSA),
  mldsa-native, the pq-crystals reference; through harnesses, Go
  `crypto/mlkem` and CIRCL. The vendor-audit tables gain the column.

### Added — audit any language through Crucible-protocol harnesses

- **`--audit-harness COMMAND PARAM_SET`** audits an ML-KEM or ML-DSA
  implementation through a harness speaking Crucible's JSON-line protocol
  (Go, Java, Rust, JS, Zig ...). Only the wire format is Crucible's: NIST's
  vectors and invalid keys and the Wycheproof/CCTV edge cases are scored by
  the same code as `--audit-kem` / `--audit-dsa`. JSON
  (`pq-verify/harness-audit-result`) and SARIF; the harness file is hashed.
- The harness is untrusted. A crash, hang or protocol violation is CANNOT
  VERIFY, never a refusal (as a refusal it would pass every invalid-input
  check). Determinism is tested: checks a harness cannot be held to are not
  applicable. Its ML-DSA message convention (M′, or M with an empty context)
  is settled against a NIST signature. It must accept its own fresh signature
  before its rejections are scored.
- Seed-form decapsulation keys (d ‖ z, FIPS 203 §7.1) are checked as such,
  not failed.
- `tools/harness_audit.py` rebuilds Crucible's Go `crypto/mlkem` and CIRCL
  harnesses at a pinned commit with Go 1.26.1 and requires their results in
  CI: Go ML-KEM-768/1024 and CIRCL ML-KEM-512/768/1024 and ML-DSA-44/65/87
  VERIFIED.
- `pq_verify.edge`: a backend may declare inputs it cannot be handed
  (`accepts`), counted as not applicable.

### Added — FN-DSA library audit, draft track (FIPS 206)

- **`--audit-fndsa PATH FN-DSA-512|FN-DSA-1024`** audits a vendor's FN-DSA
  (Falcon) library through its own entry points (NIST API / PQClean, or
  liboqs `OQS_SIG_falcon_*`, padded variants included; `--fndsa-symbol
  ROLE=SYMBOL` when a library exports more than one candidate). Report
  `pq-verify/fndsa-audit-result`, `track: "draft"`, JSON and SARIF, run in an
  isolated child process like every other audit.
- Stages: the pinned signatures verify and open; every malformed input is
  refused (including a public key with the wrong header); the library's keys
  are canonical and satisfy h·f = g mod q; its signatures verify under
  pq-verify's verifier and its own, are in range, and never reuse a nonce.
- **The public-key range check is now tested so only the decoder can catch
  it.** The case used to set a coefficient to 0x3FFF, which also changed the
  key mod q, so a verifier without the range check still rejected it at the
  norm check. A PQClean mutant with the check removed passed. The case now
  re-encodes a coefficient as `w + q`: the same key mod q.
- `tools/vendor_audit.py` pins PQClean's Falcon-512/1024 (225/225) and seven
  mutants, each failed by the audit in CI; AUDITS.md publishes the table.

## [2.10.0] — 2026-10-07

### Changed — read before upgrading

- **Failing results now fail the exit status by default.** `0` verified, `1` a
  task found problems or could not verify, `2` bad input. Before, every task
  exited 0 unless `--fail-on-finding` was passed; the GitHub Action did not
  pass it to `--acvp-all`, so a failed ACVP run published `verified=true`.
  `--no-fail` restores report-only behaviour; `--fail-on-finding` is accepted
  and changes nothing. A failed self-suite check now fails the exit status too
  (it never did, even with the flag).
- **`pqverify_acvp_all()` is not `verified` when a requested suite did not
  run.** A missing kyber-py dropped ML-KEM from both sides of the ratio and
  the API reported `verified: True`; the result now lists `not_run`. The
  per-suite functions are not verified at 0/0.
- **A modifier without its task is an input error** (exit 2):
  `--audit-hbs-full`, `--dsa-abi`, `--dsa-symbol`, `--kem-*`, `--fresh-*` and
  `--audit-timeout` used to be ignored silently.
- **`--emit-prompt` without `--fresh-key` says its answers are public.** Its
  questions are NIST's; so are the answers. The old claim that a matching
  response "proves the responder computes the standard" is withdrawn.

### Added — FN-DSA verification, draft track (FIPS 206)

- **`pq-verify --fndsa`** checks FN-DSA (Falcon) signature verification
  ahead of the final FIPS 206, in its own report (`pq-verify/fndsa-result`,
  `track: "draft"`). It is not part of the self-suite's 160 checks, the 1566
  ACVP vectors, or any FIPS 203/204/205 verdict.
- Vectors: Falcon-512/1024 outputs of PQClean's reference code at `0586a82`
  (its NIST KAT harness and deterministic generator), 30 signatures, each file
  pinned to the sha256 PQClean publishes in META.yml.
  `tools/pin_fndsa_vectors.py` regenerates them from a checkout and refuses
  output that does not match; `--check` and `tools/doctor.py` re-verify
  offline.
- For every detached signature, the encodings a verifier must refuse, each
  required to be refused for the right reason: a decoder that accepts `-0`
  would pass a norm check unchanged, so the suite distinguishes the two.
- The NTT mod 12289 (n = 512, 1024) against the negacyclic definition, and
  every butterfly through the native Z_q engine, unchanged.
- Signing is not checked: it needs the final standard's vectors.

### Added — engine tracks, macOS

- **Every self-suite check carries a track** — `pqc` (54), `harness` (13),
  `classical` (45), `research` (48) — printed per track in the summary and
  recorded in the JSON report with the post-quantum work each non-PQC engine
  is being realigned toward (FN-DSA's NTT, HQC, Classic McEliece, hybrid-KEM
  curves, isogeny test vectors). Only the PQC track is PQC evidence; a check
  without a track fails the test suite.
- **macOS (Apple silicon) is tested in CI**: Mach-O symbols (`nm -gU`), dyld's
  image list for the loaded-object binding, portable engine flags (`-lrt`
  dropped on macOS, `-march=native` retried as `-mcpu=native`
  before building untuned, with the flags each engine got recorded in
  `core.ENGINE_FLAGS`; C++ engines built as
  C++17). Engine 6 build failures are now DEGRADED with the compiler's
  message and their checks recorded as skipped, rather than vanishing from
  the count.
- **CI pinned to `ubuntu-24.04`** ahead of `ubuntu-latest` moving to
  Ubuntu 26; failing tests on the macOS job are reported as annotations.

### Added — LMS in the prompt/response path

- **LMS, fresh and pinned, for implementations that cannot be loaded.**
  `--emit-prompt LMS_SHA256_M32_H5/LMOTS_SHA256_N32_W1 --fresh-key K` (any
  SP 800-208 pairing) poses keyGen, sigGen and sigVer in NIST's LMS ACVP
  layout; NIST's own LMS prompts join the pinned path too. sigGen is answered
  as ACVP asks — the responder signs with its own key and reports it per
  group — so each signature is verified under that key, the key must be of
  the group's type, and **a leaf signing twice under one key anywhere in the
  response is a finding**: the key-state check, applied to a black box.
  Sets too large to build in Python (over 3M hash calls, e.g. height 20) get
  sigGen alone.

### Added — LMS/XMSS key state

- **LMS/XMSS key-state audit: a one-time key used twice is broken, and no
  vector can show it.** `pqv_hbs.h` gains three optional functions
  (`pqv_hbs_state_keygen`, `pqv_hbs_state_sign`, `pqv_hbs_state_skip`,
  capability `PQV_HBS_CAN_STATE`) through which the library manages its own
  key in a file. `--audit-hbs` adds a `<scheme> state` stage per sampled key:
  the key matches `pqv_hbs_keygen`; every issued signature verifies; no leaf
  is issued twice; after each signature a restart from the stored key never
  reissues a released leaf (state durable before release); and the key signs
  its last leaf, then refuses — reached by skipping ahead, so 2^40-leaf keys
  are checked. Sampling takes the cheapest key of each distinct tree height
  first. An adapter without the functions reports the stage not applicable,
  so the scope is partial. Both shipped adapters implement them.
- **Two defects found in xmss-reference** (upstream `master`, 171ccbd): the
  last leaf of every key returns success with an invalid signature (the key
  is wiped before signing), and XMSS^MT h = 40 keys never refuse once
  exhausted (the all-ones marker equals the last valid index; the index then
  wraps to 0). Pinned as known failing checks; hash-sigs passes every state
  check. Three new mutants (count never written back; index not advanced;
  exhaustion check removed) are caught by the state stage alone.

### Changed — vendor audit tooling

- `tools/vendor_audit.py` pins each LMS/XMSS row's failing checks by name
  (`failing`), and a mutant counts as caught only when it fails a check the
  library itself passes — a stage the library already fails no longer
  catches every mutant vacuously.
- A not-run count with several reasons (sampled, over budget) lists each,
  rather than the last one seen.

### Added

- **Fresh, unpublished ACVP questions** (`pq_verify/fresh.py`):
  `--emit-prompt SET --fresh-key K` derives every input from a 256-bit seed
  written only to `K` (0600, never overwritten) and writes the questions in
  NIST's ACVP layout, so an ACVP harness answers them unchanged;
  `--verify-response R --fresh-key K` re-derives them, checks the promptId and
  computes the answers then. ML-KEM (keyGen, encapsulation, decapsulation with
  implicit-rejection ciphertexts, both key checks), ML-DSA (keyGen; sigGen and
  sigVer over every interface, deterministic and hedged, boundary context
  lengths) and all twelve SLH-DSA sets (keyGen, sigGen, sigVer).
  `--fresh-count` sets tests per group. Replaying NIST's public answers scores
  nothing. The pinned prompt path gains SLH-DSA sigGen and sigVer.
- **Every vendor audit runs in a child process** (`pq_verify/isolate.py`,
  `--audit-timeout`). A crash or a hang is `CANNOT VERIFY` with the signal or
  the limit, and a report is still written. The artifact binding gains
  `loaded_objects` (every shared object the audit mapped, with sha256),
  `loader_environment` and `isolation`; a file that changes mid-audit is
  `CANNOT VERIFY`. `PQV_IN_PROCESS=1` runs in-process, for debugging.
- **`scope` on `--audit-dsa` and `--audit-hbs` reports**: checked, not
  applicable and not run, with a one-line statement. `--require-full-coverage`
  fails a partial scope.
- **`--check-no-harness PATH`**: exit 1 if a build carries the deterministic
  randombytes() harness or a pqv_hbs adapter.
- **GitHub Action**: `audit: kem | dsa | hbs | ntt` and `param-set` drive the
  vendor audits; every input reaches the shell through `env:`, closing a
  script-injection path through `library`, `symbol` and the file inputs; the
  ACVP step is gated and writes a JSON report; `verified` is derived from
  every task that ran.

### Security

- The release workflow and the Action pin every action to a commit SHA (the
  release job holds `contents: write` and the OIDC identity PyPI trusts).
  The release verify job also runs `doctor.py` and `--lms-xmss`.

### Added (LMS/XMSS)

- **`--audit-hbs`: a vendor's own LMS/HSS or XMSS/XMSS^MT library.**
  `pqverify_audit_hbs()` loads a library through a **pqv_hbs adapter**
  (`pq_verify/harness/hbs/pqv_hbs.h`, ABI 1): five C functions that map its
  API onto one encoding, since LMS and XMSS libraries share no C API.
  Adapters for cisco/hash-sigs and xmss-reference ship in the package.
  - Stages: **verify** (every pinned vector: NIST LMS, the pqc-kat LMS and
    XMSS sets, liboqs XMSS/XMSS^MT/HSS, RFC 8554), **keyGen** and **sigGen**
    byte-exact (LMS with the ACVP derivation), and **malformed**: signatures
    derived from valid ones, wrong in exactly one field (leaf index,
    typecodes, randomizer, chain values, authentication nodes, length,
    message, key), each confirmed invalid by pq-verify's own verifier.
  - What the library does not implement is not applicable; key generation
    and signing over the budget, or beyond two cases per parameter set,
    are not run (`--audit-hbs-full`). Neither counts as a pass.
  - JSON (`pq-verify/hbs-audit-result`) and SARIF (new rule PQV009).
- **LMS/XMSS vendor audits in CI, with mutants.** cisco/hash-sigs
  `44e6c7d` and xmss-reference `171ccbd` are pinned in
  `tools/vendor_audits.json` with their mutants, all caught (final counts,
  with the key-state stage, are under "LMS/XMSS key state" above). A verifier
  that ignores the LM-OTS typecode in the signature passes every published
  vector and is caught only by the malformed stage. Two candidate mutants
  were discarded as equivalent (no verdict changes), and AUDITS.md says
  which and why.

- **LMS/HSS and XMSS/XMSS^MT** (RFC 8554, RFC 8391, SP 800-208), the
  stateful hash-based signatures CNSA 2.0 requires for firmware signing.
  `pq_verify/hbs.py` implements both from the specifications, every
  SP 800-208 hash family (SHA-256, SHA-256/192, SHAKE256/256, SHAKE256/192)
  and RFC 8391's SHA-512 and SHAKE128 sets, with SP 800-208's pseudorandom
  key generation.
  - **NIST's 87 ACVP LMS vectors** (ACVP-Server `2972def`) are pinned with
    the other NIST files and run in `--acvp-all` and `--lms-acvp`: 9 keyGen
    byte-exact, 16 sigVer verdicts, and 62 sigGen signatures verified under
    their published keys (NIST's sigGen vectors carry no private key).
  - **`--lms-xmss`** runs every other pinned source (`hbs_vectors.json.gz`,
    `HBS_MANIFEST.json`, `tools/pin_hbs_vectors.py`), each labelled by origin:
    ACVP-format LMS and XMSS vectors for every family from
    post-quantum-cryptography/KAT, liboqs's XMSS^MT and HSS KATs, and
    RFC 8554 Appendix F's HSS test cases via cisco/hash-sigs. Every signature
    is verified; key generation and signing are byte-exact for each tree
    within a hash budget. The default budget takes about 10 s (1,921 checks);
    `--lms-xmss-full` builds every height-10 tree. A case over the budget is
    reported as not run with its cost, never as passed.
  - The doctor checks the new bundle's digests offline, and the watcher
    tracks NIST's five LMS directories.
- **`--audit-dsa`: a vendor's own ML-DSA, against every NIST vector.**
  `pqverify_audit_dsa()` drives a compiled library's key generation, signing
  and verification with all of NIST's ACVP ML-DSA vectors for a parameter set
  (25 keyGen, 120 sigGen, 60 sigVer) and Wycheproof's ML-DSA verify and sign
  vectors.
  - Every FIPS 204 interface is its own stage (internal, pure, pre-hash over
    twelve hashes, external μ). Each goes through the most public entry
    point the library has for it, and the report names that symbol.
    Interfaces the API lacks are reported as not applicable with the
    reason, never as passes.
  - The pq-crystals/PQClean and mldsa-native calling conventions are
    detected from symbol names; `--dsa-abi` and `--dsa-symbol ROLE=SYM`
    override. An ambiguous symbol is refused, not guessed.
  - **Randomness harness** (`pq_verify/harness/pqv_randombytes.c`, shipped
    in the package). Linked in place of `randombytes()`, it lets pq-verify
    serve NIST's seed and `rnd`, so the randomised `keypair()` and
    `signature()` that users call are audited byte-exactly, not only the
    seed-taking internals. A call that draws more or less randomness than
    FIPS 204 calls for is a finding.
  - JSON (`pq-verify/dsa-audit-result`) and SARIF (new rule PQV008) reports
    name the first failing NIST tcId or Wycheproof case.
- **ML-DSA vendor audits in CI, with mutants.** `tools/vendor_audits.json`
  pins mldsa-native `159509d`, pq-crystals dilithium ref `d35ba3f` and
  PQClean `0586a82`, all three parameter sets each. All three are byte-exact
  on every interface they expose: 1,503, 1,335 and 1,065 checks. Each row
  carries mutants, one planted bug each, and CI requires the audit to fail
  every one; all ten are caught. Two of them, a hint decoder that accepts a
  repeated index and a verifier that skips the ‖z‖ bound, pass every NIST
  sigVer vector and are caught only by Wycheproof. AUDITS.md publishes both
  tables, and tests hold them equal to the pinned file.

- **SLH-DSA signatures, against every NIST ACVP vector** (FIPS 205, all 12
  parameter sets). Until now pq-verify checked SLH-DSA key generation only.
  - **sigVer, 504 vectors, on by default.** Every verdict must match NIST's
    `testPassed`: valid signatures, and ones with a modified message, R, FORS
    or hypertree part, or one byte too short or too long.
  - **sigGen, 624 vectors, opt-in** (`--slhdsa-siggen`,
    `pqverify_slhdsa_acvp(siggen=True)`). Every signature must be byte-exact
    with NIST's, deterministic and with NIST's `additionalRandomness`.
    Signing an 's' parameter set takes seconds per signature, so the full run
    takes about 30 minutes; a weekly workflow runs it with one job per
    parameter set, and on changes to the code, the vectors or the reference.
  - Both cover the internal interface and the external pure and pre-hash
    ones, the latter over all twelve approved hash functions. pq-verify builds
    M′ itself (domain separator, context, DER OID, digest) rather than calling
    the reference's wrappers, so those encodings are checked against NIST too.
    The reference's `sign()` cannot take injected randomness, so signing uses
    FIPS 205 Algorithm 19 written over its FORS and hypertree primitives.
  - Negative controls: a verifier that always accepts or always rejects
    fails exactly 432 or 72 vectors; dropping the context from M′ fails every
    valid external signature with a non-empty one; a signer that ignores
    `additionalRandomness` misses every randomised case.
- **`--slhdsa-acvp`** runs the SLH-DSA suite on its own (keyGen and sigVer);
  `param_sets=` limits it to chosen parameter sets.

### Changed

- The Wycheproof edge-case runner counts ML-DSA cases a backend cannot
  express as not applicable. They used to be skipped without a count.

- **`--acvp-all` and `pqverify_acvp_all()` include SLH-DSA keyGen and
  sigVer (624) and NIST's LMS vectors (87): 1566 vectors, up from 855.** The run takes about
  a minute. `pqverify_acvp_all(slhdsa=False, lms=False)` gives the previous 855; the
  `slh-dsa` reference was already part of `pq-verify[full]`. If it is missing,
  the SLH-DSA suite is reported as not run instead of being left out of the
  report.
- **The SLH-DSA signature vectors ship in a second archive,**
  `pq_verify/vectors/slhdsa_sig_vectors.json.gz` (39 MB). It holds NIST's
  files verbatim (ACVP-Server `112690e`) and is opened only when an SLH-DSA
  signature suite runs. The doctor checks each entry's sha256 offline, the
  watcher tracks all four files, and `--apply` rewrites only the archive that
  changed. The wheel grows from about 15 MB to about 54 MB.
- The watcher's structural fingerprint tells signature groups apart by
  interface (`signatureInterface`/`preHash`/`deterministic`), so a change
  report no longer merges the six groups that share a parameter set.

### Fixed

- **SARIF filed some findings under the wrong rule.** Rules were chosen by
  the first matching keyword, and "malformed" (CannotVerify) matched before
  a scheme's own prefix, so a finding about malformed signatures being
  accepted would have been reported as "could not verify". Scheme prefixes
  are now matched first.
- **The GitHub Action's `slhdsa` input did nothing.** It was declared but
  never read. SLH-DSA keyGen and sigVer now run with the ACVP suites, and
  `slhdsa: siggen` adds sigGen.
- **An ACVP report was VERIFIED when a requested suite could not run.** Only
  the suites that ran were counted, so with kyber-py and dilithium-py missing,
  `--acvp-all --fail-on-finding` would pass on SLH-DSA's 624/624 alone. A
  suite that did not run now makes the report CANNOT VERIFY and is listed
  under `summary.not_run`.
- **Nothing in CI ran the SLH-DSA ACVP suite.** The documented keyGen
  120/120 was never checked on a push. CI and the release workflow now
  install `slh-dsa` and fail unless all three ACVP suites ran, because
  `--fail-on-finding` alone passes a suite that could not run.

## [2.9.0] — 2026-10-01

### Fixed

- **A response answering one question twice could verify.** A second answer
  to the same tcId replaced the first, so a response carrying a wrong answer
  followed by the right one reported VERIFIED. Any question answered more
  than once is now a finding, whatever the answers say.
- **A truncated `.json.gz` response crashed the CLI** with `EOFError` instead
  of reporting CANNOT VERIFY.
- **Readers bound their input.** A response larger than 64 MiB (measured
  after decompression, so a gzip bomb cannot expand in memory) or a hybrid
  transcript larger than 1 MiB is CANNOT VERIFY, and at most one byte past
  the limit is read. The largest genuine documents are about 3.3 MB and 8 KB.
- **Freivalds used published seeds.** Every Freivalds check drew its random
  vector from a constant in the source (42, `trial + 1`, ...), so anyone could
  compute it and build an NTT output that is wrong in several coefficients
  yet passes. The seed is now drawn from the OS once per run and printed;
  `PQV_FREIVALDS_SEED=0x...` replays a run.
- **The Hasse check rejected genuine curves.** It used `2*isqrt(p)`, which is
  one short of ⌊2√p⌋ for p = 7, 13, ..., and reported y² = x³ + 3 over F₇
  (t = −5) as CRITICAL. The bound is now `isqrt(4p)`. Since no curve can
  exceed it, a violation is now reported as a defect in pq-verify's point
  count, not the curve's, and the "near-extreme trace" MEDIUM finding, which
  is not a known weakness, is gone.
- **Two self-suite checks could not fail.** "100,000 NTT butterflies"
  compared `(a + w*b) % q` with itself; it now runs every butterfly through
  the engine's Montgomery multiply and compares with integer arithmetic.
  "Freivalds throughput" passed unconditionally; it now requires every
  correct NTT to be accepted. The self-suite is still 160 checks.
- **The Coq certificates proved almost nothing about the run.** The "Full
  Kyber-768 NTT" certificate contained one layer-0 butterfly, and the batch
  certificate proved sums of random numbers drawn for the purpose. See Changed.

### Changed

- **`--verify-hybrid` recomputes the ML-KEM half, or does not say VERIFIED.**
  Nothing tied the ciphertext in the server share to the ML-KEM secret in the
  combined secret, so a transcript with a corrupted ciphertext was reported
  VERIFIED. A transcript may now carry the client's ephemeral ML-KEM
  decapsulation key (`clientMlkemDecapsulationKey`, optional, like the ECDHE
  private scalars): pq-verify checks it against the client share and FIPS 203
  §7.3, decapsulates the ciphertext and compares the result byte-for-byte.
  Without the key that check is NOT CHECKED and the result is **PARTIAL**, so
  transcripts that verified before without it now report PARTIAL.
- **Coq certificates are real, and checked for axioms.** The NTT certificate
  defines the FIPS 203 forward NTT and zeta table in Coq and proves
  `ntt input = output` for all 256 coefficients (896 butterflies), plus
  17¹²⁸ ≡ −1 (mod 3329). The batch certificate proves pq-verify's ML-KEM and
  ML-DSA zeta tables are root^brv(i) mod q as FIPS 203/204 define them. A
  certificate passes only if coqc accepts it **and** `Print Assumptions`
  reports every theorem closed, so an `Admitted` proof (which coqc accepts)
  or an added axiom fails. The "Coq-certified" tagline is replaced by what is
  actually proved.

### Added

- **General proofs, `pq-verify --proofs`.** `pq_verify/coq/` now holds
  theorems that quantify over every input, checked by coqc with every theorem
  required to be closed (no axioms, no `Admitted`):
  - `NTT.v`: the FIPS 203 (ML-KEM) and FIPS 204 (ML-DSA) forward NTT equal
    the Chinese-remainder map they are defined to compute, for every
    256-coefficient input. The transform is written once, generic over its
    arithmetic; a map that preserves the arithmetic commutes with it, so
    running it once on symbolic linear forms gives its matrix, which Coq
    checks entry by entry against the CRT matrix.
  - `Reduce.v`: `montgomery_reduce` (ML-KEM, ML-DSA), `barrett_reduce`
    (ML-KEM, all 65,536 int16 inputs) and `reduce32` (ML-DSA) are congruent
    to their input and within bound for every input in range, with no
    intermediate overflow.
  - Per-run NTT certificates now emit `NTT.v`'s transform verbatim, so they
    are about the proved definition.
- **Finding: two documented bounds in pq-crystals/dilithium `ref/reduce.c`
  are off by one.** `montgomery_reduce` documents `-Q < r < Q` for
  `-2^31 Q <= a <= Q 2^31`, but `a = Q 2^31` returns `Q`; `reduce32`
  documents `r >= -6283008`, but `a = -255·2^23 - 2^22` returns `-6283009`.
  The code is right and no ML-DSA input comes near either point; the comments
  overstate it. The proofs state the true bounds, and both witnesses are
  checked theorems. (ML-KEM's comment excludes its corresponding point and is
  exact.)

- **Wycheproof and CCTV edge-case vectors, pinned.** 24 files from C2SP
  Wycheproof (`3fa63dd`) and CCTV (`50a8ecf`) ship in
  `pq_verify/vectors/edge_vectors.json.gz`, each with its upstream sha256 in
  `EDGE_MANIFEST.json`; `tools/pin_edge_vectors.py` re-pins them
  deterministically. They cover what NIST's ACVP vectors mostly do not:
  `strcmp`-trap ciphertexts, unlucky XOF sampling, every coefficient value
  q…4095 at every position of an encapsulation key, corrupted decapsulation
  keys, malleated ciphertexts, and ML-DSA hint, norm-bound and context edges.
  - `--audit-kem` runs them against the vendor library as three new stages,
    `edgeValid`, `edgeEk`, `edgeDk` (`edge=False` to skip). The pinned vendor
    table records them: mlkem-native 4,320/4,320; PQClean accepts all 2,931
    invalid encapsulation keys and all 6 invalid decapsulation keys while
    every valid output is byte-exact.
  - `pq-verify --edge-cases [SET]` runs them against pq-verify's own
    references (kyber-py, dilithium-py), with `--json` and `--fail-on-finding`.
  - The doctor checks the bundle's digests offline and runs the vectors
    against the installed references (`--fast` skips that run): a failure not
    in `KNOWN_REFERENCE_DEFECTS` BLOCKs.
- **Finding: dilithium-py 1.4.0 accepts a repeated hint index.** FIPS 204
  Algorithm 21 (HintBitUnpack) requires strictly increasing indices;
  dilithium-py compares with `<` instead of `<=`, so Wycheproof's "repeated
  hint" signature verifies for ML-DSA-44/65/87. It is fixed upstream
  (GiacomoPope/dilithium-py `bd9b552`) but in no release. pq-verify grades
  third-party signatures against NIST's expected results, not dilithium-py's
  verdict, so no third-party result changes; `--edge-cases` reports the
  reference as FINDINGS PRESENT until a fixed release can be pinned.

- **`tests/fuzz_readers.py`** — a structure-aware fuzzer for the readers that
  take files from outside parties. It mutates genuine responses and
  transcripts ~25 ways (type confusion, truncation, deep nesting, oversized
  and gzipped input, flipped hex digits, duplicate entries) and requires, for
  every case, no exception, an honest status, prompt termination, a CLI exit
  of 0/1/2, and no VERIFIED for a document that differs from a genuine one.
  It found all three bugs above and the hybrid gap. A seeded slice runs in
  the test suite.

## [2.8.2] — 2026-09-29

### Fixed

- **`--vector-dir` was ignored for every bundled file.** The loader consulted
  the pinned bundle first by file name, so a caller-supplied vector directory
  was never read for any file pq-verify also ships, while the report named that
  directory as the source. A directory with a corrupted expected answer
  reported 240/240; it now reports 239/240. The same loader serves
  `prompt_dir` and the prompt/response path. The bundle now answers only for
  pq-verify's own vectors directory, and a file missing from a supplied
  directory is an error rather than a silent fallback to the bundle.

### Added

- **Vendor audits run in CI, pinned.** `tools/vendor_audits.json` pins each
  audited third-party ML-KEM library to an exact commit with the result
  pq-verify must reproduce; `tools/vendor_audit.py` rebuilds every row and
  re-runs `--audit-kem` on each change to pq-verify and weekly. With the
  library, the vectors and the reference implementations all pinned, a
  failure can only mean pq-verify changed. Reintroducing the 2.8.0
  symbol-resolution bug fails it on all three mlkem-native rows. Rows are
  only added, so the table records when a library's behaviour changes, and a
  test holds AUDITS.md equal to it.
- **Results name the reference implementation that computed them.** Next to
  the pinned vector revision, each ACVP run prints and records the version of
  the library that answered it (`reference: kyber-py 1.2.0`), in the console
  and in the JSON report's `suites`. The vectors were pinned; the software
  answering them was whatever happened to be installed, and nothing said which.
- **CI pins those versions** (`constraints-reference.txt`), so a CI result
  changes only when pq-verify's code does. Bumping one is its own PR. Users are
  not held to the pins, and `tools/doctor.py` warns when an environment differs
  from them.

- **`tools/doctor.py` — the checks a NIST re-pin must pass.** In the style
  of the syndicate-genesis and Dharmapala doctors: statuses ok / DECIDE /
  WARN / BLOCK, each finding with a `next:` command, `--json` for agents, and
  a token hashing what was examined and found. Offline it checks that the
  pinned bundle is sound: manifest coverage, NIST commit per file, watcher
  coverage, and FIPS 203 length of every key-check key. With `--candidate`
  it fetches NIST's changed files and runs, side by side with the pinned
  bundle: the same length checks, a negative control (a length-only checker
  must be fooled by every invalid key), every ACVP suite, a 14-day stability
  rule and provenance. `--apply` re-pins deterministically (byte-identical to
  the 2.8.1 re-pin done by hand) and is refused while the candidate BLOCKs.
  Replayed on history, it BLOCKs the vectors 2.8.0 shipped, which the ACVP
  suite scored 240/240.
- **`REPINNING.md`** — the procedure from watcher alert to release. The
  watcher's issue now names the doctor commands, and CI runs the doctor
  offline on every change.

## [2.8.1] — 2026-09-28

### Fixed

- **`--audit-kem` with an unknown parameter set exited 1.** A typo such as
  `ML-KEM-999` raised a traceback and exited 1, which a CI gate reads as
  "this library has findings". It now names the valid sets and exits 2, like
  every other input error.
- **`--audit-so` named the wrong parameter set.** An NTT is shared by every
  parameter set of its scheme, but the scan labelled every ML-KEM NTT
  "ML-KEM-1024" and every ML-DSA NTT "ML-DSA-87", including a 768 or 65
  library's. It now reports `ML-KEM-512/768/1024` / `ML-DSA-44/65/87`.
- **ACVP prompts cited every pinned NIST commit.** An ML-KEM prompt's
  `vectorSource` listed the ML-DSA and SLH-DSA commits too; it now cites only
  the suites it was built from.
- **Install hints no longer advise `--break-system-packages`.** They point to
  `pip install "pq-verify[full]"`.
- The CLI printed the integrity verdict twice after a self-suite run; it now
  prints once and still applies `--require-full-coverage`.

- **`--audit-kem` bound the wrong function on mlkem-native.** Symbols were
  picked by substring, taking the first name containing `keypair` and
  `derand`. On mlkem-native that is the internal `indcpa_keypair_derand`, so
  a correct, formally verified library was reported as FINDINGS PRESENT
  (35/60). Its decaps (`_dec`, not `kem_dec`) was not found at all, so from
  the CLI it could not be audited. Symbols are now matched by exact suffix
  across PQClean, mlkem-native and liboqs naming, internal K-PKE routines are
  excluded, a library exporting several parameter sets resolves to the one
  asked for, and an ambiguous match is refused instead of guessed.

- **Pinned NIST vectors re-cut to NIST's corrected files.** The bundle shipped
  two files from before NIST fixed them:

  | Files | Was | Now | NIST's fix |
  |---|---|---|---|
  | `ML-KEM-encapDecap-FIPS203` (3) | `c924096` | `ad33b3d` | "corrects ML-KEM encapDecap tests that included `ek` that were longer than intended" |
  | `ML-DSA-sigVer-FIPS204` (2) | `2972def` | `a7f283c` | "corrects ML-DSA sigVer FIPS204 sample json files for issue with ModifyZ disposition" |

  In the old encapDecap file every invalid encapsulation key was 416 bytes
  over length, so it was rejected on length alone and the FIPS 203 §7.2
  modulus check never saw an invalid key. A checker with no modulus check
  scored 30/30 on it; on the corrected vectors it scores 15/30. pq-verify's
  own checks agree with all 60 key-check labels in the corrected file. Counts
  are unchanged: ML-KEM 240/240, ML-DSA 615/615, SLH-DSA 120/120, offline.

  **ML-KEM and ML-DSA prompt IDs change** (SLH-DSA's do not). A prompt from
  `--emit-prompt` under 2.8.0 for those sets was generated from the old
  questions. Re-issue it before verifying a response;
  2.8.0 still reproduces the old results.

- **The NIST watcher now checks the shipped bundle.** It compared upstream only
  to its own baseline. The baseline was advanced to NIST's fixes but the bundle
  was not, so every weekly run reported "no change". It now also compares
  upstream to `MANIFEST.json` and reports files the bundle lags, and it adds to
  one open issue instead of opening a new one each week.

### Added

- **`--audit-kem` negative testing.** The audit now feeds the library NIST's
  invalid keys: `ekCheck` (5 encapsulation keys with a coefficient ≥ q,
  FIPS 203 §7.2) and `dkCheck` (5 decapsulation keys with a corrupted H(ek),
  §7.3). Each must be refused with a nonzero return while the valid ones are
  accepted. A full audit is now 80 checks. mlkem-native passes 80/80 at all
  three parameter sets; PQClean's `clean` ML-KEM accepts all ten invalid
  keys (70/80): its API has no rejection path, so the check falls to every
  caller. Details in AUDITS.md.
- `--kem-keypair` / `--kem-encaps` / `--kem-decaps` name the entry points
  when auto-detection finds none or several.
- Reports name the vector revision, e.g. `vectors: pinned (NIST ACVP-Server
  ad33b3d)`, and ACVP / `--audit-kem` results carry it as `vectors`.
  `MANIFEST.json` records each file's NIST commit and now covers the two
  SLH-DSA files it omitted.
- Tests: every bundled key-check key has its parameter set's exact length
  (fails on the old bundle), the manifest covers the whole bundle, and the
  watcher flags a lagging bundle.

## [2.8.0] — 2026-09-20

### Added

- **`--verify-hybrid` / `--emit-hybrid-prompt` — RFC 10024 hybrid key
  agreement.** Nothing in production negotiates bare ML-KEM; every deployment
  that has turned post-quantum TLS on runs a hybrid group. The ML-KEM half is
  covered by `--acvp` and `--audit-kem`. The *composition* was not, and the
  composition is where the bugs are, because RFC 10024 does not use one order:

  | Group | Codepoint | Key share | Shared secret |
  |---|---|---|---|
  | `X25519MLKEM768` | `0x11EC` | ML-KEM ‖ ECDHE | ML-KEM ‖ ECDHE |
  | `SecP256r1MLKEM768` | `0x11EB` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |
  | `SecP384r1MLKEM1024` | `0x11ED` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |

  The first row is reversed relative to its own name — the RFC says so and
  calls it historical. An implementation can pass **every ACVP vector
  byte-for-byte** and still be wrong, because ACVP never sees the
  concatenation, and the failure is silent: two peers that make the same
  mistake interoperate with each other and with nobody else.

  From one handshake's wire bytes, `--verify-hybrid` checks the lengths, the
  component split, the FIPS 203 §7.2 encapsulation key check the RFC makes a
  MUST, ECDHE point validity (RFC 9846 §4.3.8.2), the X25519 all-zero check,
  and — given an ephemeral private scalar — the ECDHE shared secret
  recomputed and compared byte-for-byte at the pinned offset.

  When a check fails it tests the other order explicitly and says so: *"there
  is no valid encapsulation key at offset 0, but there IS one at the offset
  the other order gives"*. That is a root cause rather than a mismatch, and it
  is sound rather than heuristic — random bytes pass the FIPS 203 §7.2 check
  with probability below 2⁻¹⁴⁰.

  New rule `PQV007` (`HybridCompositionMismatch`). The report is
  `artifact: none — vendor-supplied transcript`, on the same terms as
  `--verify-response`. No private KEM key is ever requested.

- **`side_channel` on every machine-readable report.** Functional conformance
  and leakage are independent properties, and this tool only measures the
  first. KyberSlash and Clangover were byte-exact correct against every vector
  and still recovered secret material through timing; a tool that checked only
  what pq-verify checks would have passed both. Rather than leave that to be
  inferred, every native report and the SARIF output now carry
  `"measured": false` with the reason. Native report schemas move to
  `schema_version` 1.1.

### Changed

- **`--leakage` is described as what it is.** It was presented as
  "side-channel leakage analysis", which a reader hears as a measurement. It
  is an *algebraic protection allocation*: it computes, from the NTT's
  structure, how much of the secret each butterfly layer would determine if
  that layer's intermediates were exposed. Nothing is executed under
  observation and no trace is collected. The computation is unchanged; the
  claim around it now matches it.

### Fixed

- **QUICKSTART documented a file that has not existed since this became a pip
  package.** It told readers to `exec(open('pq_verify_v2_6_1.py').read())`,
  listed "eight public functions", and gave the floor as Python 3.8 — below
  the declared `requires-python`. Rewritten against what the tool actually
  does, and three guards added: every flag shown on a `pq-verify` command line
  must be one the parser accepts, every file the docs name must exist, and a
  documented Python floor must equal `requires-python`. All three were
  confirmed by reintroducing the exact defects.
- A stale line count in `pq_verify/__init__.py` ("the real 5451-line stack"),
  deleted rather than corrected — a number nothing computes will drift again.

### Verification

- 49 new tests (83 → 141), green on 3.9, 3.12 and 3.13.
- The ECDH and X25519 reference is checked against RFC 7748 §5.2/§6.1 and the
  NIST CAVS 14.1 ECC CDH vectors before it is used to judge any transcript; a
  verifier whose own arithmetic is wrong would score a correct transcript as
  broken.
- The curve parameters are self-validating at import (base point on the curve,
  n·G at infinity), so a mistyped constant cannot reach a verdict.
- The FIPS 203 §7.2 check agrees with all 20 of NIST's own labelled
  `encapsulationKeyCheck` cases for ML-KEM-768 and ML-KEM-1024.
- 14 mutations were applied to the new guards — reversed orders, a disabled
  modulus bound, each wrong-order diagnostic removed, skips counted as passes,
  the side-channel field dropped. All 14 were caught. One initially survived:
  the swapped-shared-secret test asserted over the findings as a whole, so the
  ML-KEM diagnostic covered for the disabled ECDHE one. The test now asserts
  per check.

## [2.7.0] — 2026-09-19

### Security

Both issues were found by auditing this repository against its own standards,
and both are demonstrated by regression tests so they cannot return. See
[SECURITY.md](SECURITY.md) for details.

- **Untrusted library load (CWE-426).** The CFL benchmark loaded
  `./libgf2_cfl.so` from the working directory, and `/tmp/libgf2_cfl.so`, if
  either existed. `ctypes.CDLL` runs a library's constructors, so this was
  arbitrary code execution inside the verifying process for anyone who could
  write the directory pq-verify ran in — routinely a vendor build tree — or, via
  `/tmp`, any local user. The library is now opt-in by absolute path through
  `PQV_CFL_SO` and is never discovered implicitly.
- **Symlink-following writes (CWE-59).** Generated C and Coq sources went to
  fixed paths such as `/tmp/pqv_gf2.c`; `open(path, 'w')` follows symlinks, so a
  local user who pre-created one as a symlink got an arbitrary file overwrite
  with the running user's privileges. All generated files now go to a
  per-process `mkdtemp` directory with mode `0700`.

Users of 2.6.7 or earlier on shared or multi-user hosts should upgrade.

### Fixed

- **2.6.7 could not be imported on any Python below 3.12.** Six f-strings in
  `core.py` carried a backslash inside the expression part — PEP 701 syntax —
  while `requires-python` advertised `>=3.8`. pip installed it cleanly on 3.8
  through 3.11 and every import raised `SyntaxError`.
- **`requires-python` is now `>=3.9`**, the floor that is actually exercised.
  `pq-verify[full]` cannot resolve below it: `kyber-py` and `dilithium-py` both
  require `>=3.9`.
- **`--audit-kem --fail-on-finding` always exited 0.** It assigned a variable
  nothing read, so a library with faults — or one that could not be audited at
  all — passed a CI gate.
- **`--json` and `--sarif` were silently ignored** by every task except
  `--audit-so`. ACVP and KEM runs now emit reports; a task with none says so
  instead of leaving an empty path.
- **A target the dynamic linker could not load raised a traceback** out of the
  CLI instead of being reported as cannot-verify.
- **Two report-producing tasks in one invocation** overwrote each other's
  `--json` file without saying so.
- Compiler diagnostics are no longer discarded to `/dev/null`, where a broken
  build looked identical to a missing compiler. Engine compilation no longer
  goes through a shell.

### Changed

- **The self-suite now distinguishes a check that could not run from one that
  ran and failed.** A missing `coqc` was recorded as a *failed* test, so the
  headline read `151/158` — seven broken checks — when nothing was broken.
  Worse, none of those ten sites registered with `integrity_report()`, so a run
  without coq and sympy still announced *"full coverage: every engine built,
  every dependency present"* while seven checks had silently not run. That is
  the hole the whole `DEGRADED` mechanism exists to close, in the one codebase
  it was never pointed at.

  `AuditResult.add_skip()` adds the third state. Skipped checks are excluded
  from the ratio, print as `⊘` rather than `❌`, and register their missing
  dependency. The same run now reports `151/151 passed (7 SKIPPED)` and names
  all four absent dependencies — `coq`, `cryptominisat`, `slh-dsa`, `sympy` —
  where it previously named two.

  This is the `PQV000` / `PQV006` distinction — cannot-verify versus
  verified-and-failed — applied to pq-verify's own suite, which had it for
  everyone else's code and not its own. A tool that ran and rejected a
  certificate is still a failure; only absence, timeout and startup failure
  became skips.

- **`main()` returns its results**, so the self-suite can be asserted rather
  than merely run. It printed a tally nothing checked, which is how seven
  skipped checks read as failures for as long as they did.

### Added

- **`--emit-prompt <paramset>` / `--verify-response <file>`** — verification for
  implementations that cannot be `dlopen`ed: HSMs, sealed vendor binaries,
  builds with the transform inlined. `--emit-prompt` writes the ACVP questions
  for a parameter set from the pinned bundle, with no answers in the file;
  `--verify-response` checks each answer byte-exact against the pinned values.
  All 18 parameter sets across ML-KEM, ML-DSA and SLH-DSA. Raw ACVP response
  documents are accepted alongside pq-verify's own schema.
  - A question is only asked if the bundle holds an answer for it, so no
    response can be scored against a blank.
  - Unanswered questions are counted. A response covering 3 of 205 reports
    `3 of 205 asked` and `INCOMPLETE`, never `3/3 PASS`. Groups nobody answered
    print `NOT RUN`, not `FAIL`.
- **`artifact` on every report** — `sha256 <hash>` where a file was loaded,
  `none — <reason>` where none was. Binding is recorded independently of the
  verdict: a library exposing no derandomised entry points reports its hash
  (the file was read) with status `CANNOT VERIFY` (no vector was driven through
  it). In SARIF the hash lands in `runs[].artifacts[].hashes."sha-256"`.
- **`PQV000`** (warning, an absent check) as distinct from **`PQV006`** (error,
  an answer that is genuinely wrong).
- **CI** — the full suite, the self-suite and all 855 ACVP vectors on Python
  3.9, 3.10, 3.11, 3.12 and 3.13, plus a job that installs the built wheel in a
  clean environment at the declared floor and checks the pinned vectors shipped
  inside it. The matrix covers the entire range `requires-python` declares.
- **A release workflow** (`.github/workflows/release.yml`) that re-runs the full
  matrix at the commit being released, builds at the declared floor, emits
  **SLSA build provenance** and an attested **SPDX SBOM**, creates the tag and
  release, and publishes to PyPI via Trusted Publishing — no API token stored
  anywhere. Provenance cannot be retrofitted, so artifacts built outside this
  workflow can never carry it. Guards refuse to release if `pyproject.toml`,
  `__version__` and the requested version disagree, if the tag already exists,
  or if `CHANGELOG.md` has no section for the version.
- **SECURITY.md**, including the trust boundary that was never written down:
  auditing an untrusted library executes it, by design.
- Guards that hold metadata and code together: every module must parse at the
  declared floor, the floor may not be widened below what is exercised, and no
  backslash may appear inside an f-string expression.

### Compatibility

`to_json()`'s `artifact` argument is optional and output without it is
byte-identical to 2.6.7, so existing consumers of `--audit-so` JSON are
unaffected.

## [2.6.7] — 2026-08-16

Earlier releases are described at
<https://github.com/bigDSanalyst/pq-verify/releases>.
