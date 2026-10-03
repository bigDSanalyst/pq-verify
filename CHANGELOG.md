# Changelog

All notable changes to pq-verify. This project follows [semantic
versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

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

- **`--acvp-all` and `pqverify_acvp_all()` include SLH-DSA keyGen and
  sigVer: 1479 vectors (240 + 615 + 624), up from 855.** The run takes about
  a minute. `pqverify_acvp_all(slhdsa=False)` gives the previous 855; the
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

- **The GitHub Action's `slhdsa` input did nothing.** It was declared but
  never read. SLH-DSA keyGen and sigVer now run with the ACVP suites, and
  `slhdsa: siggen` adds sigGen.
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
