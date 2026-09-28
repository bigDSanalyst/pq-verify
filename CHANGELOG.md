# Changelog

All notable changes to pq-verify. This project follows [semantic
versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
