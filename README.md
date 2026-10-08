# pq-verify v2.11.0 — PQC Implementation Verification

[![PyPI](https://img.shields.io/pypi/v/pq-verify.svg)](https://pypi.org/project/pq-verify/)
![license](https://img.shields.io/badge/license-MIT-green)
[![tests](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml/badge.svg)](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml)
![self-suite](https://img.shields.io/badge/self--suite-160%20checks-brightgreen)
![ACVP-KEM](https://img.shields.io/badge/ML--KEM%20ACVP-240%2F240-brightgreen)
![ACVP-DSA](https://img.shields.io/badge/ML--DSA%20ACVP-615%2F615-brightgreen)
![ACVP-SLH](https://img.shields.io/badge/SLH--DSA%20ACVP-1248%2F1248-brightgreen)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23092768.svg)](https://doi.org/10.5281/zenodo.23092768)

**Independent verification for ML-KEM (Kyber), ML-DSA (Dilithium), SLH-DSA (SPHINCS+), LMS/HSS and XMSS/XMSS^MT implementations.**

You deploy post-quantum cryptography. pq-verify checks that **your** implementation computes the standard correctly, three ways:

- **A library you can load** (`--audit-kem`, `--audit-dsa`, `--audit-hbs`, `--audit-so`): pq-verify drives the vendor's own entry points with every NIST ACVP vector, Wycheproof's edge cases and malformed inputs, in a child process with a timeout, and binds the verdict to the sha256 of every shared object that ran.
- **An implementation you cannot load** — an HSM, a sealed binary, a remote service (`--emit-prompt SET --fresh-key K`): fresh ACVP questions derived from a seed only the auditor holds, in NIST's own format. Their answers exist nowhere until pq-verify computes them, so a correct response had to be computed, not copied.
- **pq-verify itself**: its reference chain passes all 1566 pinned NIST ACVP vectors (ML-KEM, ML-DSA, SLH-DSA, LMS), and the NTT layers carry Coq proofs for every input. This is what makes its verdicts on your code worth trusting; it is not a verdict on your code.

Results are evidence toward FIPS 140-3 / CMVP readiness and CNSA 2.0, not a certificate: only an accredited lab issues those.

It does not compute PQC. It verifies the implementations that do: liboqs, BoringSSL, OpenSSL+OQS, HSM firmware, or your own code.

---

## What you get

Layers of an audit:

| Layer | Question answered | How |
|-------|-------------------|-----|
| **Correctness** | Does the NTT compute the FIPS definition? | Field-native verification + non-circular KAT |
| **NIST vectors** | Does it match NIST's published vectors? | ML-KEM 240/240 + ML-DSA 615/615 + SLH-DSA 624/624 + LMS 87/87 = 1566/1566 ACVP vectors (pinned); SLH-DSA sigGen 624/624 opt-in |
| **Security** | Are the parameters hard enough? | Bai-Galbraith primal-uSVP + hybrid attack estimator |
| **Composition** | Do the two halves of a hybrid agreement fit together? | RFC 10024 component order, offsets and lengths, per group |

Plus per-layer algebraic protection allocation: which NTT layers are worth
masking, computed from the transform's structure. That is a design input, not
a measurement — see [Scope](#scope).

Every result is **reproducible** — deterministic output, SHA-256 fingerprint, re-runnable by your own auditors.

---

## Proven

- **160/160** self-test across 6 field-native engines, of which **54 verify
  PQC directly**; the others check the harness itself or are classical and
  research engines, never counted as PQC evidence
  ([how the checks are tracked](ARCHITECTURE.md#engines-and-where-they-are-heading)).
  A check whose optional dependency is missing reports `⊘ SKIPPED`, never a
  pass and never a failure
- **NIST ACVP**, every vector passing: ML-KEM 240/240, ML-DSA 615/615,
  SLH-DSA 1248/1248 across all 12 parameter sets (sigGen opt-in,
  `--slhdsa-siggen`), LMS 87/87
- **LMS/HSS and XMSS/XMSS^MT** (SP 800-208, CNSA 2.0's firmware-signing
  schemes) against every other pinned source, `--lms-xmss`
- **Proofs for every input** (`pq-verify --proofs`, Coq) of the FIPS 203 and
  FIPS 204 NTTs and their modular reductions

All of it on commodity hardware (Google Colab CPU); each item in full, with
the native full-KEM, non-circular KAT and lattice-estimator results, is in
[ARCHITECTURE.md](ARCHITECTURE.md#proven-in-detail).

---

## Quick start

```bash
pip install "pq-verify[full]"
pq-verify --acvp-all            # 1566/1566, offline, no configuration, ~1 min
pq-verify --slhdsa-siggen      # + SLH-DSA sigGen, 624 signatures, ~30 min
pq-verify --fndsa              # FN-DSA verification, FIPS 206 DRAFT track, ~1 s
```

That is the whole installation. It is a command-line tool: Python 3.9+, `gcc`,
and nothing else. No notebook, no network, no service. The NIST vectors ship
inside the package, so air-gapped environments work out of the box.

Edge cases, offline: C2SP's [Wycheproof](https://github.com/C2SP/wycheproof)
and [CCTV](https://github.com/C2SP/CCTV) vectors (`strcmp` traps, unlucky
sampling, every out-of-range ek coefficient, malformed ML-DSA hints) are pinned
to exact commits and run by `--audit-kem` and `--audit-dsa` against a vendor
library, and by
`pq-verify --edge-cases` against pq-verify's own references. The latter
currently reports one finding, a known defect in the pinned dilithium-py
1.4.0 (a repeated hint index is accepted; fixed upstream, not yet released).

To audit a compiled library:

```bash
pq-verify --audit-so build/libmlkem768.so PQCLEAN_MLKEM768_CLEAN_ntt
pq-verify --audit-kem build/libmlkem768.so ML-KEM-768     # the whole KEM
pq-verify --audit-dsa build/libmldsa65.so ML-DSA-65       # the whole signature scheme
pq-verify --audit-hbs build/libhashsigs.so                # LMS/XMSS, via a pqv_hbs adapter
```

**The minimal audit.** If you run one command against an ML-KEM library,
run this one: NIST, Wycheproof and CCTV vectors, the FIPS 203 input checks,
10 000 accumulated cases and the constant-time check, with a JSON report
bound to the library's SHA-256, and (the default) a nonzero exit on any
finding:

```bash
pq-verify --audit-kem build/libmlkem768.so ML-KEM-768 --constant-time --json report.json
```

For ML-DSA, the same with `--audit-dsa` (no `--constant-time` yet).

**liboqs.** A library can hold more than one implementation: liboqs exports
its public `OQS_*` API and, beside it, every backend it dispatches to
(mlkem-native's and mldsa-native's portable C and x86-64 code). pq-verify
refuses to guess between them, lists them, and audits the one you name:

```bash
pq-verify --audit-kem   liboqs.so ML-KEM-768 --symbol-prefix OQS_KEM_ml_kem_768_ --constant-time
pq-verify --audit-dsa   liboqs.so ML-DSA-65  --symbol-prefix OQS_SIG_ml_dsa_65_
pq-verify --audit-fndsa liboqs.so FN-DSA-512 --symbol-prefix OQS_SIG_falcon_512_   # draft track
```

The public API is what your application calls; a backend's prefix
(`PQCP_MLKEM_NATIVE_MLKEM768_C_`, for one) audits the code a CPU without
AVX2 runs. liboqs 0.16.0 passes all of it, per implementation, rebuilt and
re-audited in CI ([AUDITS.md](AUDITS.md)).

For an implementation that cannot be loaded — an HSM, a sealed vendor binary,
a build with the transform inlined — ask it the questions instead:

```bash
pq-verify --emit-prompt ML-DSA-65 --prompt-out prompt.json   # 205 questions, no answers
#   ... the implementer runs them, wherever it lives, and returns a response ...
pq-verify --verify-response response.json                    # byte-exact, per test case
```

**This route is weaker than `--audit-so`, and the report says so:** a passing
response shows the standard was computed correctly, not *which binary* computed
it, so the result carries `artifact: none` ([below](#what-a-result-is-bound-to)).
Use it when the alternative is no verification at all, not when you can point
at a file.

Nothing in production negotiates bare ML-KEM. To check the part ACVP cannot
see — how the two halves of a hybrid key agreement are put together:

```bash
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
#   ... fill in the wire bytes from one handshake ...
pq-verify --verify-hybrid hybrid.json                        # RFC 10024 composition
```

`DEMO.ipynb` runs the same thing in Colab if you prefer a notebook.

The Python API, and the other install routes, are in
[ARCHITECTURE.md](ARCHITECTURE.md#public-api).

---

## What a result is bound to

Every report states its binding as a field, not as prose:

| Path | `artifact` |
|------|-----------|
| `--audit-so`, `--audit-kem`, `--audit-dsa`, `--audit-hbs` | `sha256 <hash>` — that file performed the computation |
| `--verify-response` | `none — vendor-supplied response` |
| `--verify-hybrid` | `none — vendor-supplied transcript` |
| `--acvp`, `--acvp-all` | `none — reference-chain conformance, no vendor binary loaded` |

The binding is recorded independently of the verdict, because they are
different facts. A library that exposes no derandomised entry points is
`artifact: sha256 <hash>` (the file was read) with status `CANNOT VERIFY` (no
vector was ever driven through it). In SARIF the hash is emitted as the run's
`artifacts[].hashes.sha-256`, which is where a security platform already looks
for "this exact file was analysed".

**Isolation and what actually ran.** Each `--audit-*` runs in a child process
(`--audit-timeout`, default one hour). A library that crashes on a test vector
or hangs is reported — `CANNOT VERIFY`, with the signal or the limit — instead
of taking pq-verify and its report down with it, and the code under audit does
not share memory with the code that decides its verdict. The child records
every shared object the audit mapped (`artifact.loaded_objects`: path, inode,
sha256), so the binding covers the vendor library *and* what it pulled in — a
libcrypto, a dependency found through `LD_LIBRARY_PATH` — plus any
`LD_PRELOAD`/`LD_LIBRARY_PATH` in effect (`artifact.loader_environment`). If
the audited file changes during the run, the verdict is `CANNOT VERIFY`.

**Never ship a test build.** The randomness harness and the pqv_hbs adapters
make a library deterministic and stateless on purpose. `pq-verify
--check-no-harness lib.so` exits 1 if either is present; put it in the release
job of anything audited this way.

**Ask fresh questions.** NIST's published questions have published answers:
NIST ships `expectedResults.json` beside every prompt, and so does this
package. A response to them that matches shows only that the answers were
obtained.
For an audit through `--emit-prompt`, pose questions derived from a seed only
you hold:

```bash
pq-verify --emit-prompt ML-DSA-65 --fresh-key audit.key      # send the prompt, keep the key
pq-verify --verify-response response.json --fresh-key audit.key
```

How fresh questions are derived and checked, LMS key-reuse detection, the
`scope` field, and how incomplete or unanswerable runs are reported:
[ARCHITECTURE.md](ARCHITECTURE.md#what-a-result-is-bound-to-in-depth).

---

## Use it in CI

A few lines in any repository that builds a post-quantum library. Findings
appear as annotations on the pull request, and the build fails on any result
that did not verify — including one that could not run.

```yaml
- uses: bigDSanalyst/pq-verify@v2.11.0
  with:
    audit: dsa                       # kem | dsa | hbs | ntt
    library: build/libmldsa65.so
    param-set: ML-DSA-65
```

With no library at all, it runs the NIST ACVP suites against pq-verify's own
reference chain:

```yaml
- uses: bigDSanalyst/pq-verify@v2.11.0
```

| Input | Default | Purpose |
|---|---|---|
| `audit` | — | `kem`, `dsa`, `hbs` (pqv_hbs adapter) or `ntt` |
| `library` | — | the compiled `.so` to audit |
| `param-set` | — | with `kem`/`dsa`: e.g. `ML-KEM-768`, `ML-DSA-65` |
| `symbol` | — | with `ntt`: the exported NTT symbol (`nm -D lib.so \| grep -i ntt`) |
| `acvp` | `true` | run ACVP suites; `live` fetches NIST's current vectors |
| `hybrid-transcript` | — | transcript to check against RFC 10024 (see `--emit-hybrid-prompt`) |
| `fail-on-finding` | `true` | fail the step on any result that did not verify; `false` reports only |

Outputs: `verified` (true only if every task that ran verified), `findings`,
`sarif-file`. Every input reaches the shell through the environment, never by
template substitution, and every action the Action uses is pinned to a commit.
Pin the Action itself to a release tag: `@v1` is the first upload and is not
maintained.

**Exit status** of the CLI, since 2.10.0: `0` verified, `1` a task found
problems or could not verify, `2` bad input. Gating is the default;
`--no-fail` reports without gating. Before 2.10.0 every task exited 0 unless
`--fail-on-finding` was passed, which the Action did not pass for its ACVP
step. A complete workflow is in
[`example-workflow.yml`](example-workflow.yml).

---

## Machine-readable output

```bash
pq-verify --audit-so build/libmlkem768.so PQCLEAN_MLKEM768_CLEAN_ntt \
          --sarif results.sarif --json results.json --fail-on-finding
```

**SARIF 2.1.0** is ingested natively by GitHub Code Scanning, DefectDojo, Snyk
and AWS Security Hub, so findings land in the security tooling a team already
runs rather than in a terminal someone has to read.

| Rule | Meaning |
|---|---|
| `PQV001` | NTT output diverges from the FIPS reference |
| `PQV002` | Freivalds probabilistic check failed |
| `PQV003` | Root of unity has the wrong multiplicative order |
| `PQV004` | Non-circular known-answer test failed |
| `PQV005` | Boundary/edge-case vector failed |
| `PQV006` | Vendor answer differs from the pinned NIST value |
| `PQV007` | Hybrid key agreement does not compose the way RFC 10024 pins it |
| `PQV000` | The run could not verify this — not a pass and not a failure |

`--fail-on-finding` exits non-zero, so it can gate a merge.

---

## Independent audits

pq-verify has been run against eight upstream projects — all verify clean, with
negative controls that correctly fail. Exact commits, build commands and
per-check output are in [AUDITS.md](AUDITS.md).

| Implementation | What was audited | Result |
|---|---|---|
| liboqs 0.16.0, per implementation: its `OQS_*` API and each backend behind it | **full scheme** ML-KEM (+ constant time) and ML-DSA, + Wycheproof/CCTV; FN-DSA (draft track); 9 mutants, in liboqs's wrappers and in each backend | ML-KEM 4,569/4,569 per implementation; ML-DSA 1,068/1,068 through its public API, 1,512/1,512 through each backend; every mutant caught |
| liboqs (`mlkem-native` / `mldsa-native`) | NTT symbol, ML-KEM + ML-DSA | 3/3 each |
| PQClean | NTT symbol, ML-KEM + ML-DSA | 3/3 each |
| mlkem-native ML-KEM-512/768/1024 | **full scheme** + NIST's invalid keys + Wycheproof/CCTV edge cases | 80/80 each; edge cases 4,320/4,320 |
| PQClean ML-KEM-512/768/1024 | **full scheme** + NIST's invalid keys + Wycheproof/CCTV edge cases | every valid output byte-exact; accepts all 10 NIST and all 2,931 CCTV/Wycheproof invalid encapsulation keys |
| mldsa-native ML-DSA-44/65/87 | **full scheme**: keyGen, sigGen and sigVer over internal, pure, pre-hash and external μ, + Wycheproof; 3 mutants | 1,503/1,503; every mutant caught |
| pq-crystals dilithium ref ML-DSA-44/65/87 | **full scheme** (no external-μ API) + Wycheproof; 6 mutants | 1,335/1,335; every mutant caught |
| PQClean ML-DSA-44/65/87 | **full scheme** (pure ML-DSA only) + Wycheproof; 1 mutant | 1,065/1,065; the mutant caught |
| cisco/hash-sigs (LMS/HSS) | verify, keyGen, sigGen byte-exact, malformed signatures, **key state**; 5 mutants | 686/686; every mutant caught |
| XMSS/xmss-reference (XMSS, XMSS^MT) | verify, keyGen, sigGen byte-exact, malformed signatures, **key state**; 6 mutants | 579/584: every vector passes; **two key-state defects** — the last leaf returns success with an invalid signature, and XMSS^MT h=40 keys never refuse ([AUDITS.md](AUDITS.md)); every mutant caught |
| pq-crystals reference | NTT symbol, Kyber + Dilithium | 3/3 each |
| BoringSSL | in-tree NIST vectors (NTT not exported) | 50/50 byte-exact |

The **full scheme** rows drive the library's own code with every NIST ACVP
vector for the scheme and Wycheproof's edge cases: `--audit-kem` for ML-KEM,
`--audit-dsa` for ML-DSA. The NTT-level rows check the transform against an
independently computed FIPS reference.

Every pinned library also carries **mutants**, one planted bug each, which CI
requires the audit to fail; how `--audit-dsa` reaches each FIPS 204 interface,
and randomised APIs, is in [ARCHITECTURE.md](ARCHITECTURE.md#how---audit-dsa-reaches-each-interface).

---

## More audit modes

### Accumulated vectors: 10 000 random cases, one digest

Every `--audit-kem`, `--audit-dsa` and `--audit-harness` run also drives
10 000 seeded random cases through the library and compares a SHAKE-128
digest of every output with a pinned value -- the way Go and BoringSSL test
themselves. Fixed vectors cover the edge cases someone thought of; these
reach the ones nobody did (a planted bug that fires on 1 ciphertext in 8 192
passes every NIST, Wycheproof and CCTV vector and is caught here). Coverage is
probabilistic: bugs rarer than about 1 in 10 000 operations may not be hit.
ML-DSA digests are C2SP CCTV's; ML-KEM's are Go's, because CCTV's published
ML-KEM digests turn out to be the FIPS 203 draft
([details](pq_verify/accumulated.py)). `--accumulated 0` skips them.

### Any language: Crucible-protocol harnesses

**A harness result is not bound to a library.** pq-verify hashes the
harness executable, not the library behind it, so a harness audit says what
*something answering through that harness* computes. It is not
artifact-bound evidence about a specific binary, of the kind a CMVP-style
review needs; for that, load the library (`--audit-kem`, `--audit-dsa`).

`pq-verify --audit-harness './harness-go-stdlib' ML-KEM-768` audits an
implementation in any language through a harness speaking
[Crucible](https://github.com/symbolicsoft/crucible)'s JSON-line protocol,
with pq-verify's own vectors and verdicts — only the wire format is
Crucible's. Go's `crypto/mlkem` and Cloudflare CIRCL (ML-KEM and ML-DSA) are
VERIFIED through Crucible's unmodified harnesses, rebuilt and re-audited in CI.
A harness is untrusted: its message convention is settled against NIST, its
determinism is tested, and a crash is CANNOT VERIFY, never a refusal. The
library behind a harness is not hashed, and the report says so
([AUDITS.md](AUDITS.md#any-language-through-crucible-protocol-harnesses)).

### Draft track: FN-DSA (FIPS 206)

`pq-verify --fndsa` checks FN-DSA (Falcon) **verification** ahead of the final
FIPS 206. It is a separate task with its own report (`track: "draft"`,
`standard: "FIPS 206 (draft)"`): it is not one of the 160 self-suite checks,
not one of the 1566 ACVP vectors, and never part of a FIPS 203/204/205 verdict.

| Check | What |
|---|---|
| Vectors | Falcon-512 and Falcon-1024 outputs of PQClean's reference code (NIST KAT harness + PQClean's deterministic generator), each pinned to the sha256 PQClean publishes for it in the scheme's metadata; 30 signatures, NIST-API signed messages and detached |
| Rejections | for every detached signature, the inputs a verifier must refuse — altered message or nonce, a changed `s2` coefficient, the wrong header, `-0`, nonzero padding bits, trailing bytes, a public-key coefficient ≥ q — each required to fail **for the right reason** (an encoding error from the decoder, not a lucky norm check) |
| Arithmetic | the NTT mod q = 12289 for n = 512 and 1024 against the negacyclic definition, and every butterfly of every layer through the native Z_q engine, unchanged |

`pq-verify --audit-fndsa lib.so FN-DSA-512` audits a vendor's FN-DSA library
the same way, through its own entry points (the NIST API as PQClean exports
it, or liboqs's `OQS_SIG_falcon_*`): the pinned signatures verify, every
malformed input is refused, its keys are canonical and match their secret
keys, every secret key solves the NTRU equation `f·G − g·F = q` and meets
both Gram–Schmidt bounds (checked in exact integer and rational arithmetic),
and its signatures verify under pq-verify's verifier with no nonce reused.
PQClean's Falcon passes; eight planted bugs in its source each fail the audit
in CI ([AUDITS.md](AUDITS.md)).

What is checked is Falcon round 3, the scheme FIPS 206 standardises.
Verification is integer arithmetic that the final standard is not expected to
change; framing (headers, padding, how a context string is bound) may change,
and lives in one section of `pq_verify/fndsa.py`. Signing — floating-point FFT
and a Gaussian sampler, where Falcon implementations actually go wrong — is
not checked until the final standard's vectors exist.

---

## Hybrid key agreement (RFC 10024)

Nothing in production negotiates bare ML-KEM: post-quantum TLS runs a
**hybrid** group, and ACVP never sees how its two halves are concatenated.
RFC 10024 does not use one order:

| Group | Codepoint | Key share | Shared secret |
|---|---|---|---|
| `X25519MLKEM768` | `0x11EC` | ML-KEM ‖ ECDHE | ML-KEM ‖ ECDHE |
| `SecP256r1MLKEM768` | `0x11EB` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |
| `SecP384r1MLKEM1024` | `0x11ED` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |

The first row is reversed relative to its own name. The RFC says so itself,
and calls it historical. So an implementation can pass **every ACVP vector
byte-for-byte** and still be wrong, because ACVP never sees the concatenation.

`--verify-hybrid` checks one handshake's wire bytes: every length, the FIPS 203
§7.2 encapsulation-key check, the ECDHE point, the X25519 all-zero check and,
given ephemeral test keys, both halves of the shared secret recomputed. When a
check fails it tests the other order and names the root cause. Commands are in
the [Quick start](#quick-start); what is checked, and how, is in
[HYBRID.md](HYBRID.md).

---

## Scope

pq-verify verifies the **algebraic substance** of ML-KEM/ML-DSA (NTT, module-LWE relations, parameter security) natively in Z₃₃₂₉ / Z₈₃₈₀₄₁₇. The **non-algebraic layers** (SHAKE/SHA3 hashing, sampling, compression, the FO transform) are bit/byte operations verified by NIST ACVP end-to-end testing, not native field solving.

The algebraic core is proven natively where the proof is exact; the full implementation is proven byte-exact against NIST's own bytes. We make the claims we can prove.

### Side channels are not measured

pq-verify compares values. It never executes an implementation under
measurement, collects no traces, and observes no timing, power or
electromagnetic behaviour. **It cannot detect an implementation that computes
the correct answer and leaks the key while doing it.**

This is not hypothetical. KyberSlash and Clangover were byte-exact correct
against every vector and still recovered secret material through timing. A
tool that checked only values would have passed both.

**`--audit-kem ... --constant-time` closes part of that gap, and says exactly
which part.** It runs the vendor's own Encaps (m secret) and Decaps (the
secret key and z secret, on a valid and on a random ciphertext) under
Valgrind memcheck with the secret bytes marked, and fails on every branch and
every memory address that depends on them, naming the function -- the
technique mlkem-native and BoringSSL use on themselves. It catches the
Clangover class (a compiler-introduced branch on a secret bit) and
cache-timing table lookups; three such leaks planted in PQClean, each leaving
every output correct, are caught in CI. It does **not** see instruction
timing -- KyberSlash's secret division -- so the report lists the library's
division instructions for a reviewer instead; it cannot check key generation
(the public matrix seed is derived from the secret seed); and it measures
nothing physical. The report records exactly that scope, and without the flag
claims nothing ([the report fields](ARCHITECTURE.md#side-channel-report-fields)).
`--leakage` is not an exception: it is a design input computed from the NTT's
structure, not an observation of execution.

---

## Verifying a release

Releases are built by `.github/workflows/release.yml` on GitHub's runners, from
a reviewed commit, after the full suite and all 1566 NIST ACVP vectors pass on
Python 3.9 through 3.13. Each artifact carries **SLSA build provenance** and an
attested **SPDX SBOM**. Check them yourself, trusting nothing this repository
says:

```bash
gh attestation verify pq_verify-2.11.0-py3-none-any.whl --repo bigDSanalyst/pq-verify
```

That tells you which workflow built the file, from which commit, on whose
runners — not that we assert it, but that GitHub signed it. Provenance cannot
be added to an artifact after the fact, which is why a release built anywhere
else can never have it.

The SBOM is short: **pq-verify has no unconditional runtime dependencies.**
`kyber-py`, `dilithium-py`, `sympy` and `slh-dsa` are optional extras used to
cross-check against independent implementations; the package itself installs
with none of them.

---

## How it works

[ARCHITECTURE.md](ARCHITECTURE.md) holds what is not needed to run an audit:

- [Engines and where they are heading](ARCHITECTURE.md#engines-and-where-they-are-heading):
  the PQC, harness, classical and research tracks, and why only the first is
  PQC evidence
- [The six field-native engines](ARCHITECTURE.md#architecture--six-field-native-engines)
  and the [specification front-end](ARCHITECTURE.md#specification-front-end)
- [Deterministic by default](ARCHITECTURE.md#deterministic-by-default): the
  pinned NIST vectors and how they are re-pinned
- [The Python API](ARCHITECTURE.md#public-api)
- [What a result is bound to, in depth](ARCHITECTURE.md#what-a-result-is-bound-to-in-depth)
  and the [side-channel report fields](ARCHITECTURE.md#side-channel-report-fields)
- [What's in this package](ARCHITECTURE.md#whats-in-this-package)

Third-party audit results, build commands and every planted bug are in
[AUDITS.md](AUDITS.md); hybrid composition in [HYBRID.md](HYBRID.md).

---

## Requirements

**Minimum (core engines + ~149 self-tests):**
- Python 3.9+ — **every version of the declared range (3.9, 3.10, 3.11, 3.12,
  3.13) runs the full test suite and all 1566 ACVP vectors in CI.** The floor is
  3.9 rather than 3.8 because `pq-verify[full]` cannot resolve below it:
  `kyber-py` and `dilithium-py` both require `>=3.9`. `requires-python` and the
  code are held together mechanically — a module that stops parsing at the
  declared floor fails the suite, and widening the floor fails it too.
- gcc and g++ (the C/C++ engines compile at runtime); on macOS, Xcode's
  command-line tools (Apple clang) — every engine still builds with
  `-march=native`, falling back to `-mcpu=native`
- Linux (x86-64) or macOS (Apple silicon); both run the full suite in CI

**For the full 160/160 self-suite and the 1566/1566 ACVP claim:**
- `kyber-py` — **required** for `pqverify_acvp()` (the byte-exact NIST reference) and the FIPS 203 roundtrip tests
- `dilithium-py` — **required** for `pqverify_mldsa_acvp()` (the 615 ML-DSA vectors)
- `coq` — required for the Coq certificate verification tests
- `sympy` — required for the Engine-6 Conjecture 7 exact-rational test (without it that check reports as skipped, not failed)

```bash
apt-get install -y coq gcc g++
pip install "pq-verify[full]"   # kyber-py, dilithium-py, sympy, slh-dsa
```

**Optional (1 test each, everything works without them):**
- `cryptominisat` — the CMS5 speed-comparison benchmark
- `slh-dsa` — the SLH-DSA ACVP reference and live roundtrip (parameters still validate without it)
- network access — `pqverify_acvp()` fetches NIST vectors from GitHub live; for air-gapped use the pinned vectors are used by default, or pass `vector_dir=` pointing at your own local vector set

**Deliberately NOT required** (a deployment advantage):
- No numpy, scipy, or PyTorch — pure Python + ctypes + inline C
- No SageMath — the `pqverify_params` lattice estimator is self-contained (it reproduces the lattice-estimator's results without it)

---

## License

MIT. The verifier is open-source — builds trust, enables adoption. Commercial support, custom engine development, and PQC audit engagements available separately.

## Citing this software

Archived on Zenodo with a citable DOI:

> Maino, N. C. (2026). *pq-verify: Independent verification for ML-KEM / ML-DSA
> implementations* (v2.9.0). Zenodo. https://doi.org/10.5281/zenodo.23092768

```bibtex
@software{maino_pqverify_2026,
  author    = {Maino, Nicholas Clifford},
  title     = {pq-verify: Independent verification for ML-KEM / ML-DSA implementations},
  version   = {2.9.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23092768},
  url       = {https://doi.org/10.5281/zenodo.23092768}
}
```

The DOI above resolves to this specific release. The companion paper is
[10.5281/zenodo.19302050](https://doi.org/10.5281/zenodo.19302050).

`CITATION.cff` names the version deposited on Zenodo. When a release is newer
than the last deposit, the citation lags on purpose until a new one exists — a
DOI that does not resolve to the version printed beside it would be worse than
one a release behind. For the current version see
[Releases](https://github.com/bigDSanalyst/pq-verify/releases) or the PyPI
badge at the top.

## Contact

Nicholas Maino (iamweare) · maiknown@gmail.com · https://github.com/bigDSanalyst
Zenodo: https://doi.org/10.5281/zenodo.19302050