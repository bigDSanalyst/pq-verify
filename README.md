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

## Proven (all tested on commodity hardware, Google Colab CPU)

- **160/160** self-test across 6 field-native engines, 6 phases, of which
  **54 verify PQC directly** (FIPS 203/204/205 NTTs, zetas, parameters,
  Freivalds, Coq) and 13 check the harness itself; the other 93 are classical
  and research engines being realigned toward post-quantum work (see
  [Engines and where they are heading](#engines-and-where-they-are-heading)) —
  in an environment with every optional dependency present. Where one is missing the
  dependent check reports as `⊘ SKIPPED`, is excluded from the ratio, and names
  what it needed. It is never counted as a pass, and never as a failure either
- **240/240** NIST ACVP ML-KEM vectors — keyGen + encaps + decaps byte-exact, KeyCheck bool-exact
- **1248/1248** NIST ACVP SLH-DSA vectors, all 12 parameter sets — keyGen 120 byte-exact,
  sigVer 504 verdict-exact (valid, modified message / R / FORS / hypertree, one byte
  short or long), sigGen 624 byte-exact, deterministic and with NIST's randomness;
  internal, pure and pre-hash interfaces over twelve hash functions. sigGen takes
  about 30 min, so it is `--slhdsa-siggen` and a weekly CI job
- **LMS/HSS and XMSS/XMSS^MT** (RFC 8554, RFC 8391, SP 800-208; CNSA 2.0's
  firmware-signing schemes), pq-verify's own implementation of all four
  SP 800-208 hash families: NIST's 87 LMS ACVP vectors in `--acvp-all`, and
  `--lms-xmss` over every other pinned source: ACVP-format LMS and XMSS
  vectors for every family, liboqs's XMSS^MT and HSS KATs, and RFC 8554's own
  test cases. Every signature is verified; key generation and signing are
  byte-exact up to a hash budget (`--lms-xmss-full`: every height-10 tree), and
  what the budget skips is reported as not run, never as passed
- **Native full-KEM** verified at ML-KEM-1024 (Level 5): recovery 20/20, negative control caught
- **Non-circular KAT** 100/100 against the independent FIPS reference
- Calibrated lattice estimator: reproduces lattice-estimator exactly (Kyber-512 β=406/118.6 bits)
- **Proofs for every input** (`pq-verify --proofs`, Coq): the FIPS 203 and
  FIPS 204 forward NTT equal the CRT map they are defined to compute, for
  every 256-coefficient input; `montgomery_reduce`, `barrett_reduce` and
  `reduce32` are congruent and within bound for every input in range. Each
  theorem must print `Closed under the global context` (no axioms, no
  `Admitted`), not just exit 0. Per-run certificates use the same, proved,
  NTT definition

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

For an implementation that cannot be loaded — an HSM, a sealed vendor binary,
a build with the transform inlined — ask it the questions instead:

```bash
pq-verify --emit-prompt ML-DSA-65 --prompt-out prompt.json   # 205 questions, no answers
#   ... the implementer runs them, wherever it lives, and returns a response ...
pq-verify --verify-response response.json                    # byte-exact, per test case
```

**This route is weaker than `--audit-so`, and the report says so.** A passing
response shows that whoever produced it computes the standard correctly for
those inputs. It does not show *which binary did it* — there is no signature
over the computation and no binding to code. So the result carries
`artifact: none — vendor-supplied response` where a loaded library would carry
its SHA-256. Use it when the alternative is no verification at all, not when
you can point at a file. See [What a result is bound
to](#what-a-result-is-bound-to).

Nothing in production negotiates bare ML-KEM. To check the part ACVP cannot
see — how the two halves of a hybrid key agreement are put together:

```bash
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
#   ... fill in the wire bytes from one handshake ...
pq-verify --verify-hybrid hybrid.json                        # RFC 10024 composition
```

`DEMO.ipynb` runs the same thing in Colab if you prefer a notebook.

<details>
<summary>Other install routes</summary>

```python
exec(open('pq_verify/core.py').read())   # 160-check self-suite + loads the API

pqverify_acvp()                    # full NIST ACVP, all parameter sets
pqverify_params('ML-KEM-1024')     # parameter security check
pqverify_kem(k=4)                  # native full-KEM at Level 5
```

To audit your own compiled library:

```python
ntt = pqverify_load_so('/path/to/your_library.so', 'ntt_symbol')
pqverify_scan(ntt)                 # full audit + KAT + leakage
```

See `vendor_audit_template.py` for the complete "give us your .so → get a JSON report" workflow.

</details>

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

`--audit-dsa` sends each FIPS 204 interface through the library's own entry
point for it, and reports any interface the API lacks as not applicable, never
as a pass. Linked with pq-verify's randomness harness
(`pq_verify/harness/pqv_randombytes.c`), the randomised `keypair()` and
`signature()` users actually call are audited byte-exactly too. Each pinned
library also carries **mutants**, one planted bug each, which CI requires the
audit to fail. Two of them, a verifier that accepts a repeated hint index and
one that skips the ‖z‖ bound, pass every NIST vector; only the Wycheproof
stage catches them.

Where no entry point can be loaded at all — an HSM, a sealed binary — `--emit-prompt` / `--verify-response` asks the questions instead and
checks the answers byte-exact. That result is not artifact-bound, and the
report says so rather than implying otherwise; see
[What a result is bound to](#what-a-result-is-bound-to).

---

## Engines and where they are heading

Every self-suite check is labelled with a track, printed per track in the
summary and recorded in the JSON report (`track`, `realigns_to`, `tracks`).
Only the PQC track verifies what a FIPS 203/204/205 implementation computes;
the others are exact checks of other things, and none of them is counted as
PQC evidence.

| Track | Checks | What it verifies today | Being realigned toward |
|---|---|---|---|
| **PQC** | 54 | ML-KEM/ML-DSA NTTs in their native fields, FIPS 203/204 zetas, FIPS 203/204/205 parameters, Freivalds, keygen/roundtrip, Coq NTT certificate | FN-DSA (draft FIPS 206): the Z_q engine now checks its NTT mod 12289 under `--fndsa` ([draft track](#draft-track-fn-dsa-fips-206)) |
| Harness | 13 | solver soundness (UNSAT), reproducibility hash, Coq daemon, adversarial and malformed inputs | — |
| Classical | 45 | GF(2) solving and null spaces, AES S-box affine structure, elliptic-curve point counts (singular, anomalous and supersingular curves), SafeCurves-style screening | **HQC** (arithmetic over GF(2)[x]/(xⁿ−1)), **Classic McEliece** (systematic-form public keys over GF(2), GF(2ᵐ) fields). The curve checks have no PQC target: hybrid KEMs are checked by `--verify-hybrid`, which does not use them |
| Research | 48 | Engine 6 (Gauss–Manin connections, Paper 7), CFL/DQBF pipeline, conformity gradient | correctness checks for NTT/FFT side-channel countermeasures; standards constraints as SAT/QBF obligations. Engine 6 has no PQC target yet |

"Being realigned toward" is a direction, not a capability: until an engine
checks a post-quantum implementation, it is reported under its own track.

The research track holds two different kinds of work, and neither is
evidence about an implementation. **Infrastructure:** the CFL/DQBF pipeline,
which turns standards constraints into SAT/QBF obligations and could carry
PQC checks once they are written as such. **Analysis:** the conformity
gradient D(t) and Engine 6, mathematics over ℂ with no post-quantum target
yet.

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

## Architecture — six field-native engines

pq-verify does not encode cryptographic arithmetic as generic boolean SAT and
hand it to a solver. It verifies each operation **in the field the algorithm
actually works in**. Kyber's NTT is checked in Z₃₃₂₉ directly; Dilithium's in
Z₈₃₈₀₄₁₇. That is what "field-native" means, and it is why the checks are exact
rather than an encoding of an encoding.

Six C/C++ engines are compiled at runtime from sources embedded in `core.py` —
no build step, no external `.c` files, no toolchain beyond `gcc`/`g++`.

| Engine | Field | What it verifies |
|---|---|---|
| **GF(2)** | F₂ | AES S-box affine layer, bit-packed Gaussian elimination, **null-space basis** computation (256 vars / 200 eqs → ~56 free; particular solution and basis vectors verified against the system) |
| **Z₃₃₂₉** | ML-KEM | Kyber NTT butterflies, Montgomery arithmetic, Freivalds verification |
| **Z₈₃₈₀₄₁₇** | ML-DSA | Dilithium NTT butterflies — the *complete* 8-layer transform, 32-bit Freivalds |
| **Cubic + ECC** | — | B(a,b) decomposition, elliptic curve point validation, BSGS |
| **Conformity** | — | D(t) stability on curve families — *research framework, not a security check* |
| **Period / Gauss-Manin** | — | Amari-Schwarzian, ranks 2/4/4/8 — *research framework, not a security check* |

The two schemes differ structurally and the tool distinguishes them: ML-KEM's ζ
has order n, so 2n does not divide q−1 and the transform is **incomplete** —
seven layers, last one deleted. ML-DSA's ζ has order 2n, so the transform is
**complete** — eight layers. A verifier that assumes one shape silently
mis-verifies the other.

### Specification front-end

Alongside the engines, a pipeline turns a formal specification into field
constraints:

```
CFL spec → lexer → parser → FOL → QBF → field router → engine dispatch
XML module → DQBF (Henkin dependency sets) → Tseitin linearization → GF(2)
```

The router picks the correct engine from the constraint structure — XOR-dense
systems route to GF(2), ring arithmetic to the Z_q engines. Both paths are
exercised in the self-suite (CFL 6/6, DQBF 7/7).

---

## Public API

| Function | Purpose |
|----------|---------|
| `main()` | 160-check self-suite |
| `pqverify_acvp()` | Full NIST ACVP end-to-end ML-KEM (240/240, all groups) |
| `pqverify_mldsa_acvp()` | Full NIST ACVP end-to-end ML-DSA (615/615, FIPS 204) |
| `pqverify_slhdsa_acvp()` | NIST ACVP SLH-DSA (FIPS 205, all 12 parameter sets): keyGen 120 + sigVer 504; `siggen=True` adds 624 byte-exact signatures |
| `pqverify_acvp_all()` | ML-KEM + ML-DSA + SLH-DSA keyGen/sigVer + LMS (1566/1566) offline; `slhdsa_siggen=True` adds sigGen → 2190/2190; `slhdsa=False, lms=False` → 855/855 |
| `pqverify_lms_acvp()` | NIST ACVP LMS (87/87, SP 800-208) |
| `pqverify_hbs(full=False)` | LMS/HSS + XMSS/XMSS^MT against every pinned non-NIST source, every SP 800-208 family |
| `pqverify_params(set)` | Parameter security: primal-uSVP + sparse hybrid |
| `pqverify_kem(k=4)` | Native algebraic full-KEM verification |
| `pqverify_kat(ntt, k=4)` | Non-circular KAT vs FIPS definition |
| `pqverify_load_so(path, sym)` | Load NTT from a compiled .so |
| `pqverify_scan(target)` | Auto-discover + audit NTT functions |
| `pqverify_audit_kem(path, set)` | A vendor's own ML-KEM keygen/encaps/decaps vs NIST + Wycheproof/CCTV |
| `pqverify_audit_dsa(path, set)` | A vendor's own ML-DSA keygen/sign/verify vs NIST + Wycheproof, every FIPS 204 interface |
| `pqverify_audit_hbs(path)` | A vendor's own LMS/HSS or XMSS library (pqv_hbs adapter) vs every pinned vector + malformed signatures, and its own key-state handling: no leaf issued twice, state durable before release, refusal once exhausted |
| `pqverify_leakage()` | Per-layer protection-allocation table |
| `emit_prompt(set)` | Write the ACVP question set for a parameter set (no answers) |
| `verify_response(file)` | Check a response byte-exact against the pinned answers |
| `available_parameter_sets()` | Parameter sets the pinned bundle can pose questions for |
| `emit_hybrid_prompt(group)` | Write what to supply for a hybrid group (RFC 10024) |
| `verify_hybrid(file)` | Check a hybrid transcript's composition against RFC 10024 |
| `HYBRID_GROUPS` | The pinned registry: codepoints, component order, lengths |

---

## Deterministic by default

pq-verify ships with a **frozen, versioned snapshot of NIST's ACVP vectors** bundled
inside the package (gzipped: ~8 MB, plus a ~39 MB archive of SLH-DSA signature
vectors that is opened only when an SLH-DSA suite runs). By default it verifies
against those — so:

- **the same input gives the same result, every run, forever**
- **it works with no network** — air-gapped, offline, no GitHub reachability needed
- **NIST editing their published files cannot change or break your result**

That last point is not hypothetical: NIST periodically regenerates these vectors and
has changed the ML-KEM `encapDecap` schema (the `keyFormat` seed/expanded split) more
than once. A tool that fetches live gives different answers on different days. This one
does not.

```python
pqverify_acvp_all()              # pinned bundle, offline, deterministic  → 1566/1566
pqverify_acvp_all(live=True)     # opt in: fetch NIST's current vectors instead
pqverify_acvp_all(vector_dir=d)  # or point at your own local vector set
```

Vector provenance and per-file sha256 are recorded in `pq_verify/vectors/MANIFEST.json`.
A scheduled GitHub Action watches upstream and opens an issue when NIST changes
something, so re-pinning is a deliberate, reviewed act rather than a live dependency.

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

The audit assumes the library is not adversarial toward the audit itself: a
binary built to recognise pq-verify could behave differently under test. That
is the limit of any black-box test; the prompt/response path and a build you
control are the answers to it.

**Scope is part of the verdict.** `--audit-dsa` and `--audit-hbs` reports carry
`scope`: how many cases ran, how many were not applicable (the library exports
no entry point, or its adapter declares a parameter set unsupported) and how
many were not run (sampled or over budget). `VERIFIED` with
`scope.complete: false` means every check that ran passed, not that every
check ran; `--require-full-coverage` fails it.

**Never ship a test build.** The randomness harness and the pqv_hbs adapters
make a library deterministic and stateless on purpose. `pq-verify
--check-no-harness lib.so` exits 1 if either is present; put it in the release
job of anything audited this way.

NIST's published questions have published answers: NIST ships
`expectedResults.json` beside every prompt, and so does this package. A response
to them that matches shows only that the answers were obtained. For an audit,
pose **fresh** questions:

```bash
pq-verify --emit-prompt ML-DSA-65 --fresh-key audit.key      # send the prompt, keep the key
pq-verify --verify-response response.json --fresh-key audit.key
```

The seed (256 bits from the OS) goes only to `audit.key`, created `0600` and
never overwritten. Every input is derived from it with SHAKE256; the prompt is
in NIST's ACVP layout — same suites, groups and field names, every interface
(pure, pre-hash, external mu, internal; deterministic and hedged), boundary
context lengths, implicit-rejection ciphertexts, invalid keys and invalid
signatures — so an ACVP harness answers it unchanged. Verification re-derives
the questions, confirms their `promptId` matches the one issued, and computes
every expected answer at that moment. ML-KEM, ML-DSA, all twelve SLH-DSA
sets and every SP 800-208 LMS pairing (`LMS_SHA256_M32_H10/LMOTS_SHA256_N32_W4`
and so on) are supported.

LMS is where black-box testing matters most: firmware-signing keys live in
HSMs that will not export a key or sign at a chosen leaf. Its sigGen questions
are answered the way ACVP asks — the responder signs with **its own key** and
reports the public key — so each signature is verified under that key rather
than compared, and **no leaf may sign twice under one key anywhere in the
response**: a one-time key used twice is reported, from outside the box. keyGen
and sigVer questions are posed where pq-verify can build the tree (up to about
3 million hash calls); larger sets, such as height 20, get sigGen alone.

A passing fresh response proves the responder computed the standard correctly
on inputs nobody had seen. Neither kind proves **which binary did it**: there
is no signature over the computation and no binding to code — the responder
could run a reference implementation instead of the product. So the report says
`artifact: none` rather than implying otherwise, and a reader can tell the two
kinds of result apart without reading a footnote.

The same discipline applies to coverage. A response answering 3 of 205
questions reports `3 of 205 asked`, groups nobody answered print `NOT RUN`
rather than `FAIL`, and the verdict is `INCOMPLETE` — never `3/3 PASS`.

And to pq-verify's own suite, which is where it was missing longest. A check
that could not run — `coqc` absent, `sympy` absent — prints `⊘`, stays out of
the ratio, and registers the dependency it needed, so `integrity_report()` can
never announce full coverage over a check that did not happen.
Answering a different question set (`promptId` mismatch) is `CANNOT VERIFY`,
which is reported separately from verified-and-failed: `PQV000` for an absent
check, `PQV006` for an answer that is genuinely wrong.

`--fail-on-finding` exits non-zero for all of it — findings, `INCOMPLETE`,
`CANNOT VERIFY`, a KEM audit that could not run, and an ACVP suite short of
its full count. A run that did not verify does not pass a CI gate.

---

## Hybrid key agreement (RFC 10024)

Nothing in production negotiates bare ML-KEM. Every deployment that has turned
post-quantum TLS on runs a **hybrid** group, and `X25519MLKEM768` is what
Chrome, Firefox, OpenSSL, BoringSSL and the large CDNs agree on today.

The ML-KEM half of that handshake is covered by `--acvp` and `--audit-kem`.
The **composition** is not — and the composition is where the bugs are,
because RFC 10024 does not use one order:

| Group | Codepoint | Key share | Shared secret |
|---|---|---|---|
| `X25519MLKEM768` | `0x11EC` | ML-KEM ‖ ECDHE | ML-KEM ‖ ECDHE |
| `SecP256r1MLKEM768` | `0x11EB` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |
| `SecP384r1MLKEM1024` | `0x11ED` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |

The first row is reversed relative to its own name. The RFC says so itself,
and calls it historical. So an implementation can pass **every ACVP vector
byte-for-byte** and still be wrong, because ACVP never sees the concatenation.

The failure is silent in the worst way: two peers that make the same mistake
interoperate happily with each other and with nobody else, and the peer that
got it right sees only a `decrypt_error` with no indication of which side is
at fault.

```bash
pq-verify --emit-hybrid-prompt list          # the groups this build knows
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
pq-verify --verify-hybrid hybrid.json
```

What gets checked, from one handshake's wire bytes:

- every length against the value RFC 10024 pins for that group
- the encapsulation key against the FIPS 203 §7.2 check the RFC makes a
  **MUST** for the server — validated here against NIST's own 20 labelled
  `encapsulationKeyCheck` cases, so it agrees with NIST rather than with itself
- the ECDHE share as an uncompressed point on the curve (RFC 9846 §4.3.8.2)
- the X25519 all-zero shared-secret check, which the RFC also makes a MUST
- when you supply an ephemeral private scalar, the ECDHE shared secret
  **recomputed** and compared byte-for-byte at the offset the group pins
- and, when you supply the client's ephemeral ML-KEM decapsulation key, the
  ciphertext in the server share **decapsulated** and the result compared
  byte-for-byte with the ML-KEM half of the combined secret. Without the key,
  nothing ties the ciphertext to the secret, so that check is `NOT CHECKED`
  and the result is `PARTIAL`, never `VERIFIED`

When a check fails, pq-verify tests the other order explicitly:

```
**FAIL**  clientShare ML-KEM-768 encapsulation key (FIPS 203 §7.2)
          there is no valid encapsulation key at offset 0, but there IS one
          at the offset the other order gives — the components are
          concatenated the wrong way round. RFC 10024 pins
          kem_ek ‖ ecdh_pub for X25519MLKEM768
```

That is a root cause, not a mismatch. The discriminator is sound rather than
heuristic: random bytes pass the FIPS 203 §7.2 check with probability below
2⁻¹⁴⁰, so "a valid encapsulation key is sitting at the other offset" is not a
coincidence.

Private keys are optional and should be ephemeral test keys, never production
ones. A field you cannot supply is reported as `NOT CHECKED` and stays out of the ratio; a check that does not exist for a
group — X25519 has no structural share check, and inventing one would report a
check that did not happen — is reported as `N/A` and does not hold the verdict
at `PARTIAL`.

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
nothing physical. The report records exactly that:

```json
"side_channel": {
  "measured": false,
  "constant_time_checked": {
    "operations": ["decaps", "encaps"],
    "scope": "secret-dependent branches and memory addresses in this binary, by Valgrind memcheck taint; not instruction timing (division), power, EM or microarchitecture, and not key generation",
    "leak_free": true
  }
}
```

Without the flag, nothing is claimed:


```json
"side_channel": {
  "measured": false,
  "summary": "not measured — execution time, power and electromagnetic behaviour were not observed"
}
```

`--leakage` is not an exception to this. It computes, from the NTT's algebraic
structure, how much of the secret each butterfly layer would determine *if*
that layer's intermediates were exposed — a design input for allocating
masking. It does not observe execution and makes no claim that this
implementation leaks those values. Establishing that requires leakage
assessment against the deployed binary on the deployed hardware.

---

## What's in this package

```
pq_verify/
  __init__.py              Public API
  core.py                  The stack (6 field-native engines)
  cli.py                   Command-line interface
  response.py              Prompt/response verification for un-loadable builds
  hybrid.py                RFC 10024 hybrid key-agreement composition
  fndsa.py                 FN-DSA (Falcon) verification, FIPS 206 draft track
  report.py                Native JSON + SARIF 2.1.0 output
tests/test_pqverify.py     pytest suite (run on 3.9-3.13 in CI)
pyproject.toml             Build config + console-script entry point
dist/
  pq_verify-2.11.0-py3-none-any.whl    Installable wheel
  pq_verify-2.11.0.tar.gz              Source distribution
DEMO.ipynb                 One-click Colab demo → 1566/1566
vendor_audit_template.py   Drop-in .so audit → JSON report
sample_report.json         Example output (what your auditors receive)
README.md / QUICKSTART.md / LICENSE / CITATION.cff
```

Install: `pip install "pq-verify[full]"` — or download the wheel from
[Releases](https://github.com/bigDSanalyst/pq-verify/releases).

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
