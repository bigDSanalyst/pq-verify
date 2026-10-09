# How pq-verify works

The [README](README.md) covers using pq-verify. This is the rest: how it
checks, what it pins, and what a result does and does not show. Nothing here
is needed to run an audit.

- [Proven in detail](#proven-in-detail)
- [Engines and where they are heading](#engines-and-where-they-are-heading)
- [Architecture — six field-native engines](#architecture--six-field-native-engines)
- [Deterministic by default](#deterministic-by-default)
- [Public API](#public-api)
- [What a result is bound to, in depth](#what-a-result-is-bound-to-in-depth)
- [Side-channel report fields](#side-channel-report-fields)
- [What's in this package](#whats-in-this-package)

---

## Proven in detail

All tested on commodity hardware (Google Colab CPU).

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
- Calibrated lattice estimator: ML-KEM's three sets report the lattice-estimator's
  primal-uSVP values, pinned; for custom parameters a simplified formula matches it
  at its calibration point (Kyber-512 β=406, 118.6 bits) and is close, not exact,
  elsewhere ([LIMITS.md](LIMITS.md#parameter-security))
- **Proofs for every input** (`pq-verify --proofs`, Coq): the FIPS 203 and
  FIPS 204 forward NTT equal the CRT map they are defined to compute, for
  every 256-coefficient input; `montgomery_reduce`, `barrett_reduce` and
  `reduce32` are congruent and within bound for every input in range. Each
  theorem must print `Closed under the global context` (no axioms, no
  `Admitted`), not just exit 0. Per-run certificates use the same, proved,
  NTT definition

---

## Engines and where they are heading

Every self-suite check is labelled with a track, printed per track in the
summary and recorded in the JSON report (`track`, `realigns_to`, `tracks`).
Only the PQC track verifies what a FIPS 203/204/205 implementation computes;
the others are exact checks of other things, and none of them is counted as
PQC evidence.

| Track | Checks | What it verifies today | Being realigned toward |
|---|---|---|---|
| **PQC** | 54 | ML-KEM/ML-DSA NTTs in their native fields, FIPS 203/204 zetas, FIPS 203/204/205 parameters, Freivalds, keygen/roundtrip, Coq NTT certificate | FN-DSA (draft FIPS 206): the Z_q engine now checks its NTT mod 12289 under `--fndsa` ([draft track](README.md#draft-track-fn-dsa-fips-206)) |
| Harness | 13 | solver soundness (UNSAT), reproducibility hash, Coq daemon, adversarial and malformed inputs | — |
| Classical | 45 | GF(2) solving and null spaces, AES S-box affine structure, elliptic-curve point counts (singular, anomalous and supersingular curves), SafeCurves-style screening | **HQC** (arithmetic over GF(2)[x]/(xⁿ−1)), **Classic McEliece** (systematic-form public keys over GF(2), GF(2ᵐ) fields). Classic McEliece is audited today (`--audit-mceliece`) in exact Python integers: the GF(2) engine holds at most 2048 variables and returns solutions, not the reduced matrix a public key is, so it is not used there yet. HQC's code layer is audited (`--audit-hqc`) by `pq_verify/hqc.py`, also in exact Python: GF(2⁸) tables, Reed–Solomon over it, and a Walsh–Hadamard maximum-likelihood decoder for RM(1,7). The curve checks have no PQC target: hybrid KEMs are checked by `--verify-hybrid`, which does not use them |
| Research | 48 | Engine 6 (Gauss–Manin connections, Paper 7), CFL/DQBF pipeline, conformity gradient | correctness checks for NTT/FFT side-channel countermeasures; standards constraints as SAT/QBF obligations. Engine 6 has no PQC target yet |

"Being realigned toward" is a direction, not a capability: until an engine
checks a post-quantum implementation, it is reported under its own track.

The research track holds two different kinds of work, and neither is
evidence about an implementation. **Infrastructure:** the CFL/DQBF pipeline,
which turns standards constraints into SAT/QBF obligations and could carry
PQC checks once they are written as such. **Analysis:** the conformity
gradient D(t) and Engine 6, mathematics over ℂ with no post-quantum target
yet.

---

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

### Other install routes

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

### How `--audit-dsa` reaches each interface

`--audit-dsa` sends each FIPS 204 interface through the library's own entry
point for it, and reports any interface the API lacks as not applicable, never
as a pass. Linked with pq-verify's randomness harness
(`pq_verify/harness/pqv_randombytes.c`), the randomised `keypair()` and
`signature()` users actually call are audited byte-exactly too; liboqs needs
no special build, because its own hook (`OQS_randombytes_custom_algorithm`)
supplies NIST's seeds, and pq-verify hands the hook back when it is done. Each pinned
library also carries **mutants**, one planted bug each, which CI requires the
audit to fail. Two of them, a verifier that accepts a repeated hint index and
one that skips the ‖z‖ bound, pass every NIST vector; only the Wycheproof
stage catches them.

---

## What a result is bound to, in depth

The binding table and the isolation guarantees are in the
[README](README.md#what-a-result-is-bound-to). The rest:

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

**Fresh questions.** NIST's published questions have published answers, so
for an audit through the prompt/response route pose fresh ones, whose inputs
exist nowhere until pq-verify derives them:

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

## Side-channel report fields

`--audit-kem ... --constant-time` (see the
[README](README.md#side-channels-are-not-measured) for what it checks and what
it cannot see) records exactly its scope:

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
  core.py                  The stack: 6 field-native engines, ML-KEM audit, parameter estimator
  cli.py                   Command-line interface
  report.py                Native JSON + SARIF 2.1.0 output
  symbols.py               The functions a shared library exports, per platform
  isolate.py               Runs a vendor audit in a child process
  dsa_audit.py             ML-DSA library audit
  ct_audit.py              Constant time under Valgrind memcheck (ML-KEM, Classic McEliece)
  edge.py                  Wycheproof and CCTV edge-case vectors
  accumulated.py           Accumulated vectors: 10 000 random cases, one digest
  fresh.py                 Fresh, unpublished ACVP question sets
  response.py              Prompt/response verification for un-loadable builds
  harness_audit.py         Audits through a Crucible-protocol harness
  hybrid.py                RFC 10024 hybrid key-agreement composition
  hbs.py                   LMS/HSS and XMSS/XMSS^MT (SP 800-208)
  hbs_suite.py             Their conformance suites
  hbs_audit.py             LMS/HSS and XMSS library audit
  fndsa.py                 FN-DSA (Falcon) verification, FIPS 206 draft track
  fndsa_audit.py           FN-DSA library audit, draft track
  mceliece.py              Classic McEliece reference (not a FIPS standard)
  mceliece_audit.py        Classic McEliece library audit
  hqc.py                   HQC's error-correcting code (standard not final)
  hqc_audit.py             HQC decoder audit
  proofs.py                Runs the Coq proofs (--proofs)
  coq/                     NTT.v, Reduce.v: the proofs
  harness/                 C files linked into a test build of a library: deterministic
                           randombytes(), LMS/XMSS adapters. Never in production
  vectors/                 Pinned vectors and their manifests (PROVENANCE.md)
tests/test_pqverify.py     pytest suite (run on 3.9-3.13 in CI)
tools/                     Vendor audits, vector pinning, the re-pinning doctor
pyproject.toml             Build config + console-script entry point
DEMO.ipynb                 One-click Colab demo → 1566/1566
vendor_audit_template.py   Drop-in .so audit → JSON report
sample_report.json         Example output (what your auditors receive)
README.md / QUICKSTART.md / ARCHITECTURE.md / HYBRID.md / AUDITS.md / LIMITS.md
REPINNING.md / SECURITY.md / CHANGELOG.md / LICENSE / CITATION.cff
```

The wheel and source distribution are not in the repository: they are built
by the release workflow and attached to each
[release](https://github.com/bigDSanalyst/pq-verify/releases) (see
[Verifying a release](README.md#verifying-a-release)). Install:
`pip install "pq-verify[full]"`, or download the wheel from the release.
