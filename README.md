# pq-verify v2.8.0 — PQC Implementation Verification

[![PyPI](https://img.shields.io/pypi/v/pq-verify.svg)](https://pypi.org/project/pq-verify/)
![license](https://img.shields.io/badge/license-MIT-green)
[![tests](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml/badge.svg)](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml)
![self-suite](https://img.shields.io/badge/self--suite-160%20checks-brightgreen)
![ACVP-KEM](https://img.shields.io/badge/ML--KEM%20ACVP-240%2F240-brightgreen)
![ACVP-DSA](https://img.shields.io/badge/ML--DSA%20ACVP-615%2F615-brightgreen)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22851661.svg)](https://doi.org/10.5281/zenodo.22851661)

**Independent verification for ML-KEM (Kyber) and ML-DSA (Dilithium) implementations.**

You deploy post-quantum cryptography. pq-verify checks that an implementation computes the FIPS 203/204 standard correctly — the transform verified in the native finite field, the full ML-KEM scheme byte-exact against NIST's own test vectors, with machine-checkable certificates for the algebraic identities. Plus FIPS 205 SLH-DSA parameter validation across all 12 parameter sets.

It does not compute PQC. It verifies the implementations that do: liboqs, BoringSSL, OpenSSL+OQS, HSM firmware, or your own code.

---

## What you get

A three-layer audit of any ML-KEM/ML-DSA implementation:

| Layer | Question answered | How |
|-------|-------------------|-----|
| **Correctness** | Does the NTT compute the FIPS definition? | Field-native verification + non-circular KAT |
| **Compliance** | Does it match NIST's published vectors? | ML-KEM 240/240 + ML-DSA 615/615 = 855/855 ACVP vectors (pinned) |
| **Security** | Are the parameters hard enough? | Bai-Galbraith primal-uSVP + hybrid attack estimator |

| **Composition** | Do the two halves of a hybrid agreement fit together? | RFC 10024 component order, offsets and lengths, per group |

Plus per-layer algebraic protection allocation: which NTT layers are worth
masking, computed from the transform's structure. That is a design input, not
a measurement — see [Scope](#scope).

Every result is **reproducible** — deterministic output, SHA-256 fingerprint, re-runnable by your own auditors.

---

## Proven (all tested on commodity hardware, Google Colab CPU)

- **160/160** self-test across 6 field-native engines, 6 phases — in an
  environment with every optional dependency present. Where one is missing the
  dependent check reports as `⊘ SKIPPED`, is excluded from the ratio, and names
  what it needed. It is never counted as a pass, and never as a failure either
- **240/240** NIST ACVP ML-KEM vectors — keyGen + encaps + decaps byte-exact, KeyCheck bool-exact
- **Native full-KEM** verified at ML-KEM-1024 (Level 5): recovery 20/20, negative control caught
- **Non-circular KAT** 100/100 against the independent FIPS reference
- Calibrated lattice estimator: reproduces lattice-estimator exactly (Kyber-512 β=406/118.6 bits)
- **Coq certificates** verified by `coqc` with real exit codes

---

## Quick start

```bash
pip install "pq-verify[full]"
pq-verify --acvp-all            # 855/855, offline, no configuration
```

That is the whole installation. It is a command-line tool: Python 3.9+, `gcc`,
and nothing else. No notebook, no network, no service. The NIST vectors ship
inside the package, so air-gapped environments work out of the box.

To audit a compiled library:

```bash
pq-verify --audit-so build/libmlkem768.so PQCLEAN_MLKEM768_CLEAN_ntt
```

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

Three lines in any repository that builds an ML-KEM or ML-DSA implementation.
Findings appear as annotations on the pull request, and the build fails if the
transform diverges from the FIPS 203/204 reference.

```yaml
- uses: bigDSanalyst/pq-verify@v1
  with:
    library: build/libmlkem768.so
    symbol: PQCLEAN_MLKEM768_CLEAN_ntt
```

With no library at all, it runs the NIST ACVP suites:

```yaml
- uses: bigDSanalyst/pq-verify@v1
```

| Input | Default | Purpose |
|---|---|---|
| `library` | — | compiled `.so` containing the NTT to audit |
| `symbol` | — | exported NTT symbol (`nm -D lib.so \| grep -i ntt`) |
| `acvp` | `true` | run ACVP suites; `live` fetches NIST's current vectors |
| `hybrid-transcript` | — | transcript to check against RFC 10024 (see `--emit-hybrid-prompt`) |
| `fail-on-finding` | `true` | fail the step if anything is reported |

Outputs: `verified`, `findings`, `sarif-file`. A complete workflow is in
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

pq-verify has been run against four upstream projects — all verify clean, with
negative controls that correctly fail. Exact commits, build commands and
per-check output are in [AUDITS.md](AUDITS.md).

| Implementation | What was audited | Result |
|---|---|---|
| liboqs (`mlkem-native` / `mldsa-native`) | NTT symbol, ML-KEM + ML-DSA | 3/3 each |
| PQClean | NTT symbol, ML-KEM + ML-DSA | 3/3 each |
| PQClean ML-KEM-768 | **full scheme** — keygen, encaps, decaps | 60/60 byte-exact |
| pq-crystals reference | NTT symbol, Kyber + Dilithium | 3/3 each |
| BoringSSL | in-tree NIST vectors (NTT not exported) | 50/50 byte-exact |

Most rows are **NTT-level**: the transform is checked against an independently
computed FIPS reference. Full-scheme auditing of a third party's
keygen/encaps/decaps is available for ML-KEM (`--audit-kem`); the equivalent
for ML-DSA signing is not, because most libraries do not export the
derandomised entry points NIST's seeded vectors require.

Where no entry point can be loaded at all — ML-DSA signing, an HSM, a sealed
binary — `--emit-prompt` / `--verify-response` asks the questions instead and
checks the answers byte-exact. That result is not artifact-bound, and the
report says so rather than implying otherwise; see
[What a result is bound to](#what-a-result-is-bound-to).

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

## Public API

| Function | Purpose |
|----------|---------|
| `main()` | 160-check self-suite |
| `pqverify_acvp()` | Full NIST ACVP end-to-end ML-KEM (240/240, all groups) |
| `pqverify_mldsa_acvp()` | Full NIST ACVP end-to-end ML-DSA (615/615, FIPS 204) |
| `pqverify_slhdsa_acvp()` | NIST ACVP SLH-DSA keyGen (120/120, FIPS 205, all 12 parameter sets) |
| `pqverify_acvp_all()` | ML-KEM + ML-DSA (855/855) offline; `slhdsa=True` adds FIPS 205 → 975/975 |
| `pqverify_params(set)` | Parameter security: primal-uSVP + sparse hybrid |
| `pqverify_kem(k=4)` | Native algebraic full-KEM verification |
| `pqverify_kat(ntt, k=4)` | Non-circular KAT vs FIPS definition |
| `pqverify_load_so(path, sym)` | Load NTT from a compiled .so |
| `pqverify_scan(target)` | Auto-discover + audit NTT functions |
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
inside the package (gzipped, ~7 MB). By default it verifies against those — so:

- **the same input gives the same result, every run, forever**
- **it works with no network** — air-gapped, offline, no GitHub reachability needed
- **NIST editing their published files cannot change or break your result**

That last point is not hypothetical: NIST periodically regenerates these vectors and
has changed the ML-KEM `encapDecap` schema (the `keyFormat` seed/expanded split) more
than once. A tool that fetches live gives different answers on different days. This one
does not.

```python
pqverify_acvp_all()              # pinned bundle, offline, deterministic  → 855/855
pqverify_acvp_all(live=True)     # opt in: fetch NIST's current vectors instead
pqverify_acvp_all(vector_dir=d)  # or point at your own local vector set
```

Vector provenance and per-file sha256 are recorded in `pq_verify/vectors/MANIFEST.json`.
A scheduled GitHub Action watches upstream and opens an issue when NIST changes
something, so re-pinning is a deliberate, reviewed act rather than a live dependency.

## Verifying a release

Releases are built by `.github/workflows/release.yml` on GitHub's runners, from
a reviewed commit, after the full suite and all 855 NIST ACVP vectors pass on
Python 3.9 through 3.13. Each artifact carries **SLSA build provenance** and an
attested **SPDX SBOM**. Check them yourself, trusting nothing this repository
says:

```bash
gh attestation verify pq_verify-2.8.0-py3-none-any.whl --repo bigDSanalyst/pq-verify
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
| `--audit-so`, `--audit-kem` | `sha256 <hash>` — that file performed the computation |
| `--verify-response` | `none — vendor-supplied response` |
| `--verify-hybrid` | `none — vendor-supplied transcript` |
| `--acvp`, `--acvp-all` | `none — reference-chain conformance, no vendor binary loaded` |

The binding is recorded independently of the verdict, because they are
different facts. A library that exposes no derandomised entry points is
`artifact: sha256 <hash>` (the file was read) with status `CANNOT VERIFY` (no
vector was ever driven through it). In SARIF the hash is emitted as the run's
`artifacts[].hashes.sha-256`, which is where a security platform already looks
for "this exact file was analysed".

A passing response proves that whoever produced it computes FIPS 203/204/205
correctly for those inputs. It does not prove **which binary did it**: there is
no signature over the computation and no binding to code. So the report says
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
- and, when you supply an ephemeral private scalar, the ECDHE shared secret
  **recomputed** and compared byte-for-byte at the offset the group pins

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

No private KEM key is ever requested. A field you cannot supply is reported as
`NOT CHECKED` and stays out of the ratio; a check that does not exist for a
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
tool that checked only what pq-verify checks would have passed both.

So every report carries the scope as a field rather than leaving it to be
inferred:

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
  report.py                Native JSON + SARIF 2.1.0 output
tests/test_pqverify.py     pytest suite (run on 3.9-3.13 in CI)
pyproject.toml             Build config + console-script entry point
dist/
  pq_verify-2.8.0-py3-none-any.whl    Installable wheel
  pq_verify-2.8.0.tar.gz              Source distribution
DEMO.ipynb                 One-click Colab demo → 855/855
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
  3.13) runs the full test suite and all 855 ACVP vectors in CI.** The floor is
  3.9 rather than 3.8 because `pq-verify[full]` cannot resolve below it:
  `kyber-py` and `dilithium-py` both require `>=3.9`. `requires-python` and the
  code are held together mechanically — a module that stops parsing at the
  declared floor fails the suite, and widening the floor fails it too.
- gcc and g++ (the C/C++ engines compile at runtime)

**For the full 160/160 self-suite and the 855/855 ACVP claim:**
- `kyber-py` — **required** for `pqverify_acvp()` (the byte-exact NIST reference) and the FIPS 203 roundtrip tests
- `dilithium-py` — **required** for `pqverify_mldsa_acvp()` (the 615 ML-DSA vectors)
- `coq` — required for the Coq certificate verification tests
- `sympy` — required for the Engine-6 Conjecture 7 exact-rational test (without it that check reports as skipped, not failed)

```bash
apt-get install -y coq gcc g++
pip install kyber-py dilithium-py sympy --break-system-packages
```

**Optional (1 test each, everything works without them):**
- `cryptominisat` — the CMS5 speed-comparison benchmark
- `slh-dsa` — SLH-DSA live roundtrip (parameters still validate without it)
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
> implementations* (v2.8.0). Zenodo. https://doi.org/10.5281/zenodo.22851661

```bibtex
@software{maino_pqverify_2026,
  author    = {Maino, Nicholas Clifford},
  title     = {pq-verify: Independent verification for ML-KEM / ML-DSA implementations},
  version   = {2.8.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22851661},
  url       = {https://doi.org/10.5281/zenodo.22851661}
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
