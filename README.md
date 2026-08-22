# pq-verify v2.6.7 — PQC Implementation Verification

[![PyPI](https://img.shields.io/pypi/v/pq-verify.svg)](https://pypi.org/project/pq-verify/)
![version](https://img.shields.io/badge/version-2.6.7-blue)
![license](https://img.shields.io/badge/license-MIT-green)
![tests](https://img.shields.io/badge/tests-160%2F160-brightgreen)
![ACVP-KEM](https://img.shields.io/badge/ML--KEM%20ACVP-240%2F240-brightgreen)
![ACVP-DSA](https://img.shields.io/badge/ML--DSA%20ACVP-615%2F615-brightgreen)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21739511.svg)](https://doi.org/10.5281/zenodo.21739511)

**Independent verification for ML-KEM (Kyber) and ML-DSA (Dilithium) implementations.**

You deploy post-quantum cryptography. pq-verify proves your implementation computes the FIPS 203/204 standard correctly — in the native finite field, against NIST's own test vectors, with machine-checkable certificates. Plus FIPS 205 SLH-DSA parameter validation across all 12 parameter sets.

It does not compute PQC. It verifies the implementations that do: liboqs, BoringSSL, OpenSSL+OQS, HSM firmware, or your own code.

---

## What you get

A three-layer audit of any ML-KEM/ML-DSA implementation:

| Layer | Question answered | How |
|-------|-------------------|-----|
| **Correctness** | Does the NTT compute the FIPS definition? | Field-native verification + non-circular KAT |
| **Compliance** | Does it match NIST's published vectors? | ML-KEM 240/240 + ML-DSA 615/615 = 855/855 ACVP vectors (pinned) |
| **Security** | Are the parameters hard enough? | Bai-Galbraith primal-uSVP + hybrid attack estimator |

Plus per-layer side-channel leakage analysis with protection-allocation recommendations.

Every result is **reproducible** — deterministic output, SHA-256 fingerprint, re-runnable by your own auditors.

---

## Proven (all tested on commodity hardware, Google Colab CPU)

- **160/160** self-test across 6 field-native engines, 6 phases
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

That is the whole installation. It is a command-line tool: Python 3.8+, `gcc`,
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

`DEMO.ipynb` runs the same thing in Colab if you prefer a notebook.

<details>
<summary>Other install routes</summary>

```python
exec(open('pq_verify/core.py').read())   # 160-test self-suite + loads the API

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

`--fail-on-finding` exits non-zero, so it can gate a merge.

---

## Independent audits

pq-verify has been run against four upstream projects — all verify clean, with
negative controls that correctly fail. Exact commits, build commands and
per-check output are in [AUDITS.md](AUDITS.md).

| Implementation | Result |
|---|---|
| liboqs (`mlkem-native` / `mldsa-native`) | ML-KEM and ML-DSA verified |
| PQClean | ML-KEM and ML-DSA verified |
| pq-crystals reference | Kyber and Dilithium verified |
| BoringSSL | vector cross-check, byte-exact |

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
| **GF(2)** | F₂ | AES S-box affine layer, bit-packed Gaussian elimination, **null-space enumeration** (full solution spaces, 2⁵⁶ verified) |
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
| `main()` | 160-test self-suite |
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

## What a result is bound to

Every report states its binding as a field, not as prose:

| Path | `artifact` |
|------|-----------|
| `--audit-so`, `--audit-kem` | `sha256 <hash>` — that file performed the computation |
| `--verify-response` | `none — vendor-supplied response` |

A passing response proves that whoever produced it computes FIPS 203/204/205
correctly for those inputs. It does not prove **which binary did it**: there is
no signature over the computation and no binding to code. So the report says
`artifact: none` rather than implying otherwise, and a reader can tell the two
kinds of result apart without reading a footnote.

The same discipline applies to coverage. A response answering 3 of 205
questions reports `3 of 205 asked`, groups nobody answered print `NOT RUN`
rather than `FAIL`, and the verdict is `INCOMPLETE` — never `3/3 PASS`.
Answering a different question set (`promptId` mismatch) is `CANNOT VERIFY`,
which is reported separately from verified-and-failed: `PQV000` for an absent
check, `PQV006` for an answer that is genuinely wrong.

---

## Scope

pq-verify verifies the **algebraic substance** of ML-KEM/ML-DSA (NTT, module-LWE relations, parameter security) natively in Z₃₃₂₉ / Z₈₃₈₀₄₁₇. The **non-algebraic layers** (SHAKE/SHA3 hashing, sampling, compression, the FO transform) are bit/byte operations verified by NIST ACVP end-to-end testing, not native field solving.

The algebraic core is proven natively where the proof is exact; the full implementation is proven byte-exact against NIST's own bytes. We make the claims we can prove.

---

## What's in this package

```
pq_verify/
  __init__.py              Public API (15 functions)
  core.py                  The stack (~6,100 lines, 6 field-native engines)
  cli.py                   Command-line interface
  response.py              Prompt/response verification for un-loadable builds
  report.py                Native JSON + SARIF 2.1.0 output
tests/test_pqverify.py     36-test pytest suite
pyproject.toml             Build config + console-script entry point
dist/
  pq_verify-2.6.7-py3-none-any.whl    Installable wheel
  pq_verify-2.6.7.tar.gz              Source distribution
DEMO.ipynb                 One-click Colab demo → 855/855
vendor_audit_template.py   Drop-in .so audit → JSON report
sample_report.json         Example output (what your auditors receive)
README.md / QUICKSTART.md / LICENSE / CITATION.cff
```

Install: `pip install dist/pq_verify-2.6.7-py3-none-any.whl`

---

## Requirements

**Minimum (core engines + ~149 self-tests):**
- Python 3.8+
- gcc and g++ (the C/C++ engines compile at runtime)

**For the full 160/160 self-suite and the 855/855 ACVP claim:**
- `kyber-py` — **required** for `pqverify_acvp()` (the byte-exact NIST reference) and the FIPS 203 roundtrip tests
- `dilithium-py` — **required** for `pqverify_mldsa_acvp()` (the 615 ML-DSA vectors)
- `coq` — required for the Coq certificate verification tests
- `sympy` — required for the Engine-6 Conjecture 7 exact-rational test (without it: 159/160)

```bash
apt-get install -y coq gcc g++
pip install kyber-py dilithium-py sympy --break-system-packages
```

**Optional (1 test each, everything works without them):**
- `cryptominisat` — the CMS5 speed-comparison benchmark
- `slh-dsa` — SLH-DSA live roundtrip (parameters still validate without it)
- network access — `pqverify_acvp()` fetches NIST vectors from GitHub live; for air-gapped use, pass `prompt_dir=` pointing at local vector files

**Deliberately NOT required** (a deployment advantage):
- No numpy, scipy, or PyTorch — pure Python + ctypes + inline C
- No SageMath — the `pqverify_params` lattice estimator is self-contained (it reproduces the lattice-estimator's results without it)

---

## License

MIT. The verifier is open-source — builds trust, enables adoption. Commercial support, custom engine development, and PQC audit engagements available separately.

## Citing this software

Archived on Zenodo with a citable DOI:

> Maino, N. C. (2026). *pq-verify: Independent verification for ML-KEM / ML-DSA
> implementations* (v2.6.7). Zenodo. https://doi.org/10.5281/zenodo.21739511

```bibtex
@software{maino_pqverify_2026,
  author    = {Maino, Nicholas Clifford},
  title     = {pq-verify: Independent verification for ML-KEM / ML-DSA implementations},
  version   = {2.6.7},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.21739511},
  url       = {https://doi.org/10.5281/zenodo.21739511}
}
```

The DOI above resolves to this specific release. The companion paper is
[10.5281/zenodo.19302050](https://doi.org/10.5281/zenodo.19302050).

## Contact

Nicholas Maino (iamweare) · maiknown@gmail.com · https://github.com/bigDSanalyst
Zenodo: https://doi.org/10.5281/zenodo.19302050
