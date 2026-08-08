# pq-verify v2.6.4 — PQC Implementation Verification

![version](https://img.shields.io/badge/version-2.6.4-blue)
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

Open `DEMO.ipynb` in Google Colab and run all cells. ~3 minutes to 855/855.

Or, in any Python 3.8+ environment with gcc:

```python
exec(open('pq_verify_v2_6_1.py').read())   # 160-test self-suite + loads the API

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

---

## Public API

| Function | Purpose |
|----------|---------|
| `main()` | 160-test self-suite |
| `pqverify_acvp()` | Full NIST ACVP end-to-end ML-KEM (240/240, all groups) |
| `pqverify_mldsa_acvp()` | Full NIST ACVP end-to-end ML-DSA (615/615, FIPS 204) |
| `pqverify_acvp_all()` | Both ACVP suites combined (855/855) — offline by default |
| `pqverify_params(set)` | Parameter security: primal-uSVP + sparse hybrid |
| `pqverify_kem(k=4)` | Native algebraic full-KEM verification |
| `pqverify_kat(ntt, k=4)` | Non-circular KAT vs FIPS definition |
| `pqverify_load_so(path, sym)` | Load NTT from a compiled .so |
| `pqverify_scan(target)` | Auto-discover + audit NTT functions |
| `pqverify_leakage()` | Per-layer protection-allocation table |

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

## Scope

pq-verify verifies the **algebraic substance** of ML-KEM/ML-DSA (NTT, module-LWE relations, parameter security) natively in Z₃₃₂₉ / Z₈₃₈₀₄₁₇. The **non-algebraic layers** (SHAKE/SHA3 hashing, sampling, compression, the FO transform) are bit/byte operations verified by NIST ACVP end-to-end testing, not native field solving.

The algebraic core is proven natively where the proof is exact; the full implementation is proven byte-exact against NIST's own bytes. We make the claims we can prove.

---

## What's in this package

```
pq_verify/
  __init__.py              Public API (10 functions)
  core.py                  The stack (~5,700 lines, 6 field-native engines)
  cli.py                   Command-line interface
tests/test_pqverify.py     16-test pytest suite
pyproject.toml             Build config + console-script entry point
dist/
  pq_verify-2.6.4-py3-none-any.whl    Installable wheel
  pq_verify-2.6.4.tar.gz              Source distribution
DEMO.ipynb                 One-click Colab demo → 855/855
vendor_audit_template.py   Drop-in .so audit → JSON report
sample_report.json         Example output (what your auditors receive)
README.md / QUICKSTART.md / LICENSE / CITATION.cff
```

Install: `pip install dist/pq_verify-2.6.4-py3-none-any.whl`

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
> implementations* (v2.6.4). Zenodo. https://doi.org/10.5281/zenodo.21739511

```bibtex
@software{maino_pqverify_2026,
  author    = {Maino, Nicholas Clifford},
  title     = {pq-verify: Independent verification for ML-KEM / ML-DSA implementations},
  version   = {2.6.4},
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
