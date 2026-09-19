# pq-verify — Quickstart

```bash
pip install "pq-verify[full]"
pq-verify --version
```

`[full]` pulls in `kyber-py`, `dilithium-py` and `sympy`, which the ACVP
suites and the parameter estimator need. Plain `pip install pq-verify` works
too — the checks that need those dependencies then report as **SKIPPED**
rather than passing or failing, and the run is marked DEGRADED so a CI green
cannot come from a check that never ran.

---

## 1. Confirm the tool works here

```bash
pq-verify                 # the self-suite
pq-verify --quick         # a fast subset
```

Ending in `OVERALL: 158/158 tests passed`, or fewer with some reported
`SKIPPED` when an optional dependency is absent. A skipped check stays out of
the ratio and names the dependency it needed.

```bash
pq-verify --acvp-all      # 855/855 pinned NIST ACVP vectors (ML-KEM + ML-DSA)
```

---

## 2. Verify your own implementation

### A — a compiled `.so` you can load

```bash
pq-verify --audit-so /path/to/libmlkem768.so ntt
pq-verify --audit-kem /path/to/libmlkem768.so ML-KEM-768
```

The report binds to the file: `artifact: sha256 <hash>`.

Don't know the symbol? `nm -D lib.so | grep -i ntt`. Many libraries inline the
NTT as `static`, so it is never exported — in that case either build a small
`.so` exposing `void ntt(int16_t[256])`, or use the prompt/response route
below.

> `--audit-so` and `--audit-kem` **execute the vendor's library**: `dlopen`
> runs its constructors before pq-verify calls anything. Audit binaries you
> would already be willing to run. See [SECURITY.md](SECURITY.md).

### B — an implementation you cannot load (HSM, sealed binary, inlined build)

Ask it the questions instead:

```bash
pq-verify --emit-prompt list                                  # what can be asked
pq-verify --emit-prompt ML-DSA-65 --prompt-out prompt.json    # questions, no answers
#   ... the implementer runs them, wherever it lives, and returns a response ...
pq-verify --verify-response response.json                     # byte-exact, per test case
```

A passing response shows the responder computes FIPS 203/204/205 correctly for
those inputs. It does **not** identify the binary that did it, so the report
says `artifact: none — vendor-supplied response` as a field, not a footnote.
A response covering 3 of 205 questions reports `3 of 205 asked` and
`INCOMPLETE` — never `3/3 PASS`.

### C — a hybrid handshake (what deployments actually negotiate)

```bash
pq-verify --emit-hybrid-prompt list
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
pq-verify --verify-hybrid hybrid.json
```

Checks the composition RFC 10024 pins — component order, offsets, lengths, the
FIPS 203 §7.2 encapsulation key check, ECDHE point validity, and the
recomputed ECDHE shared secret. Both halves can pass every ACVP vector while
the concatenation is wrong; that is what this catches.

---

## 3. Individual checks

```bash
pq-verify --params ML-KEM-1024      # parameter security (primal-uSVP + hybrid)
pq-verify --kem 4                   # native full-KEM at module rank 4
pq-verify --leakage                 # per-layer algebraic protection allocation
```

Or from Python:

```python
import pq_verify
pq_verify.pqverify_acvp_all()
pq_verify.pqverify_params("ML-KEM-768")
pq_verify.verify_hybrid("hybrid.json")
```

`pq_verify.__all__` lists the public API.

---

## 4. CI

```bash
pq-verify --acvp-all --fail-on-finding --require-full-coverage \
          --json report.json --sarif report.sarif
```

- `--fail-on-finding` exits non-zero for findings, `INCOMPLETE`,
  `CANNOT VERIFY`, and a suite short of its full count.
- `--require-full-coverage` exits non-zero if any dependency was missing, so a
  degraded run cannot report green.
- `--sarif` is ingested natively by GitHub Code Scanning, DefectDojo, Snyk and
  AWS Security Hub.

There is a packaged action — see [Use it in CI](README.md#use-it-in-ci).

---

## 5. Reproducibility

Vectors are **pinned inside the wheel**, so a run is deterministic: same input
→ identical output → identical SHA-256 fingerprint. `--live` fetches NIST's
current vectors instead, which is useful for detecting drift and by definition
not reproducible.

---

## Notes

- Requires Python 3.9+. Engines compile at runtime via `gcc`/`g++`, so the
  first run takes a few seconds; without a compiler those checks report as
  SKIPPED.
- Google Colab works: `pip install "pq-verify[full]"` then `!pq-verify`.
  `DEMO.ipynb` in this repository is a one-click version.
- pq-verify does not measure side channels. See
  [Scope](README.md#side-channels-are-not-measured).
