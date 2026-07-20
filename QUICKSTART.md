# pq-verify v2.6.0 — Quickstart

## 1. Run the self-test (confirms the tool works on your machine)

Google Colab, or any Linux with `gcc` + Python 3.8+:

```bash
apt-get install -y coq && pip install kyber-py    # optional: full 160/160
```

```python
exec(open('pq_verify_v2_6_0.py').read())
```

Expected: a 7-phase report ending in `OVERALL: 160/160 tests passed`.
Without coq/kyber-py you'll see ~149/160 (11 kyber-py + Coq tests skip cleanly).

After loading, eight public functions are available: `main`, `pqverify_acvp`,
`pqverify_params`, `pqverify_kem`, `pqverify_kat`, `pqverify_load_so`,
`pqverify_scan`, and `pqverify_leakage`.

## 2. Verify your own implementation

### Option A — you have a compiled .so

Edit the CONFIG block in `vendor_audit_template.py`:

```python
SO_PATH    = "/path/to/your_library.so"
NTT_SYMBOL = "ntt"                # see "find your symbol" below
ALGORITHM  = "ML-KEM-1024"        # or ML-KEM-512/768, ML-DSA-44/65/87
```

Then:

```python
exec(open('pq_verify_v2_6_0.py').read())          # load the engine
exec(open('vendor_audit_template.py').read())      # runs the audit
```

Output: console report + `pqverify_vendor_report.json` (machine-readable,
with a reproducible SHA-256 fingerprint).

### Find your symbol (if you don't know it)

```python
discover_symbols("/path/to/your_library.so")
```

Lists exported NTT symbols. Note: many libraries inline the NTT as a
`static` function, so it won't be exported — in that case a small dedicated
`.so` exposing `void ntt(int16_t[256])` is the cleanest path.

### Option B — you have a Python implementation

```python
exec(open('pq_verify_v2_6_0.py').read())
# your_ntt(list[int]) -> list[int] defined in this session
pqverify_scan(globals())     # auto-discovers and audits it
```

## 3. Individual checks

```python
pqverify_kem(k=4)                      # native full-KEM, ML-KEM-1024 / Level 5
pqverify_kat(your_ntt, k=4)            # non-circular KAT vs FIPS definition
pqverify_leakage()                     # per-layer protection-allocation table
```

`k` selects the security level: 2 → Level 1, 3 → Level 3, 4 → Level 5
(Dilithium: 4/6/8 with `family='dilithium', q=8380417, zeta=1753`).

## 4. Reproducibility

The report is deterministic: same input → identical output → identical
SHA-256 fingerprint. Re-run any audit and compare fingerprints to confirm
the result wasn't tampered with.

## Notes

- Free Colab sessions are per-tab and reset after ~90 min idle. Keep the
  `.py` files in Google Drive and `exec()` them from there to avoid re-uploading.
- Engines compile at runtime via gcc/g++ — first run takes a few seconds.
- Never install torchtext in the same Colab environment (unrelated, but it
  corrupts the runtime).
