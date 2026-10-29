
## 4. PQClean - HQC-128 (Clean C)

**Command:**
```bash
pq-verify --audit-hqc libhqc_audit.so HQC-1
```

**Result: `994/994 — VERIFIED`**

`pq-verify` audited the error-correcting code layer of HQC-128. It tested the Reed-Solomon and Reed-Muller encoders byte-for-byte, ran the decoders on built vectors, and verified the algebraic symmetry (`rm-symmetry`) without a reference decoder.

```text
  artifact: sha256 e8c8a340e3c377d7ba3748d0ac5eff3e7ac45c022d77eb9eb8e868d04515e7a0
====================================================================
  PASS  encode      18/18
  PASS  rm-decode   414/414
  PASS  rm-symmetry 387/387
  PASS  rs-decode   28/28
  PASS  code-decode 9/9
  PASS  bounds      138/138
====================================================================
  RESULT: 994/994 — VERIFIED
```
