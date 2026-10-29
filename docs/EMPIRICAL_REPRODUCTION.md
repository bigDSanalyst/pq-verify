
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

## 5. liboqs (Open Quantum Safe) - ML-KEM-768

**Command:**
```bash
pq-verify --audit-kem liboqs.so ML-KEM-768 --kem-keypair OQS_KEM_ml_kem_768_keypair_derand --kem-encaps OQS_KEM_ml_kem_768_encaps_derand --kem-decaps OQS_KEM_ml_kem_768_decaps
```

**Result: `1438/1438 — VERIFIED`**

```text
  artifact: sha256 89f14e48a0820470fd78461034f1dfc91b9e6ea8115ba4ddea88f3cc000f5e87
====================================================================
  THIRD-PARTY KEM AUDIT — ML-KEM-768
  library : liboqs.so
  keygen  : OQS_KEM_ml_kem_768_keypair_derand
  encaps  : OQS_KEM_ml_kem_768_encaps_derand
  decaps  : OQS_KEM_ml_kem_768_decaps
  vectors : pinned (NIST ACVP-Server 15c0f3d, ad33b3d)
====================================================================
  PASS  keyGen   25/25  byte-exact vs NIST
  PASS  encaps   25/25  byte-exact vs NIST
  PASS  decaps   10/10  byte-exact vs NIST
  PASS  ekCheck  10/10  encapsulation keys classified as NIST does (FIPS 203 §7.2)
  PASS  dkCheck  10/10  decapsulation keys classified as NIST does (FIPS 203 §7.3)
  edge cases: Wycheproof 3fa63dd, CCTV 50a8ecf
  PASS  edgeValid 461/461  edge-case vectors reproduced byte-for-byte
  PASS  edgeEk    892/892  invalid encapsulation keys refused (every q..4095, every position)
  PASS  edgeDk    2/2  invalid decapsulation keys refused
        64 wrong-length vectors not applicable: a C entry point takes fixed-size buffers
  PASS  accumulated 1/1  10,000 cases: digest 8a518cc63da36632… matches (Go 1.26.1 crypto/mlkem TestAccumulated (published))
  PASS  ct:encaps  1/1  no secret-dependent branch or memory access (Valgrind memcheck)
  PASS  ct:decaps  1/1  no secret-dependent branch or memory access (Valgrind memcheck)
====================================================================
  RESULT: 1438/1438 — VERIFIED
  This audits the vendor's OWN keygen/encaps/decaps against
  NIST's published vectors, including the invalid keys it
  must refuse. Constant-time: branches and addresses only, not timing or power.
====================================================================
```
