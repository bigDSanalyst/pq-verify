# Pinned NIST ACVP Vectors

Frozen snapshot of NIST ACVP-Server test vectors for FIPS 203 (ML-KEM),
captured from https://github.com/usnistgov/ACVP-Server (gen-val/json-files).

These are bundled so pq-verify is DETERMINISTIC and OFFLINE by default: the
same input yields the same result regardless of upstream edits or network.
NIST edits these files periodically (the encapDecap schema has oscillated
between 'seed'/'expanded' keyFormats and a single 'dk' form); pinning insulates
users from that.

MANIFEST.json records the sha256 of every pinned file.
Run with --live (or prompt_dir=None, live=True) to fetch current upstream
vectors instead. The bundled ML-DSA path (dilithium-py) is unaffected.


## Pinned revisions

MANIFEST.json records each file's `nist_commit`; reports print it as
`vectors: pinned (NIST ACVP-Server <commit>)`.

| Directory | NIST commit | Date |
|---|---|---|
| ML-KEM-keyGen-FIPS203 | `15c0f3d` | 2026-04-16 |
| ML-KEM-encapDecap-FIPS203 | `ad33b3d` | 2026-07-28 |
| ML-DSA-keyGen-FIPS204 | `2972def` | 2026-07-20 |
| ML-DSA-sigGen-FIPS204 | `2972def` | 2026-07-20 |
| ML-DSA-sigVer-FIPS204 | `a7f283c` | 2026-07-31 |
| SLH-DSA-keyGen-FIPS205 | `112690e` | 2025-06-12 |

Superseded pins (pq-verify ≤ 2.8.0):

- ML-KEM-encapDecap-FIPS203 `c924096`: every invalid encapsulation key was
  416 bytes over length, so the key-check groups tested length only. NIST
  fixed this in `ad33b3d`.
- ML-DSA-sigVer-FIPS204 `2972def`: NIST corrected the ModifyZ disposition in
  `a7f283c`.
