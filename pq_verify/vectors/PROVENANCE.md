# Pinned NIST ACVP Vectors

Frozen snapshot of NIST ACVP-Server test vectors for FIPS 203 (ML-KEM),
FIPS 204 (ML-DSA) and FIPS 205 (SLH-DSA), captured from https://github.com/usnistgov/ACVP-Server (gen-val/json-files).

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
| SLH-DSA-sigGen-FIPS205 | `112690e` | 2025-06-12 |
| SLH-DSA-sigVer-FIPS205 | `112690e` | 2025-06-12 |

The SLH-DSA sigGen and sigVer files (`prompt.json`, `expectedResults.json`;
about 68 MB uncompressed) are in their own archive,
`slhdsa_sig_vectors.json.gz`, which pq-verify opens only when an SLH-DSA
signature suite runs. Its entries are NIST's file text verbatim, so the
sha256 of each equals `MANIFEST.json`'s and the sha256 of the file at that
NIST commit; `tools/doctor.py` checks this offline. The other files are
stored as parsed JSON in `acvp_vectors.json.gz`.

Superseded pins (pq-verify ≤ 2.8.0):

- ML-KEM-encapDecap-FIPS203 `c924096`: every invalid encapsulation key was
  416 bytes over length, so the key-check groups tested length only. NIST
  fixed this in `ad33b3d`.
- ML-DSA-sigVer-FIPS204 `2972def`: NIST corrected the ModifyZ disposition in
  `a7f283c`.


## Edge-case vectors (Wycheproof, CCTV)

`edge_vectors.json.gz` holds C2SP edge-case vectors verbatim, one entry per
upstream file, and `EDGE_MANIFEST.json` records for each the source
repository, the pinned commit and the sha256 of the upstream text.
`tools/pin_edge_vectors.py` re-fetches them from those commits and writes the
bundle deterministically; `--check` (and `tools/doctor.py`) re-verify every
digest offline.

| Source | Commit | Files |
|---|---|---|
| [C2SP/wycheproof](https://github.com/C2SP/wycheproof) | `3fa63dd` (2026-09-02) | `mlkem_{512,768,1024}_{test,encaps_test,semi_expanded_decaps_test}.json`, `mldsa_{44,65,87}_{verify,sign_seed}_test.json` |
| [C2SP/CCTV](https://github.com/C2SP/CCTV) | `50a8ecf` (2026-09-25) | `ML-KEM/{strcmp,unluckysample,modulus}/ML-KEM-{512,768,1024}` |

CCTV's `unluckysample` keys were derived with FIPS 203 ipd's `G(d)` rather
than the final `G(d || k)`, so pq-verify checks those vectors' Encaps and
Decaps but not their KeyGen output.
