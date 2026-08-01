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

