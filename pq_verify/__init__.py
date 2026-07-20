"""
pq-verify — Independent verification for ML-KEM / ML-DSA implementations.

Verifies that post-quantum cryptography implementations compute the
FIPS 203/204 standard correctly: native field-native NTT verification,
non-circular Known Answer Tests, NIST ACVP end-to-end (240/240), a
Bai-Galbraith lattice parameter-security estimator, and per-layer
side-channel leakage analysis. Coq-certified, reproducible.

Author: Nicholas Maino (iamweare) — Melbourne AU
License: MIT
"""

__version__ = "2.6.0"
__author__ = "Nicholas Maino (iamweare)"
__license__ = "MIT"

# Re-export the public API from the core engine (the real 5451-line stack).
from .core import (
    main,
    pqverify_kat,
    pqverify_kem,
    pqverify_acvp,
    pqverify_mldsa_acvp,
    pqverify_acvp_all,
    pqverify_params,
    pqverify_leakage,
    pqverify_load_so,
    pqverify_scan,
)

# FIPS 203 input-validation oracles (used by ACVP KeyCheck groups)
try:
    from .core import check_encapsulation_key, check_decapsulation_key
except ImportError:
    pass

__all__ = [
    "__version__",
    "main",
    "pqverify_kat",
    "pqverify_kem",
    "pqverify_acvp",
    "pqverify_mldsa_acvp",
    "pqverify_acvp_all",
    "pqverify_params",
    "pqverify_leakage",
    "pqverify_load_so",
    "pqverify_scan",
    "check_encapsulation_key",
    "check_decapsulation_key",
]
