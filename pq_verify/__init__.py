"""
pq-verify — Independent verification for ML-KEM / ML-DSA implementations.

Verifies that post-quantum cryptography implementations compute the
FIPS 203/204 standard correctly: native field-native NTT verification,
non-circular Known Answer Tests, NIST ACVP end-to-end (270/270), a
Bai-Galbraith lattice parameter-security estimator, and per-layer
side-channel leakage analysis. Coq-certified, reproducible.

Author: Nicholas Maino (iamweare) — Melbourne AU
License: MIT
"""

__version__ = "2.6.7"
__author__ = "Nicholas Maino (iamweare)"
__license__ = "MIT"

# Re-export the public API from the core engine (the real 5451-line stack).
from .core import (
    main,
    pqverify_kat,
    pqverify_kem,
    pqverify_acvp,
    pqverify_mldsa_acvp,
    pqverify_slhdsa_acvp,
    pqverify_acvp_all,
    pqverify_params,
    pqverify_leakage,
    pqverify_load_so,
    pqverify_scan,
    pqverify_audit_kem,
)

# Prompt/response verification — the route to implementations that cannot be
# dlopen'd (HSMs, sealed vendor binaries, inlined builds). Results from this
# path are explicitly NOT bound to an artifact; see pq_verify.response.
from .response import emit_prompt, build_prompt, verify_response, \
    available_parameter_sets

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
    "pqverify_slhdsa_acvp",
    "pqverify_acvp_all",
    "pqverify_params",
    "pqverify_leakage",
    "pqverify_load_so",
    "pqverify_scan",
    "pqverify_audit_kem",
    "emit_prompt",
    "build_prompt",
    "verify_response",
    "available_parameter_sets",
    "check_encapsulation_key",
    "check_decapsulation_key",
]
