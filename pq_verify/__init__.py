"""
pq-verify — Independent verification for ML-KEM / ML-DSA implementations.

Verifies that post-quantum cryptography implementations compute the
FIPS 203/204 standard correctly: native field-native NTT verification,
non-circular Known Answer Tests, NIST ACVP end-to-end (855/855), a
Bai-Galbraith lattice parameter-security estimator, RFC 10024 hybrid
key-agreement composition, and per-layer algebraic protection allocation.
Coq-certified, reproducible.

Author: Nicholas Maino (iamweare) — Melbourne AU
License: MIT
"""

__version__ = "2.8.0"
__author__ = "Nicholas Maino (iamweare)"
__license__ = "MIT"

# Re-export the public API from the core engine.
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

# Hybrid key agreement (RFC 10024) — the composition ACVP cannot see. Both
# components can pass every NIST vector byte-for-byte while the concatenation
# is wrong, and that is what every deployed post-quantum TLS stack actually
# negotiates. See pq_verify.hybrid.
from .hybrid import (
    GROUPS as HYBRID_GROUPS,
    build_hybrid_prompt,
    emit_hybrid_prompt,
    verify_hybrid,
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
    "HYBRID_GROUPS",
    "build_hybrid_prompt",
    "emit_hybrid_prompt",
    "verify_hybrid",
    "check_encapsulation_key",
    "check_decapsulation_key",
]
