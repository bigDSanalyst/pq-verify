"""
pq-verify — Independent verification for ML-KEM / ML-DSA / SLH-DSA implementations.

Verifies that post-quantum cryptography implementations compute the
FIPS 203/204/205 standards correctly: native field-native NTT verification,
non-circular Known Answer Tests, NIST ACVP end-to-end (1566/1566), a
Bai-Galbraith lattice parameter-security estimator, RFC 10024 hybrid
key-agreement composition, and per-layer algebraic protection allocation.
The full ML-KEM NTT and both FIPS zeta tables are re-derived and checked in
Coq, axiom-free. Reproducible.

Author: Nicholas Maino (iamweare) — Melbourne AU
License: MIT
"""

__version__ = "2.11.0"
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

# Third-party ML-DSA audit: a vendor's own keygen/sign/verify against every
# NIST ACVP vector and Wycheproof's edge cases. See pq_verify.dsa_audit.
from .dsa_audit import pqverify_audit_dsa

# Stateful hash-based signatures (SP 800-208): LMS/HSS and XMSS/XMSS^MT.
from .hbs_suite import pqverify_lms_acvp, pqverify_hbs
from .hbs_audit import pqverify_audit_hbs

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
    "pqverify_audit_dsa",
    "pqverify_lms_acvp",
    "pqverify_hbs",
    "pqverify_audit_hbs",
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
