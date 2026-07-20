"""
pq-verify test suite.

Covers the import surface, the pure-Python public APIs (parameter
estimator, leakage analysis), and calibration anchors that must not drift.
Tests requiring compiled C engines or kyber-py are marked and skip cleanly
when those are unavailable.
"""
import io
import math
import contextlib

import pytest

import pq_verify
from pq_verify import (
    pqverify_params,
    pqverify_leakage,
    pqverify_kat,
)


# ----------------------------------------------------------------------
# Import surface
# ----------------------------------------------------------------------

def test_version():
    assert pq_verify.__version__ == "2.6.0"


def test_public_api_present():
    for name in ("main", "pqverify_kat", "pqverify_kem", "pqverify_acvp",
                 "pqverify_mldsa_acvp", "pqverify_params", "pqverify_leakage",
                 "pqverify_load_so", "pqverify_scan"):
        assert hasattr(pq_verify, name), f"missing public API: {name}"


def test_mldsa_acvp_live():
    """ML-DSA ACVP must return 615/615 against live NIST vectors (needs dilithium-py + network)."""
    pytest.importorskip("dilithium_py")
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        r = pq_verify.pqverify_mldsa_acvp(verbose=False)
    if r is None:
        pytest.skip("dilithium-py not available")
    assert r["verified"] is True
    assert r["passed"] == 615 and r["total"] == 615


# ----------------------------------------------------------------------
# Parameter estimator — standard sets must report AUTHORITATIVE values
# ----------------------------------------------------------------------

@pytest.mark.parametrize("param_set,beta,classical", [
    ("ML-KEM-512", 406, 118.6),
    ("ML-KEM-768", 630, 183.9),
    ("ML-KEM-1024", 864, 252.3),
])
def test_standard_params_authoritative(param_set, beta, classical):
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_params(param_set)
    assert r["beta"] == beta
    assert abs(r["classical"] - classical) < 0.05
    assert r["meets_level"] is True


# ----------------------------------------------------------------------
# Parameter estimator — custom formula calibration anchors (must not drift)
# ----------------------------------------------------------------------

@pytest.mark.parametrize("n,hw,beta", [
    (512, 80, 328),   # T-Kyber hw=40/poly, k=2
    (512, 48, 313),   # T-Kyber hw=24/poly, k=2
    (768, 80, 522),   # T-Kyber hw=40/poly, k=3
])
def test_custom_calibration_anchors(n, hw, beta):
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_params(n=n, q=3329, sigma_s=math.sqrt(hw / n),
                            sigma_e=1.0, hw=hw)
    assert r["beta"] == beta


def test_hybrid_cheaper_for_sparse_secret():
    """The hybrid attack must be flagged cheaper than primal for a sparse secret."""
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_params(n=512, q=3329, sigma_e=1.0, hw=80)
    assert r["hybrid"] is not None
    assert r["hybrid"] < r["classical"]


def test_weak_params_flagged_below_l1():
    """A deliberately weak parameter set must not report Level 1 security."""
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_params(n=256, q=3329, sigma_s=0.3, sigma_e=1.0, hw=20)
    effective = min(r["classical"], r["hybrid"]) if r.get("hybrid") else r["classical"]
    assert effective < 118.0


# ----------------------------------------------------------------------
# Leakage analysis — structural invariants for both fields
# ----------------------------------------------------------------------

@pytest.mark.parametrize("q,zeta", [
    (3329, 17),       # ML-KEM
    (8380417, 1753),  # ML-DSA
])
def test_leakage_table_structure(q, zeta):
    with contextlib.redirect_stdout(io.StringIO()):
        rows = pqverify_leakage(q=q, zeta=zeta, n=256)
    table = [{"CRITICAL": 3, "HIGH": 2, "MEDIUM": 1, "LOW": 0}[r["risk"]] for r in rows]
    # Validated allocation — identical for both fields (structural, not field-specific)
    assert table == [3, 2, 2, 2, 1, 1, 0]
    # Monotone non-increasing (information exposure only drops deeper into the NTT)
    assert all(table[i] >= table[i + 1] for i in range(len(table) - 1))
    # Exactly one CRITICAL layer, at layer 0
    assert table.count(3) == 1 and table[0] == 3


def test_leakage_cumulative_rank():
    """Cumulative rank of a 7-layer 256-coeff NTT is 128+64+...+2 = 254."""
    with contextlib.redirect_stdout(io.StringIO()):
        rows = pqverify_leakage(q=3329, zeta=17, n=256)
    assert sum(r["new_info"] for r in rows) == 254
    assert rows[-1]["cumul_rank"] == 254


# ----------------------------------------------------------------------
# KAT — requires the compiled C engine path; skip if unavailable
# ----------------------------------------------------------------------

def _ref_ntt_factory():
    Q = 3329
    def br7(x):
        r = 0
        for _ in range(7):
            r = (r << 1) | (x & 1); x >>= 1
        return r
    ZK = [pow(17, br7(i), Q) for i in range(128)]
    def ntt(p):
        f = [x % Q for x in p]; k = 1
        for L in (128, 64, 32, 16, 8, 4, 2):
            for s in range(0, 256, 2 * L):
                z = ZK[k]; k += 1
                for j in range(s, s + L):
                    t = (z * f[j + L]) % Q
                    f[j + L] = (f[j] - t) % Q
                    f[j] = (f[j] + t) % Q
        return f
    return ntt


def test_kat_accepts_correct_ntt():
    ntt = _ref_ntt_factory()
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_kat(ntt, k=4)
    assert r["verified"] is True


def test_kat_rejects_corrupted_ntt():
    """A single corrupted output coefficient must be caught."""
    ref = _ref_ntt_factory()
    def broken(p):
        f = ref(p); f[0] = (f[0] + 1) % 3329
        return f
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_kat(broken, k=4)
    assert r["verified"] is False
