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
    assert pq_verify.__version__ == "2.6.7"


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
    # Layer COUNT is scheme-determined: ML-KEM's zeta has order n -> incomplete
    # transform, 7 layers. ML-DSA's has order 2n -> complete, 8 layers. The
    # risk PATTERN is structural and identical; only the depth differs.
    expected = ([3, 2, 2, 2, 1, 1, 0, 0] if q == 8380417
                else [3, 2, 2, 2, 1, 1, 0])
    assert table == expected, f"q={q}: got {table}, expected {expected}"
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


def test_watcher_covers_every_bundled_vector():
    """Every pinned vector file must be watched for upstream drift.

    The bundle is frozen for determinism; the watcher is what tells the
    maintainer when upstream has moved so re-pinning is a deliberate act. A
    file that is bundled but unwatched can drift silently -- exactly the
    failure the watcher exists to prevent. This caught SLH-DSA-keyGen-FIPS205
    and the two internalProjection.json files being bundled but untracked.
    """
    import gzip, json, re, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    bundle = root / "pq_verify" / "vectors" / "acvp_vectors.json.gz"
    watcher = root / "tools" / "check_vectors.py"
    if not bundle.exists() or not watcher.exists():
        import pytest
        pytest.skip("bundle or watcher not present in this layout")

    with gzip.open(bundle, "rt") as fh:
        bundled = set(json.load(fh).keys())

    src = watcher.read_text()
    block = re.search(r"TARGETS = \{(.*?)\n\}", src, re.S).group(1)
    watched = set()
    for m in re.finditer(r'"([^"]+)":\s*\[([^\]]+)\]', block):
        for f in re.findall(r'"([^"]+)"', m.group(2)):
            watched.add(f"{m.group(1)}/{f}")

    unwatched = bundled - watched
    assert not unwatched, (
        f"bundled but NOT watched for drift: {sorted(unwatched)} -- "
        f"add them to TARGETS in tools/check_vectors.py")


def test_mldsa_freivalds_engine():
    """The 32-bit Freivalds engine must accept a correct ML-DSA NTT and reject
    a wrong one -- including a 7-layer (ML-KEM-shaped) transform.

    That last case matters: a 7-layer transform applied to ML-DSA was a real
    bug in this codebase, and a check that only ever passes would not have
    caught it.
    """
    import ctypes, random, io, contextlib
    import pq_verify.core as core
    with contextlib.redirect_stdout(io.StringIO()):
        eng = core.compile_all(); core.bind_all(eng)
    z32 = eng.get('zq32')
    if z32 is None or not hasattr(z32, 'zq32_freivalds_ntt'):
        import pytest; pytest.skip("zq32 engine unavailable")

    Q, Z, N = 8380417, 1753, 256
    mk = lambda p: (ctypes.c_uint32 * N)(*p)
    random.seed(4242)
    x = [random.randint(0, Q - 1) for _ in range(N)]

    # correct NTT -> accepted
    xa, ya = mk(x), mk(x)
    z32.zq32_ntt_forward(ya, N, Q, Z)
    assert z32.zq32_freivalds_ntt(xa, ya, N, Q, Z, 10, 1) == 1, \
        "correct ML-DSA NTT was rejected"

    # single-coefficient corruption -> rejected
    yb = mk([ya[i] for i in range(N)])
    yb[13] = (yb[13] + 1) % Q
    assert z32.zq32_freivalds_ntt(xa, yb, N, Q, Z, 10, 1) == 0, \
        "off-by-one corruption was accepted"

    # a 7-layer (ML-KEM-shaped) transform is NOT ML-DSA's NTT -> rejected
    zt = [pow(Z, int(format(i, '08b')[::-1], 2), Q) for i in range(256)]
    f, k, L = list(x), 1, 128
    while L >= 2:
        s = 0
        while s < N:
            w = zt[k]; k += 1
            for j in range(s, s + L):
                t = (w * f[j + L]) % Q
                f[j + L] = (f[j] - t) % Q
                f[j] = (f[j] + t) % Q
            s += 2 * L
        L //= 2
    assert z32.zq32_freivalds_ntt(xa, mk(f), N, Q, Z, 10, 1) == 0, \
        "a 7-layer transform was accepted as ML-DSA's 8-layer NTT"
