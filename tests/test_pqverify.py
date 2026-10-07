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
import pathlib

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
    """One version, everywhere a report or a wheel states it."""
    import re
    from pq_verify.core import VERSION
    assert pq_verify.__version__ == VERSION == "2.10.0"
    toml = (pathlib.Path(__file__).resolve().parent.parent / "pyproject.toml")
    if toml.exists():
        assert re.search(r'^version = "([^"]+)"', toml.read_text(), re.M).group(1) == VERSION


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

    from pq_verify.core import _VECTOR_BUNDLES        # the NIST archives
    bundled = set()
    for name in _VECTOR_BUNDLES:
        with gzip.open(bundle.parent / name, "rt") as fh:
            bundled |= set(json.load(fh).keys())
    assert any(k.startswith("SLH-DSA-sigGen") for k in bundled)

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


def _load_watcher():
    import importlib.util, pathlib
    path = (pathlib.Path(__file__).resolve().parent.parent
            / "tools" / "check_vectors.py")
    if not path.exists():
        pytest.skip("watcher not present in this layout")
    spec = importlib.util.spec_from_file_location("check_vectors", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_watcher_compares_upstream_to_the_shipped_bundle(tmp_path):
    """The watcher must flag a bundle that lags upstream even when upstream
    matches its own baseline.

    Comparing upstream only to the baseline let the ML-KEM encapDecap and
    ML-DSA sigVer bundles sit two NIST fixes behind while every weekly run
    reported "no change".
    """
    import json
    w = _load_watcher()
    current = {"A/x.json": {"sha256": "aa" * 32, "bytes": 1},
               "B/y.json": {"sha256": "bb" * 32, "bytes": 1},
               "C/z.json": {"sha256": "cc" * 32, "bytes": 1}}
    manifest = tmp_path / "MANIFEST.json"
    manifest.write_text(json.dumps({
        "A/x.json": {"sha256": "aa" * 32, "bytes": 1},     # current
        "B/y.json": {"sha256": "00" * 32, "bytes": 1},     # behind
    }))                                                     # C: unmanifested
    history = {"B/y.json": {"bb" * 32: {"first_seen": "2026-08-07"}}}

    out = "\n".join(w.bundle_behind(current, history, str(manifest)))
    assert "[A/x.json]" not in out
    assert "[B/y.json] BUNDLE BEHIND UPSTREAM" in out
    assert "first seen 2026-08-07" in out
    assert "[C/z.json] shipped in the bundle but missing from MANIFEST" in out

    manifest.write_text(json.dumps(current))
    assert w.bundle_behind(current, {}, str(manifest)) == []


def _bundled_keycheck_tests():
    import gzip, json, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    with gzip.open(root / "pq_verify" / "vectors" / "acvp_vectors.json.gz",
                   "rt") as fh:
        ed = json.load(fh)["ML-KEM-encapDecap-FIPS203/internalProjection.json"]
    for g in ed["testGroups"]:
        if g["function"] in ("encapsulationKeyCheck", "decapsulationKeyCheck"):
            for t in g["tests"]:
                yield g["function"], g["parameterSet"], t


def test_manifest_records_every_bundled_file_and_its_nist_commit():
    """MANIFEST.json is what the watcher compares upstream against and what
    reports cite as the vector revision, so it must cover the whole bundle."""
    import gzip, json, pathlib, re
    vec = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "vectors"
    bundled = set()
    for arc in ("acvp_vectors.json.gz", "slhdsa_sig_vectors.json.gz"):
        with gzip.open(vec / arc, "rt") as fh:
            bundled |= set(json.load(fh))
    manifest = json.loads((vec / "MANIFEST.json").read_text())
    assert set(manifest) == bundled
    for name, entry in manifest.items():
        assert re.fullmatch(r"[0-9a-f]{7,40}", entry.get("nist_commit", "")), name


def test_invalid_key_vectors_exercise_more_than_length():
    """Every bundled key-check vector must have the parameter set's exact key
    length, so a checker that tests only length cannot pass them.

    The previously pinned NIST revision (c924096) shipped every invalid
    encapsulation key 416 bytes over length (NIST fixed it in ad33b3d). A
    length-only checker scored 30/30 on it, and a fixed-size C API reading
    only the first 1184 bytes saw a valid key. Against these vectors the same
    checker scores 15/30.
    """
    from pq_verify.core import check_encapsulation_key, check_decapsulation_key
    k = {"ML-KEM-512": 2, "ML-KEM-768": 3, "ML-KEM-1024": 4}
    rejected_by_content = {"encapsulationKeyCheck": 0, "decapsulationKeyCheck": 0}
    for fn, ps, t in _bundled_keycheck_tests():
        ek, dk = bytes.fromhex(t["ek"]), bytes.fromhex(t["dk"])
        assert len(ek) == 384 * k[ps] + 32, (ps, t["tcId"], len(ek))
        assert len(dk) == 768 * k[ps] + 96, (ps, t["tcId"], len(dk))
        check = (check_encapsulation_key(ek, ps)
                 if fn == "encapsulationKeyCheck"
                 else check_decapsulation_key(dk, ps))
        assert check == t["testPassed"], (fn, ps, t["tcId"], t.get("reason"))
        if not t["testPassed"]:
            rejected_by_content[fn] += 1
    # Each group must contain invalid keys, or the negative path is untested.
    assert all(n > 0 for n in rejected_by_content.values()), rejected_by_content


def test_reports_name_the_pinned_vector_revision():
    from pq_verify.core import _vector_label, _pkg_dir
    import os
    pinned = os.path.join(_pkg_dir(), "vectors")
    label = _vector_label(pinned, "ML-KEM-encapDecap-FIPS203")
    assert label == "pinned (NIST ACVP-Server ad33b3d)"
    assert _vector_label(None).startswith("LIVE")
    assert _vector_label("/elsewhere") == "local: /elsewhere"


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


# ----------------------------------------------------------------------
# Prompt / response verification (pq_verify.response)
#
# The route to implementations that cannot be dlopen'd. The invariants that
# matter here are (a) the emitted prompt never contains an answer, and (b) a
# response that covers less than the prompt is never scored as a pass.
# ----------------------------------------------------------------------

import json

from pq_verify.response import (
    build_prompt,
    available_parameter_sets,
    verify_response,
    _prompt_id,
)

_PS = "ML-KEM-512"


@pytest.fixture(scope="module")
def prompt512():
    return build_prompt(_PS)


@pytest.fixture(scope="module")
def response512(prompt512):
    """Answer the prompt with kyber-py, standing in for a vendor."""
    pytest.importorskip("kyber_py")
    from kyber_py.ml_kem import ML_KEM_512
    from pq_verify import check_encapsulation_key, check_decapsulation_key

    out = {"schema": "pq-verify/acvp-response", "schema_version": "1.0",
           "promptId": prompt512["promptId"], "parameterSet": _PS,
           "implementation": {"name": "kyber-py"}, "suites": []}
    for s in prompt512["suites"]:
        groups = []
        for g in s["testGroups"]:
            fn, tests = g.get("function"), []
            for t in g["tests"]:
                tc = t["tcId"]
                if s["mode"] == "keyGen":
                    ek, dk = ML_KEM_512._keygen_internal(
                        bytes.fromhex(t["d"]), bytes.fromhex(t["z"]))
                    tests.append({"tcId": tc, "ek": ek.hex(), "dk": dk.hex()})
                elif fn == "encapsulation":
                    k, c = ML_KEM_512._encaps_internal(
                        bytes.fromhex(t["ek"]), bytes.fromhex(t["m"]))
                    tests.append({"tcId": tc, "c": c.hex(), "k": k.hex()})
                elif fn == "decapsulation":
                    k = ML_KEM_512._decaps_internal(
                        bytes.fromhex(t["dk"]), bytes.fromhex(t["c"]))
                    tests.append({"tcId": tc, "k": k.hex()})
                elif fn == "encapsulationKeyCheck":
                    tests.append({"tcId": tc, "testPassed": bool(
                        check_encapsulation_key(bytes.fromhex(t["ek"]), _PS))})
                else:
                    tests.append({"tcId": tc, "testPassed": bool(
                        check_decapsulation_key(bytes.fromhex(t["dk"]), _PS))})
            groups.append({"tgId": g["tgId"], "tests": tests})
        out["suites"].append({"suite": s["suite"], "testGroups": groups})
    return out


def _write(tmp_path, doc, name="response.json"):
    p = tmp_path / name
    p.write_text(json.dumps(doc))
    return str(p)


def _run(path):
    with contextlib.redirect_stdout(io.StringIO()):
        return verify_response(path, verbose=False)


def test_parameter_sets_cover_all_three_fips():
    sets = available_parameter_sets()
    assert {"ML-KEM-512", "ML-KEM-768", "ML-KEM-1024"} <= set(sets)
    assert {"ML-DSA-44", "ML-DSA-65", "ML-DSA-87"} <= set(sets)
    assert any(s.startswith("SLH-DSA-") for s in sets)


def test_prompt_carries_no_answers(prompt512):
    """A question must never contain the value it is asking for."""
    for s in prompt512["suites"]:
        for g in s["testGroups"]:
            keys = {k for t in g["tests"] for k in t}
            assert not (set(g["answerFields"]) & keys), (
                f"{s['suite']} tg{g['tgId']} leaks {g['answerFields']}")


def test_prompt_id_is_reproducible(prompt512):
    """The binding is only worth anything if it recomputes from the bundle."""
    again = build_prompt(_PS)
    assert again["promptId"] == prompt512["promptId"]
    assert _prompt_id(again["suites"]) == prompt512["promptId"]
    assert build_prompt("ML-KEM-768")["promptId"] != prompt512["promptId"]


def test_mldsa_65_prompt_asks_every_pinned_question():
    p = build_prompt("ML-DSA-65")
    assert p["questionCount"] == 205        # 25 keyGen + 120 sigGen + 60 sigVer
    assert sum(build_prompt(f"ML-DSA-{n}")["questionCount"]
               for n in (44, 65, 87)) == 615


def test_correct_response_verifies(tmp_path, response512):
    r = _run(_write(tmp_path, response512))
    assert r["status"] == "VERIFIED" and r["verified"] is True
    assert r["passed"] == r["total"] == r["questions"] == 80
    assert r["unanswered"] == 0 and r["malformed"] == 0 and not r["findings"]
    assert r["prompt_binding"] == "confirmed"


def test_response_result_is_never_artifact_bound(tmp_path, response512):
    """A response proves computation, not provenance. The report must say so."""
    r = _run(_write(tmp_path, response512))
    assert r["artifact"]["bound"] is False
    assert r["artifact"]["sha256"] is None
    assert r["artifact"]["summary"] == "none — vendor-supplied response"


def test_vendor_asserted_hash_is_not_a_binding(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    doc["artifact"] = {"sha256": "ab" * 32}
    r = _run(_write(tmp_path, doc))
    assert r["artifact"]["bound"] is False
    assert r["artifact"]["vendor_asserted_sha256"] == "ab" * 32
    assert "not verified by pq-verify" in r["artifact"]["summary"]


def test_partial_response_is_incomplete_never_a_pass(tmp_path, response512):
    """Three correct answers out of eighty is 3/80 INCOMPLETE, not 3/3 PASS.

    A skip that reads as a pass is the failure mode this tool exists to stop.
    """
    doc = json.loads(json.dumps(response512))
    kg = [s for s in doc["suites"] if s["suite"] == "ML-KEM-keyGen-FIPS203"][0]
    kg["testGroups"][0]["tests"] = kg["testGroups"][0]["tests"][:3]
    doc["suites"] = [kg]
    r = _run(_write(tmp_path, doc))
    assert r["verified"] is False
    assert r["status"] == "INCOMPLETE"
    assert r["answered"] == 3 and r["passed"] == 3
    assert r["total"] == 80 and r["unanswered"] == 77
    # groups nobody answered are not reported as failing groups
    for label, (ok, ans, tot) in r["detail"].items():
        if "keyGen" not in label:
            assert (ok, ans) == (0, 0), label


def test_wrong_answer_is_a_finding(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    kg = [s for s in doc["suites"] if s["suite"] == "ML-KEM-keyGen-FIPS203"][0]
    t = kg["testGroups"][0]["tests"][0]
    t["ek"] = ("0" if t["ek"][0] != "0" else "1") + t["ek"][1:]
    r = _run(_write(tmp_path, doc))
    assert r["verified"] is False and r["status"] == "FINDINGS PRESENT"
    assert r["passed"] == 79 and r["answered"] == 80
    assert any("mismatch" in f for f in r["findings"])


def test_flipped_boolean_decision_is_caught(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    ed = [s for s in doc["suites"] if s["suite"] == "ML-KEM-encapDecap-FIPS203"][0]
    for g in ed["testGroups"]:
        if "testPassed" in g["tests"][0]:
            g["tests"][0]["testPassed"] = not g["tests"][0]["testPassed"]
            break
    r = _run(_write(tmp_path, doc))
    assert r["verified"] is False and r["passed"] == 79


def test_malformed_answers_do_not_count_as_passes(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    kg = [s for s in doc["suites"] if s["suite"] == "ML-KEM-keyGen-FIPS203"][0]
    kg["testGroups"][0]["tests"][0]["ek"] = "not-hex"
    del kg["testGroups"][0]["tests"][1]["dk"]
    r = _run(_write(tmp_path, doc))
    assert r["malformed"] == 2
    assert r["passed"] == 78 and r["verified"] is False
    assert sum("malformed" in f for f in r["findings"]) == 2


def test_prompt_id_mismatch_refuses_to_verify(tmp_path, response512):
    """Answering a different question set is cannot-verify, not verified-and-failed."""
    doc = json.loads(json.dumps(response512))
    doc["promptId"] = "0" * 64
    r = _run(_write(tmp_path, doc))
    assert r["status"] == "CANNOT VERIFY" and r["verified"] is False
    assert r["prompt_binding"] == "mismatch"
    assert r["passed"] == 0 and r["answered"] == 0


def test_unknown_test_case_ids_are_reported(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    doc["suites"][0]["testGroups"][0]["tests"].append(
        {"tcId": 10 ** 7, "ek": "00", "dk": "00"})
    r = _run(_write(tmp_path, doc))
    assert r["unknown"] and "10000000" in r["unknown"][0]
    assert r["verified"] is False


def test_raw_acvp_response_is_accepted_without_binding(tmp_path, response512):
    """A vendor whose harness already emits ACVP responses need not reshape them."""
    kg = [s for s in response512["suites"]
          if s["suite"] == "ML-KEM-keyGen-FIPS203"][0]
    raw = {"vsId": 1, "algorithm": "ML-KEM", "mode": "keyGen",
           "revision": "FIPS203", "testGroups": kg["testGroups"]}
    r = _run(_write(tmp_path, raw))
    assert r["parameter_set"] == _PS          # inferred from the tcIds
    assert r["prompt_binding"] == "absent"    # stated, not assumed
    assert r["answered"] == 25 and r["passed"] == 25
    assert r["status"] == "INCOMPLETE"        # the prompt asked for 80


def test_hex_case_and_whitespace_are_not_findings(tmp_path, response512):
    doc = json.loads(json.dumps(response512))
    for s in doc["suites"]:
        for g in s["testGroups"]:
            for t in g["tests"]:
                for k, v in t.items():
                    if k != "tcId" and isinstance(v, str):
                        t[k] = " " + v.upper() + " "
    r = _run(_write(tmp_path, doc))
    assert r["verified"] is True and r["passed"] == 80


def test_unreadable_response_is_cannot_verify(tmp_path):
    p = tmp_path / "junk.json"
    p.write_text("{not json")
    r = _run(str(p))
    assert r["status"] == "CANNOT VERIFY" and r["verified"] is False
    r = _run(str(tmp_path / "absent.json"))
    assert r["status"] == "CANNOT VERIFY"


def test_response_report_records_the_binding(tmp_path, response512):
    from pq_verify.report import to_json_response
    doc = to_json_response(_run(_write(tmp_path, response512)))
    assert doc["schema"] == "pq-verify/response-result"
    assert doc["artifact"]["bound"] is False
    assert doc["coverage"] == {"questions": 80, "answered": 80,
                               "unanswered": 0, "unknown": []}


def test_cannot_verify_and_mismatch_map_to_different_rules():
    from pq_verify.report import _rule_for, RULES
    assert _rule_for("cannot verify: 5 of 80 unanswered") == "PQV000"
    assert _rule_for("response: x tcId 1 malformed — no") == "PQV000"
    assert _rule_for("response: x tcId 1 mismatch — no") == "PQV006"
    assert RULES["PQV000"]["level"] == "warning"   # absent check, not a failure
    assert RULES["PQV006"]["level"] == "error"


# ----------------------------------------------------------------------
# Artifact binding — every report states what it was bound to
#
# `artifact` is a field, not a caveat: `sha256 <hash>` when a file was loaded,
# `none — <why>` when one was not. It is independent of the verdict: a library
# that could not be audited is still bound to the file that was read.
# ----------------------------------------------------------------------

from pq_verify.report import (
    artifact_bound,
    artifact_unbound,
    to_json,
    to_json_acvp,
    to_json_kem,
    to_sarif,
)

_SCAN = [{"name": "lib.so:ntt", "passed": 1, "total": 3,
          "findings": ["NTT: layer 3 mismatch"]}]


def test_artifact_bound_is_the_file_digest(tmp_path):
    import hashlib
    p = tmp_path / "lib.so"
    p.write_bytes(b"\x7fELF not really")
    a = artifact_bound(str(p))
    assert a["bound"] is True
    assert a["sha256"] == hashlib.sha256(p.read_bytes()).hexdigest()
    assert a["summary"] == f"sha256 {a['sha256']}"


def test_artifact_unbound_names_the_reason():
    a = artifact_unbound("vendor-supplied response")
    assert a["bound"] is False and a["sha256"] is None
    assert a["summary"] == "none — vendor-supplied response"


def test_scan_report_carries_the_binding(tmp_path):
    p = tmp_path / "lib.so"
    p.write_bytes(b"x")
    doc = to_json(_SCAN, artifact=artifact_bound(str(p)))
    assert doc["artifact"]["bound"] is True
    assert doc["artifact"]["path"] == str(p)


def test_scan_report_without_a_binding_is_unchanged():
    """Existing output must not grow a field until a caller asks for one."""
    assert "artifact" not in to_json(_SCAN)


def test_sarif_records_the_artifact_hash(tmp_path):
    p = tmp_path / "lib.so"
    p.write_bytes(b"x")
    a = artifact_bound(str(p))
    s = to_sarif(_SCAN, artifact=a)["runs"][0]
    assert s["artifacts"][0]["hashes"]["sha-256"] == a["sha256"]
    assert s["artifacts"][0]["location"]["uri"].endswith("lib.so")
    assert s["properties"]["pqVerifyArtifact"] == a["summary"]
    # the finding still points at the target, unaffected by the new field
    assert s["results"][0]["locations"][0]["physicalLocation"][
        "artifactLocation"]["uri"] == "lib.so"


def test_sarif_omits_artifacts_when_nothing_was_loaded():
    assert "artifacts" not in to_sarif(_SCAN)["runs"][0]
    s = to_sarif(_SCAN, artifact=artifact_unbound("vendor-supplied response"))
    assert "artifacts" not in s["runs"][0]
    assert s["runs"][0]["properties"]["pqVerifyArtifact"].startswith("none —")


def test_kem_audit_binds_the_file_even_when_it_cannot_be_audited(tmp_path):
    """Binding and verdict are separate facts: the file was read either way."""
    p = tmp_path / "lib.so"
    p.write_bytes(b"x")
    doc = to_json_kem(None, artifact=artifact_bound(str(p)),
                      param_set="ML-KEM-768", library=str(p))
    assert doc["artifact"]["bound"] is True
    assert doc["status"] == "CANNOT VERIFY" and doc["verified"] is False
    assert doc["findings"] and doc["findings"][0].startswith("cannot verify:")


def test_kem_audit_report_shape():
    res = {"verified": False, "passed": 55, "total": 60,
           "detail": {"keyGen": (25, 25), "encaps": (25, 25), "decaps": (5, 10)},
           "library": "/x/lib.so", "symbols": {"keypair": "kp"}}
    doc = to_json_kem(res, param_set="ML-KEM-768")
    assert doc["status"] == "FINDINGS PRESENT"
    assert doc["summary"]["checks_passed"] == 55
    assert doc["stages"]["decaps"] == {"passed": 5, "total": 10}
    assert len(doc["findings"]) == 1 and "decaps" in doc["findings"][0]
    # no file was passed, so the report says so rather than staying silent
    assert doc["artifact"]["bound"] is False


def test_acvp_report_is_explicitly_unbound():
    doc = to_json_acvp({
        "ML-KEM (FIPS 203)": {"verified": True, "passed": 240, "total": 240,
                              "detail": {"keyGen/ML-KEM-512": (25, 25)}},
        "ML-DSA (FIPS 204)": {"verified": True, "passed": 615, "total": 615,
                              "detail": {}},
    })
    assert doc["verified"] is True and doc["status"] == "VERIFIED"
    assert doc["summary"]["checks_total"] == 855
    assert doc["artifact"]["bound"] is False
    assert "no vendor binary loaded" in doc["artifact"]["summary"]
    assert doc["groups"]["ML-KEM (FIPS 203)/keyGen/ML-KEM-512"]["total"] == 25


def test_acvp_report_marks_a_suite_that_did_not_run():
    doc = to_json_acvp({"ML-DSA (FIPS 204)": None})
    assert doc["suites"]["ML-DSA (FIPS 204)"]["ran"] is False
    assert doc["status"] == "CANNOT VERIFY" and doc["verified"] is False


def test_acvp_report_is_not_verified_when_one_requested_suite_did_not_run():
    """SLH-DSA passing 624/624 must not cover for ML-KEM and ML-DSA missing."""
    doc = to_json_acvp({"ML-KEM (FIPS 203)": None, "ML-DSA (FIPS 204)": None,
                        "SLH-DSA (FIPS 205)": {"verified": True, "passed": 624,
                                               "total": 624, "detail": {}}})
    assert doc["verified"] is False and doc["status"] == "CANNOT VERIFY"
    assert doc["summary"]["not_run"] == ["ML-DSA (FIPS 204)", "ML-KEM (FIPS 203)"]


# ----------------------------------------------------------------------
# CLI exit codes — a run that did not verify must not pass a CI gate
# ----------------------------------------------------------------------

# Libraries whose behaviour is a Python callback registered in THIS process.
# The CLI audits in a child process (pq_verify.isolate), which would load the
# same .so with nothing registered, so CLI calls on these run in-process.
_IN_PROCESS_SHIMS = set()


def _cli(*argv):
    import os
    from pq_verify.cli import main
    inproc = any(a in _IN_PROCESS_SHIMS for a in argv)
    old = os.environ.get("PQV_IN_PROCESS")
    if inproc:
        os.environ["PQV_IN_PROCESS"] = "1"
    try:
        with contextlib.redirect_stdout(io.StringIO()) as out:
            code = main(list(argv))
    finally:
        if inproc:
            if old is None:
                os.environ.pop("PQV_IN_PROCESS", None)
            else:
                os.environ["PQV_IN_PROCESS"] = old
    return code, out.getvalue()


def test_unauditable_kem_library_fails_the_gate(tmp_path):
    """--audit-kem on a library with no derandomised entry points.

    This used to set a variable nothing read, so CI saw exit 0 for a library
    that was never verified at all.
    """
    import json as _json
    so = tmp_path / "empty.so"
    so.write_bytes(b"\x7fELF")
    rpt = tmp_path / "kem.json"
    code, out = _cli("--audit-kem", str(so), "ML-KEM-768",
                     "--json", str(rpt), "--fail-on-finding")
    assert code == 1
    doc = _json.loads(rpt.read_text())
    assert doc["status"] == "CANNOT VERIFY"
    assert doc["artifact"]["bound"] is True      # the file was still read


def test_json_flag_reports_when_it_writes_nothing(tmp_path):
    rpt = tmp_path / "none.json"
    code, out = _cli("--params", "ML-KEM-768", "--json", str(rpt))
    assert code == 0
    assert not rpt.exists()
    assert "wrote nothing" in out


def test_incomplete_response_fails_the_gate(tmp_path):
    import json as _json
    bad = tmp_path / "r.json"
    bad.write_text(_json.dumps({"schema": "pq-verify/acvp-response",
                                "parameterSet": "ML-KEM-512", "suites": []}))
    code, out = _cli("--verify-response", str(bad), "--fail-on-finding")
    assert code == 1
    assert "CANNOT VERIFY" in out


# ----------------------------------------------------------------------
# Python floor — the declared one and the real one must be the same
# ----------------------------------------------------------------------

def _declared_floor():
    """(major, minor) from pyproject's requires-python. Regex, not tomllib,
    because tomllib itself is 3.11+ and this test has to run at the floor."""
    import pathlib
    import re
    txt = (pathlib.Path(__file__).resolve().parent.parent
           / "pyproject.toml").read_text()
    m = re.search(r'^requires-python\s*=\s*"[^0-9]*(\d+)\.(\d+)', txt,
                  re.MULTILINE)
    assert m, "pyproject.toml has no parseable requires-python"
    return int(m.group(1)), int(m.group(2))


def _shipped_modules():
    import pathlib
    root = pathlib.Path(__file__).resolve().parent.parent / "pq_verify"
    mods = sorted(root.rglob("*.py"))
    assert len(mods) >= 5, f"expected the package's modules, found {mods}"
    return mods


def test_every_module_parses_at_the_declared_python_floor():
    """The package must actually run on the Python it advertises.

    Six f-strings in core.py carried a backslash inside the expression part,
    which is PEP 701 syntax and parses only on 3.12+. requires-python still
    said >=3.8, so pip installed happily on 3.11 and every import raised
    SyntaxError -- a claim that held right up until someone acted on it.

    This asserts metadata and code agree, so the next one fails here rather
    than in an adopter's CI.
    """
    import ast
    floor = _declared_floor()
    # Moving the floor DOWN is a claim nothing here can check: the scan below
    # is parse-only, and no interpreter older than this is on PATH to run. So
    # widening requires exercising it first, not editing one line of metadata.
    assert floor >= (3, 9), (
        f"requires-python was widened to {floor[0]}.{floor[1]}. 3.9 is the "
        f"floor CI actually runs, and the documented `pq-verify[full]` install "
        f"cannot resolve below it -- kyber-py and dilithium-py both require "
        f">=3.9. Exercise a lower version before claiming it.")
    for path in _shipped_modules():
        try:
            ast.parse(path.read_text(), filename=str(path),
                      feature_version=floor)
        except SyntaxError as exc:
            raise AssertionError(
                f"{path.name}:{exc.lineno} does not parse on Python "
                f"{floor[0]}.{floor[1]}, which pyproject.toml advertises: "
                f"{exc.msg}") from None


def _needs_precise_fstring_positions():
    """This detector is only sound on 3.12+.

    Before 3.12 an f-string's inner nodes carry the enclosing literal's
    position, so get_source_segment hands back the whole f-string and any
    escape in the LITERAL part reads as an offender. Skipping is honest;
    reporting false positives on 3.11 would not be.
    """
    import sys
    if sys.version_info < (3, 12):
        pytest.skip("f-string node positions are only exact on Python 3.12+")


def _pep701_offenders(src):
    """Backslash escapes inside f-string expression parts: 3.12+ syntax only.

    Checked by shape rather than by parsing at the floor, because
    ast.parse(feature_version=...) does NOT gate f-string tokenising -- a 3.12
    interpreter accepts PEP 701 whatever feature_version it is handed, so the
    parse-at-the-floor test above cannot see this class of defect at all.
    """
    import ast
    out = []
    for node in ast.walk(ast.parse(src)):
        if not isinstance(node, ast.JoinedStr):
            continue
        for v in node.values:
            if not isinstance(v, ast.FormattedValue):
                continue
            seg = ast.get_source_segment(src, v) or ""
            if "\\" in seg:
                out.append((v.lineno, seg))
    return out


def test_shape_guard_catches_the_bug_it_exists_for():
    """The guard is worthless if it cannot see the mutation it was written for."""
    _needs_precise_fstring_positions()
    reintroduced = '''print(f"{'\\u2705' if ok else '\\u274c'} done")'''
    assert _pep701_offenders(reintroduced), (
        "the shape guard no longer detects a backslash inside an f-string "
        "expression -- the defect it was written for could return unnoticed")
    assert not _pep701_offenders('m = OK if ok else BAD\nprint(f"{m} done")')


def test_no_glyph_escapes_remain_inside_f_string_expressions():
    """The specific defect, by shape rather than by line number."""
    _needs_precise_fstring_positions()
    for path in _shipped_modules():
        found = _pep701_offenders(path.read_text())
        assert not found, (
            f"{path.name}:{found[0][0]} puts a backslash inside an f-string "
            f"expression ({found[0][1][:40]}) -- PEP 701, 3.12+ only")


def test_package_imports_on_every_older_interpreter_present():
    """Strongest evidence available: actually run it on older Pythons.

    Skips where none are installed, so it never blocks a single-version CI,
    but turns any older interpreter on PATH into a real compatibility check.
    """
    import pathlib
    import shutil
    import subprocess
    import sys

    floor = _declared_floor()
    root = str(pathlib.Path(__file__).resolve().parent.parent)
    older = []
    for minor in range(floor[1], sys.version_info.minor):
        exe = shutil.which(f"python3.{minor}")
        if exe:
            older.append((minor, exe))
    if not older:
        pytest.skip(f"no interpreter older than 3.{sys.version_info.minor} "
                    f"on PATH at or above the declared floor 3.{floor[1]}")
    for minor, exe in older:
        r = subprocess.run(
            [exe, "-c", "import pq_verify; print(pq_verify.__version__)"],
            capture_output=True, text=True, cwd=root)
        assert r.returncode == 0, (
            f"pq-verify does not import on python3.{minor}, which "
            f"requires-python advertises:\n{r.stderr.strip()[-600:]}")


# ----------------------------------------------------------------------
# Untrusted load paths and generated-file handling
#
# Two demonstrated defects, kept as the exploits that proved them:
#   * ./libgf2_cfl.so was loaded from the working directory, and CDLL runs a
#     library's constructors -- arbitrary code execution inside the process
#     doing the verifying, in a tool whose normal use is "cd into the vendor's
#     build tree and run it".
#   * Generated C went to fixed /tmp paths, and open(path, 'w') follows
#     symlinks -- arbitrary file overwrite for any local user.
# ----------------------------------------------------------------------

def _gcc_or_skip():
    import shutil
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")


def test_engine_workdir_is_private_and_unpredictable():
    import os
    import stat
    from pq_verify.core import _pqv_workdir
    d = _pqv_workdir()
    assert os.path.isdir(d)
    mode = stat.S_IMODE(os.stat(d).st_mode)
    assert mode == 0o700, f"scratch directory is {oct(mode)}, must be 0700"
    # mkdtemp's suffix is random; a fixed name is what made the old paths
    # predictable enough to squat on
    assert os.path.basename(d) != "pqv-"
    assert _pqv_workdir() == d, "workdir must be stable within a process"


def test_no_hardcoded_tmp_paths_remain():
    """A fixed path under a world-writable directory is the whole bug class."""
    import pathlib
    import re
    src = (pathlib.Path(__file__).resolve().parent.parent
           / "pq_verify" / "core.py").read_text()
    offenders = []
    for i, line in enumerate(src.splitlines(), 1):
        if re.search(r"""['"]/tmp/""", line) and not line.lstrip().startswith("#"):
            offenders.append(f"{i}: {line.strip()[:90]}")
    assert not offenders, "fixed /tmp paths are back:\n  " + "\n  ".join(offenders)


def test_generated_sources_do_not_land_on_predictable_paths():
    import glob
    import os
    from pq_verify.core import compile_all, _pqv_workdir
    _gcc_or_skip()

    def _snapshot():
        out = {}
        for pat in ("/tmp/pqv_*.c", "/tmp/libpqv_*.so"):
            for f in glob.glob(pat):
                try:
                    out[f] = os.stat(f).st_mtime_ns
                except OSError:
                    pass
        return out

    before = _snapshot()
    compile_all()
    after = _snapshot()
    assert after == before, (
        "the run created or rewrote a fixed path under /tmp: "
        f"{sorted(set(after) ^ set(before)) or 'contents changed'}")
    wd = _pqv_workdir()
    produced = glob.glob(os.path.join(wd, "pqv_*.c"))
    assert produced, "engine sources should be written inside the private workdir"


def test_cfl_benchmark_ignores_a_library_in_the_working_directory(tmp_path,
                                                                  monkeypatch):
    """The exploit, as a test. CDLL runs constructors; this must not reach one."""
    import subprocess
    _gcc_or_skip()
    marker = tmp_path / "executed"
    src = tmp_path / "evil.c"
    src.write_text(
        '#include <stdio.h>\n'
        '__attribute__((constructor)) static void run(void) {\n'
        '    FILE *f = fopen("%s", "w");\n'
        '    if (f) { fprintf(f, "x"); fclose(f); }\n'
        '}\n' % marker)
    lib = tmp_path / "libgf2_cfl.so"
    if subprocess.run(["gcc", "-shared", "-fPIC", "-o", str(lib), str(src)],
                      capture_output=True).returncode != 0:
        pytest.skip("could not build the probe library")

    from pq_verify.core import audit_c_cfl
    monkeypatch.delenv("PQV_CFL_SO", raising=False)
    monkeypatch.chdir(tmp_path)
    with contextlib.redirect_stdout(io.StringIO()):
        r = audit_c_cfl({})
    assert not marker.exists(), (
        "a library in the working directory was loaded and its constructor ran")
    assert r is not None, "the benchmark must still report via the Python path"


def test_cfl_library_opt_in_requires_an_absolute_path(tmp_path, monkeypatch):
    from pq_verify.core import audit_c_cfl
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PQV_CFL_SO", "libgf2_cfl.so")     # relative
    with contextlib.redirect_stdout(io.StringIO()) as out:
        audit_c_cfl({})
    assert "absolute path" in out.getvalue()


def test_engine_compilation_does_not_use_a_shell():
    """os.system() meant the compiler's diagnostics went to /dev/null, where a
    broken build looked exactly like a missing compiler."""
    import pathlib
    src = (pathlib.Path(__file__).resolve().parent.parent
           / "pq_verify" / "core.py").read_text()
    for i, line in enumerate(src.splitlines(), 1):
        if line.lstrip().startswith("#"):
            continue
        assert "os.system(" not in line, f"core.py:{i} shells out: {line.strip()[:80]}"


def test_acvp_gate_fails_when_the_reference_implementations_are_missing(
        monkeypatch):
    """A broken dependency install must not report green.

    Without kyber-py and dilithium-py the ACVP suites verify nothing and report
    0/0. Until 2.7.0 `--acvp-all --fail-on-finding` exited 0 for that, so a CI
    job whose pip step silently failed looked identical to one that checked all
    855 vectors.
    """
    import sys
    from pq_verify.core import DEGRADED

    before = {k: list(v) for k, v in DEGRADED.items()}
    try:
        # make `from kyber_py... import` and `from dilithium_py... import` fail
        for mod in ("kyber_py", "kyber_py.ml_kem",
                    "dilithium_py", "dilithium_py.ml_dsa"):
            monkeypatch.setitem(sys.modules, mod, None)
        code, out = _cli("--acvp-all", "--fail-on-finding")
    finally:
        for k, v in before.items():
            DEGRADED[k][:] = v

    assert code == 1, "a run that verified nothing passed the gate"
    assert "0/0" in out
    assert "CANNOT VERIFY" in out


# ----------------------------------------------------------------------
# A response file is untrusted input
#
# --verify-response reads a file someone else produced. Three of these crashed
# with an uncaught traceback before 2.7.0. A crash is not a verdict: the tool's
# whole premise is that a check which did not run must say so, and a traceback
# says nothing at all.
# ----------------------------------------------------------------------

_MALFORMED = {
    "deep_nest":       "[" * 2000 + "]" * 2000,
    "bare_scalar":     "42",
    "bare_string":     '"hello"',
    "not_json":        "{not json at all",
    "null_groups":     {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": None}]},
    "groups_not_list": {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": {"a": 1}}]},
    "tests_scalar":    {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203",
                            "testGroups": [{"tgId": 1, "tests": 5}]}]},
    "tcid_unhashable": {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": [
                               {"tgId": 1, "tests": [{"tcId": {"a": 1}, "ek": "00"}]}]}]},
    "tcid_huge":       {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": [
                               {"tgId": 1, "tests": [{"tcId": 10 ** 400, "ek": "00"}]}]}]},
    "tcid_bool":       {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": [
                               {"tgId": 1, "tests": [{"tcId": True, "ek": "00"}]}]}]},
    "suite_not_str":   {"parameterSet": "ML-KEM-512", "suites": [
                           {"suite": 123, "testGroups": []}]},
    "paramset_object": {"parameterSet": {"x": 1}, "suites": []},
    "promptid_list":   {"parameterSet": "ML-KEM-512", "promptId": [1, 2], "suites": []},
    "artifact_weird":  {"parameterSet": "ML-KEM-512", "artifact": [1, 2, 3], "suites": []},
    "raw_nonstr_alg":  {"algorithm": 7, "mode": "keyGen", "revision": "FIPS203",
                        "testGroups": []},
}


@pytest.mark.parametrize("name", sorted(_MALFORMED))
def test_malformed_response_never_crashes_and_never_verifies(name, tmp_path):
    """The two invariants that matter for an untrusted file.

    It must not raise -- a traceback is not a verdict -- and it must never come
    back VERIFIED, because nothing in a malformed document was checked.
    """
    import json as _json
    body = _MALFORMED[name]
    p = tmp_path / "response.json"
    p.write_text(body if isinstance(body, str) else _json.dumps(body))
    r = _run(str(p))                       # raises on regression; that is the test
    assert r["verified"] is False, f"{name} reported VERIFIED"
    assert r["status"] in ("CANNOT VERIFY", "INCOMPLETE", "FINDINGS PRESENT")
    assert r["passed"] <= r["total"]


def test_oversized_answer_is_a_finding_not_a_crash(tmp_path):
    import json as _json
    p = tmp_path / "r.json"
    p.write_text(_json.dumps({"parameterSet": "ML-KEM-512", "suites": [
        {"suite": "ML-KEM-keyGen-FIPS203", "testGroups": [
            {"tgId": 1, "tests": [{"tcId": 1, "ek": "AB" * 300000, "dk": "00"}]}]}]}))
    r = _run(str(p))
    assert r["verified"] is False
    assert r["findings"]


# ----------------------------------------------------------------------
# The self-suite's own honesty
#
# pq-verify drew the cannot-verify / verified-and-failed line for everyone
# else's code (PQV000 vs PQV006) and not for its own suite. A missing coqc was
# recorded as a FAILED test, so 151/158 read as seven broken checks when
# nothing was broken -- and worse, those sites never registered with
# integrity_report(), which would announce "full coverage: every dependency
# present" while seven checks had silently not run.
# ----------------------------------------------------------------------

import contextlib as _ctx


@_ctx.contextmanager
def _isolated_degraded():
    """DEGRADED is module-global; snapshot and restore it around a test."""
    from pq_verify.core import DEGRADED
    before = {k: list(v) for k, v in DEGRADED.items()}
    for v in DEGRADED.values():
        v.clear()
    try:
        yield DEGRADED
    finally:
        for k, v in before.items():
            DEGRADED[k][:] = v


def test_a_skipped_check_is_neither_passed_nor_failed():
    from pq_verify.core import AuditResult
    with _isolated_degraded():
        r = AuditResult("probe")
        r.add_test("ran and passed", True)
        r.add_test("ran and failed", False)
        r.add_skip("could not run", "tool absent", "sometool")
        p, t, c = r.summary()
        assert (p, t) == (1, 2), "a skipped check must not be in the denominator"
        assert r.n_skipped() == 1


def test_integrity_report_sees_a_check_that_could_not_run():
    """The hole. add_skip must reach integrity_report, or a run that verified
    less than it claims will still announce full coverage."""
    from pq_verify.core import AuditResult, integrity_report
    with _isolated_degraded():
        ok, lines = integrity_report(verbose=False)
        assert ok is True, "fixture should start clean"
        r = AuditResult("probe")
        r.add_skip("could not run", "tool absent", "sometool")
        ok, lines = integrity_report(verbose=False)
        assert ok is False, "a check that did not run was invisible to integrity"
        assert any("sometool" in l for l in lines)
        assert any("could not run" in l for l in lines)


def test_missing_coq_reaches_the_integrity_report():
    """The concrete case that was broken: coqc absent used to be invisible."""
    import shutil
    from pq_verify.core import audit_coq_daemon, integrity_report
    if shutil.which("coqtop"):
        pytest.skip("coqtop is installed; this checks the absent case")
    with _isolated_degraded():
        with contextlib.redirect_stdout(io.StringIO()):
            r = audit_coq_daemon()
        assert r.n_skipped() >= 1, "absent coqtop must be a skip, not a failure"
        assert r.summary()[0] == r.summary()[1], "nothing should be marked failed"
        ok, lines = integrity_report(verbose=False)
        assert ok is False and any("coq" in l for l in lines)


@pytest.mark.slow
def test_self_suite_has_no_failing_checks():
    """Runs the whole engine stack and asserts on it.

    The suite printed a tally that nothing checked, which is how seven skipped
    checks read as failures for as long as they did. Every non-passing check
    must now be a skip that names the dependency it needs.
    """
    from pq_verify.core import main as run_selftest
    with _isolated_degraded():
        with contextlib.redirect_stdout(io.StringIO()):
            results = run_selftest(quick=True)
        assert results, "the self-suite returned nothing to assert on"
        failed = [(r.engine, t["name"], t.get("detail", ""))
                  for r in results for t in r.tests
                  if not t.get("skipped") and not t["passed"]]
        assert not failed, f"self-suite has genuine failures: {failed[:5]}"
        critical = [f for r in results for f in r.findings
                    if f["severity"] == "CRITICAL"]
        assert not critical, f"critical findings: {critical[:3]}"
        # every skip must be attributable, or it is just a quiet hole
        for r in results:
            for t in r.tests:
                if t.get("skipped"):
                    assert t.get("detail"), f"{t['name']} skipped without a reason"


# ----------------------------------------------------------------------
# Numbers claimed in the documentation
#
# The README badge read `tests 160/160` while the suite recorded 158 in CI.
# The badge was RIGHT and the correction to 158 was wrong: CI installs neither
# coq nor slh-dsa, and two checks did not exist at all without them, so the
# denominator itself moved with the environment. Measuring in an incomplete
# environment and calling the difference a stale badge is the same error in
# the opposite direction. The count is now environment-independent (see
# audit_coq_daemon and the engine-6 certificate) and the documented figure is
# 160 again.
#
# Related stale claims, both genuinely wrong: 885/885 combined ACVP (it is
# 855) and 270/270 ML-KEM (it is 240).
#
# These pin the documented numbers to measured ones.
# ----------------------------------------------------------------------

def _docs_text():
    import pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    return {p.name: p.read_text() for p in
            [root / "README.md", root / "QUICKSTART.md",
             root / "pq_verify" / "core.py", root / "pq_verify" / "__init__.py",
             root / "pq_verify" / "cli.py"]}


def test_self_suite_check_count_matches_what_the_docs_claim():
    """The documented count must be the count the suite actually records.

    quick=True changes how many iterations each check runs, not how many
    checks there are, so it measures the same total as the full suite.
    """
    import re
    from pq_verify.core import main as run_selftest, DEGRADED
    with _isolated_degraded():
        with contextlib.redirect_stdout(io.StringIO()):
            results = run_selftest(quick=True)
        if DEGRADED["engines"]:
            pytest.skip(f"engines unavailable {DEGRADED['engines']}; the count "
                        f"is only meaningful when every engine built")
    measured = sum(len(r.tests) for r in results)

    # Targeted at self-suite claims only. A count of pytest tests, or of
    # anything else that moves every commit, does not belong in prose at all --
    # "53-test pytest suite" was written one morning and was wrong by evening.
    patterns = [
        r"self--suite-(\d+)%20checks",        # the badge
        r"(\d+)-check self-suite",            # prose and the API table
        r"\*\*(\d+)/\d+\*\* self-test",      # the Proven section
        r"full (\d+)/\d+ self-suite",         # Requirements
        r"OVERALL: (\d+)/\d+ tests passed",   # QUICKSTART's expected output
        r"main\(\)\s+# (\d+)/\d+",            # core.py's usage header
        r"run the (\d+)-check self-suite",    # cli.py's usage header
    ]
    claimed = set()
    for name, text in _docs_text().items():
        for pat in patterns:
            for m in re.finditer(pat, text):
                claimed.add((name, int(m.group(1))))
    assert claimed, "no documented self-suite count found to check against"
    wrong = [(n, c) for n, c in claimed if c != measured]
    assert not wrong, (
        f"the suite records {measured} checks; these claim otherwise: {wrong}")


def test_acvp_counts_match_the_badges():
    """240 ML-KEM and 615 ML-DSA are asserted on the README badges.

    Nothing computed them either: the combined figure was documented as
    885/885 (270+615) when the real total is 855 (240+615).
    """
    import re
    pytest.importorskip("kyber_py")
    pytest.importorskip("dilithium_py")
    from pq_verify.core import pqverify_acvp, pqverify_mldsa_acvp
    with contextlib.redirect_stdout(io.StringIO()):
        kem = pqverify_acvp(verbose=False)
        dsa = pqverify_mldsa_acvp(verbose=False)
    if kem is None or dsa is None:
        pytest.skip("reference implementations unavailable")

    assert (kem["passed"], kem["total"]) == (240, 240), kem["total"]
    assert (dsa["passed"], dsa["total"]) == (615, 615), dsa["total"]

    docs = _docs_text()
    readme = docs["README.md"]
    assert "ML--KEM%20ACVP-240%2F240" in readme, "the ML-KEM badge drifted"
    assert "ML--DSA%20ACVP-615%2F615" in readme, "the ML-DSA badge drifted"

    combined = kem["total"] + dsa["total"]
    assert combined == 855
    for name, text in docs.items():
        assert "885" not in text.replace("n885", ""), (
            f"{name} still claims 885 combined vectors; it is {combined}")


def test_the_tests_badge_is_computed_not_typed():
    """A status badge GitHub renders from real runs cannot be wrong the way a
    hand-typed one can."""
    readme = _docs_text()["README.md"]
    assert "actions/workflows/tests.yml/badge.svg" in readme, (
        "the tests badge must be the workflow status badge, not a literal")
    assert "badge/tests-" not in readme, "a hand-typed tests badge is back"


# ======================================================================
# Hybrid key agreement — RFC 10024 composition (pq_verify.hybrid)
#
# The part of a post-quantum deployment that ACVP cannot reach. Both
# components can pass every NIST vector byte-for-byte while the
# concatenation is wrong, so these tests exercise the composition itself:
# the pinned orders, the offsets, and — most of all — that a wrong order is
# named as a wrong order rather than reported as an opaque mismatch.
# ======================================================================

import gzip
import json as _json
import secrets as _secrets

from pq_verify import hybrid as _hyb
from pq_verify.hybrid import (
    CURVES,
    GROUPS,
    ek_modulus_check,
    layout,
    part_size,
    verify_hybrid,
    x25519,
)

_X_BASE = b"\x09" + b"\x00" * 31


def _kem_vectors():
    """Real ML-KEM ek/ct/K from the pinned ACVP bundle, per parameter set."""
    from pq_verify.core import _bundle_path
    with gzip.open(_bundle_path(), "rt") as fh:
        bundle = _json.load(fh)
    proj = bundle["ML-KEM-encapDecap-FIPS203/internalProjection.json"]
    out = {}
    for g in proj["testGroups"]:
        if g.get("function") == "encapsulation":
            t = g["tests"][0]
            out[g["parameterSet"]] = (t["ek"], t["c"], t["k"], t["dk"])
    return out


@pytest.fixture(scope="module")
def kem_vectors():
    return _kem_vectors()


def _ecdh_keypair(ec, seed):
    if ec == "X25519":
        d = seed
        return d, x25519(d, _X_BASE)
    c = CURVES[ec]
    d = (int.from_bytes(seed, "big") % (c.n - 1)) + 1
    pt = c.mul(d, c.g)
    return (d.to_bytes(c.flen, "big"),
            b"\x04" + pt[0].to_bytes(c.flen, "big")
            + pt[1].to_bytes(c.flen, "big"))


def _agree(ec, priv, pub):
    return x25519(priv, pub) if ec == "X25519" else CURVES[ec].ecdh(priv, pub)


def _transcript(group, kem_vectors, swap_share=None, swap_secret=False,
                drop=()):
    """A genuine transcript: NIST's ML-KEM values, real ECDH, pinned layout.

    Deterministic seeds keep the fixture reproducible; these are test keys
    and exist only inside the test process.
    """
    g = GROUPS[group]
    ek, ct, k, kem_dk = (bytes.fromhex(h) for h in kem_vectors[g["kem"]])
    ec = g["ecdh"]
    n = part_size(group, "ecdh_priv")
    cd, cp = _ecdh_keypair(ec, bytes(range(1, n + 1)))
    sd, sp = _ecdh_keypair(ec, bytes(range(101, 101 + n)))
    ss_ec = _agree(ec, cd, sp)
    assert ss_ec == _agree(ec, sd, cp), "the two sides must agree"
    pool = {"kem_ek": ek, "kem_ct": ct, "kem_ss": k}

    def cat(field, mine, swap):
        order = list(g[field])
        if swap:
            order.reverse()
        return b"".join(mine.get(p, pool.get(p, b"")) for p in order)

    doc = {
        "schema": "pq-verify/hybrid-transcript",
        "group": group,
        "clientShare": cat("client_share", {"ecdh_pub": cp},
                           swap_share == "client").hex(),
        "serverShare": cat("server_share", {"ecdh_pub": sp},
                           swap_share == "server").hex(),
        "sharedSecret": cat("shared_secret", {"ecdh_ss": ss_ec},
                            swap_secret).hex(),
        "clientEcdhPrivate": cd.hex(),
        "serverEcdhPrivate": sd.hex(),
        "mlkemSharedSecret": k.hex(),
        "clientMlkemDecapsulationKey": kem_dk.hex(),
    }
    for key in drop:
        doc.pop(key, None)
    return doc


def _write_transcript(tmp_path, name, doc):
    p = tmp_path / name
    p.write_text(_json.dumps(doc))
    return str(p)


# ---- the reference this module judges with ---------------------------

def test_hybrid_reference_passes_its_published_vectors():
    """RFC 7748 §5.2/§6.1 and NIST CAVS ECC CDH for P-256 and P-384.

    A verifier whose own arithmetic is wrong would score a correct
    transcript as broken, which is worse than not running at all.
    """
    ok, total, bad = _hyb.selftest()
    assert total == 7
    assert ok == total, bad


def test_curve_parameters_are_self_validating():
    """A mistyped constant cannot survive all three properties at once."""
    for name, c in CURVES.items():
        assert c.on_curve(c.g), f"{name}: base point off the curve"
        assert c.mul(c.n, c.g) is None, f"{name}: n*G is not infinity"


def test_a_corrupted_curve_constant_is_caught():
    """Mutation guard: the import-time check must actually reject a bad b."""
    good = CURVES["P-256"]
    bad = _hyb._Curve("P-256-mutant", p=good.p, b=good.b ^ 1,
                      gx=good.g[0], gy=good.g[1], n=good.n, flen=good.flen)
    with pytest.raises(AssertionError):
        _hyb._check_curve(bad)


# ---- the pinned RFC 10024 layout -------------------------------------

def test_rfc10024_orders_are_pinned_literally():
    """The orders differ between groups, and that is the whole point.

    Written out here rather than derived, so that a change to the registry
    has to be made twice, deliberately, in two files.
    """
    expected = {
        "X25519MLKEM768": {
            "codepoint": 0x11EC,
            "client_share": ("kem_ek", "ecdh_pub"),
            "server_share": ("kem_ct", "ecdh_pub"),
            "shared_secret": ("kem_ss", "ecdh_ss"),
            "sizes": (1216, 1120, 64),
        },
        "SecP256r1MLKEM768": {
            "codepoint": 0x11EB,
            "client_share": ("ecdh_pub", "kem_ek"),
            "server_share": ("ecdh_pub", "kem_ct"),
            "shared_secret": ("ecdh_ss", "kem_ss"),
            "sizes": (1249, 1153, 64),
        },
        "SecP384r1MLKEM1024": {
            "codepoint": 0x11ED,
            "client_share": ("ecdh_pub", "kem_ek"),
            "server_share": ("ecdh_pub", "kem_ct"),
            "shared_secret": ("ecdh_ss", "kem_ss"),
            "sizes": (1665, 1665, 80),
        },
    }
    assert set(GROUPS) == set(expected)
    for name, want in expected.items():
        g = GROUPS[name]
        assert g["codepoint"] == want["codepoint"], name
        for i, field in enumerate(
                ("client_share", "server_share", "shared_secret")):
            assert tuple(g[field]) == want[field], f"{name}/{field}"
            assert g[field + "_size"] == want["sizes"][i], f"{name}/{field}"


def test_x25519mlkem768_is_the_reversed_one():
    """The named group whose order contradicts its own name.

    RFC 10024 calls this out explicitly. If this ever stops being true the
    registry is wrong, not the RFC.
    """
    assert GROUPS["X25519MLKEM768"]["client_share"][0] == "kem_ek"
    assert GROUPS["SecP256r1MLKEM768"]["client_share"][0] == "ecdh_pub"
    assert (GROUPS["X25519MLKEM768"]["shared_secret"]
            != GROUPS["SecP256r1MLKEM768"]["shared_secret"])


def test_pinned_totals_match_the_component_sums():
    """RFC 10024 states both numbers; they must agree."""
    _hyb._check_registry()
    for name, g in GROUPS.items():
        for field in ("client_share", "server_share", "shared_secret"):
            assert (sum(part_size(name, p) for p in g[field])
                    == g[field + "_size"]), f"{name}/{field}"


def test_a_wrong_pinned_size_is_caught_at_import():
    """Mutation guard: the registry check must reject a transcription error."""
    saved = GROUPS["X25519MLKEM768"]["client_share_size"]
    GROUPS["X25519MLKEM768"]["client_share_size"] = 1215
    try:
        with pytest.raises(AssertionError):
            _hyb._check_registry()
    finally:
        GROUPS["X25519MLKEM768"]["client_share_size"] = saved
    _hyb._check_registry()


# ---- FIPS 203 §7.2, against NIST's own labelled cases ----------------

def test_ek_check_agrees_with_nists_labelled_cases():
    """NIST publishes encapsulationKeyCheck cases with a pass/fail label.

    This is the check RFC 10024 makes a MUST for the server, and it is what
    makes the wrong-order diagnostic definitive rather than a guess — so it
    is checked against NIST's answers, not against itself.
    """
    from pq_verify.core import _bundle_path
    with gzip.open(_bundle_path(), "rt") as fh:
        bundle = _json.load(fh)
    proj = bundle["ML-KEM-encapDecap-FIPS203/internalProjection.json"]
    seen = 0
    for g in proj["testGroups"]:
        if g.get("function") != "encapsulationKeyCheck":
            continue
        ps = g["parameterSet"]
        if ps not in ("ML-KEM-768", "ML-KEM-1024"):
            continue
        for t in g["tests"]:
            seen += 1
            got = ek_modulus_check(bytes.fromhex(t["ek"]), ps)
            assert got == t["testPassed"], (
                f"{ps} tcId {t['tcId']}: pq-verify says {got}, "
                f"NIST says {t['testPassed']} ({t.get('reason')})")
    assert seen == 20, f"expected NIST's 20 labelled cases, saw {seen}"


def test_random_bytes_are_not_mistaken_for_an_encapsulation_key():
    """The discriminator has to actually discriminate."""
    for _ in range(8):
        assert not ek_modulus_check(_secrets.token_bytes(1184), "ML-KEM-768")


def test_ek_check_rejects_a_wrong_length():
    assert not ek_modulus_check(b"\x00" * 1183, "ML-KEM-768")


# ---- end to end -------------------------------------------------------

def _kyber_available():
    try:
        import kyber_py.ml_kem  # noqa: F401
        return True
    except ImportError:
        return False


def _assert_only_mlkem_unchecked(res):
    """Without kyber-py the ML-KEM half cannot be decapsulated: that one check
    is NOT CHECKED, the result PARTIAL -- and nothing else may be missing."""
    unchecked = [c for c in res["checks"] if c.get("kind") == "no_input"]
    assert [c["name"] for c in unchecked] == [
        c["name"] for c in res["checks"] if "decapsulates to" in c["name"]]
    assert "kyber-py not installed" in unchecked[0]["detail"]
    assert res["status"] == "PARTIAL" and res["verified"] is False


@pytest.mark.parametrize("group", sorted(GROUPS))
def test_a_conforming_transcript_verifies(group, kem_vectors, tmp_path):
    path = _write_transcript(tmp_path, "t.json", _transcript(group, kem_vectors))
    res = verify_hybrid(path, verbose=False)
    assert res["passed"] == res["total"] > 0
    if not _kyber_available():
        _assert_only_mlkem_unchecked(res)
        return
    assert res["status"] == "VERIFIED", res["findings"]
    assert res["verified"] is True
    assert res["skipped"] == 0
    assert not res["findings"]


@pytest.mark.parametrize("group", sorted(GROUPS))
def test_a_swapped_key_share_is_named_as_a_wrong_order(group, kem_vectors,
                                                       tmp_path):
    path = _write_transcript(tmp_path, "t.json",
                  _transcript(group, kem_vectors, swap_share="client"))
    res = verify_hybrid(path, verbose=False)
    assert not res["verified"]
    joined = " ".join(res["findings"])
    assert "wrong way round" in joined, res["findings"]
    assert group in joined


@pytest.mark.parametrize("group", sorted(GROUPS))
def test_a_swapped_shared_secret_is_named_as_swapped_halves(group,
                                                            kem_vectors,
                                                            tmp_path):
    path = _write_transcript(tmp_path, "t.json",
                  _transcript(group, kem_vectors, swap_secret=True))
    res = verify_hybrid(path, verbose=False)
    assert not res["verified"]

    # Asserted per check, not over the findings as a whole. Checked in
    # aggregate, this test passed with the ECDHE diagnostic disabled, because
    # the ML-KEM one said "swapped" and covered for it. Each check that can
    # detect the reversal has to say so on its own.
    by_name = {c["name"]: c for c in res["checks"]}
    ec, kem = GROUPS[group]["ecdh"], GROUPS[group]["kem"]
    must_diagnose = [f"client {ec} shared secret recomputed",
                     f"server {ec} shared secret recomputed",
                     f"sharedSecret {kem} half placement"]
    for name in must_diagnose:
        c = by_name[name]
        assert c["passed"] is False, f"{name} should have failed"
        assert "swapped" in c["detail"], f"{name}: {c['detail']}"
        # and it must say where the value SHOULD be, not just that it is wrong
        assert "RFC 10024 pins" in c["detail"], f"{name}: {c['detail']}"


def test_an_all_zero_x25519_secret_is_a_finding(kem_vectors, tmp_path):
    """RFC 10024 makes the contributory-behaviour check a MUST."""
    doc = _transcript("X25519MLKEM768", kem_vectors)
    sec = bytearray(bytes.fromhex(doc["sharedSecret"]))
    off = next(o for p, o, _n in layout("X25519MLKEM768", "shared_secret")
               if p == "ecdh_ss")
    sec[off:off + 32] = b"\x00" * 32
    doc["sharedSecret"] = bytes(sec).hex()
    res = verify_hybrid(_write_transcript(tmp_path, "z.json", doc), verbose=False)
    assert not res["verified"]
    assert any("all zero" in f for f in res["findings"]), res["findings"]


def test_a_partial_transcript_is_partial_not_verified(kem_vectors, tmp_path):
    """The skip-that-looks-like-a-pass failure mode, on this path too."""
    doc = _transcript("X25519MLKEM768", kem_vectors,
                      drop=("clientEcdhPrivate", "serverEcdhPrivate",
                            "mlkemSharedSecret"))
    res = verify_hybrid(_write_transcript(tmp_path, "p.json", doc), verbose=False)
    assert res["status"] == "PARTIAL"
    assert res["verified"] is False
    assert res["skipped"] > 0
    # and the skipped checks are not in the denominator
    assert res["passed"] == res["total"]


def test_not_applicable_is_not_the_same_as_not_checked(kem_vectors, tmp_path):
    """X25519 has no structural share check; that is not a gap in the input."""
    res = verify_hybrid(
        _write_transcript(tmp_path, "t.json", _transcript("X25519MLKEM768", kem_vectors)),
        verbose=False)
    assert res["not_applicable"] == 2
    if not _kyber_available():
        _assert_only_mlkem_unchecked(res)       # N/A still does not hold it back
        return
    assert res["skipped"] == 0
    assert res["status"] == "VERIFIED"


def test_a_wrong_length_share_is_a_finding_not_a_crash(kem_vectors, tmp_path):
    doc = _transcript("X25519MLKEM768", kem_vectors)
    doc["clientShare"] = doc["clientShare"][:-2]
    res = verify_hybrid(_write_transcript(tmp_path, "s.json", doc), verbose=False)
    assert not res["verified"]
    assert any("1216" in f for f in res["findings"]), res["findings"]


# ---- untrusted input --------------------------------------------------

_BAD_TRANSCRIPTS = {
    "not-json": "{",
    "not-an-object": "[1, 2, 3]",
    "no-group": '{"clientShare": "00"}',
    "unknown-group": '{"group": "X25519Kyber768Draft00"}',
    "group-not-a-string": '{"group": 17}',
    "group-is-null": '{"group": null}',
    "nothing-supplied": '{"group": "X25519MLKEM768"}',
    "shares-are-numbers": '{"group": "X25519MLKEM768", "clientShare": 5}',
    "shares-are-lists": '{"group": "X25519MLKEM768", "clientShare": []}',
    "odd-hex": '{"group": "X25519MLKEM768", "clientShare": "abc"}',
    "not-hex": '{"group": "X25519MLKEM768", "clientShare": "zzzz"}',
    "share-is-nested": '{"group": "X25519MLKEM768", "clientShare": {"a": 1}}',
    "private-not-a-string": ('{"group": "X25519MLKEM768", '
                             '"clientEcdhPrivate": 1, "clientShare": "00"}'),
    "deeply-nested": "[" * 300 + "]" * 300,
    "empty": "",
    "null": "null",
}


@pytest.mark.parametrize("name", sorted(_BAD_TRANSCRIPTS))
def test_malformed_transcript_never_crashes_and_never_verifies(name, tmp_path):
    p = tmp_path / "bad.json"
    p.write_text(_BAD_TRANSCRIPTS[name])
    res = verify_hybrid(str(p), verbose=False)
    assert res["verified"] is False, name
    assert res["findings"], name
    assert res["status"] in ("CANNOT VERIFY", "FINDINGS PRESENT"), name


def test_a_transcript_that_is_not_utf8_is_cannot_verify(tmp_path):
    p = tmp_path / "bin.json"
    p.write_bytes(b"\xff\xfe\x00binary")
    res = verify_hybrid(str(p), verbose=False)
    assert res["status"] == "CANNOT VERIFY"
    assert not res["verified"]


def test_a_missing_transcript_is_cannot_verify(tmp_path):
    res = verify_hybrid(str(tmp_path / "nope.json"), verbose=False)
    assert res["status"] == "CANNOT VERIFY"
    assert any("unreadable" in f for f in res["findings"])


# ---- reporting --------------------------------------------------------

def test_hybrid_report_is_explicitly_unbound(kem_vectors, tmp_path):
    from pq_verify.report import to_json_hybrid
    res = verify_hybrid(
        _write_transcript(tmp_path, "t.json", _transcript("X25519MLKEM768", kem_vectors)),
        verbose=False)
    doc = to_json_hybrid(res)
    assert doc["schema"] == "pq-verify/hybrid-result"
    assert doc["artifact"]["bound"] is False
    assert doc["artifact"]["sha256"] is None
    assert "none" in doc["artifact"]["summary"]
    assert doc["group"] == "X25519MLKEM768"
    assert doc["codepoint"] == "0x11EC"
    assert doc["specification"] == "RFC 10024"
    assert doc["transcript"]["sha256"]
    assert doc["summary"]["checks_passed"] == doc["summary"]["checks_total"]


def test_hybrid_report_separates_the_three_outcomes(kem_vectors, tmp_path):
    from pq_verify.report import to_json_hybrid
    doc = to_json_hybrid(verify_hybrid(
        _write_transcript(tmp_path, "t.json",
               _transcript("X25519MLKEM768", kem_vectors,
                           drop=("clientEcdhPrivate",))),
        verbose=False))
    kinds = {c["result"] for c in doc["checks"]}
    assert kinds <= {"pass", "fail", "not_checked", "not_applicable"}
    assert "not_checked" in kinds
    assert "not_applicable" in kinds
    # a not-run check is in neither the numerator nor the denominator
    ran = [c for c in doc["checks"] if c["result"] in ("pass", "fail")]
    assert doc["summary"]["checks_total"] == len(ran)


def test_hybrid_findings_map_to_their_own_rule():
    from pq_verify.report import _rule_for, RULES
    rid = _rule_for("hybrid: clientShare length — 3 bytes, RFC 10024 pins 1216")
    assert rid == "PQV007"
    assert RULES[rid]["name"] == "HybridCompositionMismatch"
    assert RULES[rid]["level"] == "error"
    # and it must not shadow the response rule
    assert _rule_for("response: ML-KEM tcId 1 mismatch — x") == "PQV006"


# ---- side-channel scope, on every report shape ------------------------

def test_every_report_declares_the_side_channel_scope():
    """Functional conformance says nothing about leakage, so say so.

    KyberSlash and Clangover were byte-exact correct against every vector
    and still recovered the key through timing. A report that is silent
    about this invites "verified" to be read as "safe to deploy".
    """
    from pq_verify.report import (to_json, to_json_acvp, to_json_kem,
                                  to_json_response, to_json_hybrid)
    docs = [
        to_json([{"name": "x", "passed": 1, "total": 1, "findings": []}]),
        to_json_response({"parameter_set": "ML-KEM-768"}),
        to_json_kem(None, param_set="ML-KEM-768"),
        to_json_acvp({}),
        to_json_hybrid({"group": "X25519MLKEM768"}),
    ]
    for doc in docs:
        sc = doc.get("side_channel")
        assert sc is not None, doc.get("schema")
        assert sc["measured"] is False
        assert "not measured" in sc["summary"]
        assert sc["detail"]


def test_side_channel_scope_is_not_shared_between_reports():
    """A caller mutating one report must not change the next one."""
    from pq_verify.report import to_json, SIDE_CHANNEL
    d1 = to_json([])
    d1["side_channel"]["measured"] = "tampered"
    d2 = to_json([])
    assert d2["side_channel"]["measured"] is False
    assert SIDE_CHANNEL["measured"] is False


def test_sarif_carries_the_side_channel_scope():
    from pq_verify.report import to_sarif
    props = to_sarif([])["runs"][0]["properties"]
    assert "not measured" in props["pqVerifySideChannel"]


# ---- CLI --------------------------------------------------------------

def test_cli_verify_hybrid_gate(kem_vectors, tmp_path):
    # A VERIFIED transcript needs the ML-KEM half recomputed, which needs
    # kyber-py; without it the PARTIAL path is covered above.
    pytest.importorskip("kyber_py")
    from pq_verify.cli import main as cli_main
    good = _write_transcript(tmp_path, "good.json",
                  _transcript("X25519MLKEM768", kem_vectors))
    bad = _write_transcript(tmp_path, "bad.json",
                 _transcript("X25519MLKEM768", kem_vectors, swap_secret=True))
    out = tmp_path / "r.json"
    with contextlib.redirect_stdout(io.StringIO()):
        assert cli_main(["--verify-hybrid", good, "--fail-on-finding"]) == 0
        assert cli_main(["--verify-hybrid", bad, "--fail-on-finding"]) == 1
        assert cli_main(["--verify-hybrid", good, "--json", str(out)]) == 0
    doc = _json.loads(out.read_text())
    assert doc["schema"] == "pq-verify/hybrid-result"
    assert doc["verified"] is True


def test_cli_emit_hybrid_prompt_round_trips(tmp_path):
    from pq_verify.cli import main as cli_main
    out = tmp_path / "q.json"
    with contextlib.redirect_stdout(io.StringIO()):
        assert cli_main(["--emit-hybrid-prompt", "X25519MLKEM768",
                         "--prompt-out", str(out)]) == 0
    doc = _json.loads(out.read_text())
    assert doc["schema"] == "pq-verify/hybrid-prompt"
    assert doc["codepoint"] == "0x11EC"
    assert doc["specification"] == "RFC 10024"
    # the skeleton it hands back must be the shape --verify-hybrid reads
    assert doc["response"]["schema"] == "pq-verify/hybrid-transcript"
    assert doc["response"]["group"] == "X25519MLKEM768"
    # and the documented layout must be the layout that is actually used
    for field, key in (("client_share", "clientShare"),
                       ("server_share", "serverShare"),
                       ("shared_secret", "sharedSecret")):
        got = [(e["component"], e["offset"], e["bytes"])
               for e in doc["fields"][key]["layout"]]
        assert got == layout("X25519MLKEM768", field)


def test_cli_emit_hybrid_prompt_rejects_an_unknown_group(tmp_path):
    from pq_verify.cli import main as cli_main
    with contextlib.redirect_stdout(io.StringIO()):
        assert cli_main(["--emit-hybrid-prompt", "X25519Kyber768Draft00"]) == 2


def test_the_decapsulation_key_is_optional_and_ephemeral_only():
    """The ML-KEM decapsulation key lets the ML-KEM half be recomputed, like
    the ECDHE private scalars. It is never required, and the prompt must say
    to supply an ephemeral test key, never a production one: an ephemeral key
    exposes only the one test handshake it belongs to. (Previously the key
    was never read, and a corrupted ciphertext verified.)"""
    from pq_verify.hybrid import build_hybrid_prompt
    for group in GROUPS:
        doc = build_hybrid_prompt(group)
        field = doc["fields"]["clientMlkemDecapsulationKey"]
        assert field["required"] is False
        assert all(f["required"] is False for f in doc["fields"].values())
        how = " ".join(doc["howToRespond"]).lower()
        assert "ephemeral test key, never a production key" in how
        assert '"dk"' not in _json.dumps(doc).lower()
        assert set(doc["response"]) >= {"group", "clientShare",
                                         "clientMlkemDecapsulationKey"}


# ======================================================================
# Documentation that nothing checked
#
# QUICKSTART told readers to `exec(open('pq_verify_v2_6_1.py').read())` —
# a file that has not existed since this became a pip package — and to use
# Python 3.8, below the declared floor. Both were wrong for months because
# prose is the one surface nothing executes. These guards execute it.
# ======================================================================

import pathlib as _pathlib
import re as _re

_REPO = _pathlib.Path(__file__).resolve().parent.parent
_DOCS = ("README.md", "QUICKSTART.md")


def _doc_text(name):
    p = _REPO / name
    if not p.exists():
        pytest.skip(f"{name} not present (installed package, not a checkout)")
    return p.read_text(encoding="utf-8")


@pytest.mark.parametrize("doc", _DOCS)
def test_every_documented_flag_exists(doc):
    """A flag in the docs must be a flag the parser accepts.

    Documentation is the most-read surface in the repository and the only one
    nothing runs. This runs it.
    """
    from pq_verify.cli import build_parser
    known = set()
    for action in build_parser()._actions:
        known.update(action.option_strings)
    text = _doc_text(doc)
    # Only flags on a pq-verify command line. A `pip install
    # --break-system-packages` in the same file is someone else's flag, and
    # a guard that cannot tell the difference gets switched off.
    used = set()
    for line in text.splitlines():
        line = line.strip().lstrip("$ ").rstrip("\\").strip()
        if not line.startswith("pq-verify"):
            continue
        used.update(_re.findall(r"(?<![\w-])(--[a-z][a-z0-9-]+)",
                                line.split("#")[0]))
    assert used, f"{doc} shows no pq-verify command line at all"
    unknown = sorted(f for f in used if f not in known)
    assert not unknown, f"{doc} documents flags the CLI does not have: {unknown}"


@pytest.mark.parametrize("doc", _DOCS)
def test_docs_do_not_reference_files_that_do_not_exist(doc):
    """No more `exec(open('pq_verify_v2_6_1.py').read())`."""
    text = _doc_text(doc)
    referenced = set(_re.findall(r"[\w./-]+\.(?:py|ipynb|cff|toml|yml)", text))
    present = {q.name for q in _REPO.rglob("*") if q.is_file()
               and ".git" not in q.parts}
    missing = sorted(
        r for r in referenced
        if not (_REPO / r).exists()
        and _pathlib.PurePath(r).name not in present
        and not r.startswith("your_")
    )
    assert not missing, f"{doc} points at files that do not exist: {missing}"


@pytest.mark.parametrize("doc", _DOCS)
def test_documented_python_floor_matches_the_package(doc):
    """QUICKSTART said 3.8+ while the package declared 3.9+ and meant it."""
    pyproject = _REPO / "pyproject.toml"
    if not pyproject.exists():
        pytest.skip("no pyproject.toml in this checkout")
    m = _re.search(r'requires-python\s*=\s*"[>=~^]*\s*(\d+\.\d+)',
                   pyproject.read_text(encoding="utf-8"))
    assert m, "requires-python not found in pyproject.toml"
    floor = m.group(1)
    for claimed in _re.findall(r"Python (\d+\.\d+)\+", _doc_text(doc)):
        assert claimed == floor, (
            f"{doc} claims Python {claimed}+, pyproject.toml declares {floor}+")


def test_the_hybrid_groups_the_docs_name_are_the_ones_implemented():
    """The README prints the RFC 10024 table; it has to be this table."""
    text = _doc_text("README.md")
    for name, g in GROUPS.items():
        assert name in text, f"README does not mention {name}"
        assert f"0x{g['codepoint']:04X}" in text, (
            f"README does not give the codepoint for {name}")


def test_internal_doc_links_resolve():
    """A link to a heading that does not exist is a dead end for a reader.

    Cheap to write, cheap to break: a heading gets renamed and every anchor
    pointing at it silently stops working. GitHub renders the link happily
    and scrolls nowhere.
    """
    import pathlib as _pl
    files = ("README.md", "QUICKSTART.md", "SECURITY.md", "CHANGELOG.md",
             "AUDITS.md")
    present = {n: _pl.Path(_REPO / n) for n in files
               if (_REPO / n).exists()}
    if not present:
        pytest.skip("docs not present in this checkout")

    def anchors(text):
        out = set()
        for line in text.splitlines():
            m = _re.match(r"^#{1,6}\s+(.*?)\s*$", line)
            if m:
                t = m.group(1).replace("`", "")
                out.add(_re.sub(r"[^\w\s-]", "", t).strip().lower()
                        .replace(" ", "-"))
        return out

    text = {n: p.read_text(encoding="utf-8") for n, p in present.items()}
    anch = {n: anchors(t) for n, t in text.items()}
    broken = []
    for name, body in text.items():
        for label, target in _re.findall(r"\[([^\]]+)\]\(([^)]+)\)", body):
            if target.startswith("#"):
                if target[1:] not in anch[name]:
                    broken.append(f"{name}: [{label}]({target}) — no such heading")
            elif ".md#" in target:
                f, _, a = target.partition("#")
                f = f.split("/")[-1]
                if f in anch and a not in anch[f]:
                    broken.append(f"{name}: [{label}]({target}) — no such heading in {f}")
            elif not target.startswith(("http", "mailto")):
                if not (_REPO / target).exists():
                    broken.append(f"{name}: [{label}]({target}) — file does not exist")
    assert not broken, "broken internal doc links:\n  " + "\n  ".join(broken)


# ----------------------------------------------------------------------
# Instructions live in module docstrings and templates too
#
# PR #6 rewrote QUICKSTART, which told readers to
# `exec(open('pq_verify_v2_6_1.py').read())`. The guard added with it
# scanned README.md and QUICKSTART.md — so the identical instruction
# survived in core.py's own docstring and in vendor_audit_template.py for
# another two releases. A guard that checks the files you were thinking
# about is a guard against one instance, not against the class.
#
# These scan every text-bearing file in the repository.
# ----------------------------------------------------------------------

_HISTORY_FILES = {"CHANGELOG.md", "test_pqverify.py", "SECURITY.md"}


def _repo_text_files():
    out = {}
    for q in _REPO.rglob("*"):
        if not q.is_file() or ".git" in q.parts:
            continue
        if q.suffix not in (".py", ".md", ".yml", ".yaml", ".ipynb", ".toml",
                            ".cff"):
            continue
        try:
            out[q.relative_to(_REPO).as_posix()] = q.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
    return out


def test_nothing_tells_anyone_to_exec_a_standalone_script():
    """Those files are not shipped, and the 2.6.x ones carry CWE-426/CWE-59.

    `exec(open(...))` of a version-named script is how this project was used
    before it was a package. Any surviving instruction sends a reader to an
    artifact that is not in the release, cannot be upgraded, and — for every
    2.6.x build — loads `./libgf2_cfl.so` from the working directory.
    """
    offenders = []
    pat = _re.compile(r"exec\(\s*open\(\s*['\"]pq_verify_v2[^'\"]*['\"]")
    for name, text in _repo_text_files().items():
        if _pathlib.PurePath(name).name in _HISTORY_FILES:
            continue          # these describe the defect on purpose
        for m in pat.finditer(text):
            line = text[:m.start()].count("\n") + 1
            offenders.append(f"{name}:{line}: {m.group(0)}")
    assert not offenders, (
        "instructions to exec a standalone script remain:\n  "
        + "\n  ".join(offenders))


def test_no_file_claims_a_python_floor_the_package_does_not(  ):
    """The 3.8 claim that caused the 2.6.7 incident, hunted everywhere.

    It was corrected in README and QUICKSTART and survived in
    vendor_audit_template.py, which is the file a vendor is told to edit.
    """
    pyproject = _REPO / "pyproject.toml"
    if not pyproject.exists():
        pytest.skip("no pyproject.toml in this checkout")
    m = _re.search(r'requires-python\s*=\s*"[>=~^]*\s*(\d+)\.(\d+)',
                   pyproject.read_text(encoding="utf-8"))
    assert m, "requires-python not found"
    floor = (int(m.group(1)), int(m.group(2)))
    offenders = []
    for name, text in _repo_text_files().items():
        if _pathlib.PurePath(name).name in _HISTORY_FILES:
            continue
        lines = text.splitlines()
        for mm in _re.finditer(r"Python (\d+)\.(\d+)\+", text):
            got = (int(mm.group(1)), int(mm.group(2)))
            if got == floor:
                continue
            lineno = text[:mm.start()].count("\n") + 1
            context = " ".join(lines[max(0, lineno - 2):lineno + 1]).lower()
            # "PEP 701 syntax (Python 3.12+)" states which interpreters accept
            # a language feature. That is not a claim about what this package
            # requires, and it is true. Only requirement claims are checked.
            if any(w in context for w in ("pep ", "syntax", "f-string",
                                          "backslash", "interpreter")):
                continue
            offenders.append(
                f"{name}:{lineno}: claims Python {got[0]}.{got[1]}+, "
                f"package declares {floor[0]}.{floor[1]}+")
    assert not offenders, "\n  " + "\n  ".join(offenders)


# ----------------------------------------------------------------------
# Optional Python references: a missing one is a skip that names itself
#
# kyber-py and dilithium-py are extras. Without them the ML-KEM and ML-DSA
# size and roundtrip checks have nothing to run against, which is a check
# that could not run -- not one that failed. kyber-py used to break all
# three halves of that promise at once: its absence was a FAILED row, it
# was never named in integrity_report(), and one failed row replaced three
# per-parameter-set rows so the suite total moved.
#
# The modules are blocked through sys.modules rather than skipped when
# present, so these run identically on a base install and a [dev] install.
# ----------------------------------------------------------------------

_OPTIONAL_REFERENCES = {
    "kyber-py": ("kyber_py", "kyber_py.ml_kem"),
    "dilithium-py": ("dilithium_py", "dilithium_py.ml_dsa"),
}


def _audit_rows(block, monkeypatch):
    """Run the reference-dependent audits with `block` unimportable."""
    import sys
    from pq_verify.core import (audit_fips203_params, audit_kyber_roundtrip,
                                audit_fips204_params)
    for dist in block:
        for mod in _OPTIONAL_REFERENCES[dist]:
            monkeypatch.setitem(sys.modules, mod, None)
    rows = []
    for fn in (audit_fips203_params, audit_kyber_roundtrip,
               audit_fips204_params):
        with contextlib.redirect_stdout(io.StringIO()):
            rows.extend(fn().tests)
    return rows


@pytest.mark.parametrize("missing", ["kyber-py", "dilithium-py"])
def test_a_missing_reference_library_is_skipped_and_named(missing, monkeypatch):
    from pq_verify.core import integrity_report
    with _isolated_degraded():
        rows = _audit_rows([missing], monkeypatch)
        failed = [t["name"] for t in rows
                  if not t.get("skipped") and t["passed"] is not True]
        assert not failed, f"absent {missing} reported as failure: {failed}"
        mine = [t for t in rows if t.get("dep") == missing]
        assert mine and all(t["skipped"] for t in mine)
        ok, lines = integrity_report(verbose=False)
        assert not ok
        assert any(missing in l and "dependencies missing" in l for l in lines), (
            f"{missing} is not named as missing: {lines}")


def test_the_check_set_does_not_depend_on_the_reference_libraries(monkeypatch):
    """Same names, same count, with or without the extras installed.

    The suite's documented total is only true if absence changes a row's
    status and never whether the row exists. The kyber-py path violated
    this: one failed row stood in for four.
    """
    with _isolated_degraded():
        absent = [t["name"] for t in _audit_rows(list(_OPTIONAL_REFERENCES),
                                                 monkeypatch)]
    monkeypatch.undo()
    try:
        import kyber_py.ml_kem, dilithium_py.ml_dsa  # noqa: F401
    except ImportError:
        pytest.skip("comparison needs the extras installed; the absent "
                    "half is covered by the test above")
    with _isolated_degraded():
        present = [t["name"] for t in _audit_rows([], monkeypatch)]
    assert absent == present
    assert len(absent) == 7   # 3 ML-KEM sizes + 1 roundtrip + 3 ML-DSA sizes


def test_an_installed_reference_that_errors_still_fails(monkeypatch):
    """Only the import is a skip. A broken kyber-py is a finding."""
    import types, sys
    from pq_verify.core import audit_fips203_params, audit_kyber_roundtrip

    class _Broken:
        def keygen(self):
            raise RuntimeError("simulated kyber-py fault")
    fake = types.ModuleType("kyber_py.ml_kem")
    fake.ML_KEM_512 = fake.ML_KEM_768 = fake.ML_KEM_1024 = _Broken()
    monkeypatch.setitem(sys.modules, "kyber_py", types.ModuleType("kyber_py"))
    monkeypatch.setitem(sys.modules, "kyber_py.ml_kem", fake)
    with _isolated_degraded():
        with contextlib.redirect_stdout(io.StringIO()):
            rows = audit_fips203_params().tests + audit_kyber_roundtrip().tests
    assert len(rows) == 4
    assert all(t["passed"] is False and not t.get("skipped") for t in rows)
    assert all("simulated kyber-py fault" in t["detail"] for t in rows)


def test_batch_keypair_api_separates_absent_from_broken(monkeypatch):
    """batch_verify_keypairs feeds the self-suite's Batch Verification row.

    It folded every import problem into one 'error', and the suite recorded
    any error as a failure -- so a base install printed a cross for an
    optional dependency. Absence is now flagged as 'unavailable' (a skip);
    a kyber-py that is present but broken is still an error (a failure).
    """
    import sys, types
    from pq_verify.core import batch_verify_keypairs
    monkeypatch.setitem(sys.modules, "kyber_py", None)
    monkeypatch.setitem(sys.modules, "kyber_py.ml_kem", None)
    absent = batch_verify_keypairs(2)
    assert absent.get("unavailable") is True

    broken = types.ModuleType("kyber_py")
    monkeypatch.setitem(sys.modules, "kyber_py", broken)
    monkeypatch.delitem(sys.modules, "kyber_py.ml_kem", raising=False)
    monkeypatch.setattr(broken, "__path__", [], raising=False)
    # a package that exists but whose submodule raises on import
    class _Finder:
        def find_spec(self, name, path=None, target=None):
            if name == "kyber_py.ml_kem":
                raise RuntimeError("simulated broken install")
            return None
    monkeypatch.setattr(sys, "meta_path", [_Finder()] + sys.meta_path)
    failed = batch_verify_keypairs(2)
    assert not failed.get("unavailable")
    assert "simulated broken install" in failed["error"]


# ----------------------------------------------------------------------
# --audit-kem: symbol resolution and negative (invalid-key) testing
# ----------------------------------------------------------------------

_MLKEM_NATIVE_EXPORTS = [
    "PQCP_MLKEM_NATIVE_MLKEM768_check_pk",
    "PQCP_MLKEM_NATIVE_MLKEM768_dec",
    "PQCP_MLKEM_NATIVE_MLKEM768_enc",
    "PQCP_MLKEM_NATIVE_MLKEM768_enc_derand",
    "PQCP_MLKEM_NATIVE_MLKEM768_indcpa_dec",
    "PQCP_MLKEM_NATIVE_MLKEM768_indcpa_enc",
    "PQCP_MLKEM_NATIVE_MLKEM768_indcpa_keypair_derand",
    "PQCP_MLKEM_NATIVE_MLKEM768_keypair",
    "PQCP_MLKEM_NATIVE_MLKEM768_keypair_derand",
    "PQCP_MLKEM_NATIVE_MLKEM768_poly_decompress_d10",
]


def test_kem_symbols_resolve_across_naming_schemes():
    """The old resolver took the first name containing 'keypair' and
    'derand'. On mlkem-native that is indcpa_keypair_derand, the internal
    K-PKE routine, and a correct library was reported as FINDINGS PRESENT
    (35/60). It also could not find mlkem-native's decaps (named '_dec')."""
    from pq_verify.core import _resolve_kem_symbols as res

    found, amb = res(_MLKEM_NATIVE_EXPORTS, "ML-KEM-768")
    assert not amb
    assert found == {
        "keypair": "PQCP_MLKEM_NATIVE_MLKEM768_keypair_derand",
        "encaps": "PQCP_MLKEM_NATIVE_MLKEM768_enc_derand",
        "decaps": "PQCP_MLKEM_NATIVE_MLKEM768_dec"}

    pqclean = [f"PQCLEAN_MLKEM768_CLEAN_crypto_kem_{s}" for s in
               ("keypair", "keypair_derand", "enc", "enc_derand", "dec")]
    found, amb = res(pqclean, "ML-KEM-768")
    assert not amb and found["decaps"].endswith("crypto_kem_dec")

    # liboqs exports every parameter set from one library.
    oqs = [f"OQS_KEM_ml_kem_{n}_{s}" for n in (512, 768, 1024)
           for s in ("keypair", "keypair_derand", "encaps", "encaps_derand",
                     "decaps")]
    found, amb = res(oqs, "ML-KEM-1024")
    assert not amb
    assert found == {"keypair": "OQS_KEM_ml_kem_1024_keypair_derand",
                     "encaps": "OQS_KEM_ml_kem_1024_encaps_derand",
                     "decaps": "OQS_KEM_ml_kem_1024_decaps"}

    # Two candidates for the same parameter set: refuse, do not guess.
    two = pqclean + [s.replace("CLEAN", "AVX2") for s in pqclean]
    found, amb = res(two, "ML-KEM-768")
    assert set(amb) == {"keypair", "encaps", "decaps"}
    assert found["keypair"] is None
    found, amb = res(two, "ML-KEM-768",
                     {"keypair": "a", "encaps": "b", "decaps": "c"})
    assert not amb and found == {"keypair": "a", "encaps": "b", "decaps": "c"}


_STUB_KEM = r"""
#include <stdint.h>
int stub_kem_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *c)
{ (void)pk; (void)sk; (void)c; return 0; }
int stub_kem_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *ek,
                        const uint8_t *m) {
    (void)ct; (void)ss; (void)m;
#if defined(REJECT_ALL)
    (void)ek; return -1;
#elif defined(MODULUS_CHECK)
    for (int i = 0; i < 384 * 3; i += 3) {       /* FIPS 203 7.2, k = 3 */
        uint32_t w = ek[i] | ek[i+1] << 8 | (uint32_t)ek[i+2] << 16;
        if ((w & 0xFFF) >= 3329 || (w >> 12) >= 3329) return -1;
    }
    return 0;
#else
    (void)ek; return 0;
#endif
}
int stub_kem_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *dk) {
    (void)ss; (void)ct; (void)dk;
#if defined(REJECT_ALL)
    return -1;
#else
    return 0;
#endif
}
"""


def _stub_kem(tmp_path, variant):
    import shutil, subprocess
    cc = shutil.which("cc") or shutil.which("gcc")
    if not cc:
        pytest.skip("no C compiler")
    src = tmp_path / "stub.c"
    src.write_text(_STUB_KEM)
    so = tmp_path / f"stub_{variant or 'accept'}.so"
    flags = [f"-D{variant}"] if variant else []
    subprocess.run([cc, "-shared", "-fPIC", "-O1", *flags, "-o", str(so),
                    str(src)], check=True)
    return str(so)


@pytest.mark.parametrize("variant, ek, dk", [
    (None,            (5, 5, 0), (5, 5, 0)),   # accepts everything
    ("REJECT_ALL",    (5, 0, 5), (5, 0, 5)),   # refuses everything
    ("MODULUS_CHECK", (10, 0, 0), (5, 5, 0)),  # FIPS 203 7.2 check only
])
def test_audit_kem_feeds_nist_invalid_keys(tmp_path, variant, ek, dk):
    """Each key-check vector is a pass only if the library accepts exactly
    the keys NIST marks valid. (passed, accepted_invalid, rejected_valid)."""
    from pq_verify.core import pqverify_audit_kem
    from pq_verify.report import to_json_kem
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_kem(_stub_kem(tmp_path, variant), "ML-KEM-768")
    for stage, want in (("ekCheck", ek), ("dkCheck", dk)):
        m = r["keycheck"][stage]
        got = (r["detail"][stage][0], m["accepted_invalid"], m["rejected_valid"])
        assert got == want, (stage, got)
        assert r["detail"][stage][1] == 10

    doc = to_json_kem(r, param_set="ML-KEM-768")
    text = " ".join(doc["findings"])
    assert ("accepted 5 key(s) NIST marks invalid (FIPS 203 §7.3)"
            in text) == (dk[1] == 5)
    assert ("accepted 5 key(s) NIST marks invalid (FIPS 203 §7.2)"
            in text) == (ek[1] == 5)
    assert ("rejected 5 key(s) NIST marks valid" in text) == (variant == "REJECT_ALL")


def test_accepting_invalid_keys_fails_the_gate(tmp_path):
    so = _stub_kem(tmp_path, None)
    code, out = _cli("--audit-kem", so, "ML-KEM-768", "--fail-on-finding")
    assert code == 1
    assert "accepted 5 invalid key(s)" in out


def test_kem_symbol_flags_override_detection(tmp_path):
    so = _stub_kem(tmp_path, None)
    code, out = _cli("--audit-kem", so, "ML-KEM-768",
                     "--kem-decaps", "stub_kem_dec",
                     "--kem-keypair", "stub_kem_keypair_derand",
                     "--kem-encaps", "stub_kem_enc_derand")
    assert "decaps  : stub_kem_dec" in out


# ----------------------------------------------------------------------
# CLI and report correctness: what an operator reads must be exactly right
# ----------------------------------------------------------------------

def test_audit_kem_unknown_parameter_set_is_an_input_error(tmp_path):
    """A typo'd parameter set used to raise a traceback and exit 1, which a CI
    gate reads as "this library has findings". It is an input error: exit 2,
    and name the valid sets."""
    so = tmp_path / "x.so"
    so.write_bytes(b"\x7fELF")
    code, out = _cli("--audit-kem", str(so), "ML-KEM-999")
    assert code == 2
    assert "unknown parameter set 'ML-KEM-999'" in out
    assert "ML-KEM-768" in out


def test_ntt_scan_does_not_claim_one_parameter_set():
    """An NTT acts on one polynomial and is shared by every parameter set of
    its scheme. The scan used to label every ML-KEM NTT "ML-KEM-1024" (and
    every ML-DSA NTT "ML-DSA-87"), including a 768 library's."""
    ntt = _ref_ntt_factory()
    ntt.__name__ = "poly_ntt"
    from pq_verify.core import pqverify_scan
    with contextlib.redirect_stdout(io.StringIO()) as out:
        results = pqverify_scan(ntt, ns={})
    kat = results[0]["kat"]
    assert kat["verified"] is True
    assert kat["name"] == "ML-KEM-512/768/1024"
    assert "ML-KEM-1024 NTT" not in out.getvalue()
    # An explicit k still names that set, for callers who pass one.
    with contextlib.redirect_stdout(io.StringIO()):
        assert pqverify_kat(ntt, k=3)["name"] == "ML-KEM-768"


@pytest.mark.parametrize("param_set, cited, not_cited", [
    ("ML-KEM-768", {"15c0f3d", "ad33b3d"}, {"2972def", "a7f283c", "112690e"}),
    ("ML-DSA-65", {"2972def", "a7f283c"}, {"15c0f3d", "ad33b3d", "112690e"}),
])
def test_prompt_cites_only_its_own_vector_revisions(param_set, cited, not_cited):
    from pq_verify.response import build_prompt
    src = build_prompt(param_set)["vectorSource"]
    assert all(c in src for c in cited), src
    assert not any(c in src for c in not_cited), src


def test_install_hints_do_not_recommend_breaking_system_packages():
    """Enterprise users run this in managed environments; advising
    --break-system-packages is advice to damage them. The extra exists."""
    import pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    for f in [*(root / "pq_verify").glob("*.py"), root / "README.md"]:
        assert "--break-system-packages" not in f.read_text(), f.name


def test_self_suite_prints_integrity_once(monkeypatch):
    """The self-suite prints the integrity verdict in its summary; the CLI
    must not print it a second time, but must still apply the gate."""
    import pq_verify.cli as cli
    import pq_verify.core as core

    def fake_selftest(quick=False):
        core.integrity_report()          # what the real summary does
    monkeypatch.setattr(cli, "run_selftest", fake_selftest)
    with _isolated_degraded():
        code, out = _cli("--require-full-coverage")
        assert out.count("INTEGRITY:") == 1
        assert code == 0
        core.DEGRADED["deps"].append("kyber-py")
        code, out = _cli("--require-full-coverage")
        assert code == 1
        assert out.count("DEGRADED RUN") == 1


# ----------------------------------------------------------------------
# A caller-supplied vector directory must be what is actually checked
# ----------------------------------------------------------------------

def _loose_vectors(tmp_path, prefix, corrupt=None, drop=None):
    """Write the bundled files for `prefix` as a loose directory, optionally
    corrupting one expected answer or leaving one file out."""
    import gzip, json, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    with gzip.open(root / "pq_verify" / "vectors" / "acvp_vectors.json.gz",
                   "rt") as fh:
        bundle = json.load(fh)
    for key, doc in bundle.items():
        if not key.startswith(prefix) or key == drop:
            continue
        if key == corrupt:
            doc = json.loads(json.dumps(doc))
            t = doc["testGroups"][0]["tests"][0]
            t["ek"] = ("00" if t["ek"][:2] != "00" else "11") + t["ek"][2:]
        p = tmp_path / key
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(doc))
    return str(tmp_path)


def test_vector_dir_is_read_not_shadowed_by_the_bundle(tmp_path):
    """--vector-dir used to be ignored for every file the bundle also carries:
    the bundle was consulted first by key, so a directory with a corrupted
    expected answer still reported 240/240 -- while labelling the run
    "local: <that directory>". The directory must be what is checked."""
    pytest.importorskip("kyber_py")
    from pq_verify.core import pqverify_acvp
    d = _loose_vectors(tmp_path, "ML-KEM",
                       corrupt="ML-KEM-keyGen-FIPS203/expectedResults.json")
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_acvp(vector_dir=d)
    assert r["vectors"] == f"local: {d}"
    assert (r["passed"], r["total"]) == (239, 240)
    assert r["detail"]["keyGen/ML-KEM-512"] == [24, 25]


def test_vector_dir_missing_a_file_is_an_error_not_a_bundle_fallback(tmp_path):
    from pq_verify.core import _load_vector_json
    d = _loose_vectors(tmp_path, "ML-KEM",
                       drop="ML-KEM-keyGen-FIPS203/prompt.json")
    import os
    with pytest.raises(FileNotFoundError):
        _load_vector_json(os.path.join(d, "ML-KEM-keyGen-FIPS203", "prompt.json"),
                          "ML-KEM-keyGen-FIPS203/prompt.json")


def test_pinned_directory_still_reads_the_bundle():
    import os
    from pq_verify.core import _load_vector_json, _pkg_dir
    doc = _load_vector_json(
        os.path.join(_pkg_dir(), "vectors", "ML-KEM-keyGen-FIPS203", "prompt.json"),
        "ML-KEM-keyGen-FIPS203/prompt.json")
    assert doc["algorithm"] == "ML-KEM"


# ----------------------------------------------------------------------
# tools/doctor.py: the checks a NIST re-pin must pass
# ----------------------------------------------------------------------

def _doctor():
    import importlib.util, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    path = root / "tools" / "doctor.py"
    if not path.exists():
        pytest.skip("doctor not present in this layout")
    spec = importlib.util.spec_from_file_location("pqv_doctor", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod, root


def _doctor_repo(tmp_path, history=None):
    """A throwaway repository: the real bundle, manifest and watcher state."""
    import json, shutil
    _, root = _doctor()
    repo = tmp_path / "repo"
    (repo / "pq_verify" / "vectors").mkdir(parents=True)
    (repo / "tools" / "vector_state").mkdir(parents=True)
    for f in ("acvp_vectors.json.gz", "slhdsa_sig_vectors.json.gz", "MANIFEST.json",
              "edge_vectors.json.gz", "EDGE_MANIFEST.json",
              "hbs_vectors.json.gz", "HBS_MANIFEST.json"):
        shutil.copy(root / "pq_verify" / "vectors" / f, repo / "pq_verify" / "vectors" / f)
    shutil.copy(root / "tools" / "vector_state" / "baseline.json",
                repo / "tools" / "vector_state" / "baseline.json")
    (repo / "tools" / "vector_state" / "history.json").write_text(
        json.dumps(history or {}))
    return repo


def _doctor_candidate(tmp_path, mutate):
    """ML-KEM encapDecap as NIST might publish it, after `mutate(doc)`."""
    import gzip, json
    _, root = _doctor()
    with gzip.open(root / "pq_verify" / "vectors" / "acvp_vectors.json.gz", "rt") as fh:
        bundle = json.load(fh)
    cand = tmp_path / "cand"
    for f in ("prompt.json", "expectedResults.json", "internalProjection.json"):
        name = f"ML-KEM-encapDecap-FIPS203/{f}"
        doc = json.loads(json.dumps(bundle[name]))
        mutate(doc)
        p = cand / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(doc, indent=1))       # new bytes, same schema
    return cand


def _doctor_run(repo, *argv):
    import json
    mod, _ = _doctor()
    with contextlib.redirect_stdout(io.StringIO()) as out:
        code = mod.main(["--repo", str(repo), "--json", *argv])
    doc = json.loads(out.getvalue())
    return code, doc, {c["check"]: c["status"] for c in doc["checks"]}


def test_doctor_passes_the_shipped_bundle(tmp_path):
    code, doc, st = _doctor_run(_doctor_repo(tmp_path))
    assert code == 0
    assert st["manifest"] == st["watched"] == st["keycheck:pinned"] == "ok"
    # Same inputs, same findings, same token.
    assert _doctor_run(_doctor_repo(tmp_path / "again"))[1]["token"] == doc["token"]


def test_doctor_blocks_over_length_invalid_keys(tmp_path):
    """The defect of NIST c924096, which 2.8.0 shipped: invalid encapsulation
    keys 416 bytes too long. The ACVP suite still scores 240/240 on them; the
    doctor must refuse them, and --apply must leave the bundle untouched."""
    def overlong(doc):
        for g in doc["testGroups"]:
            if g.get("function") == "encapsulationKeyCheck":
                for t in g["tests"]:
                    if "ek" in t and t.get("testPassed") is False:
                        t["ek"] += "00" * 416
    repo = _doctor_repo(tmp_path)
    bundle = repo / "pq_verify" / "vectors" / "acvp_vectors.json.gz"
    before = bundle.read_bytes()
    code, doc, st = _doctor_run(repo, "--candidate-dir",
                                str(_doctor_candidate(tmp_path, overlong)),
                                "--apply", "--commit",
                                "ML-KEM-encapDecap-FIPS203/prompt.json=c924096")
    assert code == 1
    assert st["keycheck:candidate"] == "BLOCK"
    assert st["control"] == "BLOCK"
    assert st["apply"] == "BLOCK"
    assert bundle.read_bytes() == before


def test_doctor_blocks_a_candidate_the_references_fail(tmp_path):
    pytest.importorskip("kyber_py")
    def wrong_answer(doc):
        for g in doc["testGroups"]:
            if g.get("function") == "encapsulation":
                t = g["tests"][0]
                if "k" in t:
                    t["k"] = ("00" if t["k"][:2] != "00" else "11") + t["k"][2:]
                    return
    code, doc, st = _doctor_run(_doctor_repo(tmp_path), "--candidate-dir",
                                str(_doctor_candidate(tmp_path, wrong_answer)))
    assert code == 1
    assert st["suite:ML-KEM"] == "BLOCK"
    bad = next(c for c in doc["checks"] if c["check"] == "suite:ML-KEM")
    assert "candidate 239/240 (pinned 240/240)" in bad["headline"]


def test_doctor_waits_then_pins_a_sound_change(tmp_path):
    """A sound change is still refused until it has held for STABLE_DAYS and
    its NIST commit is known; then --apply re-pins and re-checks from disk."""
    import hashlib, json
    pytest.importorskip("kyber_py")
    cand = _doctor_candidate(tmp_path, lambda doc: None)
    code, doc, st = _doctor_run(_doctor_repo(tmp_path / "young"),
                                "--candidate-dir", str(cand), "--apply")
    assert st["stable"] == "DECIDE" and st["apply"] == "BLOCK"
    assert st.get("control") == "ok" and st["keycheck:candidate"] == "ok"

    history = {}
    for f in ("prompt.json", "expectedResults.json", "internalProjection.json"):
        name = f"ML-KEM-encapDecap-FIPS203/{f}"
        sha = hashlib.sha256((cand / name).read_bytes()).hexdigest()
        history[name] = {sha: {"first_seen": "2020-01-01", "count": 9}}
    repo = _doctor_repo(tmp_path / "held", history)
    code, doc, st = _doctor_run(repo, "--candidate-dir", str(cand), "--apply",
                                *[a for f in ("prompt.json", "expectedResults.json",
                                              "internalProjection.json")
                                  for a in ("--commit",
                                            f"ML-KEM-encapDecap-FIPS203/{f}=abc1234")])
    assert code == 0, doc["next"]
    assert st["apply"] == "ok"
    assert st["after:manifest"] == st["after:keycheck:re-pinned"] == "ok"
    manifest = json.loads((repo / "pq_verify" / "vectors" / "MANIFEST.json").read_text())
    entry = manifest["ML-KEM-encapDecap-FIPS203/prompt.json"]
    assert entry["nist_commit"] == "abc1234"
    assert entry["sha256"] == hashlib.sha256(
        (cand / "ML-KEM-encapDecap-FIPS203/prompt.json").read_bytes()).hexdigest()


# ----------------------------------------------------------------------
# AUDITS.md is the pinned vendor-audit table, not a separate claim
# ----------------------------------------------------------------------

def _vendor_audit():
    import importlib.util, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    path = root / "tools" / "vendor_audit.py"
    if not path.exists():
        pytest.skip("vendor audit tool not present in this layout")
    spec = importlib.util.spec_from_file_location("pqv_vendor_audit", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod, root


def test_audits_md_matches_the_pinned_vendor_table():
    """CI re-audits every row of tools/vendor_audits.json; AUDITS.md must
    publish exactly those rows, so the document cannot claim a result CI
    does not reproduce."""
    mod, root = _vendor_audit()
    text = (root / "AUDITS.md").read_text()
    assert mod.BEGIN in text and mod.END in text
    published = text.split(mod.BEGIN, 1)[1].split(mod.END, 1)[0].strip()
    assert published == mod.markdown(mod.load_table()).strip(), (
        "AUDITS.md is out of date: paste `python3 tools/vendor_audit.py "
        "--markdown` between the vendor-audits markers")


def test_vendor_rows_are_pinned_to_full_commits():
    """A short hash or branch name would let the library move underneath the
    recorded result."""
    import re
    mod, _ = _vendor_audit()
    rows = mod.load_table()
    assert rows
    for row in rows:
        assert re.fullmatch(r"[0-9a-f]{40}", row["commit"]), row["library"]
        assert set(row["expected"]) == set(mod.STAGES), row["library"]
        assert row["build"] in ("mlkem-native", "pqclean"), row["library"]
        assert set(row["edge"]) == set(row["sets"]), row["library"]
        for ps in row["sets"]:
            assert set(row["edge"][ps]) == set(mod.EDGE_STAGES), (row["library"], ps)
# Results name the reference implementation that computed them
# ----------------------------------------------------------------------

def test_acvp_results_name_their_reference_implementation():
    """The vectors are pinned; the software answering them is whatever is
    installed. A result that omits the version is not reproducible."""
    pytest.importorskip("kyber_py")
    from importlib import metadata
    from pq_verify.core import pqverify_acvp
    from pq_verify.report import to_json_acvp
    with contextlib.redirect_stdout(io.StringIO()) as out:
        r = pqverify_acvp()
    want = f"kyber-py {metadata.version('kyber-py')}"
    assert r["reference"] == want
    assert f"reference: {want}" in out.getvalue()
    suite = to_json_acvp({"ML-KEM (FIPS 203)": r})["suites"]["ML-KEM (FIPS 203)"]
    assert suite["reference"] == want
    assert suite["vectors"].startswith("pinned (NIST ACVP-Server ")


def test_doctor_flags_references_that_differ_from_ci(tmp_path):
    mod, root = _doctor()
    (tmp_path / "constraints-reference.txt").write_text(
        "# test\nkyber-py==0.0.1\ndilithium-py==0.0.1\nslh-dsa==0.0.1\n")
    check, have = mod.check_references(tmp_path)
    if not have:
        pytest.skip("no reference implementation installed")
    assert check.status == "WARN"
    assert "(CI pins 0.0.1)" in check.headline
    assert "constraints-reference.txt" in check.fix


def test_ci_pins_every_reference_the_doctor_checks():
    mod, root = _doctor()
    pins = mod.reference_pins(root)
    assert set(mod.REFERENCES) <= set(pins), pins


def test_doctor_reports_drift_even_when_a_reference_is_missing(tmp_path, monkeypatch):
    """A missing reference implementation used to return first and hide that
    the ones present differ from CI's pins. CI caught it only because its test
    jobs lack slh-dsa; this pins the case in every environment."""
    mod, root = _doctor()
    monkeypatch.setattr(mod, "REFERENCES", mod.REFERENCES + ("pqv-not-installed",))
    (tmp_path / "constraints-reference.txt").write_text(
        "kyber-py==0.0.1\ndilithium-py==0.0.1\nslh-dsa==0.0.1\n")
    check, have = mod.check_references(tmp_path)
    if not have:
        pytest.skip("no reference implementation installed")
    assert check.status == "WARN"
    assert "(CI pins 0.0.1)" in check.headline
    assert "missing reference implementation(s):" in check.headline
    assert "pqv-not-installed" in check.headline


# ----------------------------------------------------------------------
# Untrusted input: responses and transcripts come from outside parties
# ----------------------------------------------------------------------

@pytest.mark.parametrize("order", ["wrong-then-right", "right-then-wrong",
                                   "identical-twice"])
def test_a_question_answered_twice_never_verifies(tmp_path, response512, order):
    """A second answer to the same tcId used to replace the first, so a
    response carrying a wrong answer followed by the right one VERIFIED.
    Found by tests/fuzz_readers.py."""
    import copy
    doc = copy.deepcopy(response512)
    tests = doc["suites"][0]["testGroups"][0]["tests"]
    right = copy.deepcopy(tests[0])
    wrong = copy.deepcopy(right)
    wrong["ek"] = ("00" if wrong["ek"][:2] != "00" else "11") + wrong["ek"][2:]
    pair = {"wrong-then-right": [wrong, right], "right-then-wrong": [right, wrong],
            "identical-twice": [right, copy.deepcopy(right)]}[order]
    tests[0:1] = pair
    r = _run(_write(tmp_path, doc))
    assert r["verified"] is False
    assert r["status"] == "FINDINGS PRESENT"
    tc = right["tcId"]
    assert r["duplicates"] == [f"{doc['suites'][0]['suite']} tcId {tc}"]
    assert any("answered more than once" in f for f in r["findings"])


def test_readers_survive_hostile_input():
    """A seeded slice of tests/fuzz_readers.py: every mutated response and
    transcript yields an honest result -- no exception, a known status, a
    boolean verdict, prompt termination -- and the CLI exits 0/1/2. The full
    run (thousands of cases) is `python3 tests/fuzz_readers.py`."""
    pytest.importorskip("kyber_py")
    import importlib.util, pathlib, random, tempfile
    path = pathlib.Path(__file__).resolve().parent / "fuzz_readers.py"
    spec = importlib.util.spec_from_file_location("pqv_fuzz", path)
    F = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(F)
    from pq_verify.response import verify_response
    from pq_verify.hybrid import verify_hybrid
    rng = random.Random(20260929)
    work = tempfile.mkdtemp(prefix="pqv-fuzz-test-")
    for name, fn, flag, seeds in (
            ("response", verify_response, "--verify-response", [F.seed_response()]),
            ("hybrid", verify_hybrid, "--verify-hybrid", F.seed_transcripts())):
        violations, _ = F.fuzz(name, fn, flag, seeds, 60, rng, work, cli_every=10,
                               gz=(name == "response"))
        assert not violations, violations[:5]


@pytest.mark.parametrize("case", ["truncated-gzip", "not-gzip", "gzip-bomb",
                                  "oversized-plain"])
def test_hostile_response_files_are_refused_cleanly(tmp_path, case):
    """A truncated .json.gz raised EOFError out of the CLI; an oversized or
    bomb-like file was read in full. Each is CANNOT VERIFY, exit 1/2, and
    reads at most MAX_RESPONSE_BYTES + 1 bytes."""
    import gzip
    from pq_verify.response import MAX_RESPONSE_BYTES
    body = b'{"suites": []}' * 1000
    if case == "truncated-gzip":
        p, raw = tmp_path / "r.json.gz", gzip.compress(body)[:40]
    elif case == "not-gzip":
        p, raw = tmp_path / "r.json.gz", b"not gzip at all"
    elif case == "gzip-bomb":
        # ~65 KB on disk, 65 MiB once decompressed: past the limit.
        p, raw = tmp_path / "r.json.gz", gzip.compress(b" " * (MAX_RESPONSE_BYTES + 1024))
    else:
        p, raw = tmp_path / "r.json", b" " * (MAX_RESPONSE_BYTES + 1)
    p.write_bytes(raw)
    r = _run(str(p))
    assert r["status"] == "CANNOT VERIFY" and r["verified"] is False
    if case in ("gzip-bomb", "oversized-plain"):
        assert any("larger than" in f for f in r["findings"]), r["findings"]
    code, out = _cli("--verify-response", str(p), "--fail-on-finding")
    assert code in (1, 2)


def test_oversized_transcript_is_refused_cleanly(tmp_path):
    from pq_verify.hybrid import verify_hybrid, MAX_TRANSCRIPT_BYTES
    p = tmp_path / "t.json"
    p.write_bytes(b" " * (MAX_TRANSCRIPT_BYTES + 1))
    with contextlib.redirect_stdout(io.StringIO()):
        r = verify_hybrid(str(p), verbose=False)
    assert r["status"] == "CANNOT VERIFY"
    assert any("larger than" in f for f in r["findings"]), r["findings"]


# ----------------------------------------------------------------------
# Hybrid: the ML-KEM half is recomputed, or the result is not VERIFIED
# ----------------------------------------------------------------------

def _hybrid(tmp_path, doc, name="t.json"):
    from pq_verify.hybrid import verify_hybrid
    p = _write_transcript(tmp_path, name, doc)
    with contextlib.redirect_stdout(io.StringIO()):
        return verify_hybrid(p, verbose=False)


def _kem_check(r):
    return next(c for c in r["checks"] if "decapsulates to" in c["name"])


def _flip_kem_ct(group, doc):
    from pq_verify.hybrid import layout
    off = next(o for p, o, n in layout(group, "server_share") if p == "kem_ct")
    b = bytearray(bytes.fromhex(doc["serverShare"]))
    b[off + 10] ^= 1
    doc["serverShare"] = b.hex()


@pytest.mark.parametrize("group", ["X25519MLKEM768", "SecP256r1MLKEM768",
                                   "SecP384r1MLKEM1024"])
def test_hybrid_recomputes_the_mlkem_half(tmp_path, kem_vectors, group):
    pytest.importorskip("kyber_py")
    r = _hybrid(tmp_path, _transcript(group, kem_vectors))
    assert r["status"] == "VERIFIED", r["findings"]
    assert _kem_check(r)["passed"] is True


@pytest.mark.parametrize("group", ["X25519MLKEM768", "SecP256r1MLKEM768",
                                   "SecP384r1MLKEM1024"])
def test_a_corrupted_mlkem_ciphertext_is_caught(tmp_path, kem_vectors, group):
    """Found by tests/fuzz_readers.py: one flipped ciphertext byte was reported
    VERIFIED, because nothing tied the ciphertext to the recorded secret."""
    pytest.importorskip("kyber_py")
    doc = _transcript(group, kem_vectors)
    _flip_kem_ct(group, doc)
    r = _hybrid(tmp_path, doc)
    assert r["status"] == "FINDINGS PRESENT"
    assert _kem_check(r)["passed"] is False


def test_without_the_mlkem_key_the_result_is_partial(tmp_path, kem_vectors):
    """Without the decapsulation key the ciphertext cannot be checked, so a
    corrupted one must not come back VERIFIED."""
    for corrupt in (False, True):
        doc = _transcript("X25519MLKEM768", kem_vectors,
                          drop=("clientMlkemDecapsulationKey",))
        if corrupt:
            _flip_kem_ct("X25519MLKEM768", doc)
        r = _hybrid(tmp_path, doc, f"t{corrupt}.json")
        assert r["status"] == "PARTIAL" and r["verified"] is False
        assert _kem_check(r).get("skipped") is True


def test_a_decapsulation_key_from_another_exchange_is_refused(tmp_path, kem_vectors):
    doc = _transcript("X25519MLKEM768", kem_vectors)
    # ML-KEM-768's key from a different NIST test case: valid, but not this ek.
    import gzip, json as _j
    from pq_verify.core import _bundle_path
    with gzip.open(_bundle_path(), "rt") as fh:
        proj = _j.load(fh)["ML-KEM-encapDecap-FIPS203/internalProjection.json"]
    g = next(g for g in proj["testGroups"] if g.get("function") == "encapsulation"
             and g["parameterSet"] == "ML-KEM-768")
    doc["clientMlkemDecapsulationKey"] = g["tests"][1]["dk"]
    r = _hybrid(tmp_path, doc)
    assert r["status"] == "FINDINGS PRESENT"
    assert "does not belong" in _kem_check(r)["detail"]


def test_without_kyber_the_mlkem_half_is_not_checked(tmp_path, kem_vectors, monkeypatch):
    import sys
    monkeypatch.setitem(sys.modules, "kyber_py", None)
    monkeypatch.setitem(sys.modules, "kyber_py.ml_kem", None)
    with _isolated_degraded():
        r = _hybrid(tmp_path, _transcript("X25519MLKEM768", kem_vectors))
    assert r["status"] == "PARTIAL"
    assert "kyber-py not installed" in _kem_check(r)["detail"]


# ----------------------------------------------------------------------
# Checks that could not fail, and bounds that were wrong
# ----------------------------------------------------------------------

@pytest.mark.parametrize("a,b,p,t", [(0, 3, 7, 5), (0, 4, 13, 7)])
def test_hasse_bound_accepts_the_most_extreme_legal_curves(a, b, p, t):
    """|t| <= floor(2*sqrt(p)) = isqrt(4p). The old bound 2*isqrt(p) is one
    short at p = 7 and 13, so these genuine curves were reported CRITICAL."""
    import pq_verify.core as core
    with _isolated_degraded(), contextlib.redirect_stdout(io.StringIO()):
        r = core.audit_curve({}, a, b, p)
    hasse = next(x for x in r.tests if x["name"].startswith("Hasse bound"))
    assert f"t={t}" in hasse["detail"] or f"t={-t}" in hasse["detail"]
    assert hasse["passed"] is True, hasse
    assert not [f for f in r.findings if "Hasse" in f["description"]
                or "point count" in f["description"]]
    assert not [f for f in r.findings if "Near-extreme" in f["description"]]


def _engines():
    import pq_verify.core as core
    with contextlib.redirect_stdout(io.StringIO()):
        eng = core.compile_all(); core.bind_all(eng)
    if eng.get("zq") is None:
        pytest.skip("zq engine unavailable (no C compiler)")
    return core, eng["zq"]


def _xorshift_rows(seed, rounds, n, q):
    rng, rows = seed or 42, []
    for _ in range(rounds):
        row = []
        for _ in range(n):
            rng ^= (rng << 13) & 0xFFFFFFFF
            rng ^= rng >> 17
            rng ^= (rng << 5) & 0xFFFFFFFF
            row.append(rng % q)
        rows.append(row)
    return rows


def _orthogonal_error(rows, n, q):
    """A nonzero e with row . e == 0 mod q for every row."""
    m = [r[:] for r in rows]; piv = []; rk = 0
    for c in range(n):
        p = next((i for i in range(rk, len(m)) if m[i][c]), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        inv = pow(m[rk][c], q - 2, q)
        m[rk] = [v * inv % q for v in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][c]:
                f = m[i][c]
                m[i] = [(u - f * v) % q for u, v in zip(m[i], m[rk])]
        piv.append(c); rk += 1
        if rk == len(m):
            break
    free = next(c for c in range(n) if c not in piv)
    e = [0] * n; e[free] = 1
    for i, c in enumerate(piv):
        e[c] = (-m[i][free]) % q
    return e


def test_freivalds_cannot_be_forged_against_a_published_seed(monkeypatch):
    """An output wrong in several coefficients, built so r.e = 0 for the r a
    fixed seed produces, passes Freivalds with that seed. The vendor audit
    used seed trial+1 for every run; the seed is now drawn per run."""
    import ctypes, random
    core, zq = _engines()
    Q, N, Z, rounds = 3329, 256, 17, 5
    random.seed(99)
    x = [random.randrange(Q) for _ in range(N)]
    y = (ctypes.c_uint16 * N)(*x); zq.zq_ntt_forward(y, N, Q, Z)
    e = _orthogonal_error(_xorshift_rows(1, rounds, N, Q), N, Q)
    forged = [(y[i] + e[i]) % Q for i in range(N)]
    assert sum(1 for v in e if v) > 1
    X, F = (ctypes.c_uint16 * N)(*x), (ctypes.c_uint16 * N)(*forged)
    # the attack works against the constant main used ...
    assert zq.zq_freivalds_ntt(X, F, N, Q, Z, rounds, 1) == 1
    # ... and not against this run's seed
    monkeypatch.setattr(core, "_FREIVALDS_BASE", None)
    monkeypatch.delenv("PQV_FREIVALDS_SEED", raising=False)
    assert core.freivalds_seed(0) != 1
    assert zq.zq_freivalds_ntt(X, F, N, Q, Z, rounds, core.freivalds_seed(0)) == 0


def test_freivalds_seed_is_fresh_per_run_and_replayable(monkeypatch):
    import pq_verify.core as core
    monkeypatch.delenv("PQV_FREIVALDS_SEED", raising=False)
    seen = set()
    for _ in range(4):
        monkeypatch.setattr(core, "_FREIVALDS_BASE", None)
        seen.add(core.freivalds_seed(0))
    assert len(seen) > 1, "the seed did not change between runs"
    monkeypatch.setattr(core, "_FREIVALDS_BASE", None)
    monkeypatch.setenv("PQV_FREIVALDS_SEED", "0x1234abcd")
    first = [core.freivalds_seed(i) for i in range(5)]
    assert "0x1234abcd" in core.freivalds_seed_note()
    monkeypatch.setattr(core, "_FREIVALDS_BASE", None)
    assert [core.freivalds_seed(i) for i in range(5)] == first
    assert 0 not in first and len(set(first)) == 5


def test_batch_butterfly_check_can_fail():
    """It compared (a+w*b)%q with itself and could not report a mismatch."""
    import ctypes
    core, zq = _engines()
    Q, n = 3329, 4
    a, b, w = [5, 3328, 0, 1000], [7, 3328, 1, 2000], [17, 3328, 3328, 1729]
    e = [(a[i] + w[i] * b[i]) % Q for i in range(n)]
    o = [(a[i] - w[i] * b[i]) % Q for i in range(n)]
    U = lambda v: (ctypes.c_uint16 * n)(*v)
    ok = (ctypes.c_uint8 * n)()
    assert zq.zq_batch_butterfly(U(a), U(b), U(w), U(e), U(o), ok, n, Q) == 0
    assert list(ok) == [1] * n
    e[2] = (e[2] + 1) % Q
    ok = (ctypes.c_uint8 * n)()
    assert zq.zq_batch_butterfly(U(a), U(b), U(w), U(e), U(o), ok, n, Q) == 1
    assert list(ok) == [1, 1, 0, 1]
    r = core.audit_kyber_scale(zq, n_bf=2000)
    assert r.tests[0]["passed"] is True, r.tests[0]


def _need_coqc():
    import shutil
    if shutil.which("coqc") is None:
        pytest.skip("coqc not installed")


def test_ntt_coq_certificate_covers_the_whole_transform(tmp_path):
    """The 'Full NTT' certificate held one layer-0 butterfly. It now states
    NTT(input) = output for all 256 coefficients, recomputed by Coq, and any
    single wrong coefficient is rejected."""
    _need_coqc()
    import random
    import pq_verify.core as core
    random.seed(7)
    f = [random.randrange(3329) for _ in range(256)]
    out = core._reference_ntt(f)
    good, thms = core.gen_coq_ntt_cert("ML-KEM", f, out, str(tmp_path / "g.v"))
    ok, detail = core.coq_check(good, thms)
    assert ok, detail
    for i in (0, 131, 255):
        bad = list(out); bad[i] = (bad[i] + 1) % 3329
        path, thms = core.gen_coq_ntt_cert("ML-KEM", f, bad, str(tmp_path / f"b{i}.v"))
        assert core.coq_check(path, thms)[0] is False, f"coefficient {i}"


def test_mldsa_ntt_coq_certificate(tmp_path):
    _need_coqc()
    import random
    import pq_verify.core as core
    random.seed(8)
    f = [random.randrange(8380417) for _ in range(256)]
    out = core._reference_ntt_dili(f)
    path, thms = core.gen_coq_ntt_cert("ML-DSA", f, out, str(tmp_path / "d.v"))
    ok, detail = core.coq_check(path, thms)
    assert ok, detail


def test_an_admitted_proof_is_not_a_certificate(tmp_path):
    """coqc exits 0 on Admitted. The check must not."""
    _need_coqc()
    import random
    import pq_verify.core as core
    random.seed(9)
    f = [random.randrange(3329) for _ in range(256)]
    bad = list(core._reference_ntt(f)); bad[0] = (bad[0] + 1) % 3329
    path, thms = core.gen_coq_ntt_cert("ML-KEM", f, bad, str(tmp_path / "a.v"))
    src = open(path).read()
    i = src.index(f"Theorem {thms[1]}")
    j = src.index("Proof. vm_compute. reflexivity. Qed.", i)
    src = src[:j] + "Admitted." + src[j + len("Proof. vm_compute. reflexivity. Qed."):]
    open(path, "w").write(src)
    ok, detail = core.coq_check(path, thms)
    assert ok is False and "Admitted" in detail


def test_batch_coq_certificate_proves_the_zeta_tables(tmp_path):
    _need_coqc()
    import pq_verify.core as core

    class R:  # the only attribute gen_coq_cert reads
        def __init__(self, engine): self.engine = engine
    path = core.gen_coq_cert([R("Z_3329 (Kyber)"), R("Z_8380417 (Dilithium)")],
                             str(tmp_path / "batch.v"))
    src = open(path).read()
    assert "mlkem_zeta_table" in src and "mldsa_zeta_table" in src
    assert "random" not in src.lower()
    ok, detail = core.coq_check(path)
    assert ok, detail
    # a wrong table entry is rejected
    t = core._kyber_zeta_table()
    wrong = src.replace(core._coq_list(t), core._coq_list([t[0] + 1] + t[1:]))
    (tmp_path / "wrong.v").write_text(wrong)
    assert core.coq_check(str(tmp_path / "wrong.v"))[0] is False


# ----------------------------------------------------------------------
# Wycheproof / CCTV edge-case vectors
# ----------------------------------------------------------------------

def _pin_tool():
    import importlib.util, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    path = root / "tools" / "pin_edge_vectors.py"
    if not path.exists():
        pytest.skip("pin tool not present in this layout")
    spec = importlib.util.spec_from_file_location("pqv_pin_edge", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_edge_bundle_matches_its_manifest():
    """Every stored file hashes to the digest of the file at the pinned
    Wycheproof/CCTV commit."""
    import json
    mod = _pin_tool()
    assert mod.verify() == []
    m = json.loads(mod.MANIFEST.read_text())
    for src in ("wycheproof", "cctv"):
        assert len(m["sources"][src]["commit"]) == 40
    assert len(m["files"]) == 24


def test_edge_bundle_tampering_is_detected(tmp_path):
    import gzip, json, shutil
    mod = _pin_tool()
    with gzip.open(mod.BUNDLE, "rt") as fh:
        b = json.load(fh)
    key = "cctv/ML-KEM/strcmp/ML-KEM-768.txt"
    b[key] = b[key].replace("K = ", "K = 0", 1)
    bad = tmp_path / "edge.json.gz"
    with gzip.open(bad, "wt") as fh:
        json.dump(b, fh)
    problems = mod.verify(bad, mod.MANIFEST)
    assert problems == [f"{key}: content does not match its pinned sha256"]


@pytest.mark.parametrize("ps, ek, valid", [
    ("ML-KEM-512", 883, 459), ("ML-KEM-768", 892, 461), ("ML-KEM-1024", 1156, 463)])
def test_edge_case_inventory(ps, ek, valid):
    """The counts the vendor table records. CCTV's modulus file alone tests
    every value q..4095 at every coefficient position."""
    import collections
    from pq_verify.edge import kem_cases
    c = collections.Counter(case[0] for case in kem_cases(ps))
    assert c["edgeEk"] == ek and c["edgeValid"] == valid and c["edgeDk"] == 2
    # CCTV's unlucky keys were derived with FIPS 203 ipd's G(d): never
    # checked as KeyGen output
    assert not [x for x in kem_cases(ps) if "unlucky" in x[1] and x[3] == "keygen"]
    # Wycheproof's unflagged "Public key not reduced" cases are modulus cases
    assert not [x for x in kem_cases(ps)
                if x[0] == "edgeLength" and len(x[4][0]) == {"ML-KEM-512": 800,
                    "ML-KEM-768": 1184, "ML-KEM-1024": 1568}[ps] and x[3] == "encaps"]


class _LenientKEM:
    """kyber-py with the FIPS 203 input checks stripped: what a library that
    skips §7.2/§7.3 looks like. The edge stages must see it."""
    fixed_buffers = False
    name = "lenient"

    def __init__(self, ps):
        from pq_verify.edge import ReferenceKEM
        self.r = ReferenceKEM(ps)
        self.k = self.r.k

    def keygen(self, d, z):
        return self.r.keygen(d, z)

    def keygen_seed(self, seed):
        return self.r.keygen_seed(seed)

    def encaps(self, ek, m):
        # reduce every coefficient mod q instead of refusing (no §7.2)
        n = 384 * self.k.k
        coeffs = bytearray(ek)
        for i in range(0, n, 3):
            w = coeffs[i] | coeffs[i + 1] << 8 | coeffs[i + 2] << 16
            a, b = (w & 0xFFF) % 3329, (w >> 12) % 3329
            w = a | b << 12
            coeffs[i:i + 3] = bytes((w & 0xFF, w >> 8 & 0xFF, w >> 16))
        return self.r.encaps(bytes(coeffs), m)

    def decaps(self, dk, c):
        k = self.k.k
        # recompute H(ek) instead of checking it (no §7.3)
        ek = dk[384 * k:768 * k + 32]
        dk = dk[:768 * k + 32] + self.k._H(ek) + dk[768 * k + 64:]
        return self.r.decaps(dk, c)


def test_edge_stages_catch_a_library_without_input_checks():
    pytest.importorskip("kyber_py")
    from pq_verify.edge import run_kem
    r = run_kem(_LenientKEM("ML-KEM-768"), "ML-KEM-768")
    assert r["stages"]["edgeEk"][0] == 0 and r["stages"]["edgeEk"][1] == 892
    assert r["stages"]["edgeDk"] == [0, 2]
    assert r["stages"]["edgeValid"] == [461, 461]


def test_reference_kyber_passes_every_edge_case():
    pytest.importorskip("kyber_py")
    from pq_verify.edge import reference_run
    r = reference_run()
    for ps in ("ML-KEM-512", "ML-KEM-768", "ML-KEM-1024"):
        assert r["sets"][ps]["failures"] == [], ps
        assert all(p == t for p, t in r["sets"][ps]["stages"].values()), ps


def test_dilithium_hint_defect_is_reported_not_hidden():
    """dilithium-py 1.4.0 accepts a repeated hint index (FIPS 204 Alg. 21
    requires strictly increasing). The run must say FINDINGS PRESENT and name
    the known defect; nothing else may fail."""
    pytest.importorskip("dilithium_py")
    from importlib import metadata
    from pq_verify.edge import reference_run
    r = reference_run()
    fails = [(ps, f) for ps in ("ML-DSA-44", "ML-DSA-65", "ML-DSA-87")
             for f in r["sets"][ps]["failures"]]
    if metadata.version("dilithium-py") != "1.4.0":
        pytest.skip("the known defect is pinned to dilithium-py 1.4.0")
    assert r["status"] == "FINDINGS PRESENT"
    assert len(fails) == 3
    for ps, f in fails:
        assert f["stage"] == "sigVerify" and "InvalidHintsEncoding" in f["flags"]
        assert "HintBitUnpack" in f["known_defect"]


def test_edge_cases_cli_gates_and_rejects_bad_sets():
    code, out = _cli("--edge-cases", "ML-KEM-9")
    assert code == 2 and "unknown parameter set" in out
    pytest.importorskip("dilithium_py")
    from importlib import metadata
    if metadata.version("dilithium-py") != "1.4.0":
        pytest.skip("depends on the pinned dilithium-py defect")
    code, out = _cli("--edge-cases", "ML-DSA-44", "--fail-on-finding")
    assert code == 1
    assert "known dilithium-py 1.4.0 defect" in out


@pytest.mark.parametrize("variant, ek_ok", [(None, 0), ("MODULUS_CHECK", 892)])
def test_audit_kem_runs_the_edge_cases(tmp_path, variant, ek_ok):
    """A library that never refuses an ek fails every CCTV modulus vector; one
    that performs the §7.2 check refuses all 892 -- and the report says so in
    Wycheproof/CCTV terms, not NIST's."""
    from pq_verify.core import pqverify_audit_kem
    from pq_verify.report import to_json_kem
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_kem(_stub_kem(tmp_path, variant), "ML-KEM-768")
    assert r["detail"]["edgeEk"] == (ek_ok, 892)
    doc = to_json_kem(r, param_set="ML-KEM-768")
    text = " ".join(doc["findings"])
    assert ("accepted 892 of 892 invalid encapsulation keys" in text) == (ek_ok == 0)
    assert "edgeEk" not in text or "NIST" not in text.split("edgeEk")[1].split("stage")[0]
    assert doc["edge"]["vectors"].startswith("Wycheproof ")
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_audit_kem(_stub_kem(tmp_path, variant), "ML-KEM-768", edge=False)
    assert "edgeEk" not in r["detail"]


def test_doctor_blocks_on_a_tampered_edge_bundle(tmp_path):
    import gzip, json
    mod, _ = _doctor()
    repo = _doctor_repo(tmp_path)
    p = repo / "pq_verify" / "vectors" / "edge_vectors.json.gz"
    with gzip.open(p, "rt") as fh:
        b = json.load(fh)
    b.pop(next(iter(b)))
    with gzip.open(p, "wt") as fh:
        json.dump(b, fh)
    c = mod.check_edge_manifest(repo)
    assert c.status == "BLOCK" and "EDGE_MANIFEST" in c.headline


def test_doctor_separates_known_and_new_reference_defects(monkeypatch):
    pytest.importorskip("dilithium_py")
    from importlib import metadata
    if metadata.version("dilithium-py") != "1.4.0":
        pytest.skip("depends on the pinned dilithium-py defect")
    from pq_verify import edge as EG
    mod, _ = _doctor()
    c = mod.check_reference_edges()
    assert c.status == "WARN" and "only known reference defects" in c.headline
    assert "bd9b552" in c.detail
    # the same failures, no longer recorded as known: BLOCK
    monkeypatch.setattr(EG, "KNOWN_REFERENCE_DEFECTS", {})
    run = EG.reference_run()
    stripped = {**run, "sets": {ps: {**r, "failures": [
        {k: v for k, v in f.items() if k != "known_defect"} for f in r["failures"]]}
        for ps, r in run["sets"].items()}}
    monkeypatch.setattr(EG, "reference_run", lambda: stripped)
    c = mod.check_reference_edges()
    assert c.status == "BLOCK" and "not in KNOWN_REFERENCE_DEFECTS" in c.headline


# ----------------------------------------------------------------------
# General proofs (pq_verify/coq): every input, not tested instances
# ----------------------------------------------------------------------

def _proof_copy(tmp_path, name, old, new):
    import pathlib
    src = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "coq"
    text = (src / name).read_text()
    assert old in text, old
    (tmp_path / name).write_text(text.replace(old, new, 1))
    return str(tmp_path)


def test_shipped_proofs_are_closed():
    """Every theorem in pq_verify/coq is accepted by coqc AND closed: no
    axiom, no Admitted. Covers Montgomery/Barrett/reduce32 for all inputs
    in range and the NTT = CRT map for all 256-coefficient inputs."""
    _need_coqc()
    from pq_verify.proofs import pqverify_proofs
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_proofs()
    assert r["verified"], r
    names = r["files"]["NTT.v"]["theorems"] + r["files"]["Reduce.v"]["theorems"]
    for t in ("mlkem_ntt_correct", "mldsa_ntt_correct", "mlkem_montgomery_reduce",
              "mldsa_montgomery_reduce", "mlkem_barrett_reduce", "mldsa_reduce32"):
        assert t in names


def test_a_wrong_ntt_spec_is_rejected(tmp_path):
    """Negative control: use zeta^(2*BitRev7(i)) instead of the FIPS 203
    exponent 2*BitRev7(i)+1 in the CRT spec. The proof must fail."""
    _need_coqc()
    from pq_verify.proofs import pqverify_proofs
    d = _proof_copy(tmp_path, "NTT.v",
                    "(17 ^ (2 * brv 7 (Z.of_nat i) 0 + 1))",
                    "(17 ^ (2 * brv 7 (Z.of_nat i) 0))")
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_proofs(files=("NTT.v",), coq_dir=d)
    assert r["status"] == "FINDINGS PRESENT"


def test_the_inclusive_montgomery_range_is_false(tmp_path):
    """ML-KEM's montgomery_reduce returns q itself at a = q*2^15, which is
    why ref/reduce.c stops its range at q*2^15 - 1. Widening the theorem to
    include that point must make it unprovable."""
    _need_coqc()
    from pq_verify.proofs import pqverify_proofs
    d = _proof_copy(tmp_path, "Reduce.v",
                    "- (KQ * 2^15) <= a <= KQ * 2^15 - 1 ->",
                    "- (KQ * 2^15) <= a <= KQ * 2^15 ->")
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_proofs(files=("Reduce.v",), coq_dir=d)
    assert r["status"] == "FINDINGS PRESENT"


def test_an_admitted_general_proof_is_refused(tmp_path):
    _need_coqc()
    from pq_verify.proofs import pqverify_proofs
    d = _proof_copy(tmp_path, "Reduce.v",
                    "Theorem mldsa_qinv : (DQ * DQINV) mod 2^32 = 1.\nProof. vm_compute. reflexivity. Qed.",
                    "Theorem mldsa_qinv : (DQ * DQINV) mod 2^32 = 1.\nAdmitted.")
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_proofs(files=("Reduce.v",), coq_dir=d)
    assert r["status"] == "FINDINGS PRESENT"
    assert "Admitted" in r["files"]["Reduce.v"]["detail"]


def test_reduction_edge_witnesses_match_c_semantics():
    """The two off-by-one points the proofs found in ref/reduce.c's
    documented contracts, recomputed with C integer semantics."""
    def trunc(x, bits):
        x &= (1 << bits) - 1
        return x - (1 << bits) if x >> (bits - 1) else x
    Q = 8380417
    mont32 = lambda a: (a - trunc(a * 58728449, 32) * Q) >> 32
    reduce32 = lambda a: a - ((a + (1 << 22)) >> 23) * Q
    assert mont32(Q * 2**31) == Q                       # documented: -Q < r < Q
    assert reduce32(-255 * 2**23 - 2**22) == -6283009   # documented: r >= -6283008
    mont16 = lambda a: (a - trunc(a * -3327, 16) * 3329) >> 16
    assert mont16(3329 * 2**15) == 3329                 # outside ML-KEM's stated range


def test_no_proof_tool_is_cannot_verify(monkeypatch):
    import shutil
    from pq_verify import proofs
    monkeypatch.setattr(shutil, "which", lambda name: None)
    with contextlib.redirect_stdout(io.StringIO()):
        r = proofs.pqverify_proofs()
    assert r["status"] == "CANNOT VERIFY" and r["verified"] is False


def test_per_run_certificates_use_the_proved_transform():
    """The per-run NTT certificate must define the transform with NTT.v's
    shared block, verbatim, so it is about the proved definition."""
    import pathlib
    from pq_verify.core import _coq_ntt_prelude
    src = (pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "coq" / "NTT.v").read_text()
    shared = src[src.index("(* BEGIN SHARED"):src.index("(* END SHARED *)")]
    assert shared in _coq_ntt_prelude(3329, 17, 7, 7)


# ----------------------------------------------------------------------
# SLH-DSA signatures (FIPS 205 sigVer and sigGen)
#
# NIST's SLH-DSA signature vectors are pinned verbatim in their own archive,
# opened only by the SLH-DSA suite. sigVer (504) runs by default; sigGen
# (624 byte-exact signatures, ~30 min) is opt-in and runs weekly in CI. The
# negative controls show each check can fail: a verifier that accepts or
# rejects everything, a message encoding that drops the context, a signer
# that ignores NIST's randomness.
# ----------------------------------------------------------------------

def _slh_docs(mode):
    from pq_verify.core import _load_vector_json, _pkg_dir
    import os
    d = f"SLH-DSA-{mode}-FIPS205"
    base = os.path.join(_pkg_dir(), "vectors", d)
    return (_load_vector_json(os.path.join(base, "prompt.json"), f"{d}/prompt.json"),
            _load_vector_json(os.path.join(base, "expectedResults.json"),
                              f"{d}/expectedResults.json"))


def _slh_sigver(**kw):
    pytest.importorskip("slhdsa")
    from pq_verify.core import pqverify_slhdsa_acvp
    with contextlib.redirect_stdout(io.StringIO()):
        return pqverify_slhdsa_acvp(verbose=False, keygen=False, **kw)


def test_slhdsa_sigver_matches_every_nist_verdict():
    r = _slh_sigver()
    assert (r["passed"], r["total"]) == (504, 504), r["failures"][:5]
    assert r["modes"] == ["sigVer"]
    assert "112690e" in r["vectors"]
    # every interface and both hash families are in the denominator
    labels = set(r["detail"])
    for iface in ("internal", "pure", "preHash"):
        for ps in ("SLH-DSA-SHA2-128s", "SLH-DSA-SHAKE-256f"):
            assert f"sigVer/{ps}/{iface}" in labels


@pytest.mark.parametrize("verdict, want_failures", [(True, 432), (False, 72)])
def test_slhdsa_sigver_control_constant_verifier_fails(monkeypatch, verdict,
                                                       want_failures):
    """A verifier that ignores its input must fail exactly NIST's cases of the
    other verdict: 72 valid signatures, 432 invalid ones (modified message,
    R, FORS and hypertree parts, one byte short, one byte long)."""
    LL = pytest.importorskip("slhdsa.lowlevel.slhdsa")
    monkeypatch.setattr(LL, "verify", lambda *a, **k: verdict)
    r = _slh_sigver()
    assert r["total"] - r["passed"] == want_failures


def test_slhdsa_sigver_control_message_encoding_is_checked(monkeypatch):
    """Dropping the context from M' (FIPS 205 Alg. 24/25) must fail NIST's
    valid external signatures with a non-empty context: pq-verify builds M'
    itself, so the encoding is under test, not the library's wrapper."""
    from pq_verify import core
    real = core._slhdsa_message

    def no_ctx(g, t):
        return real(g, dict(t, context=""))
    monkeypatch.setattr(core, "_slhdsa_message", no_ctx)
    r = _slh_sigver()
    p, _ = _slh_docs("sigVer")
    _, e = _slh_docs("sigVer")
    passed = {str(t["tcId"]): t["testPassed"] for g in e["testGroups"] for t in g["tests"]}
    want = sum(1 for g in p["testGroups"] if g["signatureInterface"] == "external"
               for t in g["tests"] if t["context"] and passed[str(t["tcId"])])
    assert want > 0 and r["total"] - r["passed"] == want


def test_slhdsa_prehash_oids_are_fips205_der():
    """FIPS 205 §10.2.2: the OID is DER 06 09 60 86 48 01 65 03 04 02 xx."""
    from pq_verify.core import _slhdsa_message, _SLHDSA_PREHASH
    import hashlib
    want = {"SHA2-256": 0x01, "SHA2-384": 0x02, "SHA2-512": 0x03, "SHA2-224": 0x04,
            "SHA2-512/224": 0x05, "SHA2-512/256": 0x06, "SHA3-224": 0x07,
            "SHA3-256": 0x08, "SHA3-384": 0x09, "SHA3-512": 0x0A,
            "SHAKE-128": 0x0B, "SHAKE-256": 0x0C}
    assert {k: v[0] for k, v in _SLHDSA_PREHASH.items()} == want
    g = {"signatureInterface": "external", "preHash": "preHash"}
    m = _slhdsa_message(g, {"message": "616263", "context": "0102", "hashAlg": "SHA2-256"})
    assert m == (b"\x01\x02\x01\x02" + bytes.fromhex("0609608648016503040201")
                 + hashlib.sha256(b"abc").digest())
    m = _slhdsa_message({"signatureInterface": "external", "preHash": "pure"},
                        {"message": "616263", "context": ""})
    assert m == b"\x00\x00abc"
    assert _slhdsa_message({"signatureInterface": "internal"},
                           {"message": "616263"}) == b"abc"
    with pytest.raises(ValueError):
        _slhdsa_message(g, {"message": "", "context": "00" * 256, "hashAlg": "SHA2-256"})


def _slh_siggen_cases(param_set):
    p, e = _slh_docs("sigGen")
    sig = {str(t["tcId"]): t["signature"] for g in e["testGroups"] for t in g["tests"]}
    out = []
    for g in p["testGroups"]:
        if g["parameterSet"] == param_set:
            t = g["tests"][0]
            out.append((g, t, sig[str(t["tcId"])]))
    return out


@pytest.mark.parametrize("param_set", ["SLH-DSA-SHA2-128f", "SLH-DSA-SHAKE-128f"])
def test_slhdsa_siggen_is_byte_exact_for_every_interface(param_set):
    """One NIST case per group (internal, pure, pre-hash; deterministic and
    randomised) signed byte-exact. The full 624 run weekly."""
    pytest.importorskip("slhdsa")
    from pq_verify.core import _slhdsa_sign_internal, _slhdsa_message
    import slhdsa.lowlevel.parameters as LP
    par = getattr(LP, param_set.replace("SLH-DSA-", "").replace("-", "_").lower())
    cases = _slh_siggen_cases(param_set)
    assert len(cases) == 6
    for g, t, want in cases:
        addrnd = None if g["deterministic"] else bytes.fromhex(t["additionalRandomness"])
        got = _slhdsa_sign_internal(_slhdsa_message(g, t), bytes.fromhex(t["sk"]),
                                    addrnd, par)
        assert got.hex().upper() == want.upper(), (g["tgId"], t["tcId"])


def test_slhdsa_siggen_control_randomness_is_used():
    """A signer that ignores additionalRandomness signs deterministically, so
    it must miss every randomised case and still match every deterministic one."""
    pytest.importorskip("slhdsa")
    from pq_verify.core import _slhdsa_sign_internal, _slhdsa_message
    import slhdsa.lowlevel.parameters as LP
    for g, t, want in _slh_siggen_cases("SLH-DSA-SHA2-128f"):
        got = _slhdsa_sign_internal(_slhdsa_message(g, t), bytes.fromhex(t["sk"]),
                                    None, LP.sha2_128f)
        assert (got.hex().upper() == want.upper()) == bool(g["deterministic"])


def test_slhdsa_siggen_suite_runs_from_a_vector_dir(tmp_path):
    """The opt-in suite end to end, on one fast parameter set, through
    --vector-dir; a corrupted expected signature is a failure, not a pass."""
    pytest.importorskip("slhdsa")
    import json
    from pq_verify.core import pqverify_slhdsa_acvp
    p, e = _slh_docs("sigGen")
    keep = {g["tgId"] for g in p["testGroups"] if g["parameterSet"] == "SLH-DSA-SHA2-128f"}
    p2 = dict(p, testGroups=[g for g in p["testGroups"] if g["tgId"] in keep])
    e2 = json.loads(json.dumps(dict(e, testGroups=[g for g in e["testGroups"]
                                                   if g["tgId"] in keep])))
    sig = e2["testGroups"][0]["tests"][0]["signature"]
    e2["testGroups"][0]["tests"][0]["signature"] = ("00" if sig[:2] != "00" else "11") + sig[2:]
    d = tmp_path / "SLH-DSA-sigGen-FIPS205"
    d.mkdir()
    (d / "prompt.json").write_text(json.dumps(p2))
    (d / "expectedResults.json").write_text(json.dumps(e2))
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_slhdsa_acvp(vector_dir=str(tmp_path), verbose=False,
                                 keygen=False, sigver=False, siggen=True)
    n = sum(len(g["tests"]) for g in p2["testGroups"])
    assert r["modes"] == ["sigGen"] and r["total"] == n
    assert r["passed"] == n - 1 and len(r["failures"]) == 1


def test_slhdsa_signature_archive_is_opened_only_when_needed():
    """ML-KEM and ML-DSA runs never decompress the 39 MB SLH-DSA archive."""
    import subprocess, sys, pathlib
    root = pathlib.Path(__file__).resolve().parent.parent
    code = (
        "import os\n"
        "from pq_verify import core\n"
        "d = os.path.join(core._pkg_dir(), 'vectors', 'ML-KEM-keyGen-FIPS203')\n"
        "core._load_vector_json(os.path.join(d, 'prompt.json'), 'ML-KEM-keyGen-FIPS203/prompt.json')\n"
        "assert list(core._VECTOR_BUNDLE_CACHE) == ['acvp_vectors.json.gz'], core._VECTOR_BUNDLE_CACHE.keys()\n"
        "d = os.path.join(core._pkg_dir(), 'vectors', 'SLH-DSA-sigVer-FIPS205')\n"
        "doc = core._load_vector_json(os.path.join(d, 'expectedResults.json'), 'SLH-DSA-sigVer-FIPS205/expectedResults.json')\n"
        "assert 'slhdsa_sig_vectors.json.gz' in core._VECTOR_BUNDLE_CACHE\n"
        "assert doc['testGroups'][0]['tests'][0]['tcId'] == 1\n"
    )
    r = subprocess.run([sys.executable, "-c", code], cwd=root,
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr


def test_slhdsa_signature_archive_is_nist_verbatim():
    """Each entry hashes to MANIFEST.json's sha256: NIST's bytes, offline."""
    import gzip, hashlib, json, pathlib
    vec = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "vectors"
    manifest = json.loads((vec / "MANIFEST.json").read_text())
    with gzip.open(vec / "slhdsa_sig_vectors.json.gz", "rt") as fh:
        arc = json.load(fh)
    assert sorted(arc) == [f"SLH-DSA-{m}-FIPS205/{f}" for m in ("sigGen", "sigVer")
                           for f in ("expectedResults.json", "prompt.json")]
    for k, text in arc.items():
        assert isinstance(text, str)
        assert hashlib.sha256(text.encode()).hexdigest() == manifest[k]["sha256"], k
        assert manifest[k]["nist_commit"] == "112690e"


def test_doctor_blocks_an_altered_verbatim_vector_file(tmp_path):
    """A verbatim entry whose bytes no longer match its pinned sha256 is caught
    offline, even when it still parses and has the same tests."""
    import gzip, json
    D, _ = _doctor()
    repo = _doctor_repo(tmp_path)
    arc = repo / "pq_verify" / "vectors" / "slhdsa_sig_vectors.json.gz"
    with gzip.open(arc, "rt") as fh:
        entries = json.load(fh)
    k = "SLH-DSA-sigVer-FIPS205/expectedResults.json"
    entries[k] = entries[k].replace('"testPassed": false', '"testPassed": true', 1)
    D.write_bundle(arc, entries, verbatim=True)
    code, doc, st = _doctor_run(repo, "--fast")
    assert code == 1 and st["manifest"] == "BLOCK"
    detail = next(c for c in doc["checks"] if c["check"] == "manifest")["detail"]
    assert k in detail and "sha256" in detail


def test_doctor_repin_rewrites_only_the_archive_that_changed(tmp_path):
    """Re-pinning an SLH-DSA signature file rewrites that archive, verbatim,
    and leaves the main archive byte-identical."""
    import gzip, hashlib, json
    D, _ = _doctor()
    repo = _doctor_repo(tmp_path)
    P = D.paths(repo)
    main_before = P["bundle"].read_bytes()
    bundle, manifest = D.load_bundle(P["bundles"]), json.loads(P["manifest"].read_text())
    k = "SLH-DSA-sigVer-FIPS205/expectedResults.json"
    raw = bundle[k].replace("\n", "\r\n").encode()          # new bytes, same content
    D.apply_candidate(repo, bundle, manifest, {k: raw}, {k: {"sha": "abcdef1"}})
    assert P["bundle"].read_bytes() == main_before
    with gzip.open(P["bundles"]["slhdsa_sig_vectors.json.gz"], "rt", newline="") as fh:
        assert json.load(fh)[k].encode() == raw
    m = json.loads(P["manifest"].read_text())[k]
    assert m == {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
                 "nist_commit": "abcdef1"}
    code, doc, st = _doctor_run(repo, "--fast")
    assert st["manifest"] == "ok"


def test_main_archive_is_rewritten_byte_identically():
    """write_bundle reproduces the shipped main archive exactly, so a re-pin's
    diff is only the change."""
    import gzip, json, tempfile, pathlib
    D, root = _doctor()
    src = root / "pq_verify" / "vectors" / "acvp_vectors.json.gz"
    with gzip.open(src, "rt") as fh:
        entries = json.load(fh)
    with tempfile.TemporaryDirectory() as d:
        out = pathlib.Path(d) / "acvp_vectors.json.gz"
        D.write_bundle(out, entries, verbatim=False)
        assert out.read_bytes() == src.read_bytes()


def test_slhdsa_counts_match_the_docs():
    """1248 = keyGen 120 + sigVer 504 + sigGen 624, and 1566 = 855 + 624 +
    87 LMS, counted from the pinned prompts, not typed."""
    n = {m: sum(len(g["tests"]) for g in _slh_docs(m)[0]["testGroups"])
         for m in ("sigVer", "sigGen")}
    from pq_verify.core import _load_bundle
    kg = _load_bundle()["SLH-DSA-keyGen-FIPS205/prompt.json"]
    n["keyGen"] = sum(len(g["tests"]) for g in kg["testGroups"])
    assert n == {"keyGen": 120, "sigVer": 504, "sigGen": 624}
    readme = _docs_text()["README.md"]
    assert "SLH--DSA%20ACVP-1248%2F1248" in readme
    assert "1566/1566" in readme and "2190/2190" in readme
    assert 855 + n["keyGen"] + n["sigVer"] + 87 == 1566        # + NIST LMS
    assert 1566 + n["sigGen"] == 2190


# ----------------------------------------------------------------------
# --audit-dsa: a vendor's own ML-DSA keygen/sign/verify
#
# The pinned libraries (mldsa-native, pq-crystals ref, PQClean) and their
# mutants run in CI (tools/vendor_audit.py). Here a C shim with the
# pq-crystals ABI, linked with the randomness harness and backed by
# dilithium-py, exercises the same ctypes path offline, and plants faults.
# ----------------------------------------------------------------------

def _dsa_shim(tmp_path, keypair=None, sign=None, verify=None, extra_rng=0):
    """Build the shim, register dilithium-py-backed callbacks (each
    overridable), return (path, keepalive)."""
    import ctypes as C, pathlib, shutil, subprocess
    pytest.importorskip("dilithium_py")
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")
    from dilithium_py.ml_dsa import ML_DSA_65 as D
    root = pathlib.Path(__file__).resolve().parent.parent
    so = tmp_path / f"libpqvtest_dilithium3_{len(list(tmp_path.glob('*.so')))}.so"
    subprocess.run(["gcc", "-O1", "-fPIC", "-shared", "-o", str(so),
                    str(root / "tests" / "data" / "mldsa_shim.c"),
                    str(root / "pq_verify" / "harness" / "pqv_randombytes.c")],
                   check=True, capture_output=True)
    lib = C.CDLL(str(so))
    U8 = C.POINTER(C.c_uint8)
    KP = C.CFUNCTYPE(C.c_int, U8, U8, U8)
    SG = C.CFUNCTYPE(C.c_int, U8, C.POINTER(C.c_size_t), U8, C.c_size_t, U8,
                     C.c_size_t, U8, U8)
    VF = C.CFUNCTYPE(C.c_int, U8, C.c_size_t, U8, C.c_size_t, U8, C.c_size_t, U8)
    at = lambda p, n: C.string_at(p, n) if n else b""

    def kp(pk, sk, seed):
        a, b = (keypair or D.key_derive)(at(seed, 32))
        C.memmove(pk, a, len(a)); C.memmove(sk, b, len(b))
        return 0

    def sg(sig, siglen, m, mlen, pre, prelen, rnd, sk):
        s = (sign or D._sign_internal)(at(sk, 4032), at(pre, prelen) + at(m, mlen),
                                       at(rnd, 32))
        C.memmove(sig, s, len(s)); siglen[0] = len(s)
        return 0

    def vf(sig, siglen, m, mlen, pre, prelen, pk):
        if siglen != 3309:
            return -1
        try:
            ok = (verify or D._verify_internal)(at(pk, 1952), at(pre, prelen) + at(m, mlen),
                                                at(sig, siglen))
        except Exception:
            ok = False
        return 0 if ok else -1

    keep = (KP(kp), SG(sg), VF(vf))
    lib.pqvtest_register(*keep, extra_rng)
    _IN_PROCESS_SHIMS.add(str(so))
    return str(so), (lib, keep)


def _audit_shim(path, **kw):
    from pq_verify.dsa_audit import pqverify_audit_dsa
    with contextlib.redirect_stdout(io.StringIO()):
        return pqverify_audit_dsa(path, "ML-DSA-65", **kw)


def test_dsa_audit_resolves_the_pqcrystals_abi_and_routes_each_interface(tmp_path):
    path, keep = _dsa_shim(tmp_path)
    r = _audit_shim(path, edge=False)
    assert r["abi"] == "pqcrystals" and r["harness"] is True
    d = r["detail"]
    assert d["keyGen"] == (25, 25)
    for s in ("sigGenInternal", "sigGenPure", "sigGenPreHash"):
        assert d[s] == (30, 30), s
    for s in ("sigVerInternal", "sigVerPure", "sigVerPreHash"):
        assert d[s] == (15, 15), s
    # the public, randomness-drawing APIs are the ones exercised where present
    assert r["via"]["keyGen"].endswith("_keypair")
    assert r["via"]["sigGenPure"].endswith("_signature")
    assert r["via"]["sigVerPure"].endswith("_verify")
    assert r["via"]["sigGenPreHash"].endswith("_signature_internal")
    # no external-mu API: counted, with the reason, and never as a pass
    assert "sigGenMu" not in d and r["not_applicable"]["sigGenMu"][0] == 30
    assert "external-mu" in r["not_applicable"]["sigGenMu"][1]
    assert r["verified"] and r["rng"] == []


def test_dsa_audit_catches_a_verifier_that_accepts_everything(tmp_path):
    path, keep = _dsa_shim(tmp_path, verify=lambda pk, m, sig: True)
    r = _audit_shim(path, edge=False)
    assert not r["verified"]
    for s in ("sigVerInternal", "sigVerPure", "sigVerPreHash"):
        p, t = r["detail"][s]
        assert p < t, s
    assert r["detail"]["sigGenPure"] == (30, 30)        # signing is untouched


def test_dsa_audit_catches_a_signer_that_ignores_rnd(tmp_path):
    D = pytest.importorskip("dilithium_py.ml_dsa").ML_DSA_65
    path, keep = _dsa_shim(tmp_path, sign=lambda sk, m, rnd: D._sign_internal(sk, m, bytes(32)))
    r = _audit_shim(path, edge=False)
    # the deterministic half (rnd = 0^32) still matches; the randomised half not
    for s in ("sigGenInternal", "sigGenPure", "sigGenPreHash"):
        assert r["detail"][s] == (15, 30), s


def test_dsa_audit_catches_extra_randomness(tmp_path):
    path, keep = _dsa_shim(tmp_path, extra_rng=1)
    r = _audit_shim(path, edge=False)
    assert r["detail"]["keyGen"] == (0, 25)
    assert r["rng"] and "FIPS 204 calls for 32" in r["rng"][0]
    assert not r["verified"]


def test_dsa_audit_sees_the_reference_hint_defect_through_c(tmp_path):
    """dilithium-py 1.4.0 accepts a repeated hint index (KNOWN_REFERENCE_DEFECTS).
    Behind the C ABI it is exactly the bug class Wycheproof's verify vectors
    exist for, and the edge stage must report it."""
    from pq_verify import edge as EG
    if (("dilithium-py", EG._reference_version("dilithium-py"))
            not in EG.KNOWN_REFERENCE_DEFECTS):
        pytest.skip("installed dilithium-py does not carry the hint defect")
    path, keep = _dsa_shim(tmp_path)
    r = _audit_shim(path)
    p, t = r["detail"]["edge:sigVerify"]
    assert t - p == 1
    assert any("InvalidHintsEncoding" in f["flags"] for f in r["edge"]["failures"])


def test_dsa_symbol_resolution_never_guesses():
    from pq_verify.dsa_audit import resolve_symbols, detect_abi
    pqclean = ["PQCLEAN_MLDSA65_CLEAN_crypto_sign_keypair",
               "PQCLEAN_MLDSA65_CLEAN_crypto_sign_signature",
               "PQCLEAN_MLDSA65_CLEAN_crypto_sign_signature_ctx",
               "PQCLEAN_MLDSA65_CLEAN_crypto_sign_verify",
               "PQCLEAN_MLDSA65_CLEAN_crypto_sign_verify_ctx"]
    found, amb = resolve_symbols(pqclean, "ML-DSA-65")
    assert not amb
    assert found["sign_ctx"].endswith("signature_ctx") and found["sign"] is None
    assert detect_abi(pqclean) == "pqcrystals"
    # several parameter sets in one library: narrowed by level
    multi = [f"pqcrystals_dilithium{m}_ref_signature_internal" for m in (2, 3, 5)]
    found, amb = resolve_symbols(multi, "ML-DSA-87")
    assert found["sign_internal"] == "pqcrystals_dilithium5_ref_signature_internal"
    # two candidates at the same level: refused, not guessed
    found, amb = resolve_symbols(["a_65_signature_internal", "b_65_signature_internal"],
                                 "ML-DSA-65")
    assert found["sign_internal"] is None and "sign_internal" in amb
    native = ["PQCP_MLDSA_NATIVE_MLDSA65_signature_extmu",
              "PQCP_MLDSA_NATIVE_MLDSA65_keypair_internal"]
    assert detect_abi(native) == "mldsa-native"


def test_dsa_report_names_not_applicable_stages_and_first_failures():
    from pq_verify.report import to_json_dsa
    doc = to_json_dsa({
        "verified": False, "passed": 10, "total": 11, "abi": "pqcrystals",
        "harness": True, "detail": {"sigVerPure": (14, 15)},
        "not_applicable": {"sigGenMu": [30, "no external-mu signing entry point"]},
        "not_applicable_total": 30, "via": {"sigVerPure": "x_verify"},
        "failures": [{"stage": "sigVerPure", "tcId": 7,
                      "detail": "accepted a signature NIST marks invalid"}],
        "rng": [], "edge": None}, param_set="ML-DSA-65", library="x.so")
    assert doc["status"] == "FINDINGS PRESENT"
    assert doc["not_applicable"]["sigGenMu"]["count"] == 30
    assert doc["stages"]["sigVerPure"]["via"] == "x_verify"
    assert "NIST tcId 7" in doc["findings"][0]
    assert doc["findings"][0].startswith("ML-DSA:")
    from pq_verify.report import _rule_for
    assert _rule_for(doc["findings"][0]) == "PQV008"
    none = to_json_dsa(None, param_set="ML-DSA-65", library="x.so")
    assert none["status"] == "CANNOT VERIFY" and not none["verified"]


def test_audit_dsa_cli_gates_and_rejects_bad_arguments(tmp_path):
    path, keep = _dsa_shim(tmp_path, verify=lambda pk, m, sig: True)
    code, out = _cli("--audit-dsa", path, "ML-DSA-65", "--fail-on-finding",
                     "--json", str(tmp_path / "r.json"))
    assert code == 1 and "FAILING: ML-DSA audit FINDINGS PRESENT" in out
    import json
    doc = json.loads((tmp_path / "r.json").read_text())
    assert doc["schema"] == "pq-verify/dsa-audit-result"
    assert doc["artifact"]["bound"] is True
    code, out = _cli("--audit-dsa", path, "ML-DSA-99")
    assert code == 2
    code, out = _cli("--audit-dsa", path, "ML-DSA-65", "--dsa-symbol", "bogus=x")
    assert code == 2


def test_dsa_vendor_rows_and_mutants_are_well_formed():
    import re
    mod, _ = _vendor_audit()
    rows = mod.load_dsa_table()
    assert {r["build"] for r in rows} == set(mod.DSA_BUILDS)
    for row in rows:
        assert re.fullmatch(r"[0-9a-f]{40}", row["commit"]), row["library"]
        assert set(row["results"]) == set(row["sets"]) == set(row["not_applicable"])
        for ps in row["sets"]:
            assert set(row["results"][ps]) <= set(mod.DSA_STAGES + mod.DSA_EDGE_STAGES)
            assert row["results"][ps]["keyGen"] == [25, 25]
        assert row["mutants"], row["library"]
        for m in row["mutants"]:
            assert m["find"] != m["replace"] and m["fails"]
            assert set(m["fails"]) <= set(mod.DSA_STAGES + mod.DSA_EDGE_STAGES + ("rng",))


def test_audits_md_matches_the_pinned_dsa_vendor_table():
    mod, root = _vendor_audit()
    text = (root / "AUDITS.md").read_text()
    assert mod.DSA_BEGIN in text and mod.DSA_END in text
    published = text.split(mod.DSA_BEGIN, 1)[1].split(mod.DSA_END, 1)[0].strip()
    assert published == mod.dsa_markdown(mod.load_dsa_table()).strip(), (
        "AUDITS.md is out of date: paste the ML-DSA table from "
        "`python3 tools/vendor_audit.py --markdown` between the vendor-audits-dsa markers")


# ----------------------------------------------------------------------
# LMS/HSS and XMSS/XMSS^MT (RFC 8554, RFC 8391, SP 800-208)
# ----------------------------------------------------------------------

def test_lmots_and_wots_parameters_match_the_standards():
    """p and ls from RFC 8554 Table 1 / SP 800-208 Table 2; WOTS+ len from
    RFC 8391 §5.2 / SP 800-208 §5. Computed, then held to the tables."""
    from pq_verify import hbs as H
    table = {(32, 1): (265, 7), (32, 2): (133, 6), (32, 4): (67, 4), (32, 8): (34, 0),
             (24, 1): (200, 8), (24, 2): (101, 6), (24, 4): (51, 4), (24, 8): (26, 0)}
    for (n, w), want in table.items():
        assert H.lmots_params(n, w) == want, (n, w)
    assert len(H.LMOTS) == 16 and len(H.LMS) == 20
    assert H.LMOTS[0x05][0] == "LMOTS_SHA256_N24_W1" and H.LMOTS[0x10][0] == "LMOTS_SHAKE_N24_W8"
    assert H.LMS[0x0A][0] == "LMS_SHA256_M24_H5" and H.LMS[0x18][0] == "LMS_SHAKE_M24_H25"
    lens = {p.n: p.len for p in H.XMSS_SETS.values()}
    assert lens == {24: 51, 32: 67, 64: 131}
    assert H.XMSS_SETS[("XMSS", 1)].name == "XMSS-SHA2_10_256"
    assert H.XMSS_SETS[("XMSS", 0x0D)].name == "XMSS-SHA2_10_192"
    assert H.XMSS_SETS[("XMSS", 0x15)].name == "XMSS-SHAKE256_20_192"
    assert H.XMSS_SETS[("XMSS", 0x0D)].pad == 4 and H.XMSS_SETS[("XMSS", 0x10)].pad == 32


def test_nist_lms_acvp_is_complete():
    from pq_verify.hbs_suite import pqverify_lms_acvp
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_lms_acvp()
    assert (r["passed"], r["total"]) == (87, 87), r["failures"][:3]
    assert r["vectors"] == "pinned (NIST ACVP-Server 2972def)"
    assert sum(t for k, (p, t) in r["detail"].items() if k.startswith("keyGen")) == 9
    assert sum(t for k, (p, t) in r["detail"].items() if k.startswith("sigVer")) == 16
    assert sum(t for k, (p, t) in r["detail"].items() if k.startswith("sigGen")) == 62


def test_lms_xmss_other_sources_verify_and_report_what_did_not_run():
    from pq_verify.hbs_suite import pqverify_hbs
    with contextlib.redirect_stdout(io.StringIO()):
        r = pqverify_hbs(budget=0)
    assert r["verified"] and (r["passed"], r["total"]) == (1441, 1441)
    d = r["detail"]
    assert d["RFC 8554 HSS verify"] == (2, 2)
    assert d["liboqs XMSS^MT verify"] == (16, 16)
    assert d["liboqs XMSS verify"] == (21, 21)
    for fam in ("SHA256_M24", "SHA256_M32", "SHAKE_M24", "SHAKE_M32"):
        assert d[f"pqc-kat LMS sigVer {fam}"] == (80, 80)
    # budget 0: no tree is built, and every skipped case is counted, not passed
    assert not any("keyGen" in k for k in d)
    assert r["not_run_total"] == 2096
    assert all(v[1].startswith("tree over budget") for v in r["not_run"].values())


def test_lms_trees_are_byte_exact_on_every_family():
    """One height-5 tree per hash family: key generation and a signature
    (with the hash-sigs randomizer derivation) byte-exact."""
    import gzip, json, pathlib
    from pq_verify import hbs as H
    vec = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "vectors"
    with gzip.open(vec / "hbs_vectors.json.gz", "rt") as fh:
        b = json.load(fh)
    seen = set()
    for fam in ("SHA256-M24", "SHA256-M32", "SHAKE-M24", "SHAKE-M32"):
        doc = json.loads(b[f"pqc-kat/LMS/LMS-sigGen-1.0-{fam}-H5_H10/internalProjection.json"])
        g = next(g for g in doc["testGroups"] if g["lmsMode"].endswith("_H5")
                 and g["lmOtsMode"].endswith("_W4"))
        lt, ot = H.LMS_BY_NAME[g["lmsMode"]], H.LMOTS_BY_NAME[g["lmOtsMode"]]
        seed, I = bytes.fromhex(g["seed"]), bytes.fromhex(g["i"])
        tree = H.LMSTree(lt, ot, seed, I)
        assert tree.public_key.hex().upper() == g["publicKey"].upper(), fam
        t = g["tests"][0]
        q = int(t["q"])
        C = H.LMOTS[ot][1](I + H.u32(q) + H.u16(0xFFFD) + b"\xff" + seed)
        assert tree.sign(bytes.fromhex(t["message"]), q, C).hex().upper() == t["signature"].upper()
        seen.add(fam)
    assert len(seen) == 4


def test_xmss_tree_is_byte_exact_sp800_208_keygen():
    """SP 800-208's PRF_keygen derivation, a 192-bit set: the whole height-10
    tree and one signature, byte-exact (about 6 s)."""
    import gzip, json, pathlib
    from pq_verify import hbs as H
    from pq_verify.hbs_suite import _xmss_sig
    vec = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "vectors"
    with gzip.open(vec / "hbs_vectors.json.gz", "rt") as fh:
        b = json.load(fh)
    p = json.loads(b["pqc-kat/XMSS/XMSS-sigGen-SHA256-N24-H10/prompt.json"])
    e = json.loads(b["pqc-kat/XMSS/XMSS-sigGen-SHA256-N24-H10/expectedResults.json"])
    g = p["testGroups"][0]
    P = H.XMSS_SETS[("XMSS", int(g["OID"]))]
    tree = H.XMSSTree(P, bytes.fromhex(g["S_XMSS"]), bytes.fromhex(g["SK_PRF"]),
                      bytes.fromhex(g["I"]))
    assert tree.root.hex().upper() == g["PK_root"].upper()
    t, ex = g["tests"][0], e["testGroups"][0]["tests"][0]
    msg = bytes.fromhex(t["message"])
    sig = _xmss_sig(bytes.fromhex(ex["signature"]), msg, P)
    assert tree.sign(msg, int.from_bytes(sig[:4], "big")) == sig


def test_lms_and_xmss_verifiers_reject_every_tampering():
    """Negative controls: a valid signature with any one byte changed (in q,
    C, the OTS chains, the type fields or the path), truncated, extended, or
    under a key of another type, must be rejected."""
    import gzip, json, pathlib
    from pq_verify import hbs as H
    from pq_verify.hbs_suite import _xmss_sig, _c_arrays
    vec = pathlib.Path(__file__).resolve().parent.parent / "pq_verify" / "vectors"
    with gzip.open(vec / "hbs_vectors.json.gz", "rt") as fh:
        b = json.load(fh)
    doc = json.loads(b["pqc-kat/LMS/LMS-sigGen-1.0-SHAKE-M24-H5_H10/internalProjection.json"])
    g = doc["testGroups"][0]
    pk, t = bytes.fromhex(g["publicKey"]), g["tests"][0]
    msg, sig = bytes.fromhex(t["message"]), bytes.fromhex(t["signature"])
    assert H.lms_verify(pk, msg, sig)
    for pos in sorted({0, 3, 7, 8, 20, len(sig) // 2, len(sig) - 40, len(sig) - 1}):
        bad = bytearray(sig)
        bad[pos] ^= 1
        assert not H.lms_verify(pk, msg, bytes(bad)), pos
    assert not H.lms_verify(pk, msg, sig[:-1])
    assert not H.lms_verify(pk, msg, sig + b"\x00")
    assert not H.lms_verify(pk, msg + b"\x00", sig)
    assert not H.lms_verify(pk[:4] + H.u32(H.LMOTS_BY_NAME["LMOTS_SHAKE_N24_W8"]) + pk[8:], msg, sig)
    # q at or beyond 2^h
    h = H.LMS[int.from_bytes(pk[:4], "big")][3]
    assert not H.lms_verify(pk, msg, H.u32(1 << h) + sig[4:])
    # HSS: the RFC cases, then L that disagrees with the signature
    case = _c_arrays(b["hash-sigs/test_testvector.c"])[0]
    assert H.hss_verify(case["public_key"], case["message"], case["signature"])
    assert not H.hss_verify(case["public_key"], case["message"] + b".", case["signature"])
    assert not H.hss_verify(H.u32(3) + case["public_key"][4:], case["message"], case["signature"])
    # XMSS
    p = json.loads(b["pqc-kat/XMSS/XMSS-sigGen-SHAKE256-N32-H10/prompt.json"])
    e = json.loads(b["pqc-kat/XMSS/XMSS-sigGen-SHAKE256-N32-H10/expectedResults.json"])
    g = p["testGroups"][0]
    P = H.XMSS_SETS[("XMSS", int(g["OID"]))]
    xpk = H.u32(int(g["OID"])) + bytes.fromhex(g["PK_root"]) + bytes.fromhex(g["I"])
    xmsg = bytes.fromhex(g["tests"][0]["message"])
    xsig = _xmss_sig(bytes.fromhex(e["testGroups"][0]["tests"][0]["signature"]), xmsg, P)
    assert H.xmss_verify(xpk, xmsg, xsig)
    for pos in (0, 3, 4, 40, len(xsig) // 2, len(xsig) - 1):
        bad = bytearray(xsig)
        bad[pos] ^= 0x80
        assert not H.xmss_verify(xpk, xmsg, bytes(bad)), pos
    assert not H.xmss_verify(xpk, xmsg, xsig[:-1])
    assert not H.xmss_verify(xpk, xmsg, H.u32(1 << P.h) + xsig[4:])
    # signed-message form whose appended copy differs from the message
    assert _xmss_sig(xsig + xmsg[:-1] + b"\x00", xmsg, P) is None


def test_hbs_bundle_is_pinned_and_checked(tmp_path):
    import gzip, json, pathlib, sys
    root = pathlib.Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(root / "tools"))
    import pin_hbs_vectors as P
    assert P.verify() == []
    m = json.loads((root / "pq_verify" / "vectors" / "HBS_MANIFEST.json").read_text())
    assert set(m["sources"]) == {"pqc-kat", "liboqs", "hash-sigs"}
    for s in m["sources"].values():
        assert len(s["commit"]) == 40
    # the doctor blocks an altered entry
    D, _ = _doctor()
    repo = _doctor_repo(tmp_path)
    arc = repo / "pq_verify" / "vectors" / "hbs_vectors.json.gz"
    with gzip.open(arc, "rt") as fh:
        entries = json.load(fh)
    entries["hash-sigs/test_testvector.c"] = entries["hash-sigs/test_testvector.c"].replace(
        "0x54,0x68", "0x54,0x69", 1)
    with gzip.open(arc, "wt") as fh:
        json.dump(entries, fh)
    code, doc, st = _doctor_run(repo, "--fast")
    assert code == 1 and st["hbs:manifest"] == "BLOCK"


def test_lms_xmss_report_and_gate():
    from pq_verify.report import to_json_hbs
    doc = to_json_hbs({"verified": False, "passed": 9, "total": 10,
                       "detail": {"x": (9, 10)}, "not_run": {"y": [5, "tree over budget"]},
                       "not_run_total": 5, "failures": [{"stage": "x", "case": "c"}],
                       "budget": 0, "vectors": "v", "reference": "pq_verify.hbs"})
    assert doc["schema"] == "pq-verify/hbs-result"
    assert doc["status"] == "FINDINGS PRESENT" and doc["summary"]["not_run"] == 5
    assert doc["not_run"]["y"]["count"] == 5


# ----------------------------------------------------------------------
# --audit-hbs: a vendor's own LMS/HSS and XMSS library, through a pqv_hbs
# adapter. The pinned libraries (cisco/hash-sigs, xmss-reference) and their
# mutants run in CI; here a shim whose adapter functions call back into
# pq_verify.hbs exercises the ctypes path offline, with faults planted.
# ----------------------------------------------------------------------

def _hbs_shim(tmp_path, verify=None, sign_c=None, lms_only=False, no_keygen=False,
              state=False):
    """state: False (no state support), True (a correct stateful LMS key on
    LMS_SHA256_M32_H5/LMOTS_SHA256_N32_W1), or a planted state bug:
    'no_advance', 'memory_only', 'no_refuse'."""
    import ctypes as C, pathlib, shutil, subprocess, struct
    from pq_verify import hbs as H
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")
    root = pathlib.Path(__file__).resolve().parent.parent
    so = tmp_path / f"libhbsshim{len(list(tmp_path.glob('*.so')))}.so"
    subprocess.run(["gcc", "-O1", "-fPIC", "-shared", "-I",
                    str(root / "pq_verify" / "harness" / "hbs"), "-o", str(so),
                    str(root / "tests" / "data" / "hbs_shim.c")],
                   check=True, capture_output=True)
    lib = C.CDLL(str(so))
    U8, SZ, PSZ = C.POINTER(C.c_uint8), C.c_size_t, C.POINTER(C.c_size_t)
    SUP = C.CFUNCTYPE(C.c_int, C.c_uint32, C.c_uint32, C.c_uint32)
    VER = C.CFUNCTYPE(C.c_int, C.c_uint32, U8, SZ, U8, SZ, U8, SZ)
    KG = C.CFUNCTYPE(C.c_int, C.c_uint32, C.c_uint32, C.c_uint32, U8, SZ, U8, PSZ)
    SG = C.CFUNCTYPE(C.c_int, C.c_uint32, C.c_uint32, C.c_uint32, U8, SZ, C.c_uint64,
                     U8, SZ, U8, PSZ)
    at = lambda p, n: C.string_at(p, n) if n else b""

    def sup(s, t, o):
        if s != 1 and lms_only:
            return 0
        caps = 1 if no_keygen else 7
        if state and s == 1 and (t, o) == (5, 1):
            caps |= 8
        return caps

    def ver(s, pk, pkl, m, ml, sig, sl):
        args = (at(pk, pkl), at(m, ml), at(sig, sl))
        if verify:
            return 0 if verify(s, *args) else 1
        ok = H.hss_verify(*args) if s == 1 else H.xmss_verify(*args, mt=s == 3)
        return 0 if ok else 1

    def tree(s, t, o, seed):
        if s == 1:
            m = H.LMS[t][2]
            return H.LMSTree(t, o, seed[:m], seed[m:m + 16])
        P = H.XMSS_SETS[("XMSS", t)]
        return H.XMSSTree(P, seed[:P.n], seed[P.n:2 * P.n], seed[2 * P.n:3 * P.n])

    def kg(s, t, o, seed, sl, pk, pkl):
        tr = tree(s, t, o, at(seed, sl))
        out = H.u32(1) + tr.public_key if s == 1 else tr.public_key(t)
        C.memmove(pk, out, len(out)); pkl[0] = len(out)
        return 0

    def sg(s, t, o, seed, sl, idx, m, ml, sig, sigl):
        tr = tree(s, t, o, at(seed, sl))
        msg = at(m, ml)
        if s == 1:
            Cr = (sign_c or (lambda tr, q: H.LMOTS[o][1](
                tr.I + H.u32(q) + H.u16(0xFFFD) + b"\xff" + tr.seed)))(tr, idx)
            out = H.u32(0) + tr.sign(msg, idx, Cr)
        else:
            out = tr.sign(msg, idx)
        C.memmove(sig, out, len(out)); sigl[0] = len(out)
        return 0

    keep = (SUP(sup), VER(ver), KG(kg), SG(sg))
    lib.pqvtest_hbs_register(*keep)
    if state:
        import json as _json, os as _os
        P = C.c_char_p
        SKG = C.CFUNCTYPE(C.c_int, C.c_uint32, C.c_uint32, C.c_uint32, U8, SZ, P, U8, PSZ)
        SSG = C.CFUNCTYPE(C.c_int, C.c_uint32, P, U8, SZ, U8, PSZ)
        SSK = C.CFUNCTYPE(C.c_int, C.c_uint32, P, C.c_uint64)
        memory, trees = {}, {}

        def load(path):
            with open(path) as fh:
                d = _json.load(fh)
            if state == "memory_only" and path in memory:
                d["next"] = memory[path]
            return d

        def save(path, d):
            if state == "memory_only":
                memory[path] = d["next"]      # never reaches the file
                return
            with open(path, "w") as fh:
                _json.dump(d, fh)

        def skg(s, t, o, seed, sl, st, pk, pkl):
            path = st.decode()
            if _os.path.exists(path):
                return -1
            sd = at(seed, sl)
            with open(path, "w") as fh:
                _json.dump({"t": t, "o": o, "seed": sd.hex(), "next": 0}, fh)
            return kg(s, t, o, seed, sl, pk, pkl)

        def ssg(s, st, m, ml, sig, sigl):
            path = st.decode()
            d = load(path)
            q, h = d["next"], H.LMS[d["t"]][3]
            if q >= 1 << h:
                if state != "no_refuse":
                    return -1
                q %= 1 << h                   # wraps: leaf 0 again
            if state != "no_advance":
                d["next"] = d["next"] + 1
            save(path, d)
            sd = bytes.fromhex(d["seed"])
            key = (d["t"], d["o"], sd)
            if key not in trees:
                trees[key] = tree(1, d["t"], d["o"], sd)
            tr, o = trees[key], d["o"]
            Cr = H.LMOTS[o][1](tr.I + H.u32(q) + H.u16(0xFFFD) + b"\xff" + tr.seed)
            out = H.u32(0) + tr.sign(at(m, ml), q, Cr)
            C.memmove(sig, out, len(out)); sigl[0] = len(out)
            return 0

        def ssk(s, st, nxt):
            path = st.decode()
            d = load(path)
            if nxt < d["next"]:
                return -1
            d["next"] = nxt
            if state == "memory_only":
                memory[path] = nxt
            with open(path, "w") as fh:     # skip is the audit's, not the bug's
                _json.dump(dict(d, next=nxt), fh)
            return 0

        skeep = (SKG(skg), SSG(ssg), SSK(ssk))
        lib.pqvtest_hbs_register_state(*skeep)
        keep = keep + skeep
    _IN_PROCESS_SHIMS.add(str(so))
    return str(so), (lib, keep)


def _audit_hbs(path, **kw):
    from pq_verify.hbs_audit import pqverify_audit_hbs
    kw.setdefault("budget", 100_000)          # LMS h = 5 trees, in Python
    kw.setdefault("per_group", 1)
    with contextlib.redirect_stdout(io.StringIO()):
        return pqverify_audit_hbs(path, **kw)


def test_hbs_audit_passes_a_correct_library_and_runs_every_stage(tmp_path):
    path, keep = _hbs_shim(tmp_path)
    r = _audit_hbs(path)
    assert r["verified"], r["failures"][:3]
    d = r["detail"]
    for stage in ("LMS verify [NIST]", "LMS verify [pqc-kat]", "LMS verify [liboqs]",
                  "LMS verify [RFC 8554]", "XMSS verify [pqc-kat]", "XMSS verify [liboqs]",
                  "XMSS^MT verify [liboqs]", "LMS keyGen [pqc-kat]", "LMS sigGen [pqc-kat]",
                  "LMS malformed", "XMSS malformed", "XMSS^MT malformed"):
        assert d.get(stage, (0, 0))[1] > 0, stage
    assert d["LMS verify [NIST]"] == (78, 78)
    assert r["not_run_total"] > 0          # over budget or sampled: counted, not passed
    assert all(v[1] for v in r["not_run"].values())


def test_hbs_audit_catches_a_verifier_that_accepts_everything(tmp_path):
    path, keep = _hbs_shim(tmp_path, verify=lambda s, pk, m, sig: True)
    r = _audit_hbs(path, budget=0)
    assert not r["verified"]
    for stage in ("LMS malformed", "XMSS malformed", "LMS verify [pqc-kat]"):
        p, t = r["detail"][stage]
        assert p < t, stage


def test_hbs_audit_catches_a_wrong_randomizer(tmp_path):
    """C from random bytes instead of the ACVP derivation: every signature
    still verifies, none is byte-exact."""
    from pq_verify import hbs as H
    path, keep = _hbs_shim(tmp_path, sign_c=lambda tr, q: bytes(H.LMS[tr.lms_type][2]))
    r = _audit_hbs(path)
    p, t = r["detail"]["LMS sigGen [pqc-kat]"]
    assert t and p == 0
    assert r["detail"]["LMS verify [pqc-kat]"][0] == r["detail"]["LMS verify [pqc-kat]"][1]


def test_hbs_audit_reports_what_the_library_lacks_as_not_applicable(tmp_path):
    path, keep = _hbs_shim(tmp_path, lms_only=True, no_keygen=True)
    r = _audit_hbs(path, budget=0)
    assert not any(k.startswith("XMSS") for k in r["detail"])
    na = r["not_applicable"]
    assert "does not implement XMSS" in na["XMSS verify"][1]
    assert "no keyGen" in na["LMS keyGen"][1] and "no sigGen" in na["LMS sigGen"][1]
    assert r["not_applicable_total"] > 0


def test_hbs_malformations_are_each_rejected_by_the_reference():
    """Every derived malformation the audit scores is one pq-verify's own
    verifier rejects; and each changes the signature or key."""
    from pq_verify.hbs_audit import cases, malformed, _reference_verify
    seen = set()
    for c in cases():
        if c["kind"] != "verify" or not c["want"] or c["set"] in seen:
            continue
        seen.add(c["set"])
        assert _reference_verify(c["scheme"], c["pk"], c["msg"], c["sig"]), c["label"]
        for what, pk, msg, sig in malformed(c):
            assert (pk, msg, sig) != (c["pk"], c["msg"], c["sig"]), what
        if len(seen) > 12:
            break


def test_hbs_adapter_loader_refuses_a_library_without_the_abi(tmp_path):
    import shutil, subprocess
    from pq_verify.hbs_audit import HBSAdapter, AdapterError
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")
    src = tmp_path / "x.c"
    src.write_text("int unrelated(void) { return 0; }\n")
    so = tmp_path / "libx.so"
    subprocess.run(["gcc", "-shared", "-fPIC", "-o", str(so), str(src)], check=True)
    with pytest.raises(AdapterError):
        HBSAdapter(str(so))


def test_hbs_vendor_rows_and_mutants_are_well_formed_and_published():
    import re
    mod, root = _vendor_audit()
    rows = mod.load_hbs_table()
    assert {r["build"] for r in rows} == set(mod.HBS_BUILDS)
    for row in rows:
        assert re.fullmatch(r"[0-9a-f]{40}", row["commit"]), row["library"]
        assert row["mutants"]
        for m in row["mutants"]:
            assert m["fails"] and set(m["fails"]) <= set(row["results"]), m["name"]
    text = (root / "AUDITS.md").read_text()
    assert mod.HBS_BEGIN in text and mod.HBS_END in text
    published = text.split(mod.HBS_BEGIN, 1)[1].split(mod.HBS_END, 1)[0].strip()
    assert published == mod.hbs_markdown(rows).strip(), (
        "AUDITS.md is out of date: paste the LMS/XMSS table from "
        "`python3 tools/vendor_audit.py --markdown` between the vendor-audits-hbs markers")


def test_hbs_audit_report_and_rule():
    from pq_verify.report import to_json_hbs_audit, _rule_for
    doc = to_json_hbs_audit({"verified": False, "passed": 1, "total": 2,
                             "detail": {"LMS malformed": (1, 2)},
                             "failures": [{"stage": "LMS malformed", "case": "x: q = 2^h",
                                           "detail": "accepted"}],
                             "not_applicable": {}, "not_run": {}, "name": "lib"},
                            library="lib.so")
    assert doc["schema"] == "pq-verify/hbs-audit-result"
    assert doc["status"] == "FINDINGS PRESENT"
    assert "q = 2^h" in doc["findings"][0] and _rule_for(doc["findings"][0]) == "PQV009"


# ----------------------------------------------------------------------
# 2.10.0: a verdict that cannot be faked, and a gate that cannot be forgotten
# ----------------------------------------------------------------------

def _answer_fresh(prompt, tamper=None):
    """Answer a fresh prompt the way an implementation would: by computing."""
    from pq_verify import fresh as F
    from pq_verify.core import check_encapsulation_key, check_decapsulation_key
    ps = prompt["parameterSet"]
    H, B = (lambda b: b.hex()), bytes.fromhex
    if ps.startswith("ML-KEM"):
        import kyber_py.ml_kem as m
        K = getattr(m, ps.replace("-", "_"))
    else:
        import dilithium_py.ml_dsa as m
        O = getattr(m, ps.replace("-", "_"))
    suites = []
    for s in prompt["suites"]:
        groups = []
        for g in s["testGroups"]:
            tests = []
            for t in g["tests"]:
                a, fn, mode = {"tcId": t["tcId"]}, g.get("function"), s["mode"]
                if s["algorithm"] == "ML-KEM":
                    if mode == "keyGen":
                        ek, dk = K._keygen_internal(B(t["d"]), B(t["z"]))
                        a.update(ek=H(ek), dk=H(dk))
                    elif fn == "encapsulation":
                        k, c = K._encaps_internal(B(t["ek"]), B(t["m"]))
                        a.update(c=H(c), k=H(k))
                    elif fn == "decapsulation":
                        a["k"] = H(K._decaps_internal(B(t["dk"]), B(t["c"])))
                    elif fn == "encapsulationKeyCheck":
                        a["testPassed"] = check_encapsulation_key(B(t["ek"]), ps)
                    else:
                        a["testPassed"] = check_decapsulation_key(B(t["dk"]), ps)
                elif mode == "keyGen":
                    pk, sk = O._keygen_internal(B(t["seed"]))
                    a.update(pk=H(pk), sk=H(sk))
                elif mode == "sigGen":
                    rnd = B(t["rnd"]) if "rnd" in t else bytes(32)
                    a["signature"] = H(F._dsa_sign(O, B(t["sk"]), g, t, rnd))
                else:
                    a["testPassed"] = F._dsa_verify(O, B(t["pk"]), g, t,
                                                    B(t["signature"]))
                tests.append(a)
            groups.append({"tgId": g["tgId"], "tests": tests})
        suites.append({"suite": s["suite"], "testGroups": groups})
    doc = {"promptId": prompt["promptId"], "parameterSet": ps, "suites": suites}
    if tamper:
        tamper(doc)
    return doc


def _fresh_round(tmp_path, ps, count=2):
    import json as _json
    key, prompt = tmp_path / f"{ps}.key", tmp_path / f"{ps}.prompt.json"
    code, out = _cli("--emit-prompt", ps, "--fresh-key", str(key),
                     "--fresh-count", str(count), "--prompt-out", str(prompt))
    assert code == 0, out
    return key, _json.loads(prompt.read_text())


@pytest.mark.parametrize("ps", ["ML-KEM-512", "ML-DSA-44"])
def test_fresh_prompt_round_trip_verifies_a_computing_responder(tmp_path, ps):
    """Questions derived from an auditor-held seed, answered by computation,
    re-derived and scored at verification: VERIFIED, exit 0."""
    pytest.importorskip("kyber_py")
    pytest.importorskip("dilithium_py")
    import json as _json, stat
    key, prompt = _fresh_round(tmp_path, ps)
    seed = _json.loads(key.read_text())["seed"]
    assert prompt["fresh"] is True and seed.lower() not in _json.dumps(prompt).lower()
    assert stat.S_IMODE(key.stat().st_mode) == 0o600
    resp = tmp_path / "r.json"
    resp.write_text(_json.dumps(_answer_fresh(prompt)))
    code, out = _cli("--verify-response", str(resp), "--fresh-key", str(key))
    assert code == 0 and "RESULT: VERIFIED" in out, out
    assert "fresh questions" in out


def test_fresh_prompt_carries_no_answer(tmp_path):
    """No expected value appears anywhere in the prompt file."""
    pytest.importorskip("kyber_py")
    from pq_verify.fresh import read_key, build
    key, prompt = _fresh_round(tmp_path, "ML-KEM-768", count=4)
    k = read_key(str(key))
    _q, expected = build(k["param_set"], k["seed"], k["count"])
    text = (tmp_path / "ML-KEM-768.prompt.json").read_text().upper()
    for suite in expected.values():
        for ans in suite.values():
            for v in ans.values():
                if isinstance(v, str):
                    assert v.upper() not in text


def test_fresh_response_one_wrong_byte_is_a_finding(tmp_path):
    pytest.importorskip("dilithium_py")
    import json as _json
    key, prompt = _fresh_round(tmp_path, "ML-DSA-44")

    def tamper(doc):
        t = doc["suites"][1]["testGroups"][0]["tests"][0]
        t["signature"] = t["signature"][:-2] + ("00" if t["signature"][-2:] != "00" else "01")
    resp = tmp_path / "r.json"
    resp.write_text(_json.dumps(_answer_fresh(prompt, tamper)))
    code, out = _cli("--verify-response", str(resp), "--fresh-key", str(key))
    assert code == 1 and "FINDINGS PRESENT" in out and "first differs at byte" in out


def test_published_answers_do_not_pass_a_fresh_prompt(tmp_path):
    """Replaying NIST's public answers -- the attack on the pinned prompt --
    scores nothing against fresh questions."""
    pytest.importorskip("kyber_py")
    import json as _json
    from pq_verify.response import _load, _source
    key, prompt = _fresh_round(tmp_path, "ML-KEM-512")
    local = _source()
    suites = []
    for s in prompt["suites"]:
        E = _load(local, s["suite"], "expectedResults.json")
        suites.append({"suite": s["suite"], "testGroups": E["testGroups"]})
    resp = tmp_path / "replay.json"
    resp.write_text(_json.dumps({"promptId": prompt["promptId"],
                                 "parameterSet": "ML-KEM-512", "suites": suites}))
    code, out = _cli("--verify-response", str(resp), "--fresh-key", str(key))
    assert code == 1 and "RESULT: VERIFIED" not in out


def test_fresh_key_is_never_overwritten_and_must_match(tmp_path):
    pytest.importorskip("kyber_py")
    key, _p = _fresh_round(tmp_path, "ML-KEM-512")
    before = key.read_bytes()
    code, out = _cli("--emit-prompt", "ML-KEM-512", "--fresh-key", str(key),
                     "--prompt-out", str(tmp_path / "again.json"))
    assert code == 2 and "never overwritten" in out and key.read_bytes() == before
    code, _o = _cli("--verify-response", str(tmp_path / "missing.json"),
                    "--fresh-key", str(tmp_path / "nope.key"))
    assert code == 1


def test_fresh_derivation_is_deterministic_and_seed_dependent():
    pytest.importorskip("kyber_py")
    pytest.importorskip("slhdsa")
    from pq_verify.fresh import build
    from pq_verify.response import _prompt_id
    for ps in ("ML-KEM-512", "SLH-DSA-SHA2-128f"):
        a = build(ps, b"\x01" * 32, 1)
        assert a == build(ps, b"\x01" * 32, 1)
        assert _prompt_id(a[0]) != _prompt_id(build(ps, b"\x02" * 32, 1)[0])


def test_published_prompt_says_its_answers_are_public(tmp_path):
    code, out = _cli("--emit-prompt", "ML-KEM-512", "--prompt-out",
                     str(tmp_path / "p.json"))
    assert code == 0 and "PUBLISHED" in out


def test_gating_is_the_default(monkeypatch):
    """--acvp-all that failed used to exit 0 without --fail-on-finding, and
    the GitHub Action never passed it: a failed run published verified=true."""
    import pq_verify.cli as cli
    bad = {"verified": False, "passed": 1, "total": 2, "detail": {}}
    good = {"verified": True, "passed": 2, "total": 2, "detail": {}, "modes": []}
    monkeypatch.setattr(cli, "pqverify_acvp_all", lambda **k: {
        "ml_kem": bad, "ml_dsa": good, "slh_dsa": good, "lms": good})
    assert _cli("--acvp-all")[0] == 1
    assert _cli("--acvp-all", "--fail-on-finding")[0] == 1
    assert _cli("--acvp-all", "--no-fail")[0] == 0
    assert _cli("--acvp-all", "--no-fail", "--fail-on-finding")[0] == 2


def test_failed_self_suite_fails_the_exit_status(monkeypatch):
    import pq_verify.cli as cli
    from pq_verify.core import AuditResult
    r = AuditResult("x")
    r.add_test("broken", False)
    monkeypatch.setattr(cli, "run_selftest", lambda quick=False: [r])
    code, out = _cli("--quick")
    assert code == 1 and "self-suite" in out
    assert _cli("--quick", "--no-fail")[0] == 0


def test_api_acvp_all_is_not_verified_when_a_suite_did_not_run(monkeypatch):
    import pq_verify.core as core, pq_verify.hbs_suite as hs
    ok = {"verified": True, "passed": 2, "total": 2, "detail": {}, "modes": []}
    monkeypatch.setattr(core, "pqverify_acvp", lambda **k: None)
    monkeypatch.setattr(core, "pqverify_mldsa_acvp", lambda **k: ok)
    monkeypatch.setattr(core, "pqverify_slhdsa_acvp", lambda **k: ok)
    monkeypatch.setattr(hs, "pqverify_lms_acvp", lambda **k: ok)
    with contextlib.redirect_stdout(io.StringIO()):
        r = core.pqverify_acvp_all(verbose=False)
    assert r["verified"] is False and r["not_run"] == ["ML-KEM"]


@pytest.mark.parametrize("argv", [["--audit-hbs-full"], ["--dsa-abi", "pqcrystals"],
                                  ["--fresh-count", "3"], ["--audit-timeout", "5"],
                                  ["--kem-keypair", "x"]])
def test_a_modifier_without_its_task_is_an_input_error(argv):
    code, out = _cli(*argv)
    assert code == 2 and "does nothing without" in out


_CRASH_KEM = r"""
#include <unistd.h>
int k768_keypair_derand(unsigned char *pk, unsigned char *sk, const unsigned char *c) {
#ifdef HANG
    for (;;) sleep(1);
#else
    volatile int *p = 0; *p = 1;
#endif
    return 0;
}
int k768_enc_derand(unsigned char *ct, unsigned char *ss, const unsigned char *pk,
                    const unsigned char *c) { return 0; }
int k768_dec(unsigned char *ss, const unsigned char *ct, const unsigned char *sk) { return 0; }
"""


def _crash_kem(tmp_path, hang=False):
    import shutil, subprocess
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")
    src = tmp_path / "crash.c"
    src.write_text(_CRASH_KEM)
    so = tmp_path / ("libhang768.so" if hang else "libcrash768.so")
    subprocess.run(["gcc", "-shared", "-fPIC", *(["-DHANG"] if hang else []),
                    "-o", str(so), str(src)], check=True)
    return str(so)


def test_a_crashing_library_is_reported_not_fatal(tmp_path):
    """A SIGSEGV inside the vendor library used to take pq-verify down with
    it: no report, a bare signal in CI. The audit now runs in a child."""
    import json as _json
    so = _crash_kem(tmp_path)
    rpt = tmp_path / "r.json"
    code, out = _cli("--audit-kem", so, "ML-KEM-768", "--json", str(rpt))
    # a null write is SIGSEGV on Linux; macOS may deliver SIGBUS
    sig = "SIGSEGV" if "SIGSEGV" in out else "SIGBUS"
    assert code == 1 and sig in out
    d = _json.loads(rpt.read_text())
    assert d["status"] == "CANNOT VERIFY" and sig in d["findings"][0]
    assert d["artifact"]["isolation"] == "child process"


def test_a_hanging_library_times_out(tmp_path):
    so = _crash_kem(tmp_path, hang=True)
    code, out = _cli("--audit-kem", so, "ML-KEM-768", "--audit-timeout", "3")
    assert code == 1 and "did not finish within 3 s" in out


def test_the_artifact_binds_every_object_the_audit_loaded(tmp_path):
    import json as _json, os
    so = _stub_kem(tmp_path, None)
    rpt = tmp_path / "r.json"
    _cli("--audit-kem", so, "ML-KEM-768", "--json", str(rpt))
    a = _json.loads(rpt.read_text())["artifact"]
    if a.get("loaded_objects") is None:
        pytest.skip("no /proc/self/maps on this platform")
    mine = [o for o in a["loaded_objects"]
            if os.path.realpath(o["path"]) == os.path.realpath(so)]
    assert mine and mine[0]["sha256"] == a["sha256"]


def test_check_no_harness(tmp_path):
    import pathlib, shutil, subprocess
    if not shutil.which("gcc"):
        pytest.skip("gcc not available")
    root = pathlib.Path(__file__).resolve().parent.parent
    test_build = tmp_path / "libtest.so"
    subprocess.run(["gcc", "-shared", "-fPIC", "-o", str(test_build),
                    str(root / "pq_verify" / "harness" / "pqv_randombytes.c")], check=True)
    code, out = _cli("--check-no-harness", str(test_build))
    assert code == 1 and "randombytes() harness" in out
    clean = _stub_kem(tmp_path, None)
    assert _cli("--check-no-harness", clean)[0] == 0


def test_hbs_verdict_states_a_partial_scope(tmp_path):
    from pq_verify.report import to_json_hbs_audit
    path, keep = _hbs_shim(tmp_path, lms_only=True)
    doc = to_json_hbs_audit(_audit_hbs(path))
    assert doc["status"] == "VERIFIED"
    assert doc["scope"]["complete"] is False
    assert "not applicable" in doc["scope"]["statement"]


def test_symbol_discovery_sees_ifunc_and_weak_exports(tmp_path):
    """CPU-dispatching libraries export their entry points as GNU IFUNCs
    (nm type 'i'); only 'T' used to be read, so they had no symbols at all."""
    import shutil, subprocess
    import sys
    if not (shutil.which("gcc") and shutil.which("nm")):
        pytest.skip("gcc/nm not available")
    if not sys.platform.startswith("linux"):
        pytest.skip("GNU IFUNC is an ELF feature")
    from pq_verify.dsa_audit import exported_symbols
    src = tmp_path / "f.c"
    src.write_text("static int real(void){return 1;}\n"
                   "static void *resolve(void){return (void*)real;}\n"
                   "int lib_sign(void) __attribute__((ifunc(\"resolve\")));\n"
                   "__attribute__((weak)) int lib_verify(void){return 0;}\n")
    so = tmp_path / "libf.so"
    subprocess.run(["gcc", "-shared", "-fPIC", "-o", str(so), str(src)], check=True)
    assert {"lib_sign", "lib_verify"} <= set(exported_symbols(str(so)))


# ----------------------------------------------------------------------
# LMS/XMSS key state: a one-time key used twice is broken
# ----------------------------------------------------------------------

def _state_audit(tmp_path, state):
    path, keep = _hbs_shim(tmp_path, lms_only=True, state=state)
    return _audit_hbs(path, per_group=1)


def test_hbs_state_correct_library_passes_every_state_check(tmp_path):
    r = _state_audit(tmp_path, True)
    p, t = r["detail"]["LMS state"]
    assert t == 5 and p == t, r["failures"]
    assert r["verified"]


@pytest.mark.parametrize("bug,check,words", [
    ("no_advance", "no leaf issued twice", "issued"),
    ("memory_only", "state durable before release", "restart"),
    ("no_refuse", "refuses once exhausted", "signed again after leaf 2^h-1"),
])
def test_hbs_state_catches_each_planted_state_bug(tmp_path, bug, check, words):
    r = _state_audit(tmp_path, bug)
    assert not r["verified"]
    hit = [f for f in r["failures"] if f["stage"] == "LMS state" and check in f["case"]]
    assert hit and words in hit[0]["detail"], r["failures"]


def test_hbs_state_without_state_support_is_not_applicable(tmp_path):
    path, keep = _hbs_shim(tmp_path, lms_only=True)
    r = _audit_hbs(path, per_group=1)
    assert "LMS state" not in r["detail"]
    assert "leaf reuse cannot be checked" in r["not_applicable"]["LMS state"][1]
    from pq_verify.report import to_json_hbs_audit
    assert to_json_hbs_audit(r)["scope"]["complete"] is False


def test_a_mutant_must_add_a_failure_the_library_does_not_already_have(tmp_path,
                                                                       monkeypatch):
    """xmss-reference already fails two key-state checks upstream. A mutant
    used to count as caught whenever its stage failed at all -- on that row,
    every mutant 'caught' itself for free."""
    va, _root = _vendor_audit()
    monkeypatch.setattr(va, "mutate", lambda src, m, dest: dest)
    row = {"library": "lib", "build": "b",
           "failing": ["XMSS state: S: every issued signature verifies"],
           "mutants": [{"name": "m", "fails": ["XMSS state"]}]}
    known = {"results": {"XMSS state": [8, 10]},
             "failing": ["XMSS state: S: every issued signature verifies"]}
    new = {"results": {"XMSS state": [7, 10]},
           "failing": ["XMSS state: S: every issued signature verifies",
                       "XMSS state: S: no leaf issued twice"]}
    with contextlib.redirect_stdout(io.StringIO()) as out:
        assert va._check_mutants(row, tmp_path, tmp_path, lambda s, i: "x",
                                 lambda so: known) == 1
    assert "MISSED" in out.getvalue()
    with contextlib.redirect_stdout(io.StringIO()):
        assert va._check_mutants(row, tmp_path, tmp_path, lambda s, i: "x",
                                 lambda so: new) == 0


def test_workflows_pin_their_runner_image():
    """ubuntu-latest moves under us (Ubuntu 26 from 2026-10-19): a new gcc or
    OpenSSL would change what the pinned vendor rows were built with, and a
    reproducible result must name the image it ran on."""
    import pathlib, re
    wf = pathlib.Path(__file__).resolve().parent.parent / ".github" / "workflows"
    if not wf.is_dir():
        pytest.skip("no workflows in this layout")
    floating = [f"{f.name}: {m}" for f in sorted(wf.glob("*.yml"))
                for m in re.findall(r"runs-on:\s*(\S+)", f.read_text())
                if m.endswith("-latest")]
    assert not floating, floating


# ----------------------------------------------------------------------
# LMS in the prompt/response path: an HSM signs with its own key
# ----------------------------------------------------------------------

_LMS_SET = "LMS_SHA256_M32_H5/LMOTS_SHA256_N32_W1"


def _answer_lms(prompt, reuse=False, own_seed=b"\x07" * 32):
    """A responder: computes keyGen and sigVer, and signs sigGen messages with
    its OWN key at sequential leaves (or, with reuse, leaf 0 twice)."""
    from pq_verify import hbs as H
    suites = []
    for s in prompt["suites"]:
        groups = []
        for g in s["testGroups"]:
            t_, o_ = H.LMS_BY_NAME[g["lmsMode"]], H.LMOTS_BY_NAME[g["lmOtsMode"]]
            out = {"tgId": g["tgId"], "tests": []}
            if s["mode"] == "sigGen":
                tree = H.LMSTree(t_, o_, own_seed, b"\x01" * 16)
                out["publicKey"] = tree.public_key.hex()
            for i, t in enumerate(g["tests"]):
                a = {"tcId": t["tcId"]}
                if s["mode"] == "keyGen":
                    a["publicKey"] = H.LMSTree(t_, o_, bytes.fromhex(t["seed"]),
                                               bytes.fromhex(t["i"])).public_key.hex()
                elif s["mode"] == "sigGen":
                    q = 0 if reuse and i < 2 else i
                    a["signature"] = tree.sign(bytes.fromhex(t["message"]), q,
                                               bytes(H.LMOTS[o_][2])).hex()
                else:
                    a["testPassed"] = H.lms_verify(bytes.fromhex(g["publicKey"]),
                                                   bytes.fromhex(t["message"]),
                                                   bytes.fromhex(t["signature"]))
                out["tests"].append(a)
            groups.append(out)
        suites.append({"suite": s["suite"], "testGroups": groups})
    return {"promptId": prompt["promptId"], "parameterSet": prompt["parameterSet"],
            "suites": suites}


def test_fresh_lms_round_trip_and_leaf_reuse(tmp_path):
    import json as _json
    key, prompt = _fresh_round(tmp_path, _LMS_SET, count=1)
    assert {s["suite"] for s in prompt["suites"]} == {
        "LMS-keyGen-1.0", "LMS-sigGen-1.0", "LMS-sigVer-1.0"}
    good = tmp_path / "good.json"
    good.write_text(_json.dumps(_answer_lms(prompt)))
    code, out = _cli("--verify-response", str(good), "--fresh-key", str(key))
    assert code == 0 and "RESULT: VERIFIED" in out, out
    bad = tmp_path / "reuse.json"
    bad.write_text(_json.dumps(_answer_lms(prompt, reuse=True)))
    code, out = _cli("--verify-response", str(bad), "--fresh-key", str(key))
    assert code == 1 and "a one-time key used twice" in out, out


def test_lms_siggen_answer_must_be_the_groups_key_type(tmp_path):
    """A signature under a key of another parameter set does not answer the
    question, however valid it is."""
    import json as _json
    key, prompt = _fresh_round(tmp_path, _LMS_SET, count=1)
    doc = _answer_lms(prompt)
    from pq_verify import hbs as H
    other = H.LMSTree(H.LMS_BY_NAME["LMS_SHA256_M32_H5"],
                      H.LMOTS_BY_NAME["LMOTS_SHA256_N32_W2"], b"\x07" * 32, b"\x01" * 16)
    for s, sq in zip(doc["suites"], prompt["suites"]):
        if sq["mode"] == "sigGen":
            s["testGroups"][0]["publicKey"] = other.public_key.hex()
    p = tmp_path / "r.json"
    p.write_text(_json.dumps(doc))
    code, out = _cli("--verify-response", str(p), "--fresh-key", str(key))
    assert code == 1 and "publicKey is not a LMS_SHA256_M32_H5/LMOTS_SHA256_N32_W1" in out


def test_large_lms_sets_get_siggen_questions_only():
    """An HSM key of height 20 cannot be built in Python to pose keyGen or
    sigVer questions; the black-box part, sigGen, still applies."""
    from pq_verify.fresh import build
    q, _ = build("LMS_SHA256_M32_H20/LMOTS_SHA256_N32_W8", b"\x01" * 32, 1)
    assert [s["suite"] for s in q] == ["LMS-sigGen-1.0"]


def test_pinned_lms_prompt_is_offered():
    from pq_verify.response import available_parameter_sets, build_prompt
    sets = available_parameter_sets()
    lms = [s for s in sets if s.startswith("LMS_")]
    assert lms, sets
    doc = build_prompt(lms[0])
    assert any(g.get("groupAnswerFields") == ["publicKey"]
               for s in doc["suites"] if s["mode"] == "sigGen" for g in s["testGroups"]) \
        or all(s["mode"] != "sigGen" for s in doc["suites"])


def test_symbol_listing_strips_the_mach_o_underscore(monkeypatch):
    """Mach-O prefixes every C symbol with '_'; ctypes looks it up without."""
    import pq_verify.symbols as S
    monkeypatch.setattr(S.sys, "platform", "darwin")
    monkeypatch.setattr(S, "_nm", lambda args: "0000000000003f50 T _k768_keypair_derand\n"
                                               "0000000000003f60 T _k768_dec\n"
                                               "                 U _memcpy\n")
    assert S.exported_functions("lib.dylib") == ["k768_keypair_derand", "k768_dec"]


def test_engine_flags_that_do_not_travel_are_dropped(monkeypatch, tmp_path):
    """-lrt does not exist on macOS and Apple clang rejects -march=native; an
    engine that cannot build is a skipped check, so the flags must yield."""
    import pq_verify.core as core
    calls = []

    class P:
        def __init__(self, rc):
            self.returncode, self.stdout, self.stderr = rc, "", ""

    def fake_run(argv, **kw):
        calls.append(argv)
        return P(1 if "-march=native" in argv else 0)
    monkeypatch.setattr(core.subprocess, "run", fake_run)
    monkeypatch.setattr(core.sys, "platform", "darwin")
    proc = core._cc("gcc", "-O3 -march=native -shared -fPIC -lm -lrt", "o.so", "s.c")
    assert proc.returncode == 0
    assert all("-lrt" not in a for a in calls)
    # native tuning is kept under its arm64 spelling, not dropped
    assert "-march=native" not in calls[-1] and "-mcpu=native" in calls[-1]
    assert core.ENGINE_FLAGS["o.so"]["native"] is True


def test_linux_engine_flags_are_unchanged(monkeypatch):
    """On Linux the engines build with exactly the flags they always had."""
    import pq_verify.core as core
    calls = []

    class P:
        returncode, stdout, stderr = 0, "", ""
    monkeypatch.setattr(core.subprocess, "run", lambda argv, **k: calls.append(argv) or P())
    monkeypatch.setattr(core.sys, "platform", "linux")
    core._cc("gcc", "-O3 -march=native -shared -fPIC -lm -lrt", "o.so", "s.c")
    assert calls == [["gcc", "-O3", "-march=native", "-shared", "-fPIC", "-lm", "-lrt",
                      "-o", "o.so", "s.c"]]


def test_engine6_skip_names_are_the_checks_each_audit_records():
    """When an Engine 6 engine cannot be built, its checks are recorded as
    skipped under these names, so the list must be what the audits run."""
    from pq_verify import core
    eng = core.compile_engine6()
    core.bind_engine6(eng)
    fns = {"rank2": core.audit_engine6_rank2, "genus2": core.audit_engine6_genus2,
           "quintic": core.audit_engine6_quintic, "genus4": core.audit_engine6_genus4}
    for key, (title, names) in core._E6_CHECKS.items():
        if not eng.get(key):
            pytest.skip(f"engine6/{key} not built here")
        with contextlib.redirect_stdout(io.StringIO()):
            r = fns[key](eng[key])
        assert r.engine == title
        got = [t["name"] for t in r.tests]
        assert len(got) == len(names), (key, got)
        assert all(g.startswith(n) for g, n in zip(got, names)), (key, got, names)


def test_an_engine6_build_failure_is_degraded_not_silent(monkeypatch):
    """compile_engine6 used to print a failure and register nothing: the
    integrity report then said every engine built while four checks were
    gone from the suite."""
    from pq_verify import core

    class P:
        returncode, stdout, stderr = 1, "", "error: no matching function"
    monkeypatch.setattr(core, "_cc", lambda *a, **k: P())
    before = list(core.DEGRADED["engines"])
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            eng = core.compile_engine6()
        assert all(v is None for v in eng.values())
        assert "engine6/genus2" in core.DEGRADED["engines"]
        assert "no matching function" in core.ENGINE_ERRORS["engine6/genus2"]
    finally:
        core.DEGRADED["engines"][:] = before


def test_every_self_suite_check_has_a_track():
    """The headline counts PQC checks only; every other engine is reported
    under its track with the post-quantum work it is being realigned toward.
    A new audit nobody classified fails here instead of joining a headline."""
    from pq_verify.core import main as run_selftest, engine_track, track_totals
    with _isolated_degraded():
        with contextlib.redirect_stdout(io.StringIO()):
            results = run_selftest(quick=True)
    for r in results:
        track, target = engine_track(r.engine)
        assert track in ("pqc", "harness", "classical", "research")
        if track in ("classical", "research"):
            assert target, f"{r.engine} has no realignment target"
    totals = track_totals(results)
    assert totals["pqc"][1] + totals["pqc"][2] > 0
    assert sum(v[1] + v[2] for v in totals.values()) == sum(len(r.tests) for r in results)


def test_cpp_engines_build_as_cpp17(monkeypatch):
    import pq_verify.core as core
    seen = []

    class P:
        returncode, stdout, stderr = 0, "", ""
    monkeypatch.setattr(core.subprocess, "run", lambda argv, **k: seen.append(argv) or P())
    core._cc("g++", "-O3 -shared -fPIC -lm", "o.so", "s.cpp")
    core._cc("gcc", "-O3 -shared -fPIC -lm", "o.so", "s.c")
    assert "-std=c++17" in seen[0] and "-std=c++17" not in seen[1]
