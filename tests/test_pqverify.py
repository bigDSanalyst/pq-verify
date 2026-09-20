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
    assert pq_verify.__version__ == "2.8.0"


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


# ----------------------------------------------------------------------
# CLI exit codes — a run that did not verify must not pass a CI gate
# ----------------------------------------------------------------------

def _cli(*argv):
    from pq_verify.cli import main
    with contextlib.redirect_stdout(io.StringIO()) as out:
        code = main(list(argv))
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
            out[g["parameterSet"]] = (t["ek"], t["c"], t["k"])
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
    ek, ct, k = (bytes.fromhex(h) for h in kem_vectors[g["kem"]])
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

@pytest.mark.parametrize("group", sorted(GROUPS))
def test_a_conforming_transcript_verifies(group, kem_vectors, tmp_path):
    path = _write_transcript(tmp_path, "t.json", _transcript(group, kem_vectors))
    res = verify_hybrid(path, verbose=False)
    assert res["status"] == "VERIFIED", res["findings"]
    assert res["verified"] is True
    assert res["passed"] == res["total"] > 0
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


def test_the_prompt_never_asks_for_a_decapsulation_key():
    """Asking for a private KEM key would be asking for the whole secret."""
    from pq_verify.hybrid import build_hybrid_prompt
    for group in GROUPS:
        doc = build_hybrid_prompt(group)
        blob = _json.dumps(doc).lower()
        assert "decapsulationkey" not in blob
        assert '"dk"' not in blob
        assert set(doc["response"]) >= {"group", "clientShare"}


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
