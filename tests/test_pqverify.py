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
    assert pq_verify.__version__ == "2.7.0"


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
