"""
pq_verify.report — machine-readable output.

Two formats:

  to_json(results)   native schema, stable, for programmatic use
  to_sarif(results)  SARIF 2.1.0, which GitHub Code Scanning ingests natively
                     and which DefectDojo / Snyk / AWS Security Hub accept

Why SARIF: a verifier that reports only to a terminal cannot become part of a
security workflow. SARIF is the format security platforms already read, so
findings surface as annotations in a pull request rather than as text someone
has to go and look at.
"""

import datetime
import hashlib
import json
import os

SARIF_VERSION = "2.1.0"
SARIF_SCHEMA = ("https://raw.githubusercontent.com/oasis-tcs/sarif-spec/"
                "master/Schemata/sarif-schema-2.1.0.json")

# Rules the verifier can report. Kept explicit rather than generated so the
# descriptions stay accurate and reviewable.
RULES = {
    "PQV000": {
        "name": "CannotVerify",
        "short": "The run could not verify this — not a pass and not a failure",
        "full": ("Verification did not take place: the input was unreadable, "
                 "the response answered a different question set, or part of "
                 "the question set went unanswered. This is reported "
                 "separately from a verified failure so that an absent check "
                 "is never read as a passing one."),
        "level": "warning",
    },
    "PQV001": {
        "name": "NttMismatch",
        "short": "NTT output does not match the FIPS reference",
        "full": ("The number-theoretic transform produced output differing from an "
                 "independently computed FIPS 203/204 reference. An implementation "
                 "with this fault will not interoperate with conforming "
                 "implementations and will fail NIST ACVP validation."),
        "level": "error",
    },
    "PQV002": {
        "name": "FreivaldsFailure",
        "short": "Freivalds probabilistic check failed",
        "full": ("Verification of the linear map via r*y == (NTT^T r)*x failed. "
                 "The probability of a correct transform failing this check is "
                 "at most q^-k per polynomial, so failures indicate a real "
                 "arithmetic fault rather than sampling noise."),
        "level": "error",
    },
    "PQV003": {
        "name": "PrimitivityFailure",
        "short": "Root of unity has the wrong multiplicative order",
        "full": ("The twiddle factor does not satisfy the order required by the "
                 "scheme (ML-KEM: order n, incomplete transform; ML-DSA: order 2n, "
                 "complete transform). The transform cannot be correct."),
        "level": "error",
    },
    "PQV004": {
        "name": "KatFailure",
        "short": "Known-answer test failed against the independent reference",
        "full": ("The non-circular known-answer test failed. This test compares "
                 "against a reference derived from the FIPS specification, not "
                 "against the implementation itself, so it detects errors that "
                 "self-consistent testing cannot."),
        "level": "error",
    },
    "PQV006": {
        "name": "ResponseMismatch",
        "short": "Vendor-supplied answer differs from the pinned NIST value",
        "full": ("A test case in a prompt/response run produced a value that "
                 "does not match NIST's published answer byte for byte. The "
                 "implementation that produced this response does not compute "
                 "the standard correctly for that input."),
        "level": "error",
    },
    "PQV007": {
        "name": "HybridCompositionMismatch",
        "short": "Hybrid key agreement does not compose the way RFC 10024 pins it",
        "full": ("A hybrid transcript's components are not laid out as "
                 "RFC 10024 requires for the negotiated group: a wrong "
                 "length, a component at the wrong offset, an encapsulation "
                 "key that fails the FIPS 203 Section 7.2 check the RFC makes "
                 "a MUST, an invalid ECDHE point, or a shared secret whose "
                 "halves are in the wrong order. Both components can pass "
                 "every ACVP vector while this is wrong, because ACVP never "
                 "sees the concatenation."),
        "level": "error",
    },
    "PQV008": {
        "name": "SignatureConformanceFailure",
        "short": "ML-DSA library output or verdict differs from NIST or Wycheproof",
        "full": ("Driven with NIST's ACVP ML-DSA vectors and Wycheproof's edge "
                 "cases, the library produced a key or signature that differs "
                 "from the published one byte for byte, accepted a signature "
                 "that must be rejected (a forgery or a malleated encoding), "
                 "rejected a valid one, or drew randomness FIPS 204 does not "
                 "call for. A verifier that accepts a malleated signature "
                 "breaks strong unforgeability; one that rejects a valid one "
                 "breaks interoperability."),
        "level": "error",
    },
    "PQV009": {
        "name": "StatefulSignatureConformanceFailure",
        "short": "LMS/XMSS library output or verdict differs from the pinned vectors",
        "full": ("Driven through its pqv_hbs adapter with NIST's LMS vectors, the "
                 "pinned LMS/XMSS KATs, RFC 8554's test cases and signatures "
                 "malformed in one field, the library produced a key or signature "
                 "that differs from the vector, rejected a valid signature, or "
                 "accepted one that must be rejected. Accepting a malformed "
                 "signature is a forgery path."),
        "level": "error",
    },
    "PQV005": {
        "name": "BoundaryVectorFailure",
        "short": "Boundary/edge-case vector failed",
        "full": ("An edge-case input (zero polynomial, maximum coefficients, "
                 "single-coefficient impulse) produced incorrect output."),
        "level": "warning",
    },
}

_FINDING_MAP = (
    # Scheme prefixes first: a finding's own text may contain a later needle
    # ("LMS malformed" holds "malformed", which means CannotVerify below).
    ("ML-DSA:",     "PQV008"),
    ("LMS/XMSS:",   "PQV009"),
    ("cannot verify", "PQV000"),
    ("malformed",   "PQV000"),
    ("response:",   "PQV006"),
    ("hybrid:",     "PQV007"),
    ("NTT:",        "PQV001"),
    ("Freivalds",   "PQV002"),
    ("Primitiv",    "PQV003"),
    ("KAT",         "PQV004"),
    ("boundary",    "PQV005"),
    ("Boundary",    "PQV005"),
)


def _rule_for(finding_text):
    for needle, rule in _FINDING_MAP:
        if needle in finding_text:
            return rule
    return "PQV001"


# What this tool does not observe, stated as a field rather than left for the
# reader to infer. Functional conformance and side-channel behaviour are
# independent: KyberSlash and Clangover were byte-exact correct against every
# vector and still leaked the key through timing. A report that is silent
# about this invites "verified" to be read as "safe to deploy".
SIDE_CHANNEL = {
    "measured": False,
    "summary": ("not measured — execution time, power and electromagnetic "
                "behaviour were not observed"),
    "detail": ("pq-verify compares values against NIST's published answers. "
               "It does not execute the implementation under measurement and "
               "cannot detect a timing-dependent, cache-dependent or "
               "power-dependent implementation that computes the correct "
               "result. Establishing that requires leakage assessment against "
               "the deployed binary on the deployed hardware."),
}


def side_channel_scope():
    """The scope declaration carried by every report. Copied, not shared."""
    return dict(SIDE_CHANNEL)


def artifact_bound(path):
    """Binding for a run that loaded a file: `artifact: sha256 <hex>`."""
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    digest = h.hexdigest()
    return {"bound": True, "sha256": digest, "path": os.path.abspath(path),
            "summary": f"sha256 {digest}",
            "detail": "The audited computation was performed by this file."}


def artifact_unbound(reason):
    """Binding for a run that loaded no file: `artifact: none — <reason>`."""
    return {"bound": False, "sha256": None, "path": None,
            "summary": f"none — {reason}",
            "detail": ("No binary was loaded, so the result is not bound to "
                       "any artifact.")}


def to_json(results, extra=None, artifact=None):
    """Native schema — stable, versioned, safe to parse.

    `artifact` states the binding: what file, if any, produced the audited
    computation. It is a field rather than a caveat so a reader can see what
    was bound and what was not, the same way the coverage counts are data.
    """
    passed = sum(r.get("passed", 0) for r in results)
    total = sum(r.get("total", 0) for r in results)
    findings = sum(len(r.get("findings", [])) for r in results)
    doc = {
        "schema": "pq-verify/scan-result",
        "schema_version": "1.1",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "summary": {
            "targets": len(results),
            "checks_passed": passed,
            "checks_total": total,
            "findings": findings,
            "verified": findings == 0 and total > 0,
        },
        "targets": [
            {
                "name": r.get("name"),
                "checks_passed": r.get("passed"),
                "checks_total": r.get("total"),
                "findings": r.get("findings", []),
                "kat": r.get("kat"),
            }
            for r in results
        ],
        "side_channel": side_channel_scope(),
    }
    if artifact is not None:
        doc["artifact"] = artifact
    if extra:
        doc.update(extra)
    return doc


def to_json_response(result):
    """Native schema for a prompt/response run (pq_verify.response)."""
    doc = {
        "schema": "pq-verify/response-result",
        "schema_version": "1.1",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "parameter_set": result.get("parameter_set"),
        "status": result.get("status"),
        "verified": result.get("verified", False),
        "artifact": result.get("artifact") or artifact_unbound(
            "vendor-supplied response"),
        "side_channel": side_channel_scope(),
        "prompt": {
            "prompt_id": result.get("prompt_id"),
            "response_prompt_id": result.get("response_prompt_id"),
            "binding": result.get("prompt_binding"),
            "vector_source": result.get("vector_source"),
        },
        "response": {
            "file": result.get("response_file"),
            "sha256": result.get("response_sha256"),
            "implementation": result.get("implementation"),
        },
        "coverage": {
            "questions": result.get("questions", 0),
            "answered": result.get("answered", 0),
            "unanswered": result.get("unanswered", 0),
            "unknown": result.get("unknown", []),
        },
        "summary": {
            "checks_passed": result.get("passed", 0),
            "checks_total": result.get("total", 0),
            "malformed": result.get("malformed", 0),
            "findings": len(result.get("findings", [])),
        },
        "groups": {k: {"passed": v[0], "answered": v[1], "total": v[2]}
                   for k, v in (result.get("detail") or {}).items()},
        "findings": result.get("findings", []),
    }
    return doc


def _scope(checked, not_applicable=0, not_run=0, na_why=None):
    """What a verdict covers, as data.

    VERIFIED says every check that ran passed. It does not say how many did
    not run: a library can declare a parameter set unsupported (its adapter
    decides that), and signing is sampled within a budget by default. Without
    this field a VERIFIED over one parameter set and a VERIFIED over all of
    them read the same. --require-full-coverage fails on a partial scope.
    """
    complete = checked > 0 and not not_applicable and not not_run
    bits = []
    if not_applicable:
        bits.append(f"{not_applicable} not applicable"
                    + (f" ({na_why})" if na_why else ""))
    if not_run:
        bits.append(f"{not_run} not run (sampled or over budget)")
    return {"complete": complete, "checked": checked,
            "not_applicable": not_applicable, "not_run": not_run,
            "statement": ("full: every case pq-verify has for this target ran"
                          if complete else
                          f"partial: {checked} checked; " + "; ".join(bits)
                          if bits else "nothing checked")}


def _envelope(schema, artifact, reason="no binary was loaded"):
    """Common head of every native report: what it is, when, and what it binds to."""
    return {
        "schema": schema,
        "schema_version": "1.1",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "artifact": artifact if artifact is not None else artifact_unbound(reason),
        "side_channel": side_channel_scope(),
    }


def to_json_kem(result, artifact=None, param_set=None, library=None,
                reason=None):
    """Native schema for pqverify_audit_kem.

    `result` is None when the library exposed no derandomised entry points:
    that is CANNOT VERIFY, not a failure, and the artifact stays bound because
    the file was still read.
    """
    doc = _envelope("pq-verify/kem-audit-result", artifact)
    doc["parameter_set"] = param_set
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc["status"] = "CANNOT VERIFY"
        doc["verified"] = False
        doc["summary"] = {"checks_passed": 0, "checks_total": 0, "findings": 1}
        doc["stages"] = {}
        doc["symbols"] = {}
        doc["findings"] = ["cannot verify: " + (
            reason or "the library exposes no derandomised keygen/encaps entry "
                     "points, so NIST's seeded vectors cannot be driven "
                     "through it")]
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["status"] = "VERIFIED" if result.get("verified") else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["verified"] = bool(result.get("verified"))
    doc["symbols"] = result.get("symbols", {})
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else 1}
    if result.get("accumulated"):
        doc["accumulated"] = result["accumulated"]
    if result.get("constant_time"):
        doc["constant_time"] = result["constant_time"]
        ct = result["constant_time"]
        if "unavailable" not in ct:
            doc["side_channel"]["constant_time_checked"] = {
                "operations": sorted(ct["stages"]), "tool": ct.get("tool"),
                "scope": ("secret-dependent branches and memory addresses in this "
                          "binary, by Valgrind memcheck taint; not instruction "
                          "timing (division), power, EM or microarchitecture, "
                          "and not key generation"),
                "leak_free": all(p == t for p, t in ct["stages"].values())}
    doc["stages"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    keycheck = result.get("keycheck") or {}
    doc["keycheck"] = keycheck
    findings = []
    edge = result.get("edge") or {}
    if edge:
        doc["edge"] = {"vectors": edge.get("vectors"),
                       "not_applicable": edge.get("not_applicable", 0),
                       "failures": edge.get("failures", [])}
    _edge_msg = {
        "edgeValid": lambda p, t: (f"stage edgeValid: {p}/{t} Wycheproof/CCTV edge-case "
                                   f"vectors reproduced byte-for-byte"),
        "edgeEk": lambda p, t: (f"stage edgeEk: accepted {t - p} of {t} invalid "
                                f"encapsulation keys (Wycheproof/CCTV, FIPS 203 §7.2)"),
        "edgeDk": lambda p, t: (f"stage edgeDk: accepted {t - p} of {t} invalid "
                                f"decapsulation keys (Wycheproof, FIPS 203 §7.3)"),
    }
    for k, v in (result.get("detail") or {}).items():
        if v[0] == v[1]:
            continue
        if k in _edge_msg:
            findings.append(_edge_msg[k](v[0], v[1]))
            continue
        if k == "accumulated":
            findings.append("stage accumulated: " + (result.get("accumulated") or {}).get(
                "detail", "CCTV accumulated vectors did not match"))
            continue
        if k.startswith("ct:"):
            ct = result.get("constant_time") or {}
            if "unavailable" in ct:
                findings.append(f"constant time: requested but could not run ({ct['unavailable']})")
            else:
                where = "; ".join(f"{l['kind']} in {l['function']}"
                                  for l in (ct.get("leaks") or {}).get(k[3:], []))
                findings.append(f"stage {k}: secret-dependent behaviour under Valgrind "
                                f"memcheck: {where}")
            continue
        m = keycheck.get(k)
        if m is None:
            findings.append(f"stage {k}: {v[0]}/{v[1]} match NIST byte-for-byte")
            continue
        sec = "7.2" if k == "ekCheck" else "7.3"
        if m.get("accepted_invalid"):
            findings.append(
                f"stage {k}: accepted {m['accepted_invalid']} key(s) NIST marks "
                f"invalid (FIPS 203 §{sec}); this API does not perform the "
                f"input check, so every caller must")
        if m.get("rejected_valid"):
            findings.append(
                f"stage {k}: rejected {m['rejected_valid']} key(s) NIST marks valid")
    doc["findings"] = findings
    doc["summary"]["findings"] = len(findings)
    return doc


def to_json_dsa(result, artifact=None, param_set=None, library=None, reason=None):
    """Native schema for pqverify_audit_dsa.

    Stages the library has no entry point for are reported under
    `not_applicable` with the reason, and are never counted as passed: a
    library that exposes only pure ML-DSA is VERIFIED for what it exposes,
    and the report says what that leaves out.
    """
    doc = _envelope("pq-verify/dsa-audit-result", artifact)
    doc["parameter_set"] = param_set
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc.update(status="CANNOT VERIFY", verified=False, stages={}, symbols={},
                   not_applicable={},
                   summary={"checks_passed": 0, "checks_total": 0, "findings": 1},
                   findings=["cannot verify: " + (
                       reason or "no ML-DSA entry point could be bound unambiguously")])
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["calling_convention"] = result.get("abi")
    doc["randomness_harness"] = bool(result.get("harness"))
    doc["symbols"] = result.get("symbols", {})
    doc["stages"] = {k: {"passed": v[0], "total": v[1],
                         "via": (result.get("via") or {}).get(k)}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_applicable"] = {k: {"count": v[0], "reason": v[1]}
                             for k, v in (result.get("not_applicable") or {}).items()}
    edge = result.get("edge") or {}
    if edge:
        doc["edge"] = {"vectors": edge.get("vectors"),
                       "not_applicable": edge.get("not_applicable", 0),
                       "failures": edge.get("failures", [])}
    findings = []
    acvp_fail = result.get("failures") or []
    edge_fail = edge.get("failures") or []
    for k, v in (result.get("detail") or {}).items():
        if k == "accumulated" and v[0] != v[1]:
            findings.append("ML-DSA: stage accumulated: " + (result.get("accumulated") or {})
                            .get("detail", "CCTV accumulated vectors did not match"))
            continue
        if v[0] != v[1]:
            what = ("Wycheproof edge cases handled as specified" if k.startswith("edge:")
                    else "verdicts match NIST" if k.startswith("sigVer")
                    else "outputs match NIST byte-for-byte")
            if k.startswith("edge:"):
                first = next((f for f in edge_fail if f["stage"] == k[5:]), None)
                where = (f"; first: {first['case']} {first['flags']}: {first['detail']}"
                         if first else "")
            else:
                first = next((f for f in acvp_fail if f["stage"] == k), None)
                where = (f"; first: NIST tcId {first['tcId']}: {first['detail']}"
                         if first else "")
            findings.append(f"ML-DSA: stage {k}: {v[0]}/{v[1]} {what}{where}")
    for r in result.get("rng") or []:
        findings.append(f"ML-DSA: randomness: {r}")
    if result.get("accumulated"):
        doc["accumulated"] = result["accumulated"]
    doc["failures"] = result.get("failures", [])
    doc["findings"] = findings
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "not_applicable": result.get("not_applicable_total", 0),
                      "findings": len(findings)}
    doc["scope"] = _scope(t, result.get("not_applicable_total", 0),
                          na_why="the library exports no entry point for them")
    return doc


def to_json_hbs(result):
    """Native schema for pqverify_hbs (LMS/HSS, XMSS/XMSS^MT, non-NIST
    vectors). Cases over the key-generation budget are listed under
    `not_run` and never counted as passed."""
    doc = _envelope("pq-verify/hbs-result", None,
                    reason="reference conformance, no vendor binary loaded")
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["vectors"] = result.get("vectors")
    doc["reference"] = result.get("reference")
    doc["budget"] = result.get("budget")
    doc["groups"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_run"] = {k: {"count": v[0], "reason": v[1]}
                      for k, v in (result.get("not_run") or {}).items()}
    doc["failures"] = result.get("failures", [])
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "not_run": result.get("not_run_total", 0),
                      "findings": 0 if p == t else t - p}
    return doc


def to_json_fndsa(result):
    """Native schema for pqverify_fndsa: FN-DSA verification on the draft
    track. `track` and `standard` say so in every report; a VERIFIED here is
    against Falcon round 3, never against a final FIPS 206."""
    doc = _envelope("pq-verify/fndsa-result", None,
                    reason="reference conformance, no vendor binary loaded")
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["track"] = "draft"
    doc["standard"] = result.get("standard", "FIPS 206 (draft)")
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["vectors"] = result.get("vectors")
    doc["reference"] = result.get("reference")
    doc["native_engine"] = bool(result.get("native_engine"))
    doc["groups"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["failures"] = result.get("failures", [])
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else t - p}
    return doc


def to_json_fndsa_audit(result, artifact=None, param_set=None, library=None,
                        reason=None):
    """Native schema for pqverify_audit_fndsa: a vendor FN-DSA library on the
    draft track. A VERIFIED here is against Falcon round 3, never a final
    FIPS 206, and `track` says so."""
    doc = _envelope("pq-verify/fndsa-audit-result", artifact)
    doc["track"] = "draft"
    doc["standard"] = "FIPS 206 (draft)"
    doc["parameter_set"] = param_set
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc.update(status="CANNOT VERIFY", verified=False, stages={}, symbols={},
                   not_applicable={},
                   summary={"checks_passed": 0, "checks_total": 0, "findings": 1},
                   findings=["cannot verify: " + (
                       reason or "no FN-DSA entry point could be bound unambiguously")])
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["calling_convention"] = result.get("abi")
    doc["padded"] = bool(result.get("padded"))
    doc["symbols"] = result.get("symbols", {})
    doc["vectors"] = result.get("vectors")
    doc["stages"] = {k: {"passed": v[0], "total": v[1],
                         "via": (result.get("via") or {}).get(k)}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_applicable"] = {k: {"count": v[0], "reason": v[1]}
                             for k, v in (result.get("not_applicable") or {}).items()}
    fails = result.get("failures") or []
    findings = []
    for k, v in (result.get("detail") or {}).items():
        if v[0] != v[1]:
            first = next((f for f in fails if f["stage"] == k), None)
            where = f"; first: {first['case']}: {first['detail']}" if first else ""
            findings.append(f"FN-DSA (draft): stage {k}: {v[0]}/{v[1]}{where}")
    doc["failures"] = fails
    doc["findings"] = findings
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "not_applicable": result.get("not_applicable_total", 0),
                      "findings": len(findings)}
    doc["scope"] = _scope(t, result.get("not_applicable_total", 0),
                          na_why="the API cannot express them")
    return doc


_MCELIECE_STANDARD = "Classic McEliece round 4 (not a FIPS standard)"


def to_json_mceliece(result):
    """Native schema for pqverify_mceliece: pq-verify's Classic McEliece
    reference against the pinned KATs. Classic McEliece is not a FIPS
    standard, and `track` / `standard` say so in every report."""
    doc = _envelope("pq-verify/mceliece-result", None,
                    reason="reference conformance, no vendor binary loaded")
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["track"] = "classic-mceliece"
    doc["standard"] = result.get("standard", _MCELIECE_STANDARD)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["vectors"] = result.get("vectors")
    doc["reference"] = result.get("reference")
    doc["groups"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["failures"] = result.get("failures", [])
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else t - p}
    return doc


def to_json_mceliece_audit(result, artifact=None, param_set=None, library=None,
                           reason=None):
    """Native schema for pqverify_audit_mceliece: a vendor Classic McEliece
    library. Not a FIPS standard; `track` says so."""
    doc = _envelope("pq-verify/mceliece-audit-result", artifact)
    doc["track"] = "classic-mceliece"
    doc["standard"] = _MCELIECE_STANDARD
    doc["parameter_set"] = param_set
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc.update(status="CANNOT VERIFY", verified=False, stages={}, symbols={},
                   not_applicable={},
                   summary={"checks_passed": 0, "checks_total": 0, "findings": 1},
                   findings=["cannot verify: " + (
                       reason or "no Classic McEliece entry point could be bound "
                                 "unambiguously")])
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["calling_convention"] = result.get("abi")
    doc["symbols"] = result.get("symbols", {})
    doc["vectors"] = result.get("vectors")
    doc["stages"] = {k: {"passed": v[0], "total": v[1],
                         "via": (result.get("via") or {}).get(k)}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_applicable"] = {k: {"count": v[0], "reason": v[1]}
                             for k, v in (result.get("not_applicable") or {}).items()}
    fails = result.get("failures") or []
    findings = []
    ct = result.get("constant_time")
    if ct:
        doc["constant_time"] = ct
        if "unavailable" not in ct:
            doc.setdefault("side_channel", {})["constant_time_checked"] = {
                "operations": sorted(ct["stages"]), "tool": ct.get("tool"),
                "scope": ("secret-dependent branches and memory addresses in this "
                          "binary, by Valgrind memcheck taint, outside the function "
                          "that draws encapsulation's randomness (listed, not "
                          "judged); not key generation, instruction timing, power, "
                          "EM or microarchitecture"),
                "leak_free": all(p == t for p, t in ct["stages"].values())}
    for k, v in (result.get("detail") or {}).items():
        if v[0] != v[1] and k.startswith("ct:"):
            if ct and "unavailable" in ct:
                findings.append(f"constant time: requested but could not run "
                                f"({ct['unavailable']})")
            else:
                where = "; ".join(f"{lk['kind']} in {lk['function']}"
                                  for lk in (ct or {}).get("leaks", {}).get(k[3:], []))
                findings.append(f"Classic McEliece: stage {k}: secret-dependent behaviour "
                                f"under Valgrind memcheck: {where}")
        elif v[0] != v[1]:
            first = next((f for f in fails if f["stage"] == k), None)
            where = f"; first: {first['case']}: {first['detail']}" if first else ""
            findings.append(f"Classic McEliece: stage {k}: {v[0]}/{v[1]}{where}")
    doc["failures"] = fails
    doc["findings"] = findings
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "not_applicable": result.get("not_applicable_total", 0),
                      "findings": len(findings)}
    doc["scope"] = _scope(t, result.get("not_applicable_total", 0),
                          na_why="the parameter set or API has no such case")
    return doc


_HQC_STANDARD = "HQC code layer (selected by NIST; standard not final)"


def to_json_hqc(result):
    """Native schema for pqverify_hqc: pq-verify's HQC code-layer reference
    against the submitters' generator polynomials and decoder answers. HQC's
    standard is not final; `track` / `standard` say so."""
    doc = _envelope("pq-verify/hqc-result", None,
                    reason="reference conformance, no vendor binary loaded")
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["track"] = "hqc"
    doc["standard"] = result.get("standard", _HQC_STANDARD)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["vectors"] = result.get("vectors")
    doc["reference"] = result.get("reference")
    doc["groups"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["failures"] = result.get("failures", [])
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else t - p}
    return doc


def to_json_hqc_audit(result, artifact=None, param_set=None, library=None, reason=None):
    """Native schema for pqverify_audit_hqc: a vendor HQC decoder (the code
    layer, not the KEM). Entry points the library does not export are listed
    and make the scope partial."""
    doc = _envelope("pq-verify/hqc-audit-result", artifact)
    doc["track"] = "hqc"
    doc["standard"] = _HQC_STANDARD
    doc["parameter_set"] = param_set
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc.update(status="CANNOT VERIFY", verified=False, stages={}, symbols={},
                   summary={"checks_passed": 0, "checks_total": 0, "findings": 1},
                   findings=["cannot verify: " + (
                       reason or "no HQC decoder entry point could be bound unambiguously")])
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["profile"] = result.get("profile")
    doc["seed"] = result.get("seed")
    doc["symbols"] = result.get("symbols", {})
    doc["not_exported"] = result.get("not_exported", [])
    doc["stages"] = {k: {"passed": v[0], "total": v[1],
                         "via": (result.get("via") or {}).get(k)}
                     for k, v in (result.get("detail") or {}).items()}
    fails = result.get("failures") or []
    findings = []
    for k, v in (result.get("detail") or {}).items():
        if v[0] != v[1]:
            first = next((f for f in fails if f["stage"] == k), None)
            where = f"; first: {first['case']}: {first['detail']}" if first else ""
            findings.append(f"HQC: stage {k}: {v[0]}/{v[1]}{where}")
    doc["failures"] = fails
    doc["findings"] = findings
    missing = doc["not_exported"]
    doc["summary"] = {"checks_passed": p, "checks_total": t, "findings": len(findings)}
    doc["scope"] = _scope(t, len(missing),
                          na_why="entry points not exported: " + ", ".join(missing))
    return doc


def artifact_harness(path, command):
    """Binding for a harness audit: the harness executable is hashed, and the
    detail says that the library behind it is not."""
    a = artifact_bound(path) if path else artifact_unbound(
        "the harness command runs no file pq-verify could identify")
    a["harness_command"] = list(command)
    a["detail"] = ("A Crucible-protocol harness: this file is the harness. The "
                   "library it wraps is not hashed, and a failure can be the "
                   "harness's wiring as well as the library's.")
    return a


def to_json_harness_audit(result, artifact=None):
    """Native schema for pqverify_audit_harness."""
    doc = _envelope("pq-verify/harness-audit-result", artifact)
    doc["protocol"] = "crucible-jsonl"
    for k in ("parameter_set", "implementation", "command", "vectors",
              "deterministic", "harness_notes", "calls"):
        doc[k] = result.get(k)
    doc["status"] = result["status"]
    doc["verified"] = bool(result.get("verified"))
    doc["stages"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_applicable"] = {k: {"count": v[0], "reason": v[1]}
                             for k, v in (result.get("not_applicable") or {}).items()}
    fails = result.get("failures") or []
    findings = []
    if result["status"] == "CANNOT VERIFY":
        findings.append("cannot verify: " + (result.get("reason") or "nothing checked"))
    for k, v in (result.get("detail") or {}).items():
        if v[0] != v[1]:
            first = next((f for f in fails if f["stage"] == k), None)
            where = f"; first: {first['case']}: {first['detail']}" if first else ""
            findings.append(f"{result.get('parameter_set')}: stage {k}: {v[0]}/{v[1]}{where}")
    doc["failures"] = fails
    doc["findings"] = findings
    doc["summary"] = {"checks_passed": result.get("passed", 0),
                      "checks_total": result.get("total", 0),
                      "not_applicable": result.get("not_applicable_total", 0),
                      "findings": len(findings)}
    doc["scope"] = _scope(result.get("total", 0), result.get("not_applicable_total", 0),
                          na_why="the protocol or this harness cannot express them")
    return doc


def to_json_hbs_audit(result, artifact=None, library=None, reason=None):
    """Native schema for pqverify_audit_hbs. Not applicable (the library
    does not implement it) and not run (over budget or sampled) are listed
    separately and never counted as passed."""
    doc = _envelope("pq-verify/hbs-audit-result", artifact)
    doc["library"] = library or (result or {}).get("library")
    if result is None:
        doc.update(status="CANNOT VERIFY", verified=False, stages={},
                   not_applicable={}, not_run={},
                   summary={"checks_passed": 0, "checks_total": 0, "findings": 1},
                   findings=["cannot verify: " + (reason or "no pqv_hbs adapter")])
        return doc
    p, t = result.get("passed", 0), result.get("total", 0)
    doc["verified"] = bool(result.get("verified"))
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
    doc["implementation"] = result.get("name")
    doc["vectors"] = result.get("vectors")
    doc["budget"] = result.get("budget")
    doc["per_group"] = result.get("per_group")
    doc["stages"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["not_applicable"] = {k: {"count": v[0], "reason": v[1]}
                             for k, v in (result.get("not_applicable") or {}).items()}
    doc["not_run"] = {k: {"count": v[0], "reason": v[1]}
                      for k, v in (result.get("not_run") or {}).items()}
    fails = result.get("failures") or []
    findings = []
    for k, v in (result.get("detail") or {}).items():
        if v[0] != v[1]:
            first = next((f for f in fails if f["stage"] == k), None)
            findings.append(f"LMS/XMSS: stage {k}: {v[0]}/{v[1]}"
                            + (f"; first: {first['case']}: {first['detail']}" if first else ""))
    doc["failures"] = fails
    doc["findings"] = findings
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "not_applicable": result.get("not_applicable_total", 0),
                      "not_run": result.get("not_run_total", 0),
                      "findings": len(findings)}
    doc["scope"] = _scope(t, result.get("not_applicable_total", 0),
                          result.get("not_run_total", 0),
                          na_why="declared unsupported by the library's adapter")
    return doc


def to_json_acvp(suites, artifact=None):
    """Native schema for the ACVP suites (pqverify_acvp / _mldsa_ / _slhdsa_).

    `suites` maps a suite label to that function's result dict. These runs
    verify the reference chain against NIST's published vectors; no vendor
    binary is involved, so the binding is explicitly none.
    """
    doc = _envelope("pq-verify/acvp-result", artifact,
                    reason="reference-chain conformance, no vendor binary loaded")
    p = t = 0
    doc["suites"] = {}
    doc["groups"] = {}
    for label, r in suites.items():
        if not r:
            doc["suites"][label] = {"ran": False, "checks_passed": 0,
                                    "checks_total": 0, "verified": False}
            continue
        p += r.get("passed", 0)
        t += r.get("total", 0)
        doc["suites"][label] = {"ran": True,
                                "checks_passed": r.get("passed", 0),
                                "checks_total": r.get("total", 0),
                                "verified": bool(r.get("verified")),
                                "vectors": r.get("vectors"),
                                "reference": r.get("reference")}
        for g, v in (r.get("detail") or {}).items():
            doc["groups"][f"{label}/{g}"] = {"passed": v[0], "total": v[1]}
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else t - p}
    # A requested suite that could not run leaves its claim unchecked, so the
    # run is not verified however well the others did.
    missing = sorted(k for k, v in doc["suites"].items() if not v["ran"])
    doc["summary"]["not_run"] = missing
    doc["verified"] = bool(t) and p == t and not missing
    doc["status"] = ("VERIFIED" if doc["verified"] else
                     "FINDINGS PRESENT" if p < t else "CANNOT VERIFY")
    return doc


def to_json_hybrid(result):
    """Native schema for a hybrid composition run (pq_verify.hybrid).

    `checks_total` counts only what actually ran. A check with no input is
    reported under `not_checked`, and one that does not exist for this group
    under `not_applicable` — neither is ever folded into the passing count.
    """
    doc = _envelope("pq-verify/hybrid-result", result.get("artifact"),
                    reason="vendor-supplied transcript")
    doc["group"] = result.get("group")
    doc["codepoint"] = result.get("codepoint")
    doc["specification"] = result.get("specification")
    doc["status"] = result.get("status")
    doc["verified"] = bool(result.get("verified"))
    doc["transcript"] = {
        "file": result.get("transcript_file"),
        "sha256": result.get("transcript_sha256"),
        "implementation": result.get("implementation"),
    }
    doc["layout"] = result.get("layout", {})
    doc["summary"] = {
        "checks_passed": result.get("passed", 0),
        "checks_total": result.get("total", 0),
        "not_checked": result.get("skipped", 0),
        "not_applicable": result.get("not_applicable", 0),
        "findings": len(result.get("findings", [])),
    }
    doc["checks"] = [
        {"name": c["name"],
         "result": ("not_applicable" if c.get("kind") == "not_applicable"
                    else "not_checked" if c.get("skipped")
                    else "pass" if c["passed"] else "fail"),
         "detail": c.get("detail", "")}
        for c in result.get("checks", [])
    ]
    doc["findings"] = result.get("findings", [])
    return doc


def to_sarif(results, tool_version="unknown", source_root=None, artifact=None):
    """SARIF 2.1.0. GitHub Code Scanning renders this inline on pull requests.

    A bound artifact is emitted as the run's `artifacts` entry with its
    sha-256, which is SARIF's own place for "this exact file was analysed".
    """
    used = set()
    sarif_results = []

    for r in results:
        name = r.get("name", "unknown")
        # Where possible, point at the audited artifact rather than a source line;
        # a compiled library has no meaningful line number, so SARIF's
        # "artifactLocation" is used without a region.
        loc_uri = name.split(":")[0] if ":" in name else name
        symbol = name.split(":", 1)[1] if ":" in name else None

        for finding in r.get("findings", []):
            rule_id = _rule_for(finding)
            used.add(rule_id)
            msg = f"{finding}"
            if symbol:
                msg += f"  (symbol: {symbol})"
            sarif_results.append({
                "ruleId": rule_id,
                "level": RULES[rule_id]["level"],
                "message": {"text": msg},
                "locations": [{
                    "physicalLocation": {
                        "artifactLocation": {
                            "uri": loc_uri,
                            "uriBaseId": "%SRCROOT%" if source_root else None,
                        }
                    }
                }],
                "partialFingerprints": {
                    # stable across runs: same target + same rule = same finding
                    "pqVerifyFinding/v1": f"{loc_uri}:{rule_id}",
                },
            })

    # strip the None uriBaseId rather than emit nulls
    for res in sarif_results:
        loc = res["locations"][0]["physicalLocation"]["artifactLocation"]
        if loc.get("uriBaseId") is None:
            loc.pop("uriBaseId", None)

    rules = [{
        "id": rid,
        "name": RULES[rid]["name"],
        "shortDescription": {"text": RULES[rid]["short"]},
        "fullDescription": {"text": RULES[rid]["full"]},
        "defaultConfiguration": {"level": RULES[rid]["level"]},
        "properties": {"tags": ["cryptography", "post-quantum", "correctness"]},
    } for rid in sorted(used)] or [{
        "id": "PQV001",
        "name": RULES["PQV001"]["name"],
        "shortDescription": {"text": RULES["PQV001"]["short"]},
        "fullDescription": {"text": RULES["PQV001"]["full"]},
        "defaultConfiguration": {"level": "error"},
    }]

    run_artifacts = []
    if artifact and artifact.get("bound") and artifact.get("path"):
        entry = {"location": {"uri": "file://" + artifact["path"]}}
        if artifact.get("sha256"):
            entry["hashes"] = {"sha-256": artifact["sha256"]}
        run_artifacts.append(entry)

    run = {
        "$schema": SARIF_SCHEMA,
        "version": SARIF_VERSION,
        "runs": [{
            "tool": {
                "driver": {
                    "name": "pq-verify",
                    "version": tool_version,
                    "informationUri": "https://github.com/bigDSanalyst/pq-verify",
                    "rules": rules,
                }
            },
            "results": sarif_results,
            "invocations": [{
                "executionSuccessful": True,
                "endTimeUtc": datetime.datetime.now(
                    datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            }],
        }],
    }
    if run_artifacts:
        run["runs"][0]["artifacts"] = run_artifacts
    props = {"pqVerifySideChannel": SIDE_CHANNEL["summary"]}
    if artifact:
        props["pqVerifyArtifact"] = artifact["summary"]
    run["runs"][0]["properties"] = props
    return run


def write(path, doc):
    d = os.path.dirname(os.path.abspath(path))
    if d:
        os.makedirs(d, exist_ok=True)
    with open(path, "w") as fh:
        json.dump(doc, fh, indent=2)
    return path

