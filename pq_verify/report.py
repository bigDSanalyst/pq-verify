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
    "PQV005": {
        "name": "BoundaryVectorFailure",
        "short": "Boundary/edge-case vector failed",
        "full": ("An edge-case input (zero polynomial, maximum coefficients, "
                 "single-coefficient impulse) produced incorrect output."),
        "level": "warning",
    },
}

_FINDING_MAP = (
    ("cannot verify", "PQV000"),
    ("malformed",   "PQV000"),
    ("response:",   "PQV006"),
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
        "schema_version": "1.0",
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
        "schema_version": "1.0",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "parameter_set": result.get("parameter_set"),
        "status": result.get("status"),
        "verified": result.get("verified", False),
        "artifact": result.get("artifact") or artifact_unbound(
            "vendor-supplied response"),
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


def _envelope(schema, artifact, reason="no binary was loaded"):
    """Common head of every native report: what it is, when, and what it binds to."""
    return {
        "schema": schema,
        "schema_version": "1.0",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "artifact": artifact if artifact is not None else artifact_unbound(reason),
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
    doc["stages"] = {k: {"passed": v[0], "total": v[1]}
                     for k, v in (result.get("detail") or {}).items()}
    doc["findings"] = [] if p == t else [
        f"stage {k}: {v[0]}/{v[1]} match NIST byte-for-byte"
        for k, v in (result.get("detail") or {}).items() if v[0] != v[1]]
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
                                "verified": bool(r.get("verified"))}
        for g, v in (r.get("detail") or {}).items():
            doc["groups"][f"{label}/{g}"] = {"passed": v[0], "total": v[1]}
    doc["summary"] = {"checks_passed": p, "checks_total": t,
                      "findings": 0 if p == t else t - p}
    doc["verified"] = bool(t) and p == t
    doc["status"] = "VERIFIED" if doc["verified"] else (
        "FINDINGS PRESENT" if t else "CANNOT VERIFY")
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
    if artifact:
        run["runs"][0]["properties"] = {"pqVerifyArtifact": artifact["summary"]}
    return run


def write(path, doc):
    d = os.path.dirname(os.path.abspath(path))
    if d:
        os.makedirs(d, exist_ok=True)
    with open(path, "w") as fh:
        json.dump(doc, fh, indent=2)
    return path

