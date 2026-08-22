"""
pq_verify.response — offline prompt/response verification.

Every other audit path in this tool binds its result to a specific artifact:
`--audit-so` and `--audit-kem` dlopen a library, drive the vendor's own code
with NIST's vectors, and the result is about THAT file. Some implementations
cannot be driven that way at all -- an HSM behind PKCS#11, a sealed vendor
binary with no exported entry points, a build where the transform is inlined.
Today those are not "partially verified"; they are not verifiable by this tool
at all.

This module is the route to them:

    pq-verify --emit-prompt ML-DSA-65 -o prompt.json
        writes the QUESTIONS for that parameter set, taken from the pinned
        ACVP bundle. No answers are included.

    (the implementer runs the questions through their own implementation,
     wherever it lives, and sends back a response file)

    pq-verify --verify-response response.json
        checks every answer against the pinned expected values, byte-exact,
        per test case, and reports what was answered and what was not.

What a passing response proves: whoever produced it can compute FIPS
203/204/205 correctly for those inputs.

What it does NOT prove: which binary did it. There is no signature over the
computation and no binding to code. So the report carries the binding as a
field, not as prose:

    artifact: none — vendor-supplied response

against, on the dlopen paths:

    artifact: sha256 <hex>

Both are data. A reader sees what was bound and what was not, the same way
DEGRADED names what did not run.

Two properties are enforced rather than assumed:

  * A question is only asked if the pinned bundle has an answer for it, so a
    response can never be scored against a blank.
  * Unanswered questions are counted and reported. A response covering three
    of 205 questions reports 3/205 answered and INCOMPLETE -- never "3/3 PASS".
    A skip that looks like a pass is the failure mode this tool exists to stop.
"""

import datetime
import gzip
import hashlib
import json
import os

from .core import (
    DEGRADED,
    VERSION,
    _bundle_path,
    _load_vector_json,
    _pkg_dir,
)

PROMPT_SCHEMA = "pq-verify/acvp-prompt"
RESPONSE_SCHEMA = "pq-verify/acvp-response"
SCHEMA_VERSION = "1.0"

_ACVP_HTTP_BASE = ("https://raw.githubusercontent.com/usnistgov/ACVP-Server/"
                   "master/gen-val/json-files/")

# (directory in the ACVP tree, algorithm, mode, revision). The directory name
# is exactly "{algorithm}-{mode}-{revision}", which is what lets a raw ACVP
# response file be matched back to a suite without any pq-verify metadata.
_SUITES = (
    ("ML-KEM-keyGen-FIPS203",     "ML-KEM",  "keyGen",     "FIPS203"),
    ("ML-KEM-encapDecap-FIPS203", "ML-KEM",  "encapDecap", "FIPS203"),
    ("ML-DSA-keyGen-FIPS204",     "ML-DSA",  "keyGen",     "FIPS204"),
    ("ML-DSA-sigGen-FIPS204",     "ML-DSA",  "sigGen",     "FIPS204"),
    ("ML-DSA-sigVer-FIPS204",     "ML-DSA",  "sigVer",     "FIPS204"),
    ("SLH-DSA-keyGen-FIPS205",    "SLH-DSA", "keyGen",     "FIPS205"),
)

_MAX_LISTED = 25          # cap on individually listed failures / unknown ids
_PREFIX = 24              # hex digits shown when reporting a mismatch


# ----------------------------------------------------------------------
# vector source — same precedence as pqverify_acvp / pqverify_mldsa_acvp
# ----------------------------------------------------------------------

def _source(prompt_dir=None, vector_dir=None, live=False):
    local = prompt_dir or vector_dir
    if not local and not live:
        local = os.path.join(_pkg_dir(), "vectors")
    return local


def _source_label(local):
    if not local:
        return "LIVE from NIST (may change between runs)"
    if os.path.abspath(local) == os.path.abspath(os.path.join(_pkg_dir(), "vectors")):
        return "pinned bundle (shipped in this package)"
    return "local: " + local


def _load(local, suite, fname):
    if local:
        return _load_vector_json(os.path.join(local, suite, fname),
                                 f"{suite}/{fname}")
    import urllib.request
    return json.loads(urllib.request.urlopen(
        _ACVP_HTTP_BASE + suite + "/" + fname, timeout=60).read())


def _bundle_sha256():
    p = _bundle_path()
    if not os.path.exists(p):
        return None
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _read_json(path):
    """Read a .json or .json.gz document."""
    if path.endswith(".gz"):
        with gzip.open(path, "rt") as fh:
            return json.load(fh)
    with open(path, "r") as fh:
        return json.load(fh)


# ----------------------------------------------------------------------
# question set
# ----------------------------------------------------------------------

def _group_label(suite, g):
    bits = [g.get("function"), g.get("signatureInterface")]
    if g.get("externalMu"):
        bits.append("externalMu")
    elif g.get("preHash"):
        bits.append(g["preHash"])
    if g.get("deterministic") is True:
        bits.append("deterministic")
    elif g.get("deterministic") is False:
        bits.append("hedged")
    lab = "/".join(b for b in bits if b)
    return f"{suite}/{lab}" if lab else suite


def _questions(param_set, local):
    """The canonical question set for one parameter set.

    Verbatim ACVP prompt groups, filtered to `param_set`, plus the names (never
    the values) of the fields the response must supply. A test case with no
    pinned expected answer is dropped: asking a question this tool cannot mark
    would put an unscoreable case into someone's report.
    """
    out = []
    for suite, alg, mode, rev in _SUITES:
        try:
            P = _load(local, suite, "prompt.json")
            E = _load(local, suite, "expectedResults.json")
        except (FileNotFoundError, OSError):
            continue
        exp = {t["tcId"]: t for g in E["testGroups"] for t in g["tests"]}
        groups = []
        for g in P["testGroups"]:
            if g.get("parameterSet") != param_set:
                continue
            tests = [t for t in g["tests"] if t.get("tcId") in exp]
            if not tests:
                continue
            fields = sorted({k for t in tests for k in exp[t["tcId"]]
                             if k != "tcId"})
            if not fields:
                continue
            grp = {k: v for k, v in g.items() if k != "tests"}
            grp["answerFields"] = fields
            grp["tests"] = tests
            groups.append(grp)
        if groups:
            out.append({"suite": suite, "algorithm": alg, "mode": mode,
                        "revision": rev, "testGroups": groups})
    return out


def _prompt_id(questions):
    """sha256 over the canonical question set.

    Recomputable from the pinned bundle alone, so a response can be matched
    back to the exact questions it claims to answer.
    """
    blob = json.dumps(questions, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(blob).hexdigest()


def _count(questions):
    return sum(len(g["tests"]) for s in questions for g in s["testGroups"])


def available_parameter_sets(prompt_dir=None, vector_dir=None, live=False):
    """Every parameter set the resolved vector source can pose questions for."""
    local = _source(prompt_dir, vector_dir, live)
    seen = set()
    for suite, _a, _m, _r in _SUITES:
        try:
            P = _load(local, suite, "prompt.json")
        except (FileNotFoundError, OSError):
            continue
        for g in P["testGroups"]:
            if g.get("parameterSet"):
                seen.add(g["parameterSet"])
    return sorted(seen)


# ----------------------------------------------------------------------
# 1. --emit-prompt
# ----------------------------------------------------------------------

_HOW_TO_RESPOND = [
    "Run every test case below through your implementation.",
    "For each test case return an object with its tcId plus the fields named "
    "in that group's answerFields.",
    "Byte values are hex strings; case is not significant. testPassed is a "
    "JSON boolean (true/false), not a string.",
    "Group your answers by suite and keep tgId/tcId unchanged, so each answer "
    "can be matched to its question.",
    "Copy promptId and parameterSet into the response unchanged. Without them "
    "pq-verify cannot confirm you answered this question set.",
    "Return every test case. Unanswered cases are reported as unanswered; "
    "they are never scored as passes.",
    "artifact is optional and, if given, is recorded as a vendor assertion "
    "only: pq-verify did not load your binary and does not verify that hash.",
]


def build_prompt(param_set, prompt_dir=None, vector_dir=None, live=False):
    """The question document for `param_set`. Contains no expected answers."""
    local = _source(prompt_dir, vector_dir, live)
    questions = _questions(param_set, local)
    if not questions:
        known = available_parameter_sets(prompt_dir, vector_dir, live)
        raise ValueError(
            f"no pinned questions for parameter set {param_set!r}. "
            f"Known: {', '.join(known) if known else '(no vectors available)'}")
    pid = _prompt_id(questions)
    doc = {
        "schema": PROMPT_SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "toolVersion": VERSION,
        "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "parameterSet": param_set,
        "promptId": pid,
        "questionCount": _count(questions),
        "vectorSource": _source_label(local),
        "vectorBundleSha256": _bundle_sha256() if local else None,
        "scope": ("Answering these questions demonstrates that the responder "
                  "computes the standard correctly for these inputs. It does "
                  "not bind the result to any binary: pq-verify did not load "
                  "the code that produced the answers."),
        "howToRespond": _HOW_TO_RESPOND,
        "responseSchema": {
            "schema": RESPONSE_SCHEMA,
            "schema_version": SCHEMA_VERSION,
            "promptId": pid,
            "parameterSet": param_set,
            "implementation": {"name": "<optional>", "version": "<optional>"},
            "artifact": {"sha256": "<optional, recorded as a vendor assertion>"},
            "suites": [{
                "suite": "<one of: " + ", ".join(s["suite"] for s in questions) + ">",
                "testGroups": [{"tgId": 0, "tests": [{"tcId": 0}]}],
            }],
        },
        "suites": questions,
    }
    return doc


def emit_prompt(param_set, out_path=None, prompt_dir=None, vector_dir=None,
                live=False, verbose=True):
    """Write the question set for `param_set` to `out_path` (.gz honoured)."""
    doc = build_prompt(param_set, prompt_dir=prompt_dir, vector_dir=vector_dir,
                       live=live)
    if out_path is None:
        out_path = f"pq-verify-prompt-{param_set}.json"
    d = os.path.dirname(os.path.abspath(out_path))
    if d:
        os.makedirs(d, exist_ok=True)
    if out_path.endswith(".gz"):
        with gzip.open(out_path, "wt") as fh:
            json.dump(doc, fh, indent=2)
    else:
        with open(out_path, "w") as fh:
            json.dump(doc, fh, indent=2)

    if verbose:
        print("=" * 68)
        print(f"  ACVP PROMPT — {param_set}")
        print("=" * 68)
        print(f"  vectors    : {doc['vectorSource']}")
        print(f"  promptId   : {doc['promptId']}")
        print(f"  questions  : {doc['questionCount']}")
        for s in doc["suites"]:
            n = sum(len(g["tests"]) for g in s["testGroups"])
            print(f"    {s['suite']:30s} {n:5d}  "
                  f"({len(s['testGroups'])} group(s))")
        print(f"  wrote      : {out_path}  "
              f"({os.path.getsize(out_path) / 1048576.0:.1f} MiB)")
        print("=" * 68)
        print("  Answers are NOT in this file. Run the questions through the")
        print("  implementation, then check the response with:")
        print(f"      pq-verify --verify-response <response.json>")
        print("=" * 68)
    return out_path


# ----------------------------------------------------------------------
# 2. --verify-response
# ----------------------------------------------------------------------

def _norm_hex(v):
    """Normalise a hex answer, or None if it is not one."""
    if not isinstance(v, str):
        return None
    s = "".join(v.split())
    if s[:2].lower() == "0x":
        s = s[2:]
    s = s.upper()
    if len(s) % 2 or not s:
        return None
    if any(c not in "0123456789ABCDEF" for c in s):
        return None
    return s


def _flatten_answers(doc):
    """(param_set, prompt_id, {suite: {tcId: answer}}, meta) from a response.

    Accepts pq-verify's own response schema, a raw ACVP response document, or
    a list of raw ACVP response documents -- so a vendor whose harness already
    emits ACVP responses does not have to reshape anything.
    """
    answers, meta = {}, {}
    param_set = prompt_id = None

    def _take_raw(d):
        alg, mode, rev = d.get("algorithm"), d.get("mode"), d.get("revision")
        if not (alg and mode and rev):
            return None
        return f"{alg}-{mode}-{rev}"

    def _absorb(suite, groups):
        bucket = answers.setdefault(suite, {})
        for g in groups or []:
            for t in g.get("tests") or []:
                if "tcId" in t:
                    bucket[t["tcId"]] = t

    if isinstance(doc, list):
        for d in doc:
            if not isinstance(d, dict):
                continue
            s = _take_raw(d)
            if s:
                _absorb(s, d.get("testGroups"))
    elif isinstance(doc, dict):
        param_set = doc.get("parameterSet")
        prompt_id = doc.get("promptId")
        for k in ("implementation", "artifact", "toolVersion", "generated"):
            if k in doc:
                meta[k] = doc[k]
        if isinstance(doc.get("suites"), list):
            for s in doc["suites"]:
                if isinstance(s, dict) and s.get("suite"):
                    _absorb(s["suite"], s.get("testGroups"))
        elif doc.get("testGroups") is not None:
            s = _take_raw(doc)
            if s:
                _absorb(s, doc["testGroups"])
    return param_set, prompt_id, answers, meta


def _infer_param_set(answers, local):
    """Which parameter set the answered tcIds belong to, per the pinned prompts."""
    found = set()
    for suite, _a, _m, _r in _SUITES:
        if suite not in answers:
            continue
        try:
            P = _load(local, suite, "prompt.json")
        except (FileNotFoundError, OSError):
            continue
        for g in P["testGroups"]:
            ps = g.get("parameterSet")
            if not ps:
                continue
            for t in g["tests"]:
                if t.get("tcId") in answers[suite]:
                    found.add(ps)
    return sorted(found)


def _compare(field, want, got):
    """('ok'|'mismatch'|'malformed', note). Never mutates or prints secrets."""
    if isinstance(want, bool):
        if not isinstance(got, bool):
            return "malformed", (f"{field}: expected a JSON boolean, got "
                                 f"{type(got).__name__}")
        return ("ok" if got == want else "mismatch",
                None if got == want else f"{field}: answered {got}, expected {want}")
    if isinstance(want, str):
        w = _norm_hex(want)
        g = _norm_hex(got)
        if g is None:
            return "malformed", f"{field}: not an even-length hex string"
        if w == g:
            return "ok", None
        if len(g) != len(w):
            return "mismatch", (f"{field}: {len(g) // 2} bytes, expected "
                                f"{len(w) // 2}")
        return "mismatch", (f"{field}: {g[:_PREFIX]}… expected {w[:_PREFIX]}…")
    # A pinned answer of a type this comparator does not model must not be
    # silently treated as a pass.
    return "malformed", f"{field}: unsupported expected type {type(want).__name__}"


def _artifact_field(meta):
    """The binding, as data. This path never loads a binary, so bound is False."""
    claimed = None
    a = meta.get("artifact")
    if isinstance(a, dict):
        claimed = a.get("sha256")
    elif isinstance(a, str):
        claimed = a
    summary = "none — vendor-supplied response"
    if isinstance(claimed, str) and claimed.strip():
        summary += (f" (vendor asserts sha256 {claimed.strip()}, "
                    f"not verified by pq-verify)")
    else:
        claimed = None
    return {"bound": False, "sha256": None, "summary": summary,
            "vendor_asserted_sha256": claimed,
            "detail": ("No binary was loaded. A passing response shows the "
                       "responder computes the standard correctly for these "
                       "inputs; it does not identify the code that did so.")}


def verify_response(response_path, prompt_dir=None, vector_dir=None, live=False,
                    param_set=None, verbose=True):
    """Check a response file against the pinned expected answers, byte-exact.

    Returns a result dict; `verified` is True only when every question in the
    prompt was answered and every answer matched.
    """
    local = _source(prompt_dir, vector_dir, live)
    res = {
        "schema": "pq-verify/response-result",
        "schema_version": SCHEMA_VERSION,
        "response_file": os.path.abspath(response_path),
        "response_sha256": None,
        "parameter_set": param_set,
        "prompt_id": None, "response_prompt_id": None,
        "prompt_binding": "absent",
        "vector_source": _source_label(local),
        "questions": 0, "answered": 0, "unanswered": 0,
        "passed": 0, "total": 0, "malformed": 0,
        "unknown": [], "detail": {}, "findings": [],
        "implementation": None,
        "artifact": {"bound": False, "sha256": None,
                     "summary": "none — vendor-supplied response"},
        "status": "CANNOT VERIFY", "verified": False,
    }

    def _stop(msg):
        res["findings"].append("cannot verify: " + msg)
        DEGRADED["skipped_checks"].append("response verification")
        if verbose:
            _print(res)
        return res

    if not os.path.exists(response_path):
        return _stop(f"no such response file: {response_path}")
    res["response_sha256"] = _file_sha256(response_path)
    try:
        doc = _read_json(response_path)
    except (ValueError, OSError, gzip.BadGzipFile) as exc:
        return _stop(f"response file is not readable JSON ({exc})")

    ps, claimed_id, answers, meta = _flatten_answers(doc)
    res["response_prompt_id"] = claimed_id
    res["implementation"] = meta.get("implementation")
    res["artifact"] = _artifact_field(meta)
    if not answers:
        return _stop("no answers found — expected a 'suites' list, or an ACVP "
                     "response document with algorithm/mode/revision and "
                     "testGroups")

    param_set = param_set or ps
    if not param_set:
        guess = _infer_param_set(answers, local)
        if len(guess) == 1:
            param_set = guess[0]
        elif not guess:
            return _stop("cannot tell which parameter set this answers; none "
                         "of its tcIds appear in the pinned prompts")
        else:
            return _stop("answers span several parameter sets "
                         f"({', '.join(guess)}); emit and answer one prompt "
                         "per parameter set")
    res["parameter_set"] = param_set

    try:
        questions = _questions(param_set, local)
    except (FileNotFoundError, OSError) as exc:
        return _stop(f"vectors unavailable ({exc})")
    if not questions:
        return _stop(f"no pinned questions for parameter set {param_set!r}")
    res["prompt_id"] = _prompt_id(questions)
    res["questions"] = _count(questions)

    if claimed_id:
        if claimed_id == res["prompt_id"]:
            res["prompt_binding"] = "confirmed"
        else:
            res["prompt_binding"] = "mismatch"
            return _stop(
                "promptId does not match this question set — the response "
                "answers a different prompt (or a different vector snapshot). "
                f"expected {res['prompt_id']}, response says {claimed_id}")

    # ---- score, per test case -------------------------------------------
    remaining = {s: dict(a) for s, a in answers.items()}
    for suite_q in questions:
        suite = suite_q["suite"]
        try:
            E = _load(local, suite, "expectedResults.json")
        except (FileNotFoundError, OSError) as exc:
            return _stop(f"expected results unavailable for {suite} ({exc})")
        exp = {t["tcId"]: t for g in E["testGroups"] for t in g["tests"]}
        got_suite = remaining.setdefault(suite, {})
        for g in suite_q["testGroups"]:
            label = _group_label(suite, g)
            tally = res["detail"].setdefault(label, [0, 0, 0])
            for t in g["tests"]:
                tc = t["tcId"]
                tally[2] += 1
                res["total"] += 1
                ans = got_suite.pop(tc, None)
                if ans is None:
                    res["unanswered"] += 1
                    continue
                tally[1] += 1
                res["answered"] += 1
                verdict = "ok"
                # Score only against fields the pinned answers actually carry
                # for this test case. A group's answerFields is the union over
                # its tests, so an irregular group must not crash the run --
                # and must not be scored against a value that does not exist.
                fields = [f for f in g["answerFields"] if f in exp[tc]]
                if not fields:
                    res["malformed"] += 1
                    res["findings"].append(
                        f"cannot verify: {label} tcId {tc} has no pinned "
                        f"expected value to check against")
                    continue
                for field in fields:
                    if field not in ans:
                        verdict = "malformed"
                        res["findings"].append(
                            f"response: {label} tcId {tc} malformed — missing "
                            f"answer field {field!r}")
                        continue
                    st, note = _compare(field, exp[tc][field], ans[field])
                    if st != "ok":
                        verdict = "malformed" if st == "malformed" else (
                            verdict if verdict == "malformed" else "mismatch")
                        res["findings"].append(
                            f"response: {label} tcId {tc} "
                            f"{'malformed' if st == 'malformed' else 'mismatch'}"
                            f" — {note}")
                if verdict == "ok":
                    tally[0] += 1
                    res["passed"] += 1
                elif verdict == "malformed":
                    res["malformed"] += 1

    for suite, left in remaining.items():
        for tc in sorted(left):
            res["unknown"].append(f"{suite} tcId {tc}")

    res["detail"] = {k: tuple(v) for k, v in sorted(res["detail"].items())}

    # ---- verdict ---------------------------------------------------------
    if res["unanswered"]:
        res["findings"].append(
            f"cannot verify: {res['unanswered']} of {res['questions']} "
            f"questions unanswered — this response covers less than the prompt")
        DEGRADED["skipped_checks"].append(
            f"response coverage ({param_set}: {res['unanswered']} unanswered)")
    if res["unknown"]:
        shown = res["unknown"][:_MAX_LISTED]
        res["findings"].append(
            f"cannot verify: {len(res['unknown'])} answer(s) reference tcIds "
            f"that are not in this prompt ({', '.join(shown)}"
            f"{', …' if len(res['unknown']) > len(shown) else ''})")

    failed = res["answered"] - res["passed"]
    if failed:
        res["status"] = "FINDINGS PRESENT"
    elif res["unanswered"] or res["unknown"]:
        res["status"] = "INCOMPLETE"
    elif res["total"]:
        res["status"] = "VERIFIED"
    res["verified"] = (res["status"] == "VERIFIED")

    if verbose:
        _print(res)
    return res


def _print(res):
    print("=" * 68)
    print(f"  ACVP RESPONSE VERIFICATION — {res['parameter_set'] or '(unknown)'}")
    print("=" * 68)
    print(f"  response  : {os.path.basename(res['response_file'])}")
    print(f"  sha256    : {res['response_sha256'] or '(unreadable)'}")
    print(f"  vectors   : {res['vector_source']}")
    print(f"  promptId  : {res['prompt_id'] or '(not computed)'}")
    print(f"  binding   : {res['prompt_binding']}"
          + {"confirmed": "  (answers this exact question set)",
             "absent": "  (response carried no promptId — answers still "
                       "checked, question set not confirmed)",
             "mismatch": "  (answers a DIFFERENT question set)"}
            .get(res["prompt_binding"], ""))
    impl = res.get("implementation")
    if impl:
        print(f"  claimed   : {impl}")
    print(f"  artifact  : {res['artifact']['summary']}")
    if res["detail"]:
        print("-" * 68)
        for label, (ok, ans, tot) in res["detail"].items():
            if ans == 0:
                mark, note = "NOT RUN", "  (unanswered)"
            elif ok < ans:
                mark, note = "**FAIL**", (f"  ({ans} answered)" if ans != tot else "")
            elif ans < tot:
                mark, note = "PARTIAL", f"  ({ans} answered)"
            else:
                mark, note = "PASS", ""
            print(f"  {mark:9s} {label:44s} {ok:4d}/{tot}{note}")
    print("-" * 68)
    print(f"  answered  : {res['answered']} of {res['questions']} asked"
          + (f"   ({res['unanswered']} unanswered)" if res["unanswered"] else ""))
    print(f"  matched   : {res['passed']} of {res['answered']} answered "
          f"byte-exact vs pinned NIST values"
          + (f"   ({res['passed']} of {res['questions']} asked)"
             if res["unanswered"] else ""))
    if res["malformed"]:
        print(f"  malformed : {res['malformed']}")
    if res["findings"]:
        print("-" * 68)
        for f in res["findings"][:_MAX_LISTED]:
            print(f"    - {f}")
        if len(res["findings"]) > _MAX_LISTED:
            print(f"    … and {len(res['findings']) - _MAX_LISTED} more")
    print("=" * 68)
    print(f"  RESULT: {res['status']}")
    print("  SCOPE: this checks that the responder computes the standard")
    print("  correctly for these inputs. No binary was loaded, so the result")
    print("  is not bound to any artifact — see the artifact field above.")
    print("=" * 68)
