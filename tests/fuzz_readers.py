#!/usr/bin/env python3
"""Fuzz the readers that take files from outside parties.

`--verify-response` and `--verify-hybrid` read documents a vendor, an HSM or
a TLS capture produced. Those files are untrusted input to a verification
tool, so for every document -- well-formed, malformed or hostile -- four
things must hold:

  1. nothing escapes: no exception out of verify_response / verify_hybrid,
     and the CLI returns 0, 1 or 2 rather than a traceback;
  2. the result is honest: a known status and a boolean `verified`;
  3. it terminates promptly;
  4. no false accept: a document that differs from a genuine one is never
     VERIFIED, unless the difference is one the reader is documented to
     ignore (reported separately for review, not silently allowed).

Mutations are structure-aware: they start from genuine documents and damage
them the ways a buggy or hostile producer would. The genuine documents are
responses for every family the response reader scores (ML-KEM answered by
kyber-py; ML-DSA and SLH-DSA answered with NIST's own expected results; LMS
signed with a key of the responder's own; a fresh ML-DSA prompt answered by
dilithium-py) and real hybrid transcripts for every group.

`--audit-harness` reads a third kind of untrusted input: the replies of a
Crucible-protocol harness, one JSON line per request. Its target runs a real
audit through tests/data/fuzz_harness.py, the reference harness with one
reply corrupted, and adds a fifth invariant: a reply that breaks the
protocol ends the audit CANNOT VERIFY. It is never read as the library
refusing the input, which for an invalid input would score as a pass.

  python3 tests/fuzz_readers.py                 5000 cases per document
                                                reader (500 for the fresh
                                                prompt), 300 harness audits
  python3 tests/fuzz_readers.py --cases 200 --seed 7
  python3 tests/fuzz_readers.py --only harness

EXIT 0 all invariants held; 1 a violation (printed with a reproducer file).
"""
import argparse
import contextlib
import copy
import importlib.util
import io
import json
import os
import random
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

STATUSES = {"VERIFIED", "FINDINGS PRESENT", "CANNOT VERIFY", "INCOMPLETE", "PARTIAL"}
TIME_LIMIT = 10.0          # seconds per case; a genuine document takes well under 1


def _tests_module():
    spec = importlib.util.spec_from_file_location(
        "pqv_tests", ROOT / "tests" / "test_pqverify.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ─────────────────────────────── seeds ───────────────────────────────

def seed_response():
    """A genuine ML-KEM-512 response, answered by kyber-py."""
    from kyber_py.ml_kem import ML_KEM_512 as K
    from pq_verify import check_encapsulation_key, check_decapsulation_key
    from pq_verify.response import build_prompt
    ps = "ML-KEM-512"
    prompt = build_prompt(ps)
    out = {"schema": "pq-verify/acvp-response", "schema_version": "1.0",
           "promptId": prompt["promptId"], "parameterSet": ps,
           "implementation": {"name": "kyber-py"}, "suites": []}
    for s in prompt["suites"]:
        groups = []
        for g in s["testGroups"]:
            fn, tests = g.get("function"), []
            for t in g["tests"]:
                tc = t["tcId"]
                if s["mode"] == "keyGen":
                    ek, dk = K._keygen_internal(bytes.fromhex(t["d"]), bytes.fromhex(t["z"]))
                    tests.append({"tcId": tc, "ek": ek.hex(), "dk": dk.hex()})
                elif fn == "encapsulation":
                    k, c = K._encaps_internal(bytes.fromhex(t["ek"]), bytes.fromhex(t["m"]))
                    tests.append({"tcId": tc, "c": c.hex(), "k": k.hex()})
                elif fn == "decapsulation":
                    k = K._decaps_internal(bytes.fromhex(t["dk"]), bytes.fromhex(t["c"]))
                    tests.append({"tcId": tc, "k": k.hex()})
                elif fn == "encapsulationKeyCheck":
                    tests.append({"tcId": tc, "testPassed": bool(
                        check_encapsulation_key(bytes.fromhex(t["ek"]), ps))})
                else:
                    tests.append({"tcId": tc, "testPassed": bool(
                        check_decapsulation_key(bytes.fromhex(t["dk"]), ps))})
            groups.append({"tgId": g["tgId"], "tests": tests})
        out["suites"].append({"suite": s["suite"], "testGroups": groups})
    return out


def seed_response_nist(ps):
    """A genuine response to a pinned prompt: NIST's own expected answers,
    laid out as the prompt asks for them. Covers the families no reference
    in the test environment answers quickly (ML-DSA, SLH-DSA)."""
    from pq_verify import response as R
    prompt = R.build_prompt(ps)
    local = R._source()
    out = {"schema": "pq-verify/acvp-response", "schema_version": "1.0",
           "promptId": prompt["promptId"], "parameterSet": ps,
           "implementation": {"name": "NIST's expected results"}, "suites": []}
    for s in prompt["suites"]:
        E = R._load(local, s["suite"], "expectedResults.json")
        exp = {t["tcId"]: t for g in E["testGroups"] for t in g["tests"]}
        out["suites"].append({"suite": s["suite"], "testGroups": [
            {"tgId": g["tgId"], "tests": [
                dict({"tcId": t["tcId"]}, **{f: exp[t["tcId"]][f] for f in g["answerFields"]})
                for t in g["tests"]]}
            for g in s["testGroups"]]})
    return out


NIST_SEED_SETS = ("ML-DSA-44", "SLH-DSA-SHA2-128s", "ML-KEM-768")
# The test suite's LMS responder signs every sigGen group with one key from
# leaf 0, which the reader rightly reports as one-time keys used twice where a
# set has two sigGen groups. These two sets have one.
LMS_SETS = ("LMS_SHA256_M24_H10/LMOTS_SHA256_N24_W1",
            "LMS_SHA256_M24_H5/LMOTS_SHA256_N24_W2")


def seed_response_lms(ps):
    """LMS: keyGen and sigVer computed, and sigGen signed with the responder's
    own key, which the reader checks each signature under."""
    from pq_verify.response import build_prompt
    prompt = build_prompt(ps)
    doc = _tests_module()._answer_lms(prompt)
    doc.update(promptId=prompt["promptId"], parameterSet=ps)
    return doc


def seed_fresh(workdir, ps="ML-DSA-44"):
    """(response, key path): a fresh prompt, answered by dilithium-py. The
    reader then derives the questions and computes the answers itself."""
    from pq_verify.cli import main as cli
    key = os.path.join(workdir, f"fresh-{ps}.key")
    prompt_path = os.path.join(workdir, f"fresh-{ps}.prompt.json")
    for f in (key, prompt_path):
        if os.path.exists(f):
            os.remove(f)
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        code = cli(["--emit-prompt", ps, "--fresh-key", key, "--fresh-count", "2",
                    "--prompt-out", prompt_path])
    assert code == 0, f"--emit-prompt {ps} --fresh-key exited {code}"
    with open(prompt_path) as fh:
        prompt = json.load(fh)
    return _tests_module()._answer_fresh(prompt), key


def seed_transcripts():
    t = _tests_module()
    vecs = t._kem_vectors()
    from pq_verify.hybrid import GROUPS
    return [t._transcript(g, vecs) for g in sorted(GROUPS)]


# ─────────────────────────────── mutations ───────────────────────────────

WEIRD = [None, True, False, 0, -1, 2**64, 2**4096, 1.5, float("inf"), "", "0",
         "zz", "0x00", "00" * 7, "é" * 50, "\x00", [], {}, [[[]]], {"a": {}},
         "A" * 100_000]


def _paths(doc, prefix=()):
    """Every (path, value) inside a JSON document."""
    yield prefix, doc
    if isinstance(doc, dict):
        for k, v in doc.items():
            yield from _paths(v, prefix + (k,))
    elif isinstance(doc, list):
        for i, v in enumerate(doc):
            yield from _paths(v, prefix + (i,))


def _get(doc, path):
    for p in path:
        doc = doc[p]
    return doc


def _set(doc, path, value):
    if not path:
        return value
    _get(doc, path[:-1])[path[-1]] = value
    return doc


def _deep(n):
    d = x = {}
    for _ in range(n):
        x["a"] = {}
        x = x["a"]
    return d


def mutate(doc, rng):
    """Return (bytes to write, description)."""
    kind = rng.randrange(25)
    if kind == 0:
        return b"", "empty file"
    if kind == 1:
        return bytes(rng.randrange(256) for _ in range(rng.randrange(1, 4096))), "binary garbage"
    if kind == 2:
        raw = json.dumps(doc).encode()
        return raw[: rng.randrange(len(raw))], "truncated JSON"
    if kind == 3:
        return b"\xef\xbb\xbf" + json.dumps(doc).encode(), "UTF-8 BOM"
    if kind == 4:
        return rng.choice([b"[]", b"null", b"42", b'"x"', b"true", b"NaN", b"{}"]), "non-object top level"
    if kind == 5:
        return ("[" * 100_000 + "]" * 100_000).encode(), "100k nested arrays"
    if kind == 6:
        return ('{"a":' * 5000 + "1" + "}" * 5000).encode(), "5000 nested objects"
    if kind == 7:
        raw = json.dumps(doc)
        i = rng.randrange(len(raw))
        return (raw[:i] + rng.choice(['"', "{", "]", ",", ":", "\\"]) + raw[i:]).encode(), "one corrupted byte"
    if kind == 8:
        raw = json.dumps(doc)
        return raw.replace("{", '{"schema": 1, ', 1).encode(), "duplicate key"

    doc = copy.deepcopy(doc)
    paths = [p for p, _ in _paths(doc) if p]
    path = rng.choice(paths)
    value = _get(doc, path)
    if kind == 9:
        parent = _get(doc, path[:-1])
        if isinstance(parent, dict):
            del parent[path[-1]]
        else:
            parent.pop(path[-1])
        return json.dumps(doc).encode(), f"removed {path}"
    if kind in (10, 11, 12):
        return json.dumps(_set(doc, path, rng.choice(WEIRD)), default=str).encode(), f"weird value at {path}"
    if kind == 13 and isinstance(value, str):
        return json.dumps(_set(doc, path, value[: rng.randrange(len(value) + 1)])).encode(), f"truncated string at {path}"
    if kind == 14 and isinstance(value, str) and value:
        i = rng.randrange(len(value))
        return json.dumps(_set(doc, path, value[:i] + rng.choice("gxZ/ ") + value[i + 1:])).encode(), f"non-hex char at {path}"
    if kind == 15 and isinstance(value, str):
        return json.dumps(_set(doc, path, value * rng.randrange(2, 40))).encode(), f"repeated string at {path}"
    if kind == 16 and isinstance(value, str) and len(value) >= 2:
        i = rng.randrange(len(value))
        flipped = format(int(value[i], 16) ^ 1, "x") if value[i] in "0123456789abcdefABCDEF" else "0"
        return json.dumps(_set(doc, path, value[:i] + flipped + value[i + 1:])).encode(), f"one hex digit flipped at {path}"
    if kind == 17 and isinstance(value, list) and value:
        value.append(copy.deepcopy(rng.choice(value)))
        return json.dumps(doc).encode(), f"duplicated list element at {path}"
    if kind == 18 and isinstance(value, list):
        value.clear()
        return json.dumps(doc).encode(), f"emptied list at {path}"
    if kind == 19 and isinstance(value, list):
        # Many extra elements, capped at ~8 MB of added JSON: past that it is
        # a size test, which test_hostile_response_files_are_refused_cleanly
        # covers directly without writing hundreds of MB per case.
        elem = copy.deepcopy(value[0]) if value else {}
        n = max(1, min(20_000, (8 << 20) // max(1, len(json.dumps(elem)))))
        value.extend([elem] * n)
        return json.dumps(doc).encode(), f"{n} extra elements at {path}"
    if kind == 20 and isinstance(value, dict):
        value["unexpected"] = rng.choice(WEIRD)
        return json.dumps(doc, default=str).encode(), f"extra field at {path}"
    if kind == 21 and isinstance(value, int) and not isinstance(value, bool):
        return json.dumps(_set(doc, path, rng.choice([value + 1, -value, str(value), float(value)]))).encode(), f"number changed at {path}"
    if kind == 22 and isinstance(value, bool):
        return json.dumps(_set(doc, path, not value)).encode(), f"boolean flipped at {path}"
    if kind == 23:
        return json.dumps(doc, ensure_ascii=False).encode("utf-16"), "UTF-16 encoded"
    return json.dumps(_set(doc, path, rng.choice(WEIRD)), default=str).encode(), f"weird value at {path}"


# ─────────────────────────────── harness ───────────────────────────────

def _run(fn, path):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return fn(path, verbose=False)


def _cli(flag, path, extra=()):
    from pq_verify.cli import main
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return main([flag, path, *extra, "--fail-on-finding"])


def fuzz(name, fn, flag, seeds, cases, rng, workdir, cli_every=25, gz=False,
         cli_extra=()):
    """Returns (violations, review) lists of (description, reproducer path, detail)."""
    violations, review = [], []
    genuine = [json.dumps(s, sort_keys=True) for s in seeds]
    for i in range(cases):
        seed = rng.choice(seeds)
        raw, what = mutate(seed, rng)
        path = os.path.join(workdir, f"{name}-{i}.json")
        if gz and rng.random() < 0.2:
            # The response reader also accepts .json.gz: compressed input,
            # truncated streams and highly compressible (bomb-like) payloads.
            import gzip
            packed = gzip.compress(raw)
            if rng.random() < 0.5:
                packed = packed[: rng.randrange(len(packed) + 1)]
                what += ", gzipped and truncated"
            else:
                what += ", gzipped"
            path += ".gz"
            raw = packed
        with open(path, "wb") as fh:
            fh.write(raw)
        t0 = time.monotonic()
        try:
            r = _run(fn, path)
        except RecursionError as e:
            violations.append((what, path, f"RecursionError: {e}"))
            continue
        except Exception as e:                            # the invariant under test
            violations.append((what, path, f"{type(e).__name__}: {e}"))
            continue
        dt = time.monotonic() - t0
        if dt > TIME_LIMIT:
            violations.append((what, path, f"took {dt:.1f}s"))
        if not isinstance(r, dict) or r.get("status") not in STATUSES \
                or not isinstance(r.get("verified"), bool):
            violations.append((what, path, f"malformed result: {str(r)[:200]}"))
            continue
        if r["verified"]:
            try:
                body = raw
                if path.endswith(".gz"):
                    import gzip
                    body = gzip.decompress(raw)
                same = json.dumps(json.loads(body), sort_keys=True) in genuine
            except Exception:
                same = False
            if not same:
                review.append((what, path, "VERIFIED after mutation"))
        if i % cli_every == 0:
            try:
                code = _cli(flag, path, cli_extra)
            except SystemExit as e:
                code = e.code
            except Exception as e:
                violations.append((what, path, f"CLI raised {type(e).__name__}: {e}"))
                continue
            if code not in (0, 1, 2):
                violations.append((what, path, f"CLI exit {code!r}"))
            elif r["verified"] is False and code == 0:
                violations.append((what, path, "CLI exit 0 on an unverified document"))
    return violations, review


# ─────────────────────────────── the harness protocol ───────────────────────────────

HARNESS_SETS = ("ML-KEM-512", "ML-KEM-512", "ML-KEM-512", "ML-DSA-44")
HARNESS_CALL_TIMEOUT = 10      # seconds per reply; the reference answers in milliseconds
HARNESS_TIME_LIMIT = 180.0     # seconds per audit; a clean ML-DSA-44 one takes ~15
REF_HARNESS = ROOT / "tests" / "data" / "crucible_ref_harness.py"
FUZZ_HARNESS = ROOT / "tests" / "data" / "fuzz_harness.py"
AUDIT_STATUSES = {"VERIFIED", "FINDINGS PRESENT", "CANNOT VERIFY"}


def harness_kinds():
    """{kind: (class, applies to)}, read from fuzz_harness.py's KINDS."""
    import ast
    for node in ast.parse(FUZZ_HARNESS.read_text()).body:
        if isinstance(node, ast.Assign) and getattr(node.targets[0], "id", "") == "KINDS":
            return ast.literal_eval(node.value)
    raise RuntimeError("fuzz_harness.py defines no KINDS")


def _audit(cmd, ps):
    from pq_verify.harness_audit import pqverify_audit_harness
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return pqverify_audit_harness(cmd, ps, verbose=False, accumulated=0,
                                      timeout=HARNESS_CALL_TIMEOUT)


def _corruption(log):
    try:
        with open(log) as fh:
            return json.loads(fh.readline())
    except (OSError, ValueError):
        return None


def _answered(hit):
    out = hit.get("output")
    return f"{hit.get('function')}" + (f" {out}" if out else "")


def fuzz_harness(cases, rng, workdir, cli_every=25, sets=HARNESS_SETS, kinds=None):
    """Audits through the reference harness with one reply corrupted. Returns
    (violations, review) lists of (description, reproducer command, detail)."""
    import shlex
    kinds = kinds or sorted(harness_kinds())
    classes = harness_kinds()
    violations, review = [], []
    clean = {}
    for ps in sorted(set(sets)):
        r = _audit([sys.executable, str(REF_HARNESS)], ps)
        assert r["verified"], f"the reference harness does not verify {ps}: {r.get('reason')}"
        clean[ps] = r
    for i in range(cases):
        ps = rng.choice(sets)
        kind = rng.choice(kinds)
        if ps.startswith("ML-KEM") and rng.random() < 0.15:
            when = "bad-ek"             # an edge case, where a refusal is the right answer
        else:
            when = str(rng.randrange(clean[ps]["calls"] + 1))
        log = os.path.join(workdir, f"harness-{i}.log")
        cmd = [sys.executable, str(FUZZ_HARNESS), when, kind, str(rng.randrange(1 << 30)), log]
        what = f"{ps}, reply {when}: {kind}"
        repro = " ".join(shlex.quote(c) for c in cmd)
        t0 = time.monotonic()
        try:
            r = _audit(cmd, ps)
        except BaseException as e:                        # the invariant under test
            violations.append((what, repro, f"{type(e).__name__}: {e}"))
            continue
        dt = time.monotonic() - t0
        if dt > HARNESS_TIME_LIMIT:
            violations.append((what, repro, f"took {dt:.0f}s"))
        if not isinstance(r, dict) or r.get("status") not in AUDIT_STATUSES \
                or not isinstance(r.get("verified"), bool):
            violations.append((what, repro, f"malformed result: {str(r)[:200]}"))
            continue
        hit = _corruption(log)
        got = f"{r['status']} {r['passed']}/{r['total']}"
        if hit is None:
            # Nothing was corrupted (the kind did not apply to that reply):
            # the reference harness is deterministic, so this is the clean run.
            if (r["status"], r["passed"], r["total"]) != \
                    (clean[ps]["status"], clean[ps]["passed"], clean[ps]["total"]):
                violations.append((what, repro, f"uncorrupted audit differs: {got}"))
        elif classes[kind][0] == "protocol":
            if r["status"] != "CANNOT VERIFY":
                violations.append((what, repro, f"a reply that breaks the protocol "
                                                f"(reply {hit['reply']}, {_answered(hit)}) "
                                                f"scored {got}"))
        elif r["verified"]:
            review.append((what, repro, f"VERIFIED after a changed reply {hit['reply']} "
                                        f"({_answered(hit)}): "
                                        f"{got}, {r['not_applicable_total']} n/a (clean: "
                                        f"{clean[ps]['passed']}/{clean[ps]['total']}, "
                                        f"{clean[ps]['not_applicable_total']} n/a)"))
        if i % cli_every == 0:
            from pq_verify.cli import main as cli
            try:
                with contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()):
                    code = cli(["--audit-harness", repro, ps, "--accumulated", "0",
                                "--audit-timeout", str(HARNESS_CALL_TIMEOUT),
                                "--fail-on-finding"])
            except SystemExit as e:
                code = e.code
            except BaseException as e:
                violations.append((what, repro, f"CLI raised {type(e).__name__}: {e}"))
                continue
            if code not in (0, 1, 2):
                violations.append((what, repro, f"CLI exit {code!r}"))
            elif r["verified"] is False and code == 0:
                violations.append((what, repro, "CLI exit 0 on an unverified audit"))
    return violations, review


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--cases", type=int, default=5000, help="cases per document reader")
    ap.add_argument("--fresh-cases", type=int, default=500,
                    help="cases for the fresh prompt, whose every case recomputes "
                         "the answers (about a second each)")
    ap.add_argument("--harness-cases", type=int, default=300,
                    help="audits through a corrupted harness")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--keep", help="directory to keep reproducer files in")
    ap.add_argument("--only", help="comma-separated targets: response, response-nist, "
                                   "response-lms, response-fresh, hybrid, harness")
    a = ap.parse_args(argv)
    rng = random.Random(a.seed)
    from functools import partial
    from pq_verify.response import verify_response
    from pq_verify.hybrid import verify_hybrid
    work = a.keep or tempfile.mkdtemp(prefix="pqv-fuzz-")
    os.makedirs(work, exist_ok=True)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 1000))
    only = set(a.only.split(",")) if a.only else None
    want = lambda name: only is None or name in only
    total_v, total_r = [], []
    targets = []
    if want("response"):
        targets.append(("response", verify_response, "--verify-response",
                        [seed_response()], (), True))
    if want("response-nist"):
        targets.append(("response-nist", verify_response, "--verify-response",
                        [seed_response_nist(ps) for ps in NIST_SEED_SETS], (), False))
    if want("response-lms"):
        targets.append(("response-lms", verify_response, "--verify-response",
                        [seed_response_lms(ps) for ps in LMS_SETS], (), False))
    if want("response-fresh"):
        doc, key = seed_fresh(work)
        targets.append(("response-fresh", partial(verify_response, fresh_key=key),
                        "--verify-response", [doc], ("--fresh-key", key), False))
    if want("hybrid"):
        targets.append(("hybrid", verify_hybrid, "--verify-hybrid", seed_transcripts(),
                        (), False))
    for name, fn, flag, seeds, extra, gz in targets:
        for s in seeds:                                   # the seeds themselves must verify
            p = os.path.join(work, f"{name}-seed.json")
            with open(p, "w") as fh:
                json.dump(s, fh)
            r = _run(fn, p)
            assert r["verified"], f"{name} seed does not verify: {r.get('status')}"
        t0 = time.monotonic()
        n = a.fresh_cases if name == "response-fresh" else a.cases
        v, rv = fuzz(name, fn, flag, seeds, n, rng, work, gz=gz, cli_extra=extra)
        print(f"  {name:15s} {n} cases in {time.monotonic() - t0:.0f}s: "
              f"{len(v)} violation(s), {len(rv)} VERIFIED-after-mutation for review")
        total_v += v
        total_r += rv
    if want("harness") and a.harness_cases:
        t0 = time.monotonic()
        v, rv = fuzz_harness(a.harness_cases, rng, work)
        print(f"  {'harness':15s} {a.harness_cases} audits in {time.monotonic() - t0:.0f}s: "
              f"{len(v)} violation(s), {len(rv)} VERIFIED-after-change for review")
        total_v += v
        total_r += rv
    for what, path, detail in total_v[:40]:
        print(f"  VIOLATION  {detail}\n             {what}  ({path})")
    for what, path, detail in total_r[:40]:
        print(f"  REVIEW     {detail}: {what}  ({path})")
    if total_r:
        # Every entry, by kind of change: a reviewer checks that each kind is
        # one the reader is documented to ignore (metadata, a group label, a
        # field it does not score), without reading thousands of lines.
        counts = {}
        for what, _path, _detail in total_r:
            counts[_category(what)] = counts.get(_category(what), 0) + 1
        print(f"  review, {len(total_r)} entries by kind of change:")
        for cat, n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"    {n:6d}  {cat}")
    if a.keep:
        for fname, rows in (("violations.txt", total_v), ("review.txt", total_r)):
            with open(os.path.join(work, fname), "w") as fh:
                for what, path, detail in rows:
                    fh.write(f"{detail}\t{what}\t{path}\n")
    return 1 if total_v else 0


def _category(what):
    """A change's kind without its position: "weird value at ('suites', 0,
    'testGroups', 3, 'tgId')" -> "weird value at tgId"."""
    import re
    if ", reply " in what:                              # a harness case
        ps, rest = what.split(", reply ", 1)
        return f"harness {ps}: {rest.split(': ', 1)[-1]}"
    def last_name(m):
        names = re.findall(r"'([^']+)'", m.group(1))
        return names[-1] if names else "the top level"
    what = re.sub(r"\(((?:'[^']*'|\d+|, )*,?)\)", last_name, what)
    return re.sub(r"\b\d+\b", "N", what)


if __name__ == "__main__":
    sys.exit(main())
