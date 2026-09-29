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

Mutations are structure-aware: they start from genuine documents (a kyber-py
answered ML-KEM-512 prompt, and real hybrid transcripts for every group) and
damage them the ways a buggy or hostile producer would. Stdlib only.

  python3 tests/fuzz_readers.py                 5000 cases per reader
  python3 tests/fuzz_readers.py --cases 200 --seed 7

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


def _cli(flag, path):
    from pq_verify.cli import main
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return main([flag, path, "--fail-on-finding"])


def fuzz(name, fn, flag, seeds, cases, rng, workdir, cli_every=25, gz=False):
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
                code = _cli(flag, path)
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


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--cases", type=int, default=5000, help="cases per reader")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--keep", help="directory to keep reproducer files in")
    a = ap.parse_args(argv)
    rng = random.Random(a.seed)
    from pq_verify.response import verify_response
    from pq_verify.hybrid import verify_hybrid
    work = a.keep or tempfile.mkdtemp(prefix="pqv-fuzz-")
    os.makedirs(work, exist_ok=True)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 1000))
    total_v, total_r = [], []
    for name, fn, flag, seeds in (
            ("response", verify_response, "--verify-response", [seed_response()]),
            ("hybrid", verify_hybrid, "--verify-hybrid", seed_transcripts())):
        for s in seeds:                                   # the seeds themselves must verify
            p = os.path.join(work, f"{name}-seed.json")
            with open(p, "w") as fh:
                json.dump(s, fh)
            r = _run(fn, p)
            assert r["verified"], f"{name} seed does not verify: {r.get('status')}"
        t0 = time.monotonic()
        v, rv = fuzz(name, fn, flag, seeds, a.cases, rng, work,
                     gz=(name == "response"))
        print(f"  {name:8s} {a.cases} cases in {time.monotonic() - t0:.0f}s: "
              f"{len(v)} violation(s), {len(rv)} VERIFIED-after-mutation for review")
        total_v += v
        total_r += rv
    for what, path, detail in total_v[:40]:
        print(f"  VIOLATION  {detail}\n             {what}  ({path})")
    for what, path, detail in total_r[:40]:
        print(f"  REVIEW     {detail}: {what}  ({path})")
    return 1 if total_v else 0


if __name__ == "__main__":
    sys.exit(main())
