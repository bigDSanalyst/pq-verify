"""The reference harness with one reply corrupted, for tests/fuzz_readers.py.

    python fuzz_harness.py WHEN KIND SEED LOG

WHEN  which reply to corrupt: N (0 is the handshake, 1 the reply to the
      first request), or "bad-ek": the reply to the first ML_KEM_Encaps
      whose encapsulation key has no ML-KEM length. Only the edge cases send
      one, and there a refusal is the expected answer.
KIND  how to corrupt it; KINDS below. Each is either a protocol break, after
      which the audit must end CANNOT VERIFY, or a change of content, after
      which it must not come back VERIFIED unless the content did not matter.
SEED  seeds the choices a kind makes (which output, which digit).
LOG   gets one JSON line when the corruption is written:
      {"reply": n, "kind": ..., "class": "protocol" | "content"}.

Every other reply is the reference harness's own (crucible_ref_harness.py),
which audits VERIFIED.
"""
import json
import os
import random
import sys

WHEN, KIND, SEED, LOG = sys.argv[1:5]
sys.argv = sys.argv[:1]                  # the reference harness reads its FAULT here
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import crucible_ref_harness as ref       # noqa: E402

rng = random.Random(int(SEED))
EK_LENGTHS = {800, 1184, 1568}

# kind: (class, applies to)  "any" (the handshake included) | "reply" (any
# reply to a request) | "outputs" (a reply carrying outputs) | "error" (a
# refusal) | "handshake". The protocol-breaking kinds that need outputs build
# them, when the reply has none, from the outputs the function returns.
KINDS = {
    "garbage":          ("protocol", "any"),
    "truncated":        ("protocol", "any"),
    "not-object":       ("protocol", "any"),
    "deep-nesting":     ("protocol", "any"),
    "empty-line":       ("protocol", "any"),
    "unsupported":      ("protocol", "any"),
    "exit":             ("protocol", "any"),
    "outputs-list":     ("protocol", "reply"),
    "outputs-string":   ("protocol", "reply"),
    "outputs-number":   ("protocol", "reply"),
    "value-type":       ("protocol", "reply"),
    "value-not-hex":    ("protocol", "reply"),
    "value-odd-length": ("protocol", "reply"),
    "missing-output":   ("protocol", "reply"),
    "oversized":        ("protocol", "any"),
    "functions-type":   ("protocol", "handshake"),
    "flip-digit":       ("content", "outputs"),
    "drop-byte":        ("content", "outputs"),
    "refuse":           ("content", "outputs"),
    "extra-output":     ("content", "outputs"),
    "accept":           ("content", "error"),
}

# What each function returns, for kinds that build outputs a refusal lacks.
SHAPES = {"ML_KEM_KeyGen": {"ek": "00" * 800, "dk": "00" * 1632},
          "ML_KEM_Encaps": {"c": "00" * 768, "K": "00" * 32},
          "ML_KEM_Decaps": {"K": "00" * 32},
          "ML_DSA_KeyGen": {"pk": "00" * 1312, "sk": "00" * 2560},
          "ML_DSA_Sign": {"signature": "00" * 2420},
          "ML_DSA_Verify": {"valid": "01"}}

_n = [0]           # replies written so far; 0 is the handshake
_req = [None]      # the request being answered
_done = [False]


def _log(cls):
    with open(LOG, "a") as fh:
        fh.write(json.dumps({"reply": _n[0], "kind": KIND, "class": cls}) + "\n")


def _raw(line):
    sys.stdout.write(line)
    sys.stdout.flush()


def _due(obj):
    if _done[0]:
        return False
    if WHEN == "bad-ek":
        r = _req[0] or {}
        ek = (r.get("inputs") or {}).get("ek")
        return (r.get("function") == "ML_KEM_Encaps" and ek is not None
                and len(ek) // 2 not in EK_LENGTHS)
    return _n[0] == int(WHEN)


def _applies(obj):
    cls, where = KINDS[KIND]
    if where == "handshake":
        return _n[0] == 0
    if where == "reply":
        return _n[0] > 0
    if where == "outputs":
        return isinstance(obj, dict) and isinstance(obj.get("outputs"), dict) \
            and bool(obj["outputs"])
    if where == "error":
        return isinstance(obj, dict) and "error" in obj
    return True


def _corrupt(obj):
    """The line to write instead of obj, or None to write nothing more."""
    line = json.dumps(obj)
    outs = obj.get("outputs") if isinstance(obj, dict) else None
    if not outs:
        outs = dict(SHAPES.get((_req[0] or {}).get("function"), {"x": "00"}))
    key = rng.choice(sorted(outs))
    if KIND == "garbage":
        return "".join(chr(rng.randrange(33, 127)) for _ in range(rng.randrange(1, 80))) + "\n"
    if KIND == "truncated":
        return line[: rng.randrange(1, len(line))] + "\n"
    if KIND == "not-object":
        return rng.choice(["[]", "42", '"x"', "null", "true", json.dumps([obj])]) + "\n"
    if KIND == "deep-nesting":
        return "[" * 200_000 + "]" * 200_000 + "\n"
    if KIND == "empty-line":
        return "\n"
    if KIND == "unsupported":
        return json.dumps({"unsupported": True}) + "\n"
    if KIND == "exit":
        os._exit(0)
    if KIND == "oversized":
        return json.dumps({"outputs": {"pad": "00" * (9 << 20)}}) + "\n"
    if KIND == "functions-type":
        return json.dumps(dict(obj, functions=rng.choice([5, None, True, 1.5]))) + "\n"
    if KIND == "outputs-list":
        return json.dumps({"outputs": [outs[key]]}) + "\n"
    if KIND == "outputs-string":
        return json.dumps({"outputs": outs[key]}) + "\n"
    if KIND == "outputs-number":
        return json.dumps({"outputs": rng.choice([7, -1, 1.5])}) + "\n"
    if KIND == "value-type":
        return json.dumps({"outputs": dict(outs, **{key: rng.choice([7, None, [], {}, True])})}) + "\n"
    if KIND == "value-not-hex":
        v = outs[key]
        i = rng.randrange(len(v)) if v else 0
        return json.dumps({"outputs": dict(outs, **{key: v[:i] + "zz" + v[i + 2:]})}) + "\n"
    if KIND == "value-odd-length":
        return json.dumps({"outputs": dict(outs, **{key: outs[key] + "0"})}) + "\n"
    if KIND == "missing-output":
        return json.dumps({"outputs": {k: v for k, v in outs.items() if k != key}}) + "\n"
    if KIND == "flip-digit":
        v = outs[key]
        i = rng.randrange(len(v))
        return json.dumps(dict(obj, outputs=dict(outs, **{key: v[:i] + format(int(v[i], 16) ^ 1, "x") + v[i + 1:]}))) + "\n"
    if KIND == "drop-byte":
        return json.dumps(dict(obj, outputs=dict(outs, **{key: outs[key][2:]}))) + "\n"
    if KIND == "refuse":
        return json.dumps({"error": "fuzz: refused"}) + "\n"
    if KIND == "extra-output":
        return json.dumps(dict(obj, outputs=dict(outs, extra="00"))) + "\n"
    if KIND == "accept":
        return json.dumps({"outputs": outs}) + "\n"
    raise SystemExit(f"unknown KIND {KIND}")


def out(obj):
    if _due(obj) and _applies(obj):
        _done[0] = True
        _log(KINDS[KIND][0])
        line = _corrupt(obj)
        if line is not None:
            _raw(line)
    else:
        _raw(json.dumps(obj) + "\n")
    _n[0] += 1


_handle = ref.handle


def handle(req):
    _req[0] = req
    return _handle(req)


ref.out = out
ref.handle = handle

if __name__ == "__main__":
    ref.main()
