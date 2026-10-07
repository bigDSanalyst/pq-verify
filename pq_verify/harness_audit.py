"""Audit an implementation through a Crucible-protocol harness.

Crucible (github.com/symbolicsoft/crucible, Apache-2.0) drives ML-KEM and
ML-DSA implementations in any language through a small program -- a harness
-- that speaks JSON lines over stdin/stdout. Harnesses exist for Go's
crypto/mlkem, CIRCL, Bouncy Castle, libcrux, AWS-LC, wolfCrypt, liboqs, the
Zig standard library and more. pq-verify speaks the same protocol, so any of
them can be audited here, unchanged, with pq-verify's vectors and verdicts:

    ML-KEM   keyGen / encaps / decaps byte-exact against NIST's ACVP vectors,
             NIST's invalid encapsulation and decapsulation keys (FIPS 203
             §7.2/§7.3), and the Wycheproof/CCTV edge cases
    ML-DSA   NIST's keyGen, sigGen and sigVer for every interface the
             protocol can carry, and Wycheproof's edge cases

Protocol (Crucible's README, "Harness Protocol"): the harness prints a
handshake {"implementation", "functions"}; each request is
{"function", "inputs" (hex), "params"}; each reply is {"outputs" (hex)},
{"error"} or {"unsupported": true}.
  ML_KEM_KeyGen  randomness = d || z (64), param_set  -> ek, dk
  ML_KEM_Encaps  ek, randomness = m (32)              -> c, K
  ML_KEM_Decaps  c, dk                                -> K
  ML_DSA_KeyGen  seed (32), param_set                 -> pk, sk
  ML_DSA_Sign    sk, message = M', rnd (32)           -> signature
  ML_DSA_Verify  pk, message = M', signature          -> valid ("01"/"00")
ML-DSA's "message" is FIPS 204's M' (Sign_internal / Verify_internal), so
pq-verify formats M' itself and sends NIST's internal, pure and pre-hash
cases through it. External mu has no route and is not applicable.

What a verdict here binds to. A harness is a separate program wrapping a
library; pq-verify hashes the harness executable, not the library behind
it, and a failure can sit in the harness's wiring as well as in the library.
The report says both.

Three rules keep a harness from producing a false pass:
  * A harness that crashes, hangs, breaks the protocol, or answers
    "unsupported" for a function it advertised ends the audit: CANNOT
    VERIFY. It is never read as the library refusing an input -- which, for
    the invalid-input checks, would have scored as a pass.
  * Determinism is tested, not assumed. Crucible's harnesses differ: some
    ignore the seed. Each operation is asked twice with the same inputs; a
    byte-exact check the harness cannot be held to is not applicable, with
    the reason, never a pass.
  * An "error" reply is a refusal, as a nonzero return is for a C library.
"""
import json as _json
import os as _os
import queue as _queue
import shlex as _shlex
import shutil as _shutil
import subprocess as _sp
import threading as _threading

DEFAULT_CALL_TIMEOUT = 60          # seconds per request


class HarnessDied(BaseException):
    """The harness crashed, hung, or broke the protocol. A BaseException on
    purpose: the vector runners read any Exception from a backend as the
    library refusing the input, and a dead harness must never score as a
    refusal."""


class Refused(Exception):
    """The harness answered {"error": ...}: the implementation refused."""


class Harness:
    """A running Crucible-protocol harness."""

    def __init__(self, argv, timeout=DEFAULT_CALL_TIMEOUT):
        self.argv = list(argv)
        self.timeout = timeout
        self.calls = 0
        try:
            self.proc = _sp.Popen(self.argv, stdin=_sp.PIPE, stdout=_sp.PIPE,
                                  stderr=_sp.DEVNULL, bufsize=0)
        except OSError as exc:
            raise HarnessDied(f"cannot start the harness: {exc}") from None
        self._lines = _queue.Queue()
        t = _threading.Thread(target=self._pump, daemon=True)
        t.start()
        hs = self._read("the handshake")
        if not isinstance(hs, dict) or "implementation" not in hs:
            self.close()
            raise HarnessDied(f"the first line is not a handshake: {str(hs)[:120]}")
        self.implementation = str(hs["implementation"])
        self.functions = [str(f) for f in hs.get("functions") or []]

    def _pump(self):
        for line in iter(self.proc.stdout.readline, b""):
            self._lines.put(line)
        self._lines.put(None)

    def _read(self, what):
        try:
            line = self._lines.get(timeout=self.timeout)
        except _queue.Empty:
            self.close()
            raise HarnessDied(f"no answer to {what} within {self.timeout} s") from None
        if line is None:
            code = self.proc.wait()
            raise HarnessDied(f"the harness exited (status {code}) during {what}")
        try:
            return _json.loads(line)
        except ValueError:
            self.close()
            raise HarnessDied(f"not JSON in reply to {what}: {line[:120]!r}") from None

    def call(self, function, inputs=None, params=None):
        """outputs as bytes; Refused on an error reply; HarnessDied otherwise."""
        req = {"function": function,
               "inputs": {k: bytes(v).hex() for k, v in (inputs or {}).items()}}
        if params:
            req["params"] = params
        try:
            self.proc.stdin.write((_json.dumps(req) + "\n").encode())
            self.proc.stdin.flush()
        except (BrokenPipeError, OSError):
            raise HarnessDied(f"the harness closed its input before {function}") from None
        self.calls += 1
        r = self._read(function)
        if not isinstance(r, dict):
            raise HarnessDied(f"reply to {function} is not an object")
        if r.get("unsupported"):
            raise HarnessDied(f"the harness answered 'unsupported' for {function}, "
                              f"which it advertised")
        if r.get("error"):
            raise Refused(str(r["error"])[:200])
        try:
            return {k: bytes.fromhex(v) for k, v in (r.get("outputs") or {}).items()}
        except (ValueError, TypeError):
            raise HarnessDied(f"reply to {function} has non-hex outputs") from None

    def need(self, *functions):
        missing = [f for f in functions if f not in self.functions]
        if missing:
            raise HarnessDied(f"the harness does not advertise {', '.join(missing)}")

    def close(self):
        try:
            self.proc.stdin.close()
        except OSError:
            pass
        try:
            self.proc.wait(timeout=5)
        except _sp.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()


def _out(outs, key, function):
    if key not in outs:
        raise HarnessDied(f"{function} returned no '{key}'")
    return outs[key]


# ─────────────────────────────── ML-KEM ───────────────────────────────

class HarnessKEM:
    """The edge-case backend contract (pq_verify.edge) over a harness."""
    fixed_buffers = False           # a harness takes any length; it may refuse

    def __init__(self, h, param_set):
        self.h = h
        self.ps = int(param_set.rsplit("-", 1)[1])
        self.seed_dk = False        # dk kept as the 64-byte seed d || z

    def accepts(self, kind, args):
        """Edge cases this library can be handed: a seed-form library takes
        no expanded decapsulation key."""
        return not (self.seed_dk and kind == "decaps" and len(args[0]) != 64)

    def keygen(self, d, z):
        o = self.h.call("ML_KEM_KeyGen", {"randomness": d + z}, {"param_set": self.ps})
        return _out(o, "ek", "ML_KEM_KeyGen"), _out(o, "dk", "ML_KEM_KeyGen")

    def keygen_seed(self, seed):
        return self.keygen(seed[:32], seed[32:])

    def encaps(self, ek, m):
        o = self.h.call("ML_KEM_Encaps", {"ek": ek, "randomness": m})
        return _out(o, "c", "ML_KEM_Encaps"), _out(o, "K", "ML_KEM_Encaps")

    def decaps(self, dk, c):
        return _out(self.h.call("ML_KEM_Decaps", {"c": c, "dk": dk}), "K", "ML_KEM_Decaps")


def _deterministic(f, *args):
    try:
        return f(*args) == f(*args)
    except Refused:
        return False


def run_kem(h, param_set, load, edge=True):
    from .edge import run_kem as edge_kem, kem_cases
    h.need("ML_KEM_KeyGen", "ML_KEM_Encaps", "ML_KEM_Decaps")
    b = HarnessKEM(h, param_set)
    tally, na, failures = {}, {}, []

    def rec(stage, ok, case, why):
        p, t = tally.get(stage, (0, 0))
        tally[stage] = (p + int(ok), t + 1)
        if not ok and len(failures) < 50:
            failures.append({"stage": stage, "case": case, "detail": why})

    def skip(stage, why):
        c, _ = na.get(stage, (0, why))
        na[stage] = (c + 1, why)

    kg = load("ML-KEM-keyGen-FIPS203", "internalProjection.json")
    ed = load("ML-KEM-encapDecap-FIPS203", "internalProjection.json")
    t0 = next(t for g in kg["testGroups"] if g.get("parameterSet") == param_set
              for t in g["tests"])
    d0, z0 = bytes.fromhex(t0["d"]), bytes.fromhex(t0["z"])
    try:
        ek0, dk0 = b.keygen(d0, z0)
    except Refused as exc:
        raise HarnessDied(f"the harness refuses {param_set} key generation "
                          f"({exc}); nothing can be checked") from None
    det_kg = _deterministic(b.keygen, d0, z0)
    # FIPS 203 §7.1 lets an implementation keep the decapsulation key as its
    # seed d || z (Go's crypto/mlkem and BoringSSL do). NIST's decapsulation
    # vectors carry only the expanded key, which such a library cannot take.
    b.seed_dk = dk0 == d0 + z0
    why_seed = ("the library keeps decapsulation keys in seed form (d || z, FIPS 203 "
                "§7.1); NIST's decapsulation vectors carry only the expanded key")
    det_en = _deterministic(b.encaps, ek0, bytes(32))
    why_kg = "the harness ignores the key-generation randomness (two calls, two keys)"
    why_en = "the harness ignores the encapsulation randomness (two calls, two results)"

    for g in kg["testGroups"]:
        if g.get("parameterSet") != param_set:
            continue
        for t in g["tests"]:
            if not det_kg:
                skip("keyGen", why_kg)
                continue
            try:
                d, z = bytes.fromhex(t["d"]), bytes.fromhex(t["z"])
                ek, dk = b.keygen(d, z)
                want_dk = d + z if b.seed_dk else bytes.fromhex(t["dk"])
                ok = ek.hex().upper() == t["ek"].upper() and dk == want_dk
                rec("keyGen", ok, f"tcId {t['tcId']}",
                    "ek differs from NIST, or dk is not d || z" if b.seed_dk
                    else "ek or dk differs from NIST")
            except Refused as exc:
                rec("keyGen", False, f"tcId {t['tcId']}", f"refused: {exc}")
    for g in ed["testGroups"]:
        if g.get("parameterSet") != param_set:
            continue
        fn = g.get("function")
        for t in g["tests"]:
            case = f"tcId {t['tcId']}"
            if fn == "encapsulation":
                if not det_en:
                    skip("encaps", why_en)
                    continue
                try:
                    c, K = b.encaps(bytes.fromhex(t["ek"]), bytes.fromhex(t["m"]))
                    ok = c.hex().upper() == t["c"].upper() and K.hex().upper() == t["k"].upper()
                    rec("encaps", ok, case, "c or K differs from NIST")
                except Refused as exc:
                    rec("encaps", False, case, f"refused a valid key: {exc}")
            elif fn == "decapsulation":
                if "dk" not in t or "c" not in t or "k" not in t:
                    continue
                if b.seed_dk:
                    skip("decaps", why_seed)
                    continue
                try:
                    K = b.decaps(bytes.fromhex(t["dk"]), bytes.fromhex(t["c"]))
                    rec("decaps", K.hex().upper() == t["k"].upper(), case,
                        "K differs from NIST")
                except Refused as exc:
                    rec("decaps", False, case, f"refused: {exc}")
            elif fn in ("encapsulationKeyCheck", "decapsulationKeyCheck"):
                stage = "ekCheck" if fn == "encapsulationKeyCheck" else "dkCheck"
                if stage == "dkCheck" and b.seed_dk:
                    skip("dkCheck", why_seed)
                    continue
                try:
                    if stage == "ekCheck":
                        b.encaps(bytes.fromhex(t["ek"]), bytes(32))
                    else:
                        b.decaps(bytes.fromhex(t["dk"]), bytes(_ct_len(param_set)))
                    accepted = True
                except Refused:
                    accepted = False
                want = bool(t["testPassed"])
                rec(stage, accepted == want, case,
                    "accepted an invalid key" if accepted else "refused a valid key")

    edge_res = None
    if edge:
        if det_kg and det_en:
            edge_res = edge_kem(b, param_set)
            for stage, (p, t) in edge_res["stages"].items():
                tally[stage] = (p, t)
            failures.extend({"stage": f["stage"], "case": f["case"], "detail": f["detail"]}
                            for f in edge_res["failures"][:20])
        else:
            n = len(kem_cases(param_set))
            na["edge"] = (n, "the edge cases need deterministic key generation and "
                             "encapsulation, which this harness does not provide")
    if edge_res and edge_res.get("not_applicable"):
        na["edge"] = (edge_res["not_applicable"], why_seed if b.seed_dk else
                      "inputs this harness cannot be handed")
    return tally, na, failures, {"keyGen": det_kg, "encaps": det_en,
                                 "seed_form_dk": b.seed_dk}


def _ct_len(param_set):
    from .core import _KEM_SIZES
    return _KEM_SIZES[param_set][2]


# ─────────────────────────────── ML-DSA ───────────────────────────────

class HarnessDSA:
    """The VendorDSA contract (pq_verify.dsa_audit) over a harness, so NIST's
    vectors and the edge cases run through exactly the same scoring."""

    def __init__(self, h, param_set):
        from .dsa_audit import NotApplicable, VendorError
        self.NA, self.VE = NotApplicable, VendorError
        self.h = h
        self.param_set = param_set
        self.ps = int(param_set.rsplit("-", 1)[1])
        self.det_keygen = self.det_sign = True
        self.name = h.implementation
        # What the harness's "message" means. The protocol says M' (FIPS 204
        # Sign_internal); some of Crucible's own harnesses (CIRCL, liboqs)
        # treat it as M with an empty context. Settled against NIST below.
        self.convention = "M'"

    def detect_convention(self, load):
        """Sign one NIST deterministic, pure, empty-context case both ways and
        keep the convention whose signature is NIST's. Neither: keep M', the
        protocol's, and let the vectors report the failures."""
        p = load("ML-DSA-sigGen-FIPS204", "prompt.json")
        e = load("ML-DSA-sigGen-FIPS204", "expectedResults.json")
        exp = {str(t["tcId"]): t for g in e["testGroups"] for t in g["tests"]}
        for g in p["testGroups"]:
            if (g.get("parameterSet") != self.param_set or not g.get("deterministic")
                    or g.get("signatureInterface") != "external"
                    or g.get("preHash", "pure") != "pure"):
                continue
            for t in g["tests"]:
                if t.get("context", ""):
                    continue
                sk, m = bytes.fromhex(t["sk"]), bytes.fromhex(t["message"])
                want = bytes.fromhex(exp[str(t["tcId"])]["signature"])
                try:
                    if self._sign(sk, b"\x00\x00" + m, bytes(32)) == want:
                        self.convention = "M'"
                    elif self._sign(sk, m, bytes(32)) == want:
                        self.convention = "M, empty context"
                except self.VE:
                    pass
                return self.convention
        return self.convention

    def probe(self):
        seed = bytes(range(32))
        try:
            pk1, sk = self._keygen(seed)
        except Refused as exc:
            raise HarnessDied(f"the harness refuses {self.param_set} key generation "
                              f"({exc}); nothing can be checked") from None
        self.det_keygen = (pk1, sk) == self._keygen(seed)
        m, rnd = b"\x00\x00pq-verify", bytes(32)
        try:
            sig = self._sign(sk, m, rnd)
            self.det_sign = sig == self._sign(sk, m, rnd)
        except self.VE as exc:
            raise HarnessDied(f"the harness refuses to sign ({exc})") from None
        # A verify that errors is scored as a rejection, which on invalid
        # vectors is a pass. So the harness must first accept its own fresh
        # signature: if it cannot, its wiring is broken and nothing it
        # rejects means anything.
        try:
            o = self.h.call("ML_DSA_Verify", {"pk": pk1, "message": m,
                                              "signature": sig, "sigma": sig},
                            {"param_set": self.ps})
        except Refused as exc:
            raise HarnessDied(f"the harness's verify errors on its own fresh "
                              f"signature ({exc}); its rejections cannot be scored") from None
        if o.get("valid") != b"\x01":
            raise HarnessDied("the harness rejects its own fresh signature; its "
                              "rejections cannot be scored")

    def entry(self, op):
        return {"keygen": "ML_DSA_KeyGen", "sign_mu": None, "verify_mu": None}.get(
            op, "ML_DSA_Sign" if op.startswith("sign") else "ML_DSA_Verify")

    def _keygen(self, seed):
        o = self.h.call("ML_DSA_KeyGen", {"seed": seed}, {"param_set": self.ps})
        return _out(o, "pk", "ML_DSA_KeyGen"), _out(o, "sk", "ML_DSA_KeyGen")

    def _sign(self, sk, mprime, rnd):
        try:
            o = self.h.call("ML_DSA_Sign", {"sk": sk, "message": mprime, "rnd": rnd},
                            {"param_set": self.ps})
        except Refused as exc:
            raise self.VE(f"refused: {exc}") from None
        return _out(o, "signature", "ML_DSA_Sign")

    def _verify(self, pk, mprime, sig):
        try:
            # Crucible's README names this input "signature"; its battery and
            # several harnesses (CIRCL, tob-mldsa) read "sigma". Send both.
            o = self.h.call("ML_DSA_Verify", {"pk": pk, "message": mprime,
                                              "signature": sig, "sigma": sig},
                            {"param_set": self.ps})
        except Refused:
            return False
        v = _out(o, "valid", "ML_DSA_Verify")
        if v not in (b"\x00", b"\x01"):
            raise HarnessDied(f"ML_DSA_Verify returned valid={v.hex()}")
        return v == b"\x01"

    def keygen(self, seed):
        if len(seed) != 32:
            raise self.NA(f"the protocol takes a 32-byte seed, not {len(seed)}")
        if not self.det_keygen:
            raise self.NA("the harness ignores the key-generation seed (two calls, two keys)")
        try:
            return self._keygen(seed)
        except Refused as exc:
            raise self.VE(f"refused: {exc}") from None

    def _external_only(self, pre):
        """Under the "M, empty context" convention only M' = 0x00 0x00 || M
        can be expressed: send M."""
        if self.convention == "M'":
            return None
        if pre != b"\x00\x00":
            raise self.NA("this harness signs and verifies M with an empty context "
                          "(not the protocol's M'), so internal, pre-hash and "
                          "context cases cannot be passed")
        return True

    def sign_internal(self, pre, m, rnd, sk):
        if not self.det_sign:
            raise self.NA("the harness ignores rnd (two calls, two signatures)")
        if self._external_only(pre):
            return self._sign(sk, m, rnd)
        return self._sign(sk, pre + m, rnd)

    def _prefix(self, kind, ctx):
        if len(ctx) > 255:
            raise self.NA("a context over 255 bytes cannot be encoded in M'")
        return bytes([kind, len(ctx)]) + ctx

    def sign_pure(self, m, ctx, rnd, sk):
        return self.sign_internal(self._prefix(0, ctx), m, rnd, sk)


    def sign_prehash(self, ph, oid, hash_alg, ctx, rnd, sk):
        return self.sign_internal(self._prefix(1, ctx) + oid, ph, rnd, sk)

    def sign_mu(self, mu, rnd, sk):
        raise self.NA("the protocol carries M', not an external mu")

    def verify_internal(self, pre, m, sig, pk):
        if self._external_only(pre):
            return self._verify(pk, m, sig)
        return self._verify(pk, pre + m, sig)

    def verify_pure(self, m, ctx, sig, pk):
        return self.verify_internal(self._prefix(0, ctx), m, sig, pk)

    def verify_prehash(self, ph, oid, hash_alg, ctx, sig, pk):
        return self.verify_internal(self._prefix(1, ctx) + oid, ph, sig, pk)

    def verify_mu(self, mu, sig, pk):
        raise self.NA("the protocol carries M', not an external mu")

    # the edge-case backend (pq_verify.edge.run_dsa)
    def verify(self, pk, msg, sig, ctx):
        return self.verify_pure(msg, ctx, sig, pk)

    def sign(self, seed, msg, mu, ctx, rnd):
        pk, sk = self.keygen(seed)
        r = bytes.fromhex(rnd) if rnd is not None else bytes(32)
        if mu is not None and msg is None:
            return pk, self.sign_mu(bytes.fromhex(mu), r, sk)
        return pk, self.sign_pure(bytes.fromhex(msg), ctx, r, sk)


def run_dsa(h, param_set, load, edge=True):
    from .dsa_audit import run_acvp
    from .edge import run_dsa as edge_dsa
    h.need("ML_DSA_KeyGen", "ML_DSA_Sign", "ML_DSA_Verify")
    v = HarnessDSA(h, param_set)
    v.probe()
    v.detect_convention(load)
    tally, na, failures = run_acvp(v, lambda d: (load(d, "prompt.json"),
                                                 load(d, "expectedResults.json")))
    failures = [{"stage": f["stage"], "case": f"tcId {f.get('tcId')}",
                 "detail": f.get("detail")} for f in failures]
    na = {k: tuple(x) for k, x in na.items()}
    if edge:
        res = edge_dsa(v, param_set)
        for stage, (p, t) in res["stages"].items():
            tally["edge:" + stage] = (p, t)
        if res["not_applicable"]:
            na["edge"] = (res["not_applicable"], "cases the protocol or this harness "
                                                 "cannot express (seed or rnd ignored, "
                                                 "external mu)")
        failures.extend({"stage": "edge:" + f["stage"], "case": f["case"],
                         "detail": f["detail"]} for f in res["failures"][:20])
    return tally, na, failures, {"keyGen": v.det_keygen, "sign": v.det_sign,
                                 "message": v.convention}


# ─────────────────────────────── the audit ───────────────────────────────

KEM_SETS = ("ML-KEM-512", "ML-KEM-768", "ML-KEM-1024")
DSA_SETS = ("ML-DSA-44", "ML-DSA-65", "ML-DSA-87")


def harness_executable(argv):
    """The file the harness command runs, for binding: the first argument
    that is an existing file (a script's interpreter is skipped)."""
    import re
    interpreter = re.compile(r"(python[0-9.]*|pypy[0-9.]*|java|node|deno|bun|ruby|"
                             r"perl|sh|bash|dash|zsh|env|go|cargo|dotnet)(\.exe)?$")
    for a in argv:
        p = a if _os.sep in a else _shutil.which(a)
        if p and _os.path.isfile(p) and not interpreter.match(_os.path.basename(p)):
            return _os.path.abspath(p)
    return None


def pqverify_audit_harness(command, param_set, timeout=DEFAULT_CALL_TIMEOUT,
                           verbose=True, edge=True):
    """Audit the implementation behind a Crucible-protocol harness.

    `command` is the harness command line (a string, split with shlex, or a
    list). Returns a result dict; 'status' is CANNOT VERIFY (with 'reason')
    when the harness died or lacks the functions the parameter set needs.
    """
    from .core import _load_vector_json, _pkg_dir, _vector_label
    argv = _shlex.split(command) if isinstance(command, str) else list(command)
    if param_set not in KEM_SETS + DSA_SETS:
        raise ValueError(f"unknown parameter set {param_set}")
    kem = param_set in KEM_SETS
    vec = _os.path.join(_pkg_dir(), "vectors")
    load = lambda d, f: _load_vector_json(_os.path.join(vec, d, f), f"{d}/{f}")
    dirs = (("ML-KEM-keyGen-FIPS203", "ML-KEM-encapDecap-FIPS203") if kem else
            ("ML-DSA-keyGen-FIPS204", "ML-DSA-sigGen-FIPS204", "ML-DSA-sigVer-FIPS204"))
    base = {"command": argv, "parameter_set": param_set,
            "vectors": _vector_label(vec, *dirs)}
    h = None
    try:
        h = Harness(argv, timeout=timeout)
        base["implementation"] = h.implementation
        if verbose:
            print("=" * 68)
            print(f"  HARNESS AUDIT (Crucible protocol) — {param_set}")
            print(f"  harness : {' '.join(argv)}")
            print(f"  reports : {h.implementation}")
            print(f"  vectors : {base['vectors']}")
            print("=" * 68)
        runner = run_kem if kem else run_dsa
        tally, na, failures, det = runner(h, param_set, load, edge=edge)
        calls = h.calls
    except HarnessDied as exc:
        if verbose:
            print(f"  CANNOT VERIFY: {exc}")
        return dict(base, verified=False, status="CANNOT VERIFY", reason=str(exc),
                    passed=0, total=0, detail={}, not_applicable={},
                    not_applicable_total=0, failures=[])
    finally:
        if h is not None:
            h.close()
    p_all = sum(p for p, _ in tally.values())
    t_all = sum(t for _, t in tally.values())
    na_all = sum(c for c, _ in na.values())
    verified = p_all == t_all and t_all > 0
    status = "VERIFIED" if verified else ("FINDINGS PRESENT" if t_all else "CANNOT VERIFY")
    notes = []
    if det.get("message") == "M, empty context":
        notes.append("the harness treats ML_DSA_Sign/Verify's \"message\" as M with an "
                     "empty context (FIPS 204 external signing), not the protocol's M'; "
                     "only pure, empty-context cases can be passed to it")
    if det.get("seed_form_dk"):
        notes.append("the library keeps decapsulation keys in seed form (d || z)")
    for k in ("keyGen", "encaps", "sign"):
        if det.get(k) is False:
            notes.append(f"the harness's {k} ignores its randomness input; byte-exact "
                         f"{k} checks are not applicable")
    if verbose:
        for s, (p, t) in tally.items():
            print(f"  {'PASS' if p == t else 'FAIL'}  {s:16s} {p}/{t}")
        for s, (c, why) in na.items():
            print(f"  n/a   {s:16s} {c}: {why}")
        for f in failures[:5]:
            print(f"        ✗ {f['stage']} {f['case']}: {f['detail']}")
        for n in notes:
            print(f"  note: {n}")
        print("=" * 68)
        print(f"  RESULT: {p_all}/{t_all} — {status}"
              + (f"   ({na_all} not applicable)" if na_all else ""))
        print("  Audited: the harness AND the implementation behind it. A failure")
        print("  can be the harness's wiring; the library itself is not hashed.")
        print("=" * 68)
    return dict(base, verified=verified, status=status, passed=p_all, total=t_all,
                detail=tally, not_applicable={k: list(x) for k, x in na.items()},
                not_applicable_total=na_all, failures=failures, deterministic=det,
                harness_notes=notes, calls=calls)
