"""Audit a THIRD-PARTY Classic McEliece library (round 4; not a FIPS standard).

The vendor's own compiled code is driven through its public entry points and
judged by pq_verify.mceliece, the reference that reproduces every pinned KAT
(`pq-verify --mceliece`):

    keyGen   vendor key pairs, regenerated from the seed each private key
             begins with: the public key byte for byte, the private key's
             pivots c, Goppa polynomial g and rejection string s byte for
             byte, and its Benes control bits applied to the identity giving
             the regenerated permutation. No control over the library's
             randomness is needed: the key carries its own seed.
    encaps   vendor ciphertexts decode under pq-verify's decoder to an error
             vector of weight exactly t, the vendor's key is
             SHAKE256(1 || e || C), its own Decap returns the same key, and
             no error vector repeats
    decaps   ciphertexts built against the vendor's own key, each with its
             answer computed by pq-verify's decoder:
               weight-t errors at random positions, in the first t positions
               (the identity part of H), in the last t (the T part) and
               through the support's zero element
                                            -> SHAKE256(1 || e || C)
               weight t-1 (also through the zero element), t+1, C = 0, random
               C, and a ciphertext for the vendor's other key
                                            -> SHAKE256(0 || s || C)
             A decoder that accepts t-1 errors (it can correct them), skips
             the re-encoding check or hashes the wrong string fails here.
    padding  6960119 only (mt = 1547, k = 5413: both end mid-byte): a valid
             ciphertext with a padding bit set, and a public key with one,
             must be refused (nonzero return), as the submitters' reference
             (SUPERCOP-20221025) does

Calling conventions, by symbol name: the NIST API as PQClean exports it
(crypto_kem_{keypair,enc,dec}), and liboqs's
OQS_KEM_classic_mceliece_<set>_{keypair,encaps,decaps}; the argument orders
are the same. An ambiguous role is never guessed (--mceliece-symbol,
--symbol-prefix).
"""
import ctypes as _ct
import random
import re as _re

from . import mceliece as M

STAGES = ("keyGen", "encaps", "decaps", "padding")
KEYS = 2
ENCAPS_PER_KEY = 3
_ROLES = {
    "keypair": r"(?:crypto_kem_keypair|_keypair)$",
    "enc":     r"(?:crypto_kem_enc|_encaps)$",
    "dec":     r"(?:crypto_kem_dec|_decaps)$",
}


def exported_symbols(so_path):
    from .symbols import exported_functions
    return exported_functions(so_path)


def _matches_set(name, param_set):
    """The symbol names this parameter set: 'mceliece348864' and not
    'mceliece348864f', and the reverse."""
    digits = param_set[len("mceliece"):].rstrip("f")
    low = name.lower()
    if "mceliece" not in low:
        return False
    if param_set.endswith("f"):
        return _re.search(rf"{digits}f(?![0-9a-z])", low) is not None
    return _re.search(rf"{digits}(?![0-9a-z])", low) is not None


def resolve_symbols(exported, param_set, explicit=None, prefix=None):
    from .symbols import with_prefix
    explicit = explicit or {}
    exported = with_prefix(exported, prefix)
    found, ambiguous = {}, {}
    for role, pat in _ROLES.items():
        if explicit.get(role):
            found[role] = explicit[role]
            continue
        cands = sorted(e for e in exported
                       if _re.search(pat, e.lower()) and _matches_set(e, param_set))
        found[role] = cands[0] if len(cands) == 1 else None
        if len(cands) > 1:
            ambiguous[role] = cands
    return found, ambiguous


class VendorMcEliece:
    def __init__(self, so_path, param_set, symbols=None, prefix=None):
        import os
        self.path = os.path.abspath(so_path)
        self.name = os.path.basename(so_path)
        self.P = M.Params(param_set)
        self.lib = _ct.CDLL(self.path)
        self.sym, self.ambiguous = resolve_symbols(exported_symbols(self.path),
                                                   param_set, symbols, prefix)
        self.fn = {}
        for role, s in self.sym.items():
            if s:
                f = getattr(self.lib, s)
                f.restype = _ct.c_int
                self.fn[role] = f
        self.abi = "oqs" if any((s or "").startswith("OQS_") for s in self.sym.values()) \
            else "nist"

    def has(self, role):
        return role in self.fn

    def keypair(self):
        P = self.P
        pk = (_ct.c_uint8 * P.pk_bytes)()
        sk = (_ct.c_uint8 * P.sk_bytes)()
        rc = self.fn["keypair"](pk, sk)
        if rc != 0:
            raise RuntimeError(f"keypair returned {rc}")
        return bytes(pk), bytes(sk)

    def enc(self, pk):
        P = self.P
        ct = (_ct.c_uint8 * P.ct_bytes)()
        ss = (_ct.c_uint8 * 32)()
        rc = self.fn["enc"](ct, ss, _ct.c_char_p(bytes(pk)))
        return rc, bytes(ct), bytes(ss)

    def dec(self, ct, sk):
        ss = (_ct.c_uint8 * 32)()
        rc = self.fn["dec"](ss, _ct.c_char_p(bytes(ct)), _ct.c_char_p(bytes(sk)))
        return rc, bytes(ss)


class _Tally:
    def __init__(self):
        self.detail, self.na, self.failures = {}, {}, []

    def rec(self, stage, ok, case, detail=""):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        if not ok and len(self.failures) < 50:
            self.failures.append({"stage": stage, "case": case, "detail": detail})

    def not_applicable(self, stage, count, why):
        c, _ = self.na.get(stage, (0, why))
        self.na[stage] = (c + count, why)


def crafted(P, sk, pk, other_ct, rng):
    """[(label, C)] built against one key; answers come from pq-verify's
    decoder, never from the label."""
    def weight(w, where=None):
        pos = where if where is not None else rng.sample(range(P.n), w)
        return M.encode(P, pk, M.e_bytes(P, pos))
    out = [("weight-t error, random positions", weight(P.t)),
           ("weight-t error, random positions (2)", weight(P.t)),
           ("weight-t error in the first t positions (identity part of H)",
            weight(P.t, range(P.t))),
           ("weight-t error in the last t positions (T part of H)",
            weight(P.t, range(P.n - P.t, P.n))),
           ("weight t-1 (decodable, must still be rejected)", weight(P.t - 1))]
    # The support's zero element: an error there drops the locator's degree,
    # the classic place for a decoder to slip (a weight t-1 vector through
    # 0 is what a decoder without the weight check accepts). A key whose
    # support lacks 0 uses its smallest element, so the count never varies.
    _, support, _ = M.support_from_sk(P, sk)
    z = support.index(min(support))
    rest = rng.sample([i for i in range(P.n) if i != z], P.t)
    out += [("weight-t error through the support's zero element",
             weight(P.t, [z] + rest[:P.t - 1])),
            ("weight t-1 through the support's zero element (must be rejected)",
             weight(P.t - 1, [z] + rest[:P.t - 2])),
            ("weight t+1", weight(P.t + 1)),
            ("C = 0", bytes(P.ct_bytes))]
    for i in range(2):
        r = int.from_bytes(rng.randbytes(P.ct_bytes), "little") & ((1 << P.mt) - 1)
        out.append((f"random C ({i + 1})", r.to_bytes(P.ct_bytes, "little")))
    if other_ct is not None:
        out.append(("a valid ciphertext for the vendor's other key", other_ct))
    return out


def run(v):
    P = v.P
    T = _Tally()
    rng = random.Random(f"pq-verify mceliece audit {P.name}")
    if not v.has("keypair"):
        T.not_applicable("keyGen", KEYS * 5, "no keypair entry point")
        return T
    keys = []
    for k in range(KEYS):
        try:
            pk, sk = v.keypair()
        except RuntimeError as exc:
            T.rec("keyGen", False, f"key {k}", str(exc))
            continue
        for name, ok, why in M.check_key(P, pk, sk):
            T.rec("keyGen", ok, f"key {k}: {name}", why)
        keys.append((pk, sk))
    if not keys:
        return T

    # ---- encaps: vendor ciphertexts through pq-verify's decoder
    seen = set()
    other_ct = {}
    for k, (pk, sk) in enumerate(keys):
        if not v.has("enc"):
            T.not_applicable("encaps", ENCAPS_PER_KEY, "no encapsulation entry point")
            break
        for i in range(ENCAPS_PER_KEY):
            rc, ct, K = v.enc(pk)
            case = f"key {k}, encapsulation {i}"
            problems = []
            if rc != 0:
                problems.append(f"returned {rc}")
            e = M.decode(P, sk, ct) if rc == 0 else None
            if rc == 0 and e is None:
                problems.append("the ciphertext does not decode to a weight-t error vector")
            if e is not None:
                if K != M.shared_key(1, e, ct):
                    problems.append("the key is not SHAKE256(1 || e || C)")
                if e in seen:
                    problems.append("an error vector repeated")
                seen.add(e)
                if v.has("dec"):
                    drc, K2 = v.dec(ct, sk)
                    if drc != 0 or K2 != K:
                        problems.append("its own Decap does not return the key")
                other_ct[k] = ct
            T.rec("encaps", not problems, case, "; ".join(problems))

    # ---- decaps: crafted ciphertexts against the vendor's own key
    if not v.has("dec"):
        T.not_applicable("decaps", KEYS * 12, "no decapsulation entry point")
    else:
        for k, (pk, sk) in enumerate(keys):
            other = other_ct.get(1 - k) if len(keys) > 1 else None
            for label, C in crafted(P, sk, pk, other, rng):
                status, want, how = M.decap(P, sk, C)
                rc, got = v.dec(C, sk)
                ok = rc == 0 and got == want
                why = "" if ok else (f"returned {rc}" if rc != 0 else
                                     f"key differs from SHAKE256({1 if how == 'decoded' else 0}"
                                     f" || {'e' if how == 'decoded' else 's'} || C)")
                T.rec("decaps", ok, f"key {k}: {label} (expected: {how})", why)

    # ---- padding (6960119): refused, as the submitters' reference does. Sets
    # whose mt and k are multiples of 8 have no padding bits: no such case
    # exists, so nothing is recorded (not "not applicable": nothing is missing)
    if P.padded:
        pk, sk = keys[0]
        if v.has("dec"):
            C = M.encode(P, pk, M.e_bytes(P, rng.sample(range(P.n), P.t)))
            C = C[:-1] + bytes([C[-1] | (1 << (P.mt % 8))])
            rc, _ = v.dec(C, sk)
            T.rec("padding", rc != 0, "valid ciphertext with a padding bit set",
                  "" if rc != 0 else "decapsulated instead of refused")
        if v.has("enc"):
            bad = bytearray(pk)
            bad[P.row_bytes - 1] |= 1 << (P.k % 8)
            rc, _, _ = v.enc(bytes(bad))
            T.rec("padding", rc != 0, "public key with a padding bit set",
                  "" if rc != 0 else "encapsulated instead of refused")
    return T


def constant_time(v, keys=2):
    """Encaps and Decaps under Valgrind memcheck (pq_verify.ct_audit), on key
    pairs and ciphertexts the library made itself, outside Valgrind."""
    from . import ct_audit as CT
    material = []
    for _ in range(keys):
        pk, sk = v.keypair()
        rc, ct, _ss = v.enc(pk)
        if rc != 0:
            raise CT.Unavailable(f"encapsulation returned {rc} outside Valgrind")
        material.append((pk, sk, ct))
    return CT.run_mceliece(v.path, v.P.name, v.sym["enc"], v.sym["dec"], material)


def pqverify_audit_mceliece(so_path, param_set="mceliece348864", symbols=None,
                            verbose=True, prefix=None, constant_time_check=False):
    """Audit a third-party Classic McEliece library; see the module docstring.

    Returns None when it cannot be audited (an ambiguous symbol, no entry
    point). Otherwise {'detail': {stage: (p, t)}, 'not_applicable', 'via',
    'failures', ...}."""
    from .core import DEGRADED
    v = VendorMcEliece(so_path, param_set, symbols=symbols, prefix=prefix)
    if v.ambiguous:
        from .symbols import ambiguity_message
        print(ambiguity_message(v.path, v.ambiguous, _ROLES, "--mceliece-symbol ROLE=SYMBOL"))
        DEGRADED["skipped_checks"].append(f"Classic McEliece audit ({param_set})")
        return None
    if not v.has("keypair") or not v.has("dec"):
        print(f"  Cannot audit {v.path}: no Classic McEliece keypair/decapsulation entry "
              f"point for {param_set}.")
        hint = [e for e in exported_symbols(v.path) if "mceliece" in e.lower()][:8]
        if hint:
            print(f"    exported: {hint}")
        DEGRADED["skipped_checks"].append(f"Classic McEliece audit ({param_set})")
        return None
    if verbose:
        print("=" * 68)
        print(f"  THIRD-PARTY CLASSIC McELIECE AUDIT — {param_set} — NOT A FIPS STANDARD")
        print(f"  library : {v.name}   (calling convention: {v.abi})")
        print(f"  reference: pq_verify.mceliece ({M.sources()})")
        print("=" * 68)
    T = run(v)
    ct_res = None
    if constant_time_check:
        from . import ct_audit as CT
        if not (v.has("enc") and v.has("dec")):
            ct_res = {"unavailable": "no encapsulation or decapsulation entry point"}
            T.detail["ct:unavailable"] = (0, 1)
        else:
            try:
                ct_res = constant_time(v)
                for op, val in ct_res["stages"].items():
                    T.detail["ct:" + op] = val
            except CT.Unavailable as exc:
                # Asked for and not run is not a pass: a stage that fails, saying why.
                ct_res = {"unavailable": str(exc)}
                T.detail["ct:unavailable"] = (0, 1)
    p_all = sum(p for p, _ in T.detail.values())
    t_all = sum(t for _, t in T.detail.values())
    na_all = sum(c for c, _ in T.na.values())
    verified = p_all == t_all and t_all > 0
    via = {"keyGen": v.sym.get("keypair"), "encaps": v.sym.get("enc"),
           "decaps": v.sym.get("dec"), "padding": v.sym.get("dec"),
           "ct:encaps": v.sym.get("enc"), "ct:decaps": v.sym.get("dec")}
    if verbose:
        for s in STAGES:
            if s in T.detail:
                p, t = T.detail[s]
                print(f"  {'PASS' if p == t else 'FAIL'}  {s:8s} {p}/{t}   via {via[s]}")
            if s in T.na:
                c, why = T.na[s]
                print(f"  n/a   {s:8s} {c}: {why}")
        if ct_res and "unavailable" in ct_res:
            print(f"  FAIL  constant time: could not run ({ct_res['unavailable']})")
        elif ct_res:
            for op, (p, t) in ct_res["stages"].items():
                print(f"  {'PASS' if p == t else 'FAIL'}  ct:{op:7s} {p}/{t}   no secret-dependent "
                      f"branch or memory address (Valgrind memcheck)")
                for lk in ct_res["leaks"][op][:3]:
                    print(f"        \u2717 {lk['kind']} in {lk['function']} ({lk['count']} report(s))")
                for lk in ct_res["sampling"][op][:3]:
                    print(f"        listed, not judged: {lk['kind']} in {lk['function']}, the "
                          f"function that draws the randomness ({lk['count']})")
            print(f"  n/a   ct:keyGen   {ct_res['not_applicable']['keyGen'][:60]}...")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']} {f['case']}: {f['detail']}")
        print("=" * 68)
        status = "VERIFIED" if verified else ("FINDINGS PRESENT" if t_all else "CANNOT VERIFY")
        print(f"  RESULT: {p_all}/{t_all} — {status}"
              + (f"   ({na_all} not applicable)" if na_all else ""))
        print(f"  {M.TRACK_NOTE}")
        print("  Encapsulation's error-vector sampling is checked for validity and")
        print("  repetition, not distribution. " + (
            "Constant time: branches and addresses only, not timing or power."
            if constant_time_check else "Not a side-channel review."))
        print("=" * 68)
    return {"verified": verified, "passed": p_all, "total": t_all,
            "detail": T.detail, "not_applicable": {k: list(x) for k, x in T.na.items()},
            "not_applicable_total": na_all, "via": via, "abi": v.abi,
            "failures": T.failures, "library": v.path, "vectors": M.sources(),
            "track": "classic-mceliece", "constant_time": ct_res,
            "standard": "Classic McEliece round 4 (not a FIPS standard)",
            "symbols": {k: s for k, s in v.sym.items() if s}}
