"""Audit a THIRD-PARTY FN-DSA (Falcon) library — DRAFT TRACK, ahead of FIPS 206.

The vendor's own compiled code is driven through its public entry points and
checked against pq_verify.fndsa (the reference verifier, itself checked by
`pq-verify --fndsa`):

    verify     the pinned PQClean vectors (detached)     -> must accept
    open       the pinned signed messages                 -> must accept, return M
    reject     every input a verifier must refuse         -> must reject
               (altered message or nonce, a changed s2 coefficient, the wrong
               header on the signature or the key, -0, nonzero padding bits,
               trailing bytes, a public-key coefficient >= q)
    keyGen     vendor key pairs: the public key is canonical (header, every
               coefficient below q) and matches the secret key (h * f = g mod q);
               the secret key solves the NTRU equation (f G - g F = q, with G
               recomputed) and meets both Gram-Schmidt bounds, in exact
               integer and rational arithmetic
    sign       vendor signatures: pq-verify's verifier accepts each one, the
               vendor's own verifier accepts it, the encoding is canonical
               and in range, and no nonce repeats

Falcon's signatures are randomised (a fresh 40-byte nonce, a Gaussian
sampler), and there are no final FIPS 206 vectors, so signing is checked for
what every valid signature must satisfy, not byte-for-byte. A signer that
reuses a nonce, or emits a vector outside the norm bound or a non-canonical
encoding, fails; a subtly biased sampler would not, and the report says so.

Calling conventions, by symbol name:
  nist   the NIST API, as PQClean and Falcon's reference export it:
         crypto_sign_{keypair,signature,verify,open} (PQClean prefixes them)
  oqs    liboqs: OQS_SIG_falcon_{512,1024}_{keypair,sign,verify}, and the
         falcon_padded_* variants, whose signatures are fixed-length
A library exporting several sets is narrowed by "512" / "1024"; an
ambiguous role is never guessed (--fndsa-symbol ROLE=SYMBOL).
"""
import ctypes as _ct
import re as _re
from fractions import Fraction as _Fraction

from . import fndsa as F

SETS = {"FN-DSA-512": 9, "FN-DSA-1024": 10}
# secret key: header 0x50 + logn, f and g at FG_BITS[logn] bits, F at 8 bits
SK_BYTES = {9: 1281, 10: 2305}
FG_BITS = {9: 6, 10: 5}
STAGES = ("verify", "open", "reject", "keyGen", "sign")

_ROLES = {
    "keypair": r"(?:crypto_sign_keypair|_keypair)$",
    "sign":    r"(?:crypto_sign_signature|^oqs_sig_falcon_(?:padded_)?\d+_sign)$",
    "verify":  r"(?:crypto_sign_verify|^oqs_sig_falcon_(?:padded_)?\d+_verify)$",
    "open":    r"crypto_sign_open$",
}
SIGN_MESSAGES = (b"", b"\x00", bytes(range(33)), b"FN-DSA" * 170)
SIGS_PER_MESSAGE = 2
KEYS = 3


class NotApplicable(NotImplementedError):
    """The library has no entry point for this case."""


def exported_symbols(so_path):
    from .symbols import exported_functions
    return exported_functions(so_path)


def _is_falcon(name):
    n = name.lower()
    return "falcon" in n or "fndsa" in n or "fn_dsa" in n or n.startswith("crypto_sign")


def resolve_symbols(exported, param_set, explicit=None):
    """{role: symbol or None}, {role: [candidates]} for ambiguous roles."""
    explicit = explicit or {}
    n = str(1 << SETS[param_set])
    other = "1024" if n == "512" else "512"
    found, ambiguous = {}, {}
    for role, pat in _ROLES.items():
        if explicit.get(role):
            found[role] = explicit[role]
            continue
        cands = [e for e in exported if _is_falcon(e) and _re.search(pat, e.lower())]
        same = [e for e in cands if n in e and other not in e]
        if same or any(other in e for e in cands):
            cands = same
        found[role] = cands[0] if len(cands) == 1 else None
        if len(cands) > 1:
            ambiguous[role] = sorted(cands)
    return found, ambiguous


def _buf(b):
    return (_ct.c_uint8 * max(1, len(b))).from_buffer_copy(bytes(b) or b"\0")


class VendorFNDSA:
    def __init__(self, so_path, param_set, symbols=None):
        import os
        self.path = os.path.abspath(so_path)
        self.name = os.path.basename(so_path)
        self.set = param_set
        self.logn = SETS[param_set]
        _, self.n, _, self.pk_len, self.padded_len, self.max_sig = F.PARAMS[self.logn]
        self.lib = _ct.CDLL(self.path)
        self.sym, self.ambiguous = resolve_symbols(exported_symbols(self.path),
                                                   param_set, symbols)
        names = [s for s in self.sym.values() if s]
        self.abi = "oqs" if any(s.lower().startswith("oqs_") for s in names) else "nist"
        self.padded = any("padded" in s.lower() for s in names)
        self.sk_len = SK_BYTES[self.logn]
        P8, SZ, PSZ = _ct.POINTER(_ct.c_uint8), _ct.c_size_t, _ct.POINTER(_ct.c_size_t)
        self.fn = {}
        for role, s in self.sym.items():
            if not s:
                continue
            f = getattr(self.lib, s)
            f.restype = _ct.c_int
            f.argtypes = {
                "keypair": [P8, P8],
                "sign": [P8, PSZ, P8, SZ, P8],
                "verify": ([P8, SZ, P8, SZ, P8] if self.abi == "nist"
                           else [P8, SZ, P8, SZ, P8]),
                "open": [P8, PSZ, P8, SZ, P8],
            }[role]
            self.fn[role] = f

    def has(self, role):
        return role in self.fn

    def frame(self, sig):
        """A detached signature in this library's format: zero-padded to the
        fixed length for a padded variant."""
        if self.padded and len(sig) < self.padded_len:
            return sig + bytes(self.padded_len - len(sig))
        return sig

    def verify(self, pk, msg, sig):
        if not self.has("verify"):
            raise NotApplicable("no verify entry point")
        if self.abi == "nist":
            rc = self.fn["verify"](_buf(sig), len(sig), _buf(msg), len(msg), _buf(pk))
        else:
            rc = self.fn["verify"](_buf(msg), len(msg), _buf(sig), len(sig), _buf(pk))
        return rc == 0

    def open(self, pk, sm):
        if not self.has("open"):
            raise NotApplicable("no crypto_sign_open entry point")
        out = (_ct.c_uint8 * max(1, len(sm)))()
        mlen = _ct.c_size_t(0)
        rc = self.fn["open"](out, _ct.byref(mlen), _buf(sm), len(sm), _buf(pk))
        return bytes(out[:mlen.value]) if rc == 0 else None

    def keypair(self):
        if not self.has("keypair"):
            raise NotApplicable("no keypair entry point")
        pk = (_ct.c_uint8 * self.pk_len)()
        sk = (_ct.c_uint8 * (self.sk_len + 64))()          # slack: never trust a size
        if self.fn["keypair"](pk, sk) != 0:
            raise RuntimeError("keypair returned an error")
        return bytes(pk), bytes(sk[:self.sk_len])

    def sign(self, sk, msg):
        if not self.has("sign"):
            raise NotApplicable("no signing entry point")
        cap = max(self.max_sig, self.padded_len) + 64
        sig = (_ct.c_uint8 * cap)()
        slen = _ct.c_size_t(cap)
        if self.fn["sign"](sig, _ct.byref(slen), _buf(msg), len(msg), _buf(sk)) != 0:
            raise RuntimeError("signing returned an error")
        return bytes(sig[:slen.value])


# ---------------------------------------------------------------------------
# Secret-key decoding (Falcon reference format) for the h * f = g check
# ---------------------------------------------------------------------------

def _trim_decode(bits_str, pos, n, bits):
    out, lim = [], 1 << (bits - 1)
    for _ in range(n):
        w = int(bits_str[pos:pos + bits], 2)
        pos += bits
        if w >= lim:
            w -= 1 << bits
        if w == -lim:
            raise F.Reject("secret key coefficient at the forbidden minimum")
        out.append(w)
    return out, pos


def decode_secret_key(sk, logn):
    """(f, g, F) from the reference encoding, or Reject. G is not stored:
    the key's owner recomputes it (see ntru_checks)."""
    n = 1 << logn
    if len(sk) != SK_BYTES[logn] or sk[0] != 0x50 + logn:
        raise F.Reject("not the reference secret-key encoding")
    bits = "".join(f"{b:08b}" for b in sk[1:])
    f, pos = _trim_decode(bits, 0, n, FG_BITS[logn])
    g, pos = _trim_decode(bits, pos, n, FG_BITS[logn])
    F_, pos = _trim_decode(bits, pos, n, 8)
    return f, g, F_


# ---------------------------------------------------------------------------
# Exact key checks: the NTRU equation and the Gram-Schmidt bound
# ---------------------------------------------------------------------------
# Every Falcon key generator must output (f, g, F, G) with
#     f G - g F = q                in Z[x]/(x^n + 1)           (NTRU equation)
#     ||(g, -f)||^2              < 1.17^2 q                     (Gram-Schmidt
#     ||(q f*/D, q g*/D)||^2     < 1.17^2 q,  D = f f* + g g*    bound)
# (round 3, section 3.8; the reference's 16822.4121). Its signatures are only
# as short, and its sampler only as sound, as these make them. Both are
# checked here in exact arithmetic -- integers and rationals, never floating
# point: the second norm is q^2 times the constant coefficient of 1/D, since
# D is self-adjoint and ||u||^2 is the constant coefficient of u u*.

BOUND_SQ = _Fraction(168224121, 10000)        # 1.17^2 * 12289, exactly
KEY_CHECKS = ("f G - g F = q", "||(g, -f)||^2 < 1.17^2 q",
              "||(q f*/D, q g*/D)||^2 < 1.17^2 q")


def _zmul(a, b):
    """a * b in Z[x]/(x^n + 1), exactly (Kronecker substitution)."""
    n = len(a)
    k = (max(map(abs, a), default=0).bit_length() + max(map(abs, b), default=0).bit_length()
         + n.bit_length() + 2)
    pa = sum(c << (k * i) for i, c in enumerate(a))
    pb = sum(c << (k * i) for i, c in enumerate(b))
    prod, full, half, mask = pa * pb, [], 1 << (k - 1), (1 << k) - 1
    for _ in range(2 * n - 1):
        d = prod & mask
        if d >= half:
            d -= 1 << k
        full.append(d)
        prod = (prod - d) >> k
    return [full[i] - (full[i + n] if i + n < len(full) else 0) for i in range(n)]


def _zmul_school(a, b):
    """a * b in Z[x]/(x^n + 1) when b's coefficients are huge and a's small:
    cheaper than packing both."""
    n = len(a)
    out = [0] * n
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if i + j < n:
                    out[i + j] += ai * bj
                else:
                    out[i + j - n] -= ai * bj
    return out


def _inverse_scaled(d):
    """(p, den), integers, with d * p = den in Z[x]/(x^n + 1): the field-norm
    tower (as in NTRUSolve), d(x) d(-x) = N(x^2)."""
    if len(d) == 1:
        return [1], d[0]
    de, do = d[0::2], d[1::2]
    sq_o = _zmul(do, do)
    norm = [x - (sq_o[i - 1] if i else -sq_o[-1]) for i, x in enumerate(_zmul(de, de))]
    q, den = _inverse_scaled(norm)
    # 1/d = d(-x) / N(x^2) = (de(x^2) - x do(x^2)) q(x^2) / den
    pe, po = _zmul_school(de, q), _zmul_school(do, q)
    p = [0] * len(d)
    p[0::2], p[1::2] = pe, [-x for x in po]
    return p, den


def recover_G(f, g, F_, logn):
    """G = g F / f mod q, centred (as the reference recomputes it), or None
    if f is not invertible mod q."""
    fh = F.ntt([x % F.Q for x in f], logn)
    if any(x == 0 for x in fh):
        return None
    gh, Fh = F.ntt([x % F.Q for x in g], logn), F.ntt([x % F.Q for x in F_], logn)
    G = F.intt([a * b * pow(c, -1, F.Q) % F.Q for a, b, c in zip(gh, Fh, fh)], logn)
    return [x - F.Q if x > F.Q // 2 else x for x in G]


def ntru_checks(f, g, F_, logn):
    """[(name, ok, detail)]: the NTRU equation and both Gram-Schmidt norms,
    exactly."""
    out = []
    G = recover_G(f, g, F_, logn)
    if G is None:
        out.append(("f G - g F = q", False, "f is not invertible mod q"))
    else:
        fG, gF = _zmul(f, G), _zmul(g, F_)
        lhs = [a - b for a, b in zip(fG, gF)]
        ok = lhs[0] == F.Q and not any(lhs[1:]) and max(map(abs, G)) <= 127
        why = ("" if ok else "G has a coefficient beyond 127" if lhs[0] == F.Q and not any(lhs[1:])
               else f"f G - g F has constant {lhs[0]} and "
                    f"{sum(1 for x in lhs[1:] if x)} other nonzero coefficients")
        out.append(("f G - g F = q", ok, why))
    n1 = sum(x * x for x in f) + sum(x * x for x in g)
    out.append(("||(g, -f)||^2 < 1.17^2 q", n1 < BOUND_SQ, f"{n1}"))
    n = 1 << logn
    adj = lambda a: [a[0]] + [-a[n - i] for i in range(1, n)]
    d = [a + b for a, b in zip(_zmul(f, adj(f)), _zmul(g, adj(g)))]
    p, den = _inverse_scaled(d)
    n2 = _Fraction(F.Q * F.Q * p[0], den)
    out.append(("||(q f*/D, q g*/D)||^2 < 1.17^2 q", n2 < BOUND_SQ,
                f"{float(n2):.4f}"))
    return out


# ---------------------------------------------------------------------------
# The audit
# ---------------------------------------------------------------------------

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


def run(v):
    T = _Tally()
    vectors = [x for x in F.load_vectors() if x[0] == v.set]

    # ---- verify / reject: the pinned detached signatures and their mutants
    for _name, _label, kind, pk, msg, blob in vectors:
        if kind != "sig":
            continue
        if not v.has("verify"):
            T.not_applicable("verify", 1, "no verify entry point")
            continue
        T.rec("verify", v.verify(pk, msg, v.frame(blob)),
              f"pinned {len(msg)}-byte message", "a valid signature was rejected")
        for what, _enc, mpk, mmsg, msig in F._mutants(pk, msg, blob):
            if len(mpk) != len(pk):
                # Neither API takes a public-key length: the library would
                # read past the buffer, which tests nothing but the caller.
                T.not_applicable("reject", 1, "a wrong-length public key: the API "
                                 "takes no key length")
                continue
            if v.padded and what == "trailing garbage byte":
                msig = v.frame(blob) + b"\x01"
            elif v.padded and not what.startswith("padded"):
                msig = v.frame(msig) if len(msig) <= v.padded_len else msig
            T.rec("reject", not v.verify(mpk, mmsg, msig), what,
                  f"accepted ({len(mmsg)}-byte message)")

        # A header naming the other parameter set, on an otherwise valid key:
        # only the header check can reject it (the coefficients still decode).
        bad_pk = bytes([(19 - v.logn)]) + pk[1:]
        T.rec("reject", not v.verify(bad_pk, msg, v.frame(blob)),
              "public key header names the other parameter set",
              f"accepted ({len(msg)}-byte message)")

    # ---- open: the pinned signed messages (NIST API only)
    for _name, _label, kind, pk, msg, blob in vectors:
        if kind != "sm":
            continue
        if not v.has("open") or v.padded:
            T.not_applicable("open", 1, "no crypto_sign_open entry point"
                             if not v.has("open") else "padded variant: no signed-message API")
            continue
        got = v.open(pk, blob)
        T.rec("open", got == msg, f"pinned {len(msg)}-byte signed message",
              "rejected" if got is None else "returned a different message")

    # ---- keyGen and sign: what every key and every signature must satisfy
    if not v.has("keypair"):
        T.not_applicable("keyGen", KEYS, "no keypair entry point")
        T.not_applicable("sign", KEYS * len(SIGN_MESSAGES) * SIGS_PER_MESSAGE,
                         "no keypair entry point to make a key with")
        return T
    nonces = set()
    for k in range(KEYS):
        pk, sk = v.keypair()
        try:
            logn, h = F.decode_public_key(pk)
            ok = logn == v.logn
            why = "" if ok else f"header names logn {logn}"
        except F.Reject as exc:
            ok, why, h = False, str(exc), None
        T.rec("keyGen", ok, f"key {k}: public key canonical", why)
        try:
            f, g, F_ = decode_secret_key(sk, v.logn)
            if h is not None:
                T.rec("keyGen", F.poly_mul([x % F.Q for x in f], h, v.logn)
                      == [x % F.Q for x in g], f"key {k}: h * f = g mod q",
                      "the public key does not belong to the secret key")
            for name, ok, why in ntru_checks(f, g, F_, v.logn):
                T.rec("keyGen", ok, f"key {k}: {name}", why if not ok else "")
        except F.Reject:
            T.not_applicable("keyGen", 1 + len(KEY_CHECKS),
                             "secret key not in the reference encoding")
        if not v.has("sign"):
            T.not_applicable("sign", len(SIGN_MESSAGES) * SIGS_PER_MESSAGE,
                             "no signing entry point")
            continue
        for msg in SIGN_MESSAGES:
            for _ in range(SIGS_PER_MESSAGE):
                case = f"key {k}, {len(msg)}-byte message"
                try:
                    sig = v.sign(sk, msg)
                except RuntimeError as exc:     # refused its own key: a failure
                    T.rec("sign", False, case, str(exc))
                    continue
                problems = []
                if v.padded and len(sig) != v.padded_len:
                    problems.append(f"length {len(sig)}, padded variant must be "
                                    f"{v.padded_len}")
                if not v.padded and len(sig) > v.max_sig:
                    problems.append(f"length {len(sig)} over {v.max_sig}")
                ok, why = F.verify(pk, msg, sig)
                if not ok:
                    problems.append(f"pq-verify's verifier rejects it: {why}")
                if not v.verify(pk, msg, sig):
                    problems.append("the library's own verifier rejects it")
                nonce = sig[1:1 + F.NONCE_LEN]
                if nonce in nonces:
                    problems.append("nonce repeated")
                nonces.add(nonce)
                T.rec("sign", not problems, case, "; ".join(problems))
    return T


def pqverify_audit_fndsa(so_path, param_set="FN-DSA-512", symbols=None, verbose=True):
    """Audit a third-party FN-DSA library; see the module docstring.

    Returns None when it cannot be audited at all (an ambiguous symbol, or no
    entry point). Otherwise a dict with 'detail' {stage: (p, t)},
    'not_applicable' {stage: (count, reason)}, 'via', 'failures'.
    """
    from .core import DEGRADED
    v = VendorFNDSA(so_path, param_set, symbols=symbols)
    if v.ambiguous:
        print(f"  Cannot audit {v.path}: more than one candidate for")
        for role, cands in v.ambiguous.items():
            print(f"    {role}: {', '.join(cands)}")
        print("    Name the symbol explicitly (--fndsa-symbol ROLE=SYMBOL) rather "
              "than let pq-verify guess.")
        DEGRADED["skipped_checks"].append(f"FN-DSA audit ({param_set})")
        return None
    if not v.has("verify"):
        print(f"  Cannot audit {v.path}: no FN-DSA verify entry point for {param_set}.")
        hint = [e for e in exported_symbols(v.path)
                if any(k in e.lower() for k in ("sign", "keypair", "verify"))][:8]
        if hint:
            print(f"    exported: {hint}")
        DEGRADED["skipped_checks"].append(f"FN-DSA audit ({param_set})")
        return None
    if verbose:
        print("=" * 68)
        print(f"  THIRD-PARTY FN-DSA AUDIT — {param_set} — FIPS 206 DRAFT TRACK")
        print(f"  library : {v.name}   (calling convention: {v.abi}"
              f"{', padded signatures' if v.padded else ''})")
        print(f"  vectors : {F.sources()}")
        print("=" * 68)
    T = run(v)
    p_all = sum(p for p, _ in T.detail.values())
    t_all = sum(t for _, t in T.detail.values())
    na_all = sum(c for c, _ in T.na.values())
    verified = p_all == t_all and t_all > 0
    via = {"verify": v.sym.get("verify"), "reject": v.sym.get("verify"),
           "open": v.sym.get("open"), "keyGen": v.sym.get("keypair"),
           "sign": v.sym.get("sign")}
    if verbose:
        for s in STAGES:
            if s in T.detail:
                p, t = T.detail[s]
                print(f"  {'PASS' if p == t else 'FAIL'}  {s:8s} {p}/{t}   via {via[s]}")
            if s in T.na:
                c, why = T.na[s]
                print(f"  n/a   {s:8s} {c}: {why}")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']} {f['case']}: {f['detail']}")
        print("=" * 68)
        status = "VERIFIED (draft)" if verified else (
            "FINDINGS PRESENT" if t_all else "CANNOT VERIFY")
        print(f"  RESULT: {p_all}/{t_all} — {status}"
              + (f"   ({na_all} not applicable to this API)" if na_all else ""))
        print(f"  {F.DRAFT_NOTE}")
        print("  Signing is checked for validity, encoding and nonce reuse, not")
        print("  byte-for-byte; a biased sampler is out of scope. Not a side-channel review.")
        print("=" * 68)
    return {"verified": verified, "passed": p_all, "total": t_all,
            "detail": T.detail, "not_applicable": {k: list(x) for k, x in T.na.items()},
            "not_applicable_total": na_all, "via": via, "abi": v.abi,
            "padded": v.padded, "failures": T.failures, "library": v.path,
            "vectors": F.sources(), "track": "draft", "standard": "FIPS 206 (draft)",
            "symbols": {k: s for k, s in v.sym.items() if s}}
