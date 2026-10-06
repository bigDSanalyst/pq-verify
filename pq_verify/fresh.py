"""
pq_verify.fresh — fresh, unpublished ACVP question sets.

`--emit-prompt` poses NIST's own published questions. Their answers are public
(NIST publishes expectedResults.json, and this package ships them), so a
response that matches them shows only that the responder can copy a file. A
black-box check -- an HSM, a sealed binary, a remote service -- needs
questions whose answers exist nowhere until the auditor computes them.

This module makes them:

    pq-verify --emit-prompt ML-DSA-65 --fresh --fresh-key audit.key
        draws a 256-bit seed from the OS, derives every input from it, and
        writes the questions in NIST's own ACVP layout (same suites, groups
        and field names), so a harness built for ACVP answers them unchanged.
        The seed goes to audit.key, which the auditor keeps. The prompt holds
        no answers and no seed.

    pq-verify --verify-response response.json --fresh-key audit.key
        re-derives the questions from the seed, computes every expected answer
        with pq-verify's reference implementations at that moment, and scores
        the response exactly like a pinned one.

What a pass shows: the responder computed the standard correctly on inputs
nobody had seen before. What it still does not show is WHICH code did so --
the responder could run a reference implementation instead of the product.
The report keeps that binding as data (artifact: none), as for every
prompt/response run.

Every input is derived deterministically: SHAKE256 over a domain tag, the
seed and a label naming the field (suite, group, test, field). The same seed
and tool version always give the same questions; `promptId` (sha256 of the
canonical question set) is recorded in the key, so a regenerated set that
differs -- a different pq-verify, a changed reference -- is refused rather
than scored.
"""

import hashlib
import json
import os
import secrets

from .core import (
    VERSION,
    _MLDSA_PH,
    _mldsa_mprime,
    _mldsa_verify_with_mu,
    _slhdsa_message,
    _slhdsa_sign_internal,
    _SLHDSA_PREHASH,
    check_decapsulation_key,
    check_encapsulation_key,
)

KEY_SCHEMA = "pq-verify/fresh-key"
DERIVATION = "pq-verify fresh v1"          # bump if the derivation ever changes
_DOMAIN = DERIVATION.encode() + b"\x00"

KEM_SETS = ("ML-KEM-512", "ML-KEM-768", "ML-KEM-1024")
DSA_SETS = ("ML-DSA-44", "ML-DSA-65", "ML-DSA-87")
SLH_SETS = tuple(f"SLH-DSA-{h}-{b}{v}" for h in ("SHA2", "SHAKE")
                 for b in (128, 192, 256) for v in ("s", "f"))


def _lms_sets():
    """Every SP 800-208 LMS/LM-OTS pairing: one hash family, n = m."""
    from . import hbs as H
    return tuple(f"{tn}/{on}" for t, (tn, _, m, _h) in H.LMS.items()
                 for o, (on, _, n, _w) in H.LMOTS.items()
                 if n == m and tn.split("_")[1] == on.split("_")[1])


LMS_SETS = _lms_sets()
PARAMETER_SETS = KEM_SETS + DSA_SETS + SLH_SETS + LMS_SETS

# Building an LMS tree is the cost of a keyGen or sigVer question here (pure
# Python). Above this many hash calls a set gets sigGen questions only: the
# responder signs with its own key, and pq-verify only verifies.
LMS_TREE_BUDGET = 3_000_000

# Tests per group. SLH-DSA signing is slow in pure Python (a few seconds for
# the -f sets, much longer for -s), so it gets fewer; --fresh-count overrides.
DEFAULT_COUNT = {"ML-KEM": 8, "ML-DSA": 4, "SLH-DSA": 1, "LMS": 2}


class FreshError(ValueError):
    """A fresh prompt cannot be built or a key cannot be used."""


# ----------------------------------------------------------------------
# derivation
# ----------------------------------------------------------------------

class _Derive:
    """Every byte of every question, as a function of (seed, label)."""

    def __init__(self, seed):
        if not isinstance(seed, bytes) or len(seed) != 32:
            raise FreshError("a fresh-prompt seed is 32 bytes")
        self.seed = seed

    def bytes(self, label, n):
        return hashlib.shake_256(_DOMAIN + self.seed + label.encode()).digest(n)

    def int(self, label, lo, hi):
        """Uniform in [lo, hi] (bias below 2^-64)."""
        span = hi - lo + 1
        return lo + int.from_bytes(self.bytes(label, 16), "big") % span

    def choice(self, label, seq):
        return seq[self.int(label, 0, len(seq) - 1)]


def _flip(blob, pos, bit=0):
    b = bytearray(blob)
    b[pos] ^= 1 << bit
    return bytes(b)


def _hex(b):
    return b.hex().upper()


def _require(module, dist):
    try:
        return __import__(module, fromlist=["_"])
    except ImportError as exc:
        raise FreshError(f"{dist} is required to build or check fresh questions "
                         f"for this parameter set: pip install \"pq-verify[full]\"") from exc


# ----------------------------------------------------------------------
# ML-KEM (FIPS 203)
# ----------------------------------------------------------------------

def _mlkem(ps, D, n):
    mod = _require("kyber_py.ml_kem", "kyber-py")
    K = getattr(mod, ps.replace("-", "_"))
    k = {"ML-KEM-512": 2, "ML-KEM-768": 3, "ML-KEM-1024": 4}[ps]
    suites = []

    # keyGen: (d, z) -> (ek, dk)
    tests, exp = [], {}
    for i in range(n):
        tc = i + 1
        d, z = D.bytes(f"kem/keyGen/{tc}/d", 32), D.bytes(f"kem/keyGen/{tc}/z", 32)
        ek, dk = K._keygen_internal(d, z)
        tests.append({"tcId": tc, "d": _hex(d), "z": _hex(z)})
        exp[tc] = {"ek": _hex(ek), "dk": _hex(dk)}
    suites.append(("ML-KEM-keyGen-FIPS203", "ML-KEM", "keyGen", "FIPS203",
                   [({"testType": "AFT"}, ["dk", "ek"], tests)], exp))

    groups, exp, tc = [], {}, 0

    def keypair(label):
        return K._keygen_internal(D.bytes(label + "/d", 32), D.bytes(label + "/z", 32))

    # encapsulation: (ek, m) -> (c, k)
    tests = []
    for i in range(n):
        tc += 1
        ek, _dk = keypair(f"kem/encap/{tc}")
        m = D.bytes(f"kem/encap/{tc}/m", 32)
        kk, c = K._encaps_internal(ek, m)
        tests.append({"tcId": tc, "ek": _hex(ek), "m": _hex(m)})
        exp[tc] = {"c": _hex(c), "k": _hex(kk)}
    groups.append(({"testType": "AFT", "function": "encapsulation"}, ["c", "k"], tests))

    # decapsulation: (dk, c) -> k. Half the ciphertexts are altered, so the
    # answer is FIPS 203's implicit-rejection key J(z || c), not an error.
    tests = []
    for i in range(n):
        tc += 1
        ek, dk = keypair(f"kem/decap/{tc}")
        _k, c = K._encaps_internal(ek, D.bytes(f"kem/decap/{tc}/m", 32))
        if i % 2:
            c = _flip(c, D.int(f"kem/decap/{tc}/pos", 0, len(c) - 1),
                      D.int(f"kem/decap/{tc}/bit", 0, 7))
        tests.append({"tcId": tc, "dk": _hex(dk), "c": _hex(c)})
        exp[tc] = {"k": _hex(K._decaps_internal(dk, c))}
    groups.append(({"testType": "VAL", "function": "decapsulation"}, ["k"], tests))

    # encapsulationKeyCheck (FIPS 203 §7.2): odd tests carry a coefficient >= q
    tests = []
    for i in range(n):
        tc += 1
        ek, _dk = keypair(f"kem/ekc/{tc}")
        want = True
        if i % 2:
            j = D.int(f"kem/ekc/{tc}/coef", 0, 256 * k - 1)   # which 12-bit coefficient
            v = D.int(f"kem/ekc/{tc}/val", 3329, 4095)
            b = bytearray(ek)
            off = (j // 2) * 3
            if j % 2 == 0:
                b[off] = v & 0xFF
                b[off + 1] = (b[off + 1] & 0xF0) | (v >> 8)
            else:
                b[off + 1] = (b[off + 1] & 0x0F) | ((v & 0x0F) << 4)
                b[off + 2] = v >> 4
            ek, want = bytes(b), False
        got = check_encapsulation_key(ek, ps)
        if got != want:
            raise FreshError(f"internal: encapsulation key check disagrees with "
                             f"the constructed case ({ps} tcId {tc})")
        tests.append({"tcId": tc, "ek": _hex(ek)})
        exp[tc] = {"testPassed": got}
    groups.append(({"testType": "VAL", "function": "encapsulationKeyCheck"},
                   ["testPassed"], tests))

    # decapsulationKeyCheck (FIPS 203 §7.3): odd tests alter H(ek) inside dk
    tests = []
    for i in range(n):
        tc += 1
        _ek, dk = keypair(f"kem/dkc/{tc}")
        want = True
        if i % 2:
            h_off = 768 * k + 32
            dk = _flip(dk, h_off + D.int(f"kem/dkc/{tc}/pos", 0, 31),
                       D.int(f"kem/dkc/{tc}/bit", 0, 7))
            want = False
        got = check_decapsulation_key(dk, ps)
        if got != want:
            raise FreshError(f"internal: decapsulation key check disagrees with "
                             f"the constructed case ({ps} tcId {tc})")
        tests.append({"tcId": tc, "dk": _hex(dk)})
        exp[tc] = {"testPassed": got}
    groups.append(({"testType": "VAL", "function": "decapsulationKeyCheck"},
                   ["testPassed"], tests))

    suites.append(("ML-KEM-encapDecap-FIPS203", "ML-KEM", "encapDecap", "FIPS203",
                   groups, exp))
    return suites


# ----------------------------------------------------------------------
# ML-DSA (FIPS 204)
# ----------------------------------------------------------------------

_DSA_IFACES = (
    {"signatureInterface": "external", "preHash": "pure"},
    {"signatureInterface": "external", "preHash": "preHash"},
    {"signatureInterface": "internal", "externalMu": False},
    {"signatureInterface": "internal", "externalMu": True},
)


def _ctx_len(D, label, i):
    # The boundaries are where encoders break: empty and the 255-byte maximum.
    return 0 if i == 0 else 255 if i == 1 else D.int(label, 1, 254)


def _dsa_inputs(D, label, g, i, O):
    """The non-key fields of one sigGen/sigVer test, per its interface."""
    t = {}
    if g["signatureInterface"] == "internal" and g.get("externalMu"):
        t["mu"] = _hex(D.bytes(label + "/mu", 64))
        return t
    t["message"] = _hex(D.bytes(label + "/msg", D.int(label + "/mlen", 1, 1024)))
    if g["signatureInterface"] == "external":
        t["context"] = _hex(D.bytes(label + "/ctx", _ctx_len(D, label + "/clen", i)))
        if g.get("preHash") == "preHash":
            t["hashAlg"] = D.choice(label + "/hash", sorted(_MLDSA_PH))
    return t


def _dsa_sign(O, sk, g, t, rnd):
    if g["signatureInterface"] == "internal" and g.get("externalMu"):
        return O._sign_internal(sk, bytes.fromhex(t["mu"]), rnd, external_mu=True)
    if g["signatureInterface"] == "internal":
        return O._sign_internal(sk, bytes.fromhex(t["message"]), rnd)
    return O._sign_internal(sk, _mldsa_mprime(t, g), rnd)


def _dsa_verify(O, pk, g, t, sig):
    if g["signatureInterface"] == "internal" and g.get("externalMu"):
        return bool(_mldsa_verify_with_mu(O, pk, bytes.fromhex(t["mu"]), sig))
    if g["signatureInterface"] == "internal":
        return bool(O._verify_internal(pk, bytes.fromhex(t["message"]), sig))
    return bool(O._verify_internal(pk, _mldsa_mprime(t, g), sig))


def _mldsa(ps, D, n):
    mod = _require("dilithium_py.ml_dsa", "dilithium-py")
    O = getattr(mod, ps.replace("-", "_"))
    suites = []

    tests, exp = [], {}
    for i in range(n):
        tc = i + 1
        seed = D.bytes(f"dsa/keyGen/{tc}/seed", 32)
        pk, sk = O._keygen_internal(seed)
        tests.append({"tcId": tc, "seed": _hex(seed)})
        exp[tc] = {"pk": _hex(pk), "sk": _hex(sk)}
    suites.append(("ML-DSA-keyGen-FIPS204", "ML-DSA", "keyGen", "FIPS204",
                   [({"testType": "AFT"}, ["pk", "sk"], tests)], exp))

    # sigGen: every interface, deterministic and hedged
    groups, exp, tc = [], {}, 0
    for det in (True, False):
        for iface in _DSA_IFACES:
            g = {"testType": "AFT", "deterministic": det, **iface}
            tests = []
            for i in range(n):
                tc += 1
                lab = f"dsa/sigGen/{tc}"
                _pk, sk = O._keygen_internal(D.bytes(lab + "/seed", 32))
                t = {"tcId": tc, "sk": _hex(sk), **_dsa_inputs(D, lab, g, i, O)}
                rnd = bytes(32)
                if not det:
                    rnd = D.bytes(lab + "/rnd", 32)
                    t["rnd"] = _hex(rnd)
                exp[tc] = {"signature": _hex(_dsa_sign(O, sk, g, t, rnd))}
                tests.append(t)
            groups.append((g, ["signature"], tests))
    suites.append(("ML-DSA-sigGen-FIPS204", "ML-DSA", "sigGen", "FIPS204", groups, exp))

    # sigVer: valid signatures and ones made invalid in a single place. The
    # alterations avoid the hint encoding, where the reference implementation
    # has a known leniency (edge.KNOWN_REFERENCE_DEFECTS), so every expected
    # verdict is one FIPS 204 leaves no room on.
    groups, exp, tc = [], {}, 0
    for iface in _DSA_IFACES:
        g = {"testType": "AFT", **iface}
        tests = []
        for i in range(n):
            tc += 1
            lab = f"dsa/sigVer/{tc}"
            pk, sk = O._keygen_internal(D.bytes(lab + "/seed", 32))
            t = {"tcId": tc, "pk": _hex(pk), **_dsa_inputs(D, lab, g, i, O)}
            sig = _dsa_sign(O, sk, g, t, D.bytes(lab + "/rnd", 32))
            want = True
            kind = i % 4
            if kind == 1:                                 # c~ altered
                sig = _flip(sig, D.int(lab + "/pos", 0, O.c_tilde_bytes - 1),
                            D.int(lab + "/bit", 0, 7))
                want = False
            elif kind == 2:                               # the signed input altered
                f = "mu" if "mu" in t else "message"
                v = bytes.fromhex(t[f])
                t[f] = _hex(_flip(v, D.int(lab + "/mpos", 0, len(v) - 1)))
                want = False
            elif kind == 3:                               # another key's pk
                other, _ = O._keygen_internal(D.bytes(lab + "/other", 32))
                t["pk"] = _hex(other)
                want = False
            t["signature"] = _hex(sig)
            got = _dsa_verify(O, bytes.fromhex(t["pk"]), g, t, sig)
            if got != want:
                raise FreshError(f"internal: reference verdict disagrees with the "
                                 f"constructed case ({ps} sigVer tcId {tc})")
            exp[tc] = {"testPassed": got}
            tests.append(t)
        groups.append((g, ["testPassed"], tests))
    suites.append(("ML-DSA-sigVer-FIPS204", "ML-DSA", "sigVer", "FIPS204", groups, exp))
    return suites


# ----------------------------------------------------------------------
# SLH-DSA (FIPS 205)
# ----------------------------------------------------------------------

_SLH_IFACES = (
    {"signatureInterface": "internal"},
    {"signatureInterface": "external", "preHash": "pure"},
    {"signatureInterface": "external", "preHash": "preHash"},
)


def _slhdsa(ps, D, n):
    _require("slhdsa", "slh-dsa")
    from slhdsa.lowlevel.slhdsa import Address, XMSS
    from slhdsa.lowlevel.slhdsa import verify as slh_verify
    import slhdsa.lowlevel.parameters as LP
    par = getattr(LP, ps.replace("SLH-DSA-", "").replace("-", "_").lower())
    N = par.n

    def keypair(lab):
        sk_seed, sk_prf, pk_seed = (D.bytes(f"{lab}/{f}", N)
                                    for f in ("skSeed", "skPrf", "pkSeed"))
        root = XMSS(par).node(sk_seed, 0, par.h_m, pk_seed, Address(par.d - 1, 0))
        return sk_seed, sk_prf, pk_seed, pk_seed + root, sk_seed + sk_prf + pk_seed + root

    def inputs(lab, g, i):
        t = {"message": _hex(D.bytes(lab + "/msg", D.int(lab + "/mlen", 1, 512)))}
        if g["signatureInterface"] == "external":
            t["context"] = _hex(D.bytes(lab + "/ctx", _ctx_len(D, lab + "/clen", i)))
            if g.get("preHash") == "preHash":
                t["hashAlg"] = D.choice(lab + "/hash", sorted(_SLHDSA_PREHASH))
        return t

    suites = []
    tests, exp = [], {}
    for i in range(n):
        tc = i + 1
        s, p, ps_, pk, sk = keypair(f"slh/keyGen/{tc}")
        tests.append({"tcId": tc, "skSeed": _hex(s), "skPrf": _hex(p), "pkSeed": _hex(ps_)})
        exp[tc] = {"pk": _hex(pk), "sk": _hex(sk)}
    suites.append(("SLH-DSA-keyGen-FIPS205", "SLH-DSA", "keyGen", "FIPS205",
                   [({"testType": "AFT"}, ["pk", "sk"], tests)], exp))

    groups, exp, tc = [], {}, 0
    for det in (True, False):
        for iface in _SLH_IFACES:
            g = {"testType": "AFT", "deterministic": det, **iface}
            tests = []
            for i in range(n):
                tc += 1
                lab = f"slh/sigGen/{tc}"
                *_s, sk = keypair(lab)
                t = {"tcId": tc, "sk": _hex(sk), **inputs(lab, g, i)}
                addrnd = None
                if not det:
                    addrnd = D.bytes(lab + "/addrnd", N)
                    t["additionalRandomness"] = _hex(addrnd)
                sig = _slhdsa_sign_internal(_slhdsa_message(g, t), sk, addrnd, par)
                exp[tc] = {"signature": _hex(sig)}
                tests.append(t)
            groups.append((g, ["signature"], tests))
    suites.append(("SLH-DSA-sigGen-FIPS205", "SLH-DSA", "sigGen", "FIPS205", groups, exp))

    groups, exp, tc = [], {}, 0
    for iface in _SLH_IFACES:
        g = {"testType": "AFT", **iface}
        tests = []
        for i in range(max(n, 2)):          # at least one valid, one invalid
            tc += 1
            lab = f"slh/sigVer/{tc}"
            *_s, pk, sk = keypair(lab)
            t = {"tcId": tc, "pk": _hex(pk), **inputs(lab, g, i)}
            sig = _slhdsa_sign_internal(_slhdsa_message(g, t), sk,
                                        D.bytes(lab + "/addrnd", N), par)
            want = True
            if i % 2:
                if (i // 2) % 2 == 0:                         # randomizer R altered
                    sig = _flip(sig, D.int(lab + "/pos", 0, N - 1))
                else:                                         # message altered
                    m = bytes.fromhex(t["message"])
                    t["message"] = _hex(_flip(m, D.int(lab + "/mpos", 0, len(m) - 1)))
                want = False
            t["signature"] = _hex(sig)
            got = bool(slh_verify(_slhdsa_message(g, t), sig, (pk[:N], pk[N:]), par))
            if got != want:
                raise FreshError(f"internal: reference verdict disagrees with the "
                                 f"constructed case ({ps} sigVer tcId {tc})")
            exp[tc] = {"testPassed": got}
            tests.append(t)
        groups.append((g, ["testPassed"], tests))
    suites.append(("SLH-DSA-sigVer-FIPS205", "SLH-DSA", "sigVer", "FIPS205", groups, exp))
    return suites


# ----------------------------------------------------------------------
# LMS (SP 800-208)
# ----------------------------------------------------------------------

def _lms(ps, D, n):
    from . import hbs as H
    tname, oname = ps.split("/")
    t, o = H.LMS_BY_NAME[tname], H.LMOTS_BY_NAME[oname]
    m = H.LMS[t][2]
    h = H.LMS[t][3]
    attrs = {"testType": "AFT", "lmsMode": tname, "lmOtsMode": oname}
    small = H.lms_keygen_cost(t, o) <= LMS_TREE_BUDGET
    suites = []

    if small:
        # keyGen: (SEED, I) -> public key
        tests, exp = [], {}
        for i in range(n):
            tc = i + 1
            seed, I = D.bytes(f"lms/keyGen/{tc}/seed", m), D.bytes(f"lms/keyGen/{tc}/I", 16)
            tests.append({"tcId": tc, "seed": _hex(seed), "i": _hex(I)})
            exp[tc] = {"publicKey": _hex(H.LMSTree(t, o, seed, I).public_key)}
        suites.append(("LMS-keyGen-1.0", "LMS", "keyGen", "1.0",
                       [(dict(attrs), ["publicKey"], tests)], exp))

    # sigGen: the responder's own key, one per group; each signature is
    # verified under it and no leaf may repeat (response._score_lms_siggen).
    tests, exp = [], {}
    for i in range(4 * n):
        tc = i + 1
        lab = f"lms/sigGen/{tc}"
        tests.append({"tcId": tc,
                      "message": _hex(D.bytes(lab + "/msg", D.int(lab + "/mlen", 1, 512)))})
        exp[tc] = {}
    suites.append(("LMS-sigGen-1.0", "LMS", "sigGen", "1.0",
                   [(dict(attrs, groupAnswerFields=["publicKey"]), ["signature"], tests)],
                   exp))

    if small:
        # sigVer: one key, valid signatures and ones wrong in one place
        seed, I = D.bytes("lms/sigVer/seed", m), D.bytes("lms/sigVer/I", 16)
        tree = H.LMSTree(t, o, seed, I)
        _, _, nn, _w = H.LMOTS[o]
        tests, exp = [], {}
        for i in range(4 * n):
            tc = i + 1
            lab = f"lms/sigVer/{tc}"
            msg = D.bytes(lab + "/msg", D.int(lab + "/mlen", 1, 512))
            q = D.int(lab + "/q", 0, (1 << h) - 1)
            sig = tree.sign(msg, q, D.bytes(lab + "/C", nn))
            want, kind = True, i % 4
            if kind == 1:                       # another message
                msg = _flip(msg, D.int(lab + "/mpos", 0, len(msg) - 1))
                want = False
            elif kind == 2:                     # another leaf index
                sig = (q ^ 1).to_bytes(4, "big") + sig[4:]
                want = False
            elif kind == 3:                     # an authentication-path node
                sig = _flip(sig, len(sig) - 1 - D.int(lab + "/ppos", 0, h * m - 1))
                want = False
            got = H.lms_verify(tree.public_key, msg, sig)
            if got != want:
                raise FreshError(f"internal: reference verdict disagrees with the "
                                 f"constructed case ({ps} sigVer tcId {tc})")
            tests.append({"tcId": tc, "message": _hex(msg), "signature": _hex(sig)})
            exp[tc] = {"testPassed": got}
        suites.append(("LMS-sigVer-1.0", "LMS", "sigVer", "1.0",
                       [(dict(attrs, publicKey=_hex(tree.public_key)), ["testPassed"],
                         tests)], exp))
    return suites


# ----------------------------------------------------------------------
# assembly
# ----------------------------------------------------------------------

def _family(ps):
    if ps in KEM_SETS:
        return "ML-KEM"
    if ps in DSA_SETS:
        return "ML-DSA"
    if ps in SLH_SETS:
        return "SLH-DSA"
    if ps in LMS_SETS:
        return "LMS"
    raise FreshError(f"no fresh questions for {ps!r}; known: {', '.join(PARAMETER_SETS)}")


def build(param_set, seed, count=None):
    """(questions, expected) for `param_set` derived from `seed`.

    `questions` has the shape response._questions returns (suites of ACVP
    test groups, each with answerFields); `expected` maps suite -> tcId ->
    the answer fields. Deterministic in (param_set, seed, count, pq-verify).
    """
    fam = _family(param_set)
    n = count or DEFAULT_COUNT[fam]
    if not 1 <= n <= 1000:
        raise FreshError("--fresh-count must be between 1 and 1000")
    D = _Derive(seed)
    gen = {"ML-KEM": _mlkem, "ML-DSA": _mldsa, "SLH-DSA": _slhdsa, "LMS": _lms}[fam]
    questions, expected = [], {}
    tg = 0
    for suite, alg, mode, rev, groups, exp in gen(param_set, D, n):
        out = []
        for attrs, fields, tests in groups:
            tg += 1
            head = {} if fam == "LMS" else {"parameterSet": param_set}
            out.append({"tgId": tg, **head, **attrs,
                        "answerFields": sorted(fields), "tests": tests})
        questions.append({"suite": suite, "algorithm": alg, "mode": mode,
                          "revision": rev, "testGroups": out})
        expected[suite] = exp
    return questions, expected


def new_seed():
    return secrets.token_bytes(32)


def write_key(path, param_set, seed, count, prompt_id, question_count):
    """The auditor's half. 0600 from creation: it is the only copy of the seed."""
    doc = {"schema": KEY_SCHEMA, "schema_version": "1.0",
           "derivation": DERIVATION, "toolVersion": VERSION,
           "parameterSet": param_set, "count": count,
           "seed": seed.hex(), "promptId": prompt_id,
           "questionCount": question_count,
           "note": ("Keep this file private. It is the only record of the seed "
                    "these questions were derived from; with it, the questions "
                    "and their answers can be recomputed.")}
    d = os.path.dirname(os.path.abspath(path))
    os.makedirs(d, exist_ok=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w") as fh:
        json.dump(doc, fh, indent=2)
    return path


def read_key(path):
    try:
        with open(path) as fh:
            doc = json.load(fh)
    except (OSError, ValueError) as exc:
        raise FreshError(f"cannot read fresh key {path}: {exc}") from exc
    if not isinstance(doc, dict) or doc.get("schema") != KEY_SCHEMA:
        raise FreshError(f"{path} is not a pq-verify fresh key")
    if doc.get("derivation") != DERIVATION:
        raise FreshError(f"{path} uses derivation {doc.get('derivation')!r}; this "
                         f"pq-verify implements {DERIVATION!r}")
    try:
        seed = bytes.fromhex(doc["seed"])
    except (KeyError, TypeError, ValueError):
        raise FreshError(f"{path} has no valid seed") from None
    if len(seed) != 32:
        raise FreshError(f"{path} has a seed of {len(seed)} bytes, not 32")
    ps = doc.get("parameterSet")
    _family(ps)
    count = doc.get("count")
    if count is not None and not isinstance(count, int):
        raise FreshError(f"{path} has a non-integer count")
    return {"param_set": ps, "seed": seed, "count": count,
            "prompt_id": doc.get("promptId"), "tool_version": doc.get("toolVersion")}
