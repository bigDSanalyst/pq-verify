"""Audit a THIRD-PARTY SLH-DSA library against NIST's ACVP vectors (FIPS 205).

The ML-DSA counterpart is pqverify_audit_dsa. This drives the vendor's own
compiled code with every pinned NIST ACVP SLH-DSA vector for one parameter
set:

    keyGen          NIST SK.seed, SK.prf, PK.seed -> vendor pk, sk     byte-exact
    keyGenRBG       the same seeds, served as one stream through the
                    library's random-bit-generator callback to its own key
                    generation; exactly 3n bytes drawn, however the requests
                    are split                                         byte-exact
    sigGen*         NIST sk, M, ctx, addrnd       -> vendor signature  byte-exact
    sigVer*         NIST pk, M, ctx, signature    -> vendor verdict    = NIST testPassed

for each interface FIPS 205 defines: internal (Algorithms 19/20), external
pure (Algorithms 22/24) and external pre-hash (HashSLH-DSA, Algorithms 23/25).
Each case goes through the library's own entry point for its interface, so
the library's own encoding of M' (domain separator, context length, the
pre-hash OID) is what NIST's vectors check; for NIST's cases pq-verify builds
no M' (the reference check, pqverify_slhdsa_acvp, builds its own).

Edge cases, beyond NIST's set:

    preHashVerify   for each of the twelve approved pre-hash functions, the
                    library's verifier accepts a signature its signer made with
                    it. NIST's sigVer vectors hold a valid pre-hash signature
                    for only two of the twelve per parameter set, so a verifier
                    hashing wrongly for the other ten passes them all; signing
                    is NIST-checked for all twelve (sigGenPreHash)
    contextLength   a 256-byte context is refused (FIPS 205 Algorithms
                    22-25): signing refuses it outright, and verification
                    whatever signature comes with it
    unknownPreHash  a pre-hash function the library does not know neither
                    signs nor verifies
    rbgFailure      key generation whose random bit generator fails returns
                    an error (FIPS 205 Algorithm 21)
    sizes           the library's own size functions, where it has them,
                    give FIPS 205's sizes (Table 2)

A refused verification is only evidence if the call could have succeeded.
Each one is offered a signature that one way of getting the check wrong would
accept, and that the library accepts where it does belong:

    256-byte context, verifying
      the context ignored          a signature made with an empty context
      the length kept in a byte    256 -> 0: a signature over ctx || M with an
                                   empty context (pure); an internal signature
                                   over 1 || 0 || ctx || OID || PH(M) (pre-hash)
      256 read as "no context"     an internal signature over M (slhdsa-c
                                   marks its internal calls with length 256)
    unknown pre-hash name, verifying
      a default hash used          a SHA2-256 signature
      the name matching nothing    an internal signature over 1 || 0
      the error ignored            an internal signature over the empty message

Randomness. FIPS 205 takes its randomness as arguments to the internal
functions, and the audited API passes it through: the seeds to
slh_keygen_internal, addrnd to every signing function (NULL selects the
deterministic variant, opt_rand = PK.seed). Its randomised key generation
draws through a callback, which pq-verify supplies. No randomness harness or
special build is needed. liboqs's API draws through OQS_randombytes instead;
see oqs below.

Calling conventions, by symbol name:
  slhdsa-c   pq-code-package/slhdsa-c: one library for all twelve parameter
             sets, each a `const slh_param_t` object (slh_dsa_sha2_128s, ...);
             slh_keygen_internal and slh_keygen, slh_sign_internal and
             slh_verify_internal, slh_sign and slh_verify (pure, with a
             context), hash_slh_sign and hash_slh_verify (pre-hash, the hash
             named as ACVP names it)
  oqs        liboqs's public API, as in 0.16.0: per parameter set a pure
             algorithm, OQS_SIG_slh_dsa_pure_<set>_*, and one HashSLH-DSA
             algorithm per approved hash, OQS_SIG_slh_dsa_<hash>_prehash_<set>_*,
             each with keypair, sign and verify (no context) and
             sign_with_ctx_str and verify_with_ctx_str. NIST's cases with an
             empty context go through the plain entry points, the rest through
             the context ones, so both are checked. Randomness reaches key
             generation and signing through liboqs's own hook,
             OQS_randombytes_custom_algorithm: NIST's seeds, and NIST's addrnd.
             liboqs signs hedged only, so a deterministic case is served PK.seed
             as addrnd: FIPS 205's deterministic variant is the hedged one with
             opt_rand = PK.seed. Each signature must draw exactly n bytes.
             Every algorithm's keypair is checked, and its sizes, read from
             OQS_SIG_new. The internal interface goes through slh_sign_internal
             and slh_verify_internal, which liboqs exports from the same
             slhdsa-c copy its wrappers call (its patch internal_api.patch).
             Not applicable through this API: seeded key generation (not
             exported), an unknown hash name (each algorithm fixes its hash),
             and a failing random bit generator (the hook returns void).
             Chosen when the library exports OQS_SIG_slh_dsa_pure_<set>_keypair
             and no entry point is named.
A case no entry point can express is counted as not applicable, with the
reason, and never as a pass. An ambiguous role is never guessed
(--slhdsa-symbol ROLE=SYMBOL).
"""
import ctypes as _ct
import hashlib as _hashlib
import os as _os
import re as _re

from .bounds import Guarded, outside_writes, print_line as print_bounds
from .dsa_audit import _OQSRNG

# FIPS 205 Table 2: n and the signature size; pk is 2n bytes, sk 4n.
SETS = {
    "SLH-DSA-SHA2-128s": (16, 7856), "SLH-DSA-SHAKE-128s": (16, 7856),
    "SLH-DSA-SHA2-128f": (16, 17088), "SLH-DSA-SHAKE-128f": (16, 17088),
    "SLH-DSA-SHA2-192s": (24, 16224), "SLH-DSA-SHAKE-192s": (24, 16224),
    "SLH-DSA-SHA2-192f": (24, 35664), "SLH-DSA-SHAKE-192f": (24, 35664),
    "SLH-DSA-SHA2-256s": (32, 29792), "SLH-DSA-SHAKE-256s": (32, 29792),
    "SLH-DSA-SHA2-256f": (32, 49856), "SLH-DSA-SHAKE-256f": (32, 49856),
}
STAGES = ("keyGen", "keyGenRBG",
          "sigGenInternal", "sigGenPure", "sigGenPreHash",
          "sigVerInternal", "sigVerPure", "sigVerPreHash")
EDGE_STAGES = ("preHashVerify", "contextLength", "unknownPreHash", "rbgFailure", "sizes")

# Entry points by role, matched against the lowercased symbol.
_ROLES = {
    "keypair_seed":    r"(?:^|_)slh_keygen_internal$",
    "keypair":         r"(?:^|_)slh_keygen$",
    "sign_internal":   r"(?:^|_)slh_sign_internal$",
    "verify_internal": r"(?:^|_)slh_verify_internal$",
    "sign":            r"(?:^|_)(?<!hash_)slh_sign$",
    "verify":          r"(?:^|_)(?<!hash_)slh_verify$",
    "sign_prehash":    r"(?:^|_)hash_slh_sign$",
    "verify_prehash":  r"(?:^|_)hash_slh_verify$",
    "pk_size":         r"(?:^|_)slh_pk_sz$",
    "sk_size":         r"(?:^|_)slh_sk_sz$",
    "sig_size":        r"(?:^|_)slh_sig_sz$",
}
# The stage each entry point serves, for the report.
_VIA = {"keyGen": "keypair_seed", "keyGenRBG": "keypair",
        "sigGenInternal": "sign_internal", "sigGenPure": "sign",
        "sigGenPreHash": "sign_prehash", "sigVerInternal": "verify_internal",
        "sigVerPure": "verify", "sigVerPreHash": "verify_prehash"}
_RBG = _ct.CFUNCTYPE(_ct.c_int, _ct.POINTER(_ct.c_uint8), _ct.c_size_t)
# SHA2-256's OID, 2.16.840.1.101.3.4.2.1, DER-encoded (FIPS 205 §10.2.2).
_SHA256_OID = bytes.fromhex("0609608648016503040201")
_P8, _SZ, _VP = _ct.POINTER(_ct.c_uint8), _ct.c_size_t, _ct.c_void_p

# The approved pre-hash functions (FIPS 205 §10.2.2), by ACVP's name. liboqs
# names each FIPS 205 algorithm on its own: the pure one, and one HashSLH-DSA
# algorithm per approved hash. ACVP's hashAlg -> liboqs's name.
OQS_HASHES = {"SHA2-224": "sha2_224", "SHA2-256": "sha2_256", "SHA2-384": "sha2_384",
              "SHA2-512": "sha2_512", "SHA2-512/224": "sha2_512_224",
              "SHA2-512/256": "sha2_512_256", "SHA3-224": "sha3_224",
              "SHA3-256": "sha3_256", "SHA3-384": "sha3_384", "SHA3-512": "sha3_512",
              "SHAKE-128": "shake_128", "SHAKE-256": "shake_256"}
PREHASHES = tuple(OQS_HASHES)


class NotApplicable(NotImplementedError):
    """The library has no entry point for this case."""


def param_symbol(param_set):
    """slhdsa-c's name for a parameter set's object: SLH-DSA-SHA2-128s ->
    slh_dsa_sha2_128s."""
    return param_set.lower().replace("-", "_")


def oqs_token(param_set):
    """liboqs's name for a parameter set: SLH-DSA-SHA2-128f -> sha2_128f."""
    return param_set.lower().replace("slh-dsa-", "").replace("-", "_")


def oqs_algorithms(param_set):
    """[(function prefix, OQS_SIG_new name, ACVP hash or None)]: liboqs's
    pure algorithm for the parameter set, then its HashSLH-DSA one per hash."""
    t = oqs_token(param_set)
    algs = [(f"OQS_SIG_slh_dsa_pure_{t}_", f"SLH_DSA_PURE_{t.upper()}", None)]
    algs += [(f"OQS_SIG_slh_dsa_{h}_prehash_{t}_", f"SLH_DSA_{h.upper()}_PREHASH_{t.upper()}",
              ph) for ph, h in OQS_HASHES.items()]
    return algs


def exported_symbols(so_path):
    from .symbols import exported_functions
    return exported_functions(so_path)


def resolve_symbols(exported, explicit=None, prefix=None):
    """{role: symbol or None}, {role: [candidates]} for ambiguous roles."""
    from .symbols import with_prefix
    explicit = explicit or {}
    exported = with_prefix(exported, prefix)
    found, ambiguous = {}, {}
    for role, pat in _ROLES.items():
        if explicit.get(role):
            found[role] = explicit[role]
            continue
        cands = [e for e in exported if _re.search(pat, e.lower())]
        found[role] = cands[0] if len(cands) == 1 else None
        if len(cands) > 1:
            ambiguous[role] = sorted(cands)
    return found, ambiguous


def _buf(b):
    return (_ct.c_uint8 * max(1, len(b))).from_buffer_copy(bytes(b) or b"\0")


def _opt(b):
    """addrnd: None is the deterministic variant (a NULL pointer)."""
    return None if b is None else _buf(b)


class VendorSLHDSA:
    # Buffers are the sizes FIPS 205 gives. The room to see a write past the
    # end is the guard bytes every call's buffers sit between (pq_verify.bounds),
    # which are checked; slack bytes here would hide a short overflow.
    SLACK = 0

    def __init__(self, so_path, param_set, symbols=None, prefix=None):
        self.path = _os.path.abspath(so_path)
        self.name = _os.path.basename(so_path)
        self.set = param_set
        self.n, self.sig_len = SETS[param_set]
        self.pk_len, self.sk_len = 2 * self.n, 4 * self.n
        self.lib = _ct.CDLL(self.path)
        symbols = dict(symbols or {})
        self.param_name = symbols.pop("param", None) or (prefix or "") + param_symbol(param_set)
        self.sym, self.ambiguous = resolve_symbols(exported_symbols(self.path), symbols, prefix)
        self.abi = "slhdsa-c"
        try:
            self.prm = _ct.c_void_p(_ct.addressof(_ct.c_uint8.in_dll(self.lib, self.param_name)))
        except ValueError:
            self.prm = None
        P8, SZ, VP, CP = _ct.POINTER(_ct.c_uint8), _ct.c_size_t, _ct.c_void_p, _ct.c_char_p
        sigs = {
            "keypair_seed":    (_ct.c_int, [P8, P8, P8, P8, P8, VP]),
            "keypair":         (_ct.c_int, [P8, P8, _RBG, VP]),
            "sign_internal":   (SZ, [P8, P8, SZ, P8, P8, VP]),
            "verify_internal": (_ct.c_int, [P8, SZ, P8, SZ, P8, VP]),
            "sign":            (SZ, [P8, P8, SZ, P8, SZ, P8, P8, VP]),
            "verify":          (_ct.c_int, [P8, SZ, P8, SZ, P8, SZ, P8, VP]),
            "sign_prehash":    (SZ, [P8, P8, SZ, P8, SZ, CP, P8, P8, VP]),
            "verify_prehash":  (_ct.c_int, [P8, SZ, P8, SZ, P8, SZ, CP, P8, VP]),
            "pk_size":         (SZ, [VP]),
            "sk_size":         (SZ, [VP]),
            "sig_size":        (SZ, [VP]),
        }
        self.fn = {}
        for role, s in self.sym.items():
            if not s:
                continue
            f = getattr(self.lib, s)
            f.restype, f.argtypes = sigs[role]
            self.fn[role] = Guarded(f, role)

    def has(self, role):
        return role in self.fn and self.prm is not None

    def _need(self, role, what):
        if not self.has(role):
            raise NotApplicable(f"no {what} entry point")
        return self.fn[role]

    def keypair_seed(self, sk_seed, sk_prf, pk_seed):
        f = self._need("keypair_seed", "seeded key-generation")
        sk = (_ct.c_uint8 * (self.sk_len + self.SLACK))()
        pk = (_ct.c_uint8 * (self.pk_len + self.SLACK))()
        rc = f(sk, pk, _buf(sk_seed), _buf(sk_prf), _buf(pk_seed), self.prm)
        if rc != 0:
            raise RuntimeError(f"seeded key generation returned {rc}")
        return bytes(sk[:self.sk_len]), bytes(pk[:self.pk_len])

    def keypair_rbg(self, draw):
        """(rc, sk, pk, draws): key generation with the callback serving `draw`
        (bytes) as one stream, however the library splits its requests, and
        zeros past its end, as pqv_randombytes.c does; with draw None every
        request fails. `draws` lists the size of each request."""
        f = self._need("keypair", "randomised key-generation")
        draws, pos = [], [0]

        def rbg(out, n):
            draws.append(n)
            if draw is None or n > 1 << 16:   # FIPS 205 draws 96 bytes at most
                return -1
            _ct.memmove(out, draw[pos[0]:pos[0] + n].ljust(n, b"\0"), n)
            pos[0] += n
            return 0

        cb = _RBG(rbg)
        sk = (_ct.c_uint8 * (self.sk_len + self.SLACK))()
        pk = (_ct.c_uint8 * (self.pk_len + self.SLACK))()
        rc = f(sk, pk, cb, self.prm)
        return rc, bytes(sk[:self.sk_len]), bytes(pk[:self.pk_len]), draws

    def _sig(self, n):
        if n == 0:
            return None                       # refused
        if n != self.sig_len:
            raise RuntimeError(f"signature of {n} bytes, FIPS 205 says {self.sig_len}")
        return n

    def sign_internal(self, m, sk, addrnd):
        f = self._need("sign_internal", "internal signing")
        sig = (_ct.c_uint8 * (self.sig_len + self.SLACK))()
        n = self._sig(f(sig, _buf(m), len(m), _buf(sk), _opt(addrnd), self.prm))
        return None if n is None else bytes(sig[:n])

    def sign(self, m, ctx, sk, addrnd):
        f = self._need("sign", "pure signing")
        sig = (_ct.c_uint8 * (self.sig_len + self.SLACK))()
        n = self._sig(f(sig, _buf(m), len(m), _buf(ctx), len(ctx), _buf(sk), _opt(addrnd),
                        self.prm))
        return None if n is None else bytes(sig[:n])

    def sign_prehash(self, m, ctx, ph, sk, addrnd):
        f = self._need("sign_prehash", "pre-hash signing")
        sig = (_ct.c_uint8 * (self.sig_len + self.SLACK))()
        n = self._sig(f(sig, _buf(m), len(m), _buf(ctx), len(ctx), ph.encode(), _buf(sk),
                        _opt(addrnd), self.prm))
        return None if n is None else bytes(sig[:n])

    def verify_internal(self, m, sig, pk):
        f = self._need("verify_internal", "internal verification")
        return f(_buf(m), len(m), _buf(sig), len(sig), _buf(pk), self.prm) == 1

    def verify(self, m, sig, ctx, pk):
        f = self._need("verify", "pure verification")
        return f(_buf(m), len(m), _buf(sig), len(sig), _buf(ctx), len(ctx), _buf(pk),
                 self.prm) == 1

    def verify_prehash(self, m, sig, ctx, ph, pk):
        f = self._need("verify_prehash", "pre-hash verification")
        return f(_buf(m), len(m), _buf(sig), len(sig), _buf(ctx), len(ctx), ph.encode(),
                 _buf(pk), self.prm) == 1

    # ---- what the audit asks of every convention ---------------------------

    def unusable_reason(self):
        if self.prm is None:
            return f"no parameter-set object {self.param_name!r}"
        if not any(self.has(r) for r in _VIA.values()):
            return "no SLH-DSA entry point"
        return None

    def other_keypairs(self):
        """Further key-generation entry points: [(label, key)] for keypair_rbg."""
        return []

    def sizes(self):
        """(case, ok, detail) for each size the library reports."""
        return [(role, got == want, f"{got} bytes, FIPS 205 says {want}")
                for role, want in (("pk_size", self.pk_len), ("sk_size", self.sk_len),
                                   ("sig_size", self.sig_len)) if self.has(role)
                for got in [self.fn[role](self.prm)]]

    def via_map(self):
        via = {s: self.sym.get(r) for s, r in _VIA.items()}
        via.update({"contextLength": "pure and pre-hash entry points",
                    "preHashVerify": self.sym.get("sign_prehash") and (
                        f"{self.sym.get('sign_prehash')} / {self.sym.get('verify_prehash')}"),
                    "unknownPreHash": "pre-hash entry points",
                    "rbgFailure": self.sym.get("keypair"), "sizes": "size functions"})
        return via

    def symbols(self):
        return {k: s for k, s in self.sym.items() if s}

    def close(self):
        pass


class _OQSDraws(_OQSRNG):
    """liboqs's RNG hook (see dsa_audit), recording the size of each request."""

    def __init__(self, lib):
        self.sizes = []
        super().__init__(lib)

    def _draw(self, buf, n):
        self.sizes.append(n)
        super()._draw(buf, n)

    def queue(self, data):
        super().queue(data)
        self.sizes = []


class _OQSSigHead(_ct.Structure):
    """The head of liboqs's OQS_SIG (src/sig/sig.h), as far as its sizes."""
    _fields_ = [("method_name", _ct.c_char_p), ("alg_version", _ct.c_char_p),
                ("claimed_nist_level", _ct.c_uint8), ("euf_cma", _ct.c_bool),
                ("suf_cma", _ct.c_bool), ("sig_with_ctx_support", _ct.c_bool),
                ("length_public_key", _ct.c_size_t), ("length_secret_key", _ct.c_size_t),
                ("length_signature", _ct.c_size_t)]


class VendorSLHDSAOQS:
    """One parameter set of liboqs's SLH-DSA, through the API its users call
    (the oqs convention in the module docstring). Same methods as
    VendorSLHDSA; a call the API cannot express raises NotApplicable."""
    SLACK = 0           # as in VendorSLHDSA: the guard bytes are the room past the end
    _ARGS = {"keypair": ("keypair", [_P8, _P8]),
             "sign": ("sign", [_P8, _ct.POINTER(_SZ), _P8, _SZ, _P8]),
             "sign_ctx": ("sign_with_ctx_str", [_P8, _ct.POINTER(_SZ), _P8, _SZ, _P8, _SZ, _P8]),
             "verify": ("verify", [_P8, _SZ, _P8, _SZ, _P8]),
             "verify_ctx": ("verify_with_ctx_str", [_P8, _SZ, _P8, _SZ, _P8, _SZ, _P8])}

    def __init__(self, so_path, param_set, exported=None):
        self.path = _os.path.abspath(so_path)
        self.name = _os.path.basename(so_path)
        self.set = param_set
        self.n, self.sig_len = SETS[param_set]
        self.pk_len, self.sk_len = 2 * self.n, 4 * self.n
        self.lib = _ct.CDLL(self.path)
        self.abi, self.ambiguous = "oqs", {}
        exported = set(exported if exported is not None else exported_symbols(self.path))
        self.algs = [a for a in oqs_algorithms(param_set) if a[0] + "keypair" in exported]
        self.fn, self.names = {}, {}
        for prefix, _name, ph in self.algs:
            for role, (suffix, args) in self._ARGS.items():
                if prefix + suffix in exported:
                    f = getattr(self.lib, prefix + suffix)
                    f.restype, f.argtypes = _ct.c_int, args
                    self.fn[(role, ph)] = Guarded(f, prefix + suffix)
                    self.names[(role, ph)] = prefix + suffix
        # The internal interface: liboqs exports slhdsa-c's own functions and
        # parameter objects (src/sig/slh_dsa/patches/internal_api.patch).
        self.param_name = param_symbol(param_set)
        try:
            self.prm = _ct.c_void_p(_ct.addressof(_ct.c_uint8.in_dll(self.lib, self.param_name)))
        except ValueError:
            self.prm = None
        for role, sym, res, args in (
                ("sign_internal", "slh_sign_internal", _SZ, [_P8, _P8, _SZ, _P8, _P8, _VP]),
                ("verify_internal", "slh_verify_internal", _ct.c_int,
                 [_P8, _SZ, _P8, _SZ, _P8, _VP])):
            if sym in exported and self.prm is not None:
                f = getattr(self.lib, sym)
                f.restype, f.argtypes = res, args
                self.fn[(role, None)], self.names[(role, None)] = Guarded(f, sym), sym
        hook = {"OQS_randombytes_custom_algorithm", "OQS_randombytes_switch_algorithm"}
        self.rng = _OQSDraws(self.lib) if hook <= exported else None
        self._new = self._free = None
        if {"OQS_SIG_new", "OQS_SIG_free"} <= exported:
            self._new, self._free = self.lib.OQS_SIG_new, self.lib.OQS_SIG_free
            self._new.restype, self._new.argtypes = _ct.c_void_p, [_ct.c_char_p]
            self._free.restype, self._free.argtypes = None, [_ct.c_void_p]

    def has(self, role):
        if role == "keypair":
            return ("keypair", None) in self.fn and self.rng is not None
        return (role, None) in self.fn

    def _need(self, role, ph, what):
        f = self.fn.get((role, ph))
        if f is None:
            raise NotApplicable(f"liboqs exports no {what}")
        return f

    def _drawing(self, data, call):
        """call() with liboqs's RNG serving `data`: (result, request sizes)."""
        if self.rng is None:
            raise NotApplicable("liboqs exports no OQS_randombytes_custom_algorithm hook")
        self.rng.queue(data)
        return call(), list(self.rng.sizes)

    def keypair_seed(self, sk_seed, sk_prf, pk_seed):
        raise NotApplicable("liboqs exports no seeded key generation")

    def keypair_rbg(self, draw, key=None):
        if draw is None:
            raise NotApplicable("liboqs's random-bytes hook returns void: "
                                "it cannot report a failure")
        f = self._need("keypair", key, f"keypair for {key or 'the pure algorithm'}")
        sk = (_ct.c_uint8 * (self.sk_len + self.SLACK))()
        pk = (_ct.c_uint8 * (self.pk_len + self.SLACK))()
        rc, sizes = self._drawing(draw, lambda: f(pk, sk))
        return rc, bytes(sk[:self.sk_len]), bytes(pk[:self.pk_len]), sizes

    def sign_internal(self, m, sk, addrnd):
        f = self._need("sign_internal", None, "internal signing (slh_sign_internal)")
        sig = (_ct.c_uint8 * (self.sig_len + self.SLACK))()
        n = f(sig, _buf(m), len(m), _buf(sk), _opt(addrnd), self.prm)
        if n == 0:
            return None
        if n != self.sig_len:
            raise RuntimeError(f"signature of {n} bytes, FIPS 205 says {self.sig_len}")
        return bytes(sig[:n])

    def verify_internal(self, m, sig, pk):
        f = self._need("verify_internal", None, "internal verification (slh_verify_internal)")
        return f(_buf(m), len(m), _buf(sig), len(sig), _buf(pk), self.prm) == 1

    def _hash(self, ph):
        if ph not in OQS_HASHES:
            raise NotApplicable("each liboqs algorithm fixes its pre-hash function: "
                                "no name is passed")
        return ph

    def sign(self, m, ctx, sk, addrnd):
        return self._sign(None, m, ctx, sk, addrnd)

    def sign_prehash(self, m, ctx, ph, sk, addrnd):
        return self._sign(self._hash(ph), m, ctx, sk, addrnd)

    def _sign(self, ph, m, ctx, sk, addrnd):
        role = "sign_ctx" if ctx else "sign"
        f = self._need(role, ph, f"{self._ARGS[role][0]} for {ph or 'the pure algorithm'}")
        # liboqs signs hedged only; FIPS 205's deterministic variant is the
        # hedged one with addrnd = PK.seed: the same signature, computed alike.
        rnd = bytes(sk[2 * self.n:3 * self.n] if addrnd is None else addrnd)
        sig = (_ct.c_uint8 * (self.sig_len + self.SLACK))()
        siglen = _SZ(0)
        args = [sig, _ct.byref(siglen), _buf(m), len(m)]
        args += [_buf(ctx), len(ctx)] if ctx else []
        rc, sizes = self._drawing(rnd, lambda: f(*args, _buf(sk)))
        if rc != 0:
            return None                         # OQS_ERROR: refused
        if siglen.value != self.sig_len:
            raise RuntimeError(f"signature of {siglen.value} bytes, FIPS 205 says {self.sig_len}")
        if sum(sizes) != self.n:
            raise RuntimeError(f"signing drew {sum(sizes)} random bytes in requests {sizes}; "
                               f"FIPS 205 draws n = {self.n} (addrnd)")
        return bytes(sig[:self.sig_len])

    def verify(self, m, sig, ctx, pk):
        return self._verify(None, m, sig, ctx, pk)

    def verify_prehash(self, m, sig, ctx, ph, pk):
        return self._verify(self._hash(ph), m, sig, ctx, pk)

    def _verify(self, ph, m, sig, ctx, pk):
        role = "verify_ctx" if ctx else "verify"
        f = self._need(role, ph, f"{self._ARGS[role][0]} for {ph or 'the pure algorithm'}")
        args = [_buf(m), len(m), _buf(sig), len(sig)] + ([_buf(ctx), len(ctx)] if ctx else [])
        return f(*args, _buf(pk)) == 0             # OQS_SUCCESS

    def unusable_reason(self):
        return None if self.fn else f"no OQS_SIG_slh_dsa entry point for {self.set}"

    def other_keypairs(self):
        return [(name, ph) for _p, name, ph in self.algs
                if ph is not None and ("keypair", ph) in self.fn]

    def sizes(self):
        if self._new is None:
            return []
        out = []
        for _p, name, _ph in self.algs:
            obj = self._new(name.encode())
            if not obj:
                out.append((f"OQS_SIG_new({name!r})", False, "returned NULL"))
                continue
            try:
                head = _ct.cast(obj, _ct.POINTER(_OQSSigHead)).contents
                out += [(f"{name} {field}", getattr(head, field) == want,
                         f"{getattr(head, field)} bytes, FIPS 205 says {want}")
                        for field, want in (("length_public_key", self.pk_len),
                                            ("length_secret_key", self.sk_len),
                                            ("length_signature", self.sig_len))]
            finally:
                self._free(obj)
        return out

    def via_map(self):
        t = oqs_token(self.set)
        pure = f"OQS_SIG_slh_dsa_pure_{t}_" if ("keypair", None) in self.fn else None
        pre = (f"OQS_SIG_slh_dsa_<hash>_prehash_{t}_"
               if any(ph for _p, _n, ph in self.algs) else None)

        def pair(prefix, a, b):
            return f"{prefix}{a} / {prefix}{b}" if prefix else None
        keypairs = [f"{x}keypair" for x in (pure, pre) if x]
        return {"keyGen": None,
                "keyGenRBG": ", and ".join(keypairs) or None,
                "sigGenInternal": self.names.get(("sign_internal", None)),
                "sigGenPure": pair(pure, "sign", "sign_with_ctx_str"),
                "sigGenPreHash": pair(pre, "sign", "sign_with_ctx_str"),
                "sigVerInternal": self.names.get(("verify_internal", None)),
                "sigVerPure": pair(pure, "verify", "verify_with_ctx_str"),
                "sigVerPreHash": pair(pre, "verify", "verify_with_ctx_str"),
                "contextLength": "pure and pre-hash entry points",
                "preHashVerify": pair(pre, "sign_with_ctx_str", "verify_with_ctx_str"),
                "unknownPreHash": None, "rbgFailure": None,
                "sizes": "OQS_SIG_new" if self._new else None}

    def symbols(self):
        out = {f"{role}[{ph}]" if ph else role: s for (role, ph), s in self.names.items()}
        if self.rng is not None:
            out["rng"] = "OQS_randombytes_custom_algorithm"
        return out

    def close(self):
        """Hand liboqs's RNG back (its "system" algorithm)."""
        if self.rng is not None:
            self.rng.release()


def open_library(so_path, param_set, symbols=None, prefix=None):
    """The library, behind the convention its exports follow: liboqs's public
    API when it exports OQS_SIG_slh_dsa_pure_<set>_keypair and nothing else is
    asked for (no entry point named, no other prefix); slhdsa-c's otherwise."""
    exported = exported_symbols(so_path)
    pure = oqs_algorithms(param_set)[0][0] + "keypair"
    if not symbols and (prefix is None or prefix.startswith("OQS_SIG_slh_dsa")) \
            and pure in exported:
        return VendorSLHDSAOQS(so_path, param_set, exported)
    return VendorSLHDSA(so_path, param_set, symbols=symbols, prefix=prefix)


class _Tally:
    def __init__(self):
        self.detail, self._na, self.failures = {}, {}, []

    def rec(self, stage, ok, case, detail=""):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        if not ok and len(self.failures) < 50:
            self.failures.append({"stage": stage, "case": case, "detail": detail})

    def not_applicable(self, stage, count, why):
        c, reasons = self._na.get(stage, (0, []))
        self._na[stage] = (c + count, reasons + [why] if why not in reasons else reasons)

    @property
    def na(self):
        """{stage: (count, the distinct reasons, joined)}"""
        return {k: (c, "; ".join(r)) for k, (c, r) in self._na.items()}


def _passed(v):
    return v if isinstance(v, bool) else str(v).lower() == "true"


def load_cases(mode, param_set, vector_dir=None, live=False):
    """(group, test, expected) for one ACVP mode and parameter set: from
    `vector_dir` (read from disk), NIST's ACVP-Server with live=True, else
    the pinned bundle -- the precedence pqverify_slhdsa_acvp uses."""
    from .core import _SLHDSA_DIRS, _SLHDSA_ACVP_BASE, _load_vector_json, _pkg_dir
    d = _SLHDSA_DIRS[mode]
    if live and not vector_dir:
        import json, urllib.request
        get = lambda f: json.load(urllib.request.urlopen(  # noqa: E731
            _SLHDSA_ACVP_BASE + d + "/" + f, timeout=120))
        prompt, exp = get("prompt.json"), get("expectedResults.json")
    else:
        base = _os.path.join(vector_dir or _os.path.join(_pkg_dir(), "vectors"), d)
        prompt = _load_vector_json(_os.path.join(base, "prompt.json"), f"{d}/prompt.json")
        exp = _load_vector_json(_os.path.join(base, "expectedResults.json"),
                                f"{d}/expectedResults.json")
    want = {g["tgId"]: {t["tcId"]: t for t in g["tests"]} for g in exp["testGroups"]}
    for g in prompt["testGroups"]:
        if g.get("parameterSet") != param_set:
            continue
        for t in g["tests"]:
            yield g, t, want[g["tgId"]][t["tcId"]]


def _keygen_rbg(T, case, n, want, keypair):
    """keyGenRBG: NIST's seeds served as one stream must give NIST's key,
    drawn as exactly 3n bytes, however the requests are split."""
    ok, got = _call(T, "keyGenRBG", case, keypair)
    if not ok:
        return
    rc, sk, pk, draws = got
    if rc != 0:
        why = f"returned {rc}; requests {draws}"
    elif sum(draws) != 3 * n:
        why = (f"drew {sum(draws)} bytes in requests {draws}; FIPS 205 Algorithm 21 "
               f"draws {3 * n}: SK.seed, SK.prf, PK.seed")
    else:
        why = "sk or pk differs from NIST's" if (sk, pk) != want else ""
    T.rec("keyGenRBG", not why, case, why)


def _interface(g):
    if g.get("signatureInterface") == "internal":
        return "Internal"
    return "PreHash" if g.get("preHash") == "preHash" else "Pure"


def _call(T, stage, case, fn):
    """Run fn(); NotApplicable is counted, an exception a failure."""
    try:
        return True, fn()
    except NotApplicable as e:
        T.not_applicable(stage, 1, str(e))
    except Exception as e:                     # noqa: BLE001 -- the library's fault, reported
        T.rec(stage, False, case, f"{type(e).__name__}: {e}")
    return False, None


def run(v, vector_dir=None, live=False):
    T = _Tally()
    h = bytes.fromhex
    n = v.n
    key = None                                 # a NIST key pair for the edge cases

    first = None                               # NIST's first keyGen case
    for g, t, ref in load_cases("keyGen", v.set, vector_dir, live):
        case = f"keyGen tcId {t['tcId']}"
        seeds = (h(t["skSeed"]), h(t["skPrf"]), h(t["pkSeed"]))
        want = (h(ref["sk"]), h(ref["pk"]))
        key = key or want
        first = first or (t["tcId"], seeds, want)
        ok, got = _call(T, "keyGen", case, lambda: v.keypair_seed(*seeds))
        if ok:
            T.rec("keyGen", got == want, case, "sk or pk differs from NIST's")
        _keygen_rbg(T, case, n, want, lambda: v.keypair_rbg(b"".join(seeds)))
    # Every other key-generation entry point (liboqs: each HashSLH-DSA
    # algorithm's keypair), with NIST's first case.
    for label, other in v.other_keypairs() if first else ():
        tc, seeds, want = first
        _keygen_rbg(T, f"keyGen tcId {tc} via {label}", n, want,
                    lambda: v.keypair_rbg(b"".join(seeds), other))

    for g, t, ref in load_cases("sigGen", v.set, vector_dir, live):
        stage = "sigGen" + _interface(g)
        case = f"{stage} tcId {t['tcId']}" + (" deterministic" if g.get("deterministic") else "")
        m, sk, ctx = h(t["message"]), h(t["sk"]), h(t.get("context", ""))
        addrnd = None if g.get("deterministic") else h(t["additionalRandomness"])
        sign = {"sigGenInternal": lambda: v.sign_internal(m, sk, addrnd),
                "sigGenPure": lambda: v.sign(m, ctx, sk, addrnd),
                "sigGenPreHash": lambda: v.sign_prehash(m, ctx, t.get("hashAlg", ""), sk,
                                                        addrnd)}[stage]
        ok, sig = _call(T, stage, case, sign)
        if ok:
            T.rec(stage, sig == h(ref["signature"]), case,
                  "refused" if sig is None else "signature differs from NIST's")

    for g, t, ref in load_cases("sigVer", v.set, vector_dir, live):
        stage = "sigVer" + _interface(g)
        case = f"{stage} tcId {t['tcId']}" + (f" ({t['reason']})" if t.get("reason") else "")
        m, sig, pk, ctx = h(t["message"]), h(t["signature"]), h(t["pk"]), h(t.get("context", ""))
        if len(pk) != v.pk_len:
            # No entry point takes a public-key length: the library would read
            # past the buffer, so this case is not one its API can be given.
            T.not_applicable(stage, 1, "a public key of the wrong length: the API takes none")
            continue
        verify = {"sigVerInternal": lambda: v.verify_internal(m, sig, pk),
                  "sigVerPure": lambda: v.verify(m, sig, ctx, pk),
                  "sigVerPreHash": lambda: v.verify_prehash(m, sig, ctx, t.get("hashAlg", ""),
                                                            pk)}[stage]
        ok, got = _call(T, stage, case, verify)
        if ok:
            want = _passed(ref["testPassed"])
            T.rec(stage, got == want, case, f"verdict {got}, NIST says {want}")

    _edges(T, v, key)
    return T


def _refusal(T, stage, case, make, valid, call):
    """One refusal that could have failed: `make` builds a signature that one
    way of getting the check wrong would accept, `valid` confirms the library
    accepts it where it does belong (None: no entry point to confirm it
    with), and `call`, the call under test, must refuse it."""
    def attempt():
        sig = make()
        if sig is None:
            return "refused to make the test signature"
        if valid is not None and valid(sig) is not True:
            return "rejected its own test signature where it is valid"
        return "" if call(sig) is False else "accepted it"
    ok, why = _call(T, stage, case, attempt)
    if ok:
        T.rec(stage, not why, case, why)


# Checks per edge stage, for a parameter set with no NIST key to run them with.
_EDGE_COUNTS = {"contextLength": 7, "unknownPreHash": 8}


def _edges(T, v, key):
    if key is None:
        for stage, count in _EDGE_COUNTS.items():
            T.not_applicable(stage, count, "no NIST key pair for this parameter set")
    else:
        _refusals(T, v, key)
    _prehash_round_trips(T, v, key)
    _limits(T, v)


def _prehash_round_trips(T, v, key):
    """preHashVerify (see the module docstring): each approved pre-hash
    function's verifier accepts a signature the library made with it."""
    if key is None:
        T.not_applicable("preHashVerify", len(PREHASHES),
                         "no NIST key pair for this parameter set")
        return
    sk, pk = key
    m, ctx = b"pq-verify", b"pq-verify pre-hash round trip"
    for ph in PREHASHES:
        case = f"pre-hash round trip with {ph}"

        def trip():
            sig = v.sign_prehash(m, ctx, ph, sk, None)
            if sig is None:
                return "refused to sign"
            return "" if v.verify_prehash(m, sig, ctx, ph, pk) is True else \
                "rejected the signature it made"
        ok, why = _call(T, "preHashVerify", case, trip)
        if ok:
            T.rec("preHashVerify", not why, case, why)


def _refusals(T, v, key):
    sk, pk = key
    m, ctx = b"pq-verify", bytes(256)
    memo = {}

    def once(name, fn):                       # each test signature is made once
        def get():
            if name not in memo:
                memo[name] = fn()
            return memo[name]
        return get

    def internal(msg):                        # (make, valid) for an internal signature
        valid = ((lambda s: v.verify_internal(msg, s, pk)) if v.has("verify_internal")
                 else None)
        return once(msg, lambda: v.sign_internal(msg, sk, None)), valid

    pure_empty = (once("pure", lambda: v.sign(m, b"", sk, None)),
                  lambda s: v.verify(m, s, b"", pk))
    hash_empty = (once("pre-hash", lambda: v.sign_prehash(m, b"", "SHA2-256", sk, None)),
                  lambda s: v.verify_prehash(m, s, b"", "SHA2-256", pk))

    # contextLength: FIPS 205 Algorithms 22-25 refuse a context over 255
    # bytes. Signing must refuse one outright...
    for case, fn in (("pure sign, 256-byte context", lambda: v.sign(m, ctx, sk, None)),
                     ("pre-hash sign, 256-byte context",
                      lambda: v.sign_prehash(m, ctx, "SHA2-256", sk, None))):
        ok, sig = _call(T, "contextLength", case, fn)
        if ok:
            T.rec("contextLength", sig is None, case, "signed it")
    # ...and verification must refuse one whatever signature comes with it.
    pure_long = (once("pure, ctx || M", lambda: v.sign(ctx + m, b"", sk, None)),
                 lambda s: v.verify(ctx + m, s, b"", pk))
    for what, (make, valid) in (
            ("a signature made with an empty context", pure_empty),
            ("a signature over ctx || M with an empty context", pure_long),
            ("an internal signature over M", internal(m))):
        _refusal(T, "contextLength", f"pure verify, 256-byte context, {what}", make, valid,
                 lambda s: v.verify(m, s, ctx, pk))
    digest = _SHA256_OID + _hashlib.sha256(m).digest()
    for what, (make, valid) in (
            ("a signature made with an empty context", hash_empty),
            ("an internal signature over 1 || 0 || ctx || OID || SHA-256(M)",
             internal(b"\x01\x00" + ctx + digest))):
        _refusal(T, "contextLength", f"pre-hash verify, 256-byte context, {what}", make, valid,
                 lambda s: v.verify_prehash(m, s, ctx, "SHA2-256", pk))
    # unknownPreHash: a hash function the library does not know must neither
    # sign nor verify.
    for ph in ("MD5", ""):
        case = f"pre-hash sign with {ph!r}"
        ok, sig = _call(T, "unknownPreHash", case, lambda: v.sign_prehash(m, b"", ph, sk, None))
        if ok:
            T.rec("unknownPreHash", sig is None, case, "signed it")
        for what, (make, valid) in (
                ("a SHA2-256 signature", hash_empty),
                ("an internal signature over 1 || 0", internal(b"\x01\x00")),
                ("an internal signature over the empty message", internal(b""))):
            _refusal(T, "unknownPreHash", f"pre-hash verify with {ph!r}, {what}", make, valid,
                     lambda s: v.verify_prehash(m, s, b"", ph, pk))


def _limits(T, v):
    # rbgFailure: FIPS 205 Algorithm 21 returns an error when the draw fails.
    if v.has("keypair"):
        ok, got = _call(T, "rbgFailure", "failing random bit generator",
                        lambda: v.keypair_rbg(None))
        if ok:
            rc, sk, _pk, draws = got
            T.rec("rbgFailure", rc != 0, "failing random bit generator",
                  f"returned {rc} after the generator failed")
    else:
        T.not_applicable("rbgFailure", 1, "no randomised key-generation entry point")
    # sizes: the sizes the library reports, against FIPS 205 Table 2.
    for case, ok, detail in v.sizes():
        T.rec("sizes", ok, case, detail)


def pqverify_audit_slhdsa(so_path, param_set="SLH-DSA-SHA2-128f", symbols=None, verbose=True,
                          prefix=None, vector_dir=None, live=False):
    """Audit a third-party SLH-DSA library; see the module docstring.

    Returns None when it cannot be audited at all (an ambiguous symbol, no
    parameter-set object, no entry point). Otherwise a dict with 'detail'
    {stage: (p, t)}, 'not_applicable' {stage: (count, reason)}, 'via',
    'failures'.
    """
    from .core import DEGRADED, _vector_label, _SLHDSA_DIRS, _pkg_dir
    v = open_library(so_path, param_set, symbols=symbols, prefix=prefix)
    try:
        if v.ambiguous:
            from .symbols import ambiguity_message
            print(ambiguity_message(v.path, v.ambiguous, _ROLES,
                                    "--slhdsa-symbol ROLE=SYMBOL"))
            DEGRADED["skipped_checks"].append(f"SLH-DSA audit ({param_set})")
            return None
        why = v.unusable_reason()
        if why:
            print(f"  Cannot audit {v.path}: {why} for {param_set}.")
            hint = [e for e in exported_symbols(v.path) if "slh" in e.lower()][:8]
            if hint:
                print(f"    exported: {hint}")
            DEGRADED["skipped_checks"].append(f"SLH-DSA audit ({param_set})")
            return None
        local = vector_dir or (None if live else _os.path.join(_pkg_dir(), "vectors"))
        source = _vector_label(local, *_SLHDSA_DIRS.values())
        if verbose:
            print("=" * 68)
            print(f"  THIRD-PARTY SLH-DSA AUDIT — {param_set} — FIPS 205")
            print(f"  library : {v.name}   (calling convention: {v.abi})")
            print(f"  vectors : {source}")
            print("=" * 68)
        T = run(v, vector_dir, live)
    finally:
        v.close()
    bounds = outside_writes(*v.fn.values())
    if bounds["outside_total"]:
        T.detail["bounds"] = (0, 1)
    p_all = sum(p for p, _ in T.detail.values())
    t_all = sum(t for _, t in T.detail.values())
    na_all = sum(c for c, _ in T.na.values())
    verified = p_all == t_all and t_all > 0
    via = v.via_map()
    if verbose:
        for s in STAGES + EDGE_STAGES:
            if s in T.detail:
                p, t = T.detail[s]
                print(f"  {'PASS' if p == t else 'FAIL'}  {s:15s} {p}/{t}   via {via.get(s)}")
            if s in T.na:
                c, why = T.na[s]
                print(f"  n/a   {s:15s} {c}: {why}")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']} {f['case']}: {f['detail']}")
        print_bounds(bounds)
        print("=" * 68)
        status = "VERIFIED" if verified else ("FINDINGS PRESENT" if t_all else "CANNOT VERIFY")
        print(f"  RESULT: {p_all}/{t_all} — {status}"
              + (f"   ({na_all} not applicable to this API)" if na_all else ""))
        print("  Byte-exact against NIST ACVP. Not a side-channel review.")
        print("=" * 68)
    return {"verified": verified, "passed": p_all, "total": t_all,
            "detail": T.detail, "not_applicable": {k: list(x) for k, x in T.na.items()},
            "not_applicable_total": na_all, "via": via, "abi": v.abi,
            "failures": T.failures, "library": v.path, "vectors": source,
            "standard": "FIPS 205", "param_set": param_set, "bounds": bounds,
            "symbols": v.symbols()}
