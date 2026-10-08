"""Audit a THIRD-PARTY ML-DSA implementation against NIST's ACVP vectors.

The ML-KEM counterpart is pqverify_audit_kem. This drives the vendor's own
compiled code with every pinned NIST ACVP ML-DSA vector for one parameter set
(FIPS 204), and with the pinned Wycheproof ML-DSA edge cases:

    keyGen         NIST seed            -> vendor pk, sk      byte-exact
    sigGen*        NIST sk, M, ctx, rnd -> vendor signature   byte-exact
    sigVer*        NIST pk, M, ctx, sig -> vendor verdict     = NIST testPassed
    sigVerify      Wycheproof verify vectors (malleated hints, bad norms, ...)
    sigGen (edge)  Wycheproof sign vectors, incl. inputs that must be refused
    edgeLength     wrong-length signatures, where the API takes a length

for each interface FIPS 204 defines: internal (Algorithms 7/8), external
pure (Algorithms 2/3), external pre-hash (HashML-DSA, Algorithms 4/5) and
external mu. Each NIST case is sent through the most public entry point the
library has for it -- the one its users call -- and the report names that
entry point per stage. A case no entry point can express is counted as
not applicable, with the reason, and never as a pass.

Randomness. NIST's vectors are seeded. Two kinds of API can be audited
byte-exactly:
  - one that takes the seed or rnd as an argument (keypair_internal,
    signature_internal), and
  - one that draws it from randombytes(), when the library is linked with
    pq-verify's harness (pq_verify/harness/pqv_randombytes.c), which lets
    pq-verify queue NIST's bytes before each call. The harness also reports
    a call that draws more randomness than FIPS 204 calls for, or less.
Never ship a build linked with the harness: it is deterministic by design.

Three calling conventions are recognised, by symbol name:
  pqcrystals    pq-crystals/dilithium ref and PQClean: signatures carry a
                length (size_t *siglen / size_t siglen)
  mldsa-native  pq-code-package/mldsa-native v2 (2.0.0, 2026-08, and
                later): fixed-size signatures, an external-mu flag, a native
                HashML-DSA API
  mldsa-native-v1
                the same API before 2.0.0, as liboqs 0.16 vendors it: every
                signature argument carries its length (size_t *siglen /
                size_t siglen). Told apart by the NIST signed-message entry
                points (_sign, _open) that 2.0.0 removed
  oqs           liboqs's public API, OQS_SIG_ml_dsa_*: the message comes
                first in verify (m, mlen, sig, siglen, pk), and the context
                variants are *_sign_with_ctx_str / *_verify_with_ctx_str.
                Its randomness is supplied through liboqs's own documented
                hook, OQS_randombytes_custom_algorithm, so keyGen and pure
                sigGen are byte-exact against NIST without a special build.
The convention follows the entry points actually bound: liboqs also exports
mldsa-native's own API for each backend, and binding OQS_* symbols with
mldsa-native's argument order would test nothing. A binding that mixes
liboqs's public API with any other entry point is refused.
"""
import ctypes as _ct
import os as _os
import re as _re

# (pk, sk, sig) bytes per FIPS 204 Table 2
DSA_SIZES = {
    'ML-DSA-44': (1312, 2560, 2420),
    'ML-DSA-65': (1952, 4032, 3309),
    'ML-DSA-87': (2592, 4896, 4627),
}
# pq-crystals names parameter sets by the round-3 Dilithium level.
_LEVEL_TOKENS = {'ML-DSA-44': ('44', 'dilithium2'), 'ML-DSA-65': ('65', 'dilithium3'),
                 'ML-DSA-87': ('87', 'dilithium5')}

STAGES = ('keyGen',
          'sigGenInternal', 'sigGenPure', 'sigGenPreHash', 'sigGenMu',
          'sigVerInternal', 'sigVerPure', 'sigVerPreHash', 'sigVerMu')
EDGE_STAGES = ('sigVerify', 'sigGen', 'edgeLength')

# Entry points by role, matched as a suffix of the lowercased symbol.
_ROLES = {
    'keypair_seed':    r'_keypair_internal$',
    'keypair':         r'(?:^|_)keypair$',
    'sign_internal':   r'_signature_internal$',
    'verify_internal': r'_verify_internal$',
    'sign_ctx':        r'(?:_signature_ctx|_sign_with_ctx_str)$',
    'verify_ctx':      r'(?:_verify_ctx|_verify_with_ctx_str)$',
    'sign':            r'(?:_signature|^oqs_sig_ml_dsa_\d+_sign)$',
    'verify':          r'_verify$',
    'sign_mu':         r'_signature_extmu$',
    'verify_mu':       r'_verify_extmu$',
    'sign_prehash':    r'_signature_pre_hash_internal$',
    'verify_prehash':  r'_verify_pre_hash_internal$',
}

# mldsa-native's MLD_PREHASH_* constants (mldsa_native.h). Its own numbering,
# not the OID arc.
_MLDSA_NATIVE_PREHASH = {
    'SHA2-224': 1, 'SHA2-256': 2, 'SHA2-384': 3, 'SHA2-512': 4,
    'SHA2-512/224': 5, 'SHA2-512/256': 6, 'SHA3-224': 7, 'SHA3-256': 8,
    'SHA3-384': 9, 'SHA3-512': 10, 'SHAKE-128': 11, 'SHAKE-256': 12,
}


class NotApplicable(NotImplementedError):
    """The library has no entry point that can express this case."""


class VendorError(Exception):
    """The vendor call returned nonzero (refused the input)."""


def exported_symbols(so_path):
    from .symbols import exported_functions
    return exported_functions(so_path)


def resolve_symbols(exported, param_set, explicit=None, prefix=None):
    """{role: symbol or None}, {role: [candidates]} for ambiguous roles.

    A library exporting several parameter sets (liboqs) names each one, so
    candidates are narrowed to this set's level first. An ambiguous role is
    never guessed: a wrong binding is a false finding against a correct
    library.
    """
    from .symbols import with_prefix
    explicit = explicit or {}
    rng = 'pqv_rng_set' if 'pqv_rng_set' in exported else None   # never prefixed
    exported = with_prefix(exported, prefix)
    tokens = _LEVEL_TOKENS[param_set]
    found, ambiguous = {}, {}
    for role, pat in _ROLES.items():
        if explicit.get(role):
            found[role] = explicit[role]
            continue
        cands = [e for e in exported if _re.search(pat, e.lower())]
        same = [e for e in cands if any(t in e.lower() for t in tokens)]
        if same:
            cands = same
        found[role] = cands[0] if len(cands) == 1 else None
        if len(cands) > 1:
            ambiguous[role] = sorted(cands)
    # PQClean exports crypto_sign_signature (no context) next to
    # crypto_sign_signature_ctx; the context-taking one is FIPS 204's API.
    # An entry point named explicitly is never dropped.
    for ctx_role, plain in (('sign_ctx', 'sign'), ('verify_ctx', 'verify')):
        if found.get(ctx_role) and not explicit.get(plain):
            found[plain] = None
            ambiguous.pop(plain, None)
    found['rng'] = rng
    return found, ambiguous


def bound_abi(sym, exported):
    """The convention of the entry points actually bound. liboqs exports
    its OQS_* API and mldsa-native's beside it; each needs its own argument
    order, and one binding must not mix them."""
    bound = [s for r, s in sym.items() if s and r != 'rng']
    oqs = [s for s in bound if s.startswith('OQS_SIG_')]
    if oqs and len(oqs) != len(bound):
        raise ValueError("the binding mixes liboqs's public API (OQS_SIG_*) with "
                         f"other entry points: {sorted(bound)}; choose one "
                         "implementation (--symbol-prefix)")
    if oqs:
        return 'oqs'
    abi = detect_abi(exported)
    if abi == 'mldsa-native':
        # v1 exports the signed-message API (crypto_sign / _open) beside the
        # rest, in the same namespace; 2.0.0 removed it.
        for role, name in sym.items():
            m = _re.search(_ROLES[role], name.lower()) if name and role in _ROLES else None
            if m and m.start() > 0 and name[:m.start()] + '_open' in exported:
                return 'mldsa-native-v1'
    return abi


def detect_abi(exported):
    low = [e.lower() for e in exported]
    if any('mldsa_native' in e or e.endswith('_signature_extmu') for e in low):
        return 'mldsa-native'
    return 'pqcrystals'


def _buf(b):
    """A const input: ctypes passes bytes as a pointer to their storage."""
    return _ct.c_char_p(bytes(b))


class _HarnessRNG:
    """pq-verify's randombytes harness linked into the library."""

    def __init__(self, lib):
        self.lib = lib
        lib.pqv_rng_overrun.restype = _ct.c_size_t
        lib.pqv_rng_unused.restype = _ct.c_size_t

    def queue(self, data):
        if self.lib.pqv_rng_set(_buf(data), _ct.c_size_t(len(data))) != 0:
            raise RuntimeError("pqv_rng_set refused the seed")

    def overrun(self):
        return self.lib.pqv_rng_overrun()

    def unused(self):
        return self.lib.pqv_rng_unused()


class _OQSRNG:
    """liboqs's documented RNG hook, OQS_randombytes_custom_algorithm: every
    random byte the library draws comes from the queue, and a draw past its
    end (zeros) is counted, as the harness counts it.

    The hook is process-wide and deterministic, so it is installed only when
    the first seed is queued and always handed back (release: liboqs's
    "system" RNG) when the audit ends. Left in place, a caller using liboqs
    in the same process afterwards would draw zeros."""
    _CB = _ct.CFUNCTYPE(None, _ct.POINTER(_ct.c_uint8), _ct.c_size_t)

    def __init__(self, lib):
        self.lib, self.q, self.over, self.installed = lib, b"", 0, False
        self._cb = self._CB(self._draw)          # kept alive with the object

    def release(self):
        if self.installed:
            self.lib.OQS_randombytes_switch_algorithm(_ct.c_char_p(b"system"))
            self.installed = False

    def _draw(self, buf, n):
        take = self.q[:n]
        self.q = self.q[n:]
        self.over += n - len(take)
        _ct.memmove(buf, take + bytes(n - len(take)), n)

    def queue(self, data):
        if not self.installed:
            self.lib.OQS_randombytes_custom_algorithm(self._cb)
            self.installed = True
        self.q, self.over = bytes(data), 0

    def overrun(self):
        return self.over

    def unused(self):
        return len(self.q)


class VendorDSA:
    """One parameter set of a vendor ML-DSA library, behind FIPS 204's
    algorithms. Methods raise NotApplicable when no entry point can express
    the call, VendorError when the library refuses it."""

    def __init__(self, so_path, param_set, abi=None, symbols=None, prefix=None):
        self.path = _os.path.abspath(_os.path.expanduser(so_path))
        if not _os.path.exists(self.path):
            raise FileNotFoundError(self.path)
        if param_set not in DSA_SIZES:
            raise ValueError(f"unknown parameter set {param_set}")
        self.param_set = param_set
        self.pk_n, self.sk_n, self.sig_n = DSA_SIZES[param_set]
        self.lib = _ct.CDLL(self.path)
        exported = exported_symbols(self.path)
        self.sym, self.ambiguous = resolve_symbols(exported, param_set, symbols, prefix)
        self.abi = abi or bound_abi(self.sym, exported)
        if self.abi not in ('pqcrystals', 'mldsa-native', 'mldsa-native-v1', 'oqs'):
            raise ValueError(f"unknown ABI {self.abi!r}")
        self.name = _os.path.basename(self.path)
        self.rng_findings = []
        self._fn = {}
        for role, s in self.sym.items():
            if s and role != 'rng':
                f = getattr(self.lib, s)
                f.restype = _ct.c_int
                self._fn[role] = f
        self._rng = None
        if self.sym.get('rng'):
            self._rng = _HarnessRNG(self.lib)
        elif self.abi == 'oqs' and 'OQS_randombytes_custom_algorithm' in exported:
            self.sym['rng'] = 'OQS_randombytes_custom_algorithm'
            self._rng = _OQSRNG(self.lib)
        if self._rng:
            self._fn['rng'] = self._rng

    def close(self):
        """Hand back anything the audit took over (liboqs's RNG hook)."""
        if isinstance(self._rng, _OQSRNG):
            self._rng.release()

    # ---- capability --------------------------------------------------------

    def has(self, role):
        return role in self._fn

    def via(self, op):
        """The entry point `op` would use, or None."""
        r = self.has
        rng = r('rng')
        table = {
            'keygen': ('keypair' if r('keypair') and rng else
                       'keypair_seed' if r('keypair_seed') else None),
            'sign_internal': 'sign_internal' if r('sign_internal') else None,
            'verify_internal': 'verify_internal' if r('verify_internal') else None,
            'sign_pure': ('sign_ctx' if r('sign_ctx') and rng else
                          'sign' if r('sign') and rng else
                          'sign_internal' if r('sign_internal') else None),
            'verify_pure': ('verify_ctx' if r('verify_ctx') else
                            'verify' if r('verify') else
                            'verify_internal' if r('verify_internal') else None),
            'sign_prehash': ('sign_prehash' if r('sign_prehash') else
                             'sign_internal' if r('sign_internal') else None),
            'verify_prehash': ('verify_prehash' if r('verify_prehash') else
                               'verify_internal' if r('verify_internal') else None),
            'sign_mu': ('sign_mu' if r('sign_mu') and rng else
                        'sign_internal' if r('sign_internal') and self.abi.startswith('mldsa-native')
                        else None),
            'verify_mu': ('verify_mu' if r('verify_mu') else
                          'verify_internal' if r('verify_internal') and self.abi.startswith('mldsa-native')
                          else None),
        }
        return table[op]

    def entry(self, op):
        role = self.via(op)
        return self.sym.get(role) if role else None

    # ---- randomness --------------------------------------------------------

    def _queue(self, data):
        self._rng.queue(data)

    def _drained(self, what, want):
        over = self._rng.overrun()
        left = self._rng.unused()
        if over or left:
            self.rng_findings.append(
                f"{what}: drew {want + over - left} random byte(s), FIPS 204 "
                f"calls for {want}")
            return False
        return True

    # ---- FIPS 204 operations -------------------------------------------------

    def keygen(self, seed):
        role = self.via('keygen')
        if len(seed) != 32:
            raise NotApplicable(f"keypair takes a 32-byte seed; a {len(seed)}-byte "
                                f"one cannot be passed")
        pk = _ct.create_string_buffer(self.pk_n)
        sk = _ct.create_string_buffer(self.sk_n)
        if role == 'keypair':
            self._queue(seed)
            rc = self._fn['keypair'](pk, sk)
            exact = self._drained('keypair', len(seed))
        elif role == 'keypair_seed':
            rc = self._fn['keypair_seed'](pk, sk, _buf(seed))
            exact = True
        else:
            raise NotApplicable("no keypair_internal(seed), and keypair() is not "
                                "linked with pq-verify's randomness harness")
        if rc != 0:
            raise VendorError(f"keypair returned {rc}")
        if not exact:
            raise VendorError("keypair drew the wrong amount of randomness")
        return pk.raw, sk.raw

    def _sig_out(self):
        return _ct.create_string_buffer(self.sig_n), _ct.c_size_t(0)

    def _finish(self, rc, sig, siglen, fixed):
        if rc != 0:
            raise VendorError(f"returned {rc}")
        if not fixed and siglen.value != self.sig_n:
            raise VendorError(f"signature length {siglen.value}, FIPS 204 says "
                              f"{self.sig_n}")
        return sig.raw

    def sign_internal(self, pre, m, rnd, sk):
        """Sign_internal(sk, pre || m, rnd): the caller formats M'."""
        if not self.has('sign_internal'):
            raise NotApplicable("no signature_internal entry point")
        sig, siglen = self._sig_out()
        if self.abi == 'pqcrystals':
            rc = self._fn['sign_internal'](sig, _ct.byref(siglen), _buf(m),
                                           _ct.c_size_t(len(m)), _buf(pre),
                                           _ct.c_size_t(len(pre)), _buf(rnd), _buf(sk))
            return self._finish(rc, sig, siglen, False)
        if self.abi == 'mldsa-native-v1':
            rc = self._fn['sign_internal'](sig, _ct.byref(siglen), _buf(m),
                                           _ct.c_size_t(len(m)), _buf(pre),
                                           _ct.c_size_t(len(pre)), _buf(rnd), _buf(sk),
                                           _ct.c_int(0))
            return self._finish(rc, sig, siglen, False)
        rc = self._fn['sign_internal'](sig, _buf(m), _ct.c_size_t(len(m)), _buf(pre),
                                       _ct.c_size_t(len(pre)), _buf(rnd), _buf(sk),
                                       _ct.c_int(0))
        return self._finish(rc, sig, siglen, True)

    def sign_pure(self, m, ctx, rnd, sk):
        role = self.via('sign_pure')
        if role == 'sign_internal':
            if len(ctx) > 255:
                raise NotApplicable("context over 255 bytes cannot be encoded "
                                    "for signature_internal")
            return self.sign_internal(bytes([0, len(ctx)]) + ctx, m, rnd, sk)
        if role is None:
            raise NotApplicable("no pure signing entry point")
        sig, siglen = self._sig_out()
        if self.abi == 'oqs' and role == 'sign' and ctx:
            raise NotApplicable("OQS_SIG_*_sign takes no context; a non-empty one "
                                "needs *_sign_with_ctx_str")
        self._queue(rnd)
        if self.abi == 'oqs':
            ctx_args = (_buf(ctx), _ct.c_size_t(len(ctx))) if role == 'sign_ctx' else ()
            rc = self._fn[role](sig, _ct.byref(siglen), _buf(m), _ct.c_size_t(len(m)),
                                *ctx_args, _buf(sk))
            fixed = False
        elif self.abi in ('pqcrystals', 'mldsa-native-v1'):
            rc = self._fn[role](sig, _ct.byref(siglen), _buf(m), _ct.c_size_t(len(m)),
                                _buf(ctx), _ct.c_size_t(len(ctx)), _buf(sk))
            fixed = False
        else:
            rc = self._fn[role](sig, _buf(m), _ct.c_size_t(len(m)), _buf(ctx),
                                _ct.c_size_t(len(ctx)), _buf(sk))
            fixed = True
        out = self._finish(rc, sig, siglen, fixed)
        if not self._drained(role, len(rnd)):
            raise VendorError("signing drew the wrong amount of randomness")
        return out

    def sign_prehash(self, ph, oid, hash_alg, ctx, rnd, sk):
        role = self.via('sign_prehash')
        if role == 'sign_internal':
            if len(ctx) > 255:
                raise NotApplicable("context over 255 bytes")
            return self.sign_internal(bytes([1, len(ctx)]) + ctx + oid, ph, rnd, sk)
        if role is None:
            raise NotApplicable("no pre-hash signing entry point")
        alg = _MLDSA_NATIVE_PREHASH.get(hash_alg)
        if alg is None:
            raise NotApplicable(f"{hash_alg} has no MLD_PREHASH constant")
        sig, siglen = self._sig_out()
        v1 = self.abi == 'mldsa-native-v1'
        rc = self._fn[role](sig, *((_ct.byref(siglen),) if v1 else ()), _buf(ph),
                            _ct.c_size_t(len(ph)), _buf(ctx), _ct.c_size_t(len(ctx)),
                            _buf(rnd), _buf(sk), _ct.c_int(alg))
        return self._finish(rc, sig, siglen, not v1)

    def sign_mu(self, mu, rnd, sk):
        role = self.via('sign_mu')
        sig, siglen = self._sig_out()
        v1 = self.abi == 'mldsa-native-v1'
        sl = (_ct.byref(siglen),) if v1 else ()
        if role == 'sign_mu':
            self._queue(rnd)
            rc = self._fn[role](sig, *sl, _buf(mu), _buf(sk))
            out = self._finish(rc, sig, siglen, not v1)
            if not self._drained(role, len(rnd)):
                raise VendorError("signing drew the wrong amount of randomness")
            return out
        if role == 'sign_internal':
            rc = self._fn[role](sig, *sl, _buf(mu), _ct.c_size_t(len(mu)), _buf(b''),
                                _ct.c_size_t(0), _buf(rnd), _buf(sk), _ct.c_int(1))
            return self._finish(rc, sig, siglen, not v1)
        raise NotApplicable("no external-mu signing entry point")

    def _sig_arg(self, sig):
        """A signature argument. A fixed-size API reads sig_n bytes, so a
        signature of another length cannot be passed to it at all."""
        if self.abi == 'mldsa-native' and len(sig) != self.sig_n:
            raise NotApplicable("fixed-size signature argument: a signature of "
                                f"{len(sig)} bytes cannot be passed")
        return _buf(sig)

    def _pk_arg(self, pk):
        if len(pk) != self.pk_n:
            raise NotApplicable(f"fixed-size public key argument: a key of "
                                f"{len(pk)} bytes cannot be passed")
        return _buf(pk)

    def verify_internal(self, pre, m, sig, pk):
        if not self.has('verify_internal'):
            raise NotApplicable("no verify_internal entry point")
        f, s, p = self._fn['verify_internal'], self._sig_arg(sig), self._pk_arg(pk)
        if self.abi == 'pqcrystals':
            rc = f(s, _ct.c_size_t(len(sig)), _buf(m), _ct.c_size_t(len(m)), _buf(pre),
                   _ct.c_size_t(len(pre)), p)
        elif self.abi == 'mldsa-native-v1':
            rc = f(s, _ct.c_size_t(len(sig)), _buf(m), _ct.c_size_t(len(m)), _buf(pre),
                   _ct.c_size_t(len(pre)), p, _ct.c_int(0))
        else:
            rc = f(s, _buf(m), _ct.c_size_t(len(m)), _buf(pre), _ct.c_size_t(len(pre)),
                   p, _ct.c_int(0))
        return rc == 0

    def verify_pure(self, m, ctx, sig, pk):
        role = self.via('verify_pure')
        if role == 'verify_internal':
            if len(ctx) > 255:
                raise NotApplicable("context over 255 bytes")
            return self.verify_internal(bytes([0, len(ctx)]) + ctx, m, sig, pk)
        if role is None:
            raise NotApplicable("no pure verification entry point")
        f, s, p = self._fn[role], self._sig_arg(sig), self._pk_arg(pk)
        if self.abi == 'oqs':
            if role == 'verify' and ctx:
                raise NotApplicable("OQS_SIG_*_verify takes no context; a non-empty "
                                    "one needs *_verify_with_ctx_str")
            ctx_args = (_buf(ctx), _ct.c_size_t(len(ctx))) if role == 'verify_ctx' else ()
            rc = f(_buf(m), _ct.c_size_t(len(m)), s, _ct.c_size_t(len(sig)), *ctx_args, p)
        elif self.abi in ('pqcrystals', 'mldsa-native-v1'):
            rc = f(s, _ct.c_size_t(len(sig)), _buf(m), _ct.c_size_t(len(m)), _buf(ctx),
                   _ct.c_size_t(len(ctx)), p)
        else:
            rc = f(s, _buf(m), _ct.c_size_t(len(m)), _buf(ctx), _ct.c_size_t(len(ctx)), p)
        return rc == 0

    def verify_prehash(self, ph, oid, hash_alg, ctx, sig, pk):
        role = self.via('verify_prehash')
        if role == 'verify_internal':
            if len(ctx) > 255:
                raise NotApplicable("context over 255 bytes")
            return self.verify_internal(bytes([1, len(ctx)]) + ctx + oid, ph, sig, pk)
        if role is None:
            raise NotApplicable("no pre-hash verification entry point")
        alg = _MLDSA_NATIVE_PREHASH.get(hash_alg)
        if alg is None:
            raise NotApplicable(f"{hash_alg} has no MLD_PREHASH constant")
        sl = (_ct.c_size_t(len(sig)),) if self.abi == 'mldsa-native-v1' else ()
        rc = self._fn[role](self._sig_arg(sig), *sl, _buf(ph), _ct.c_size_t(len(ph)),
                            _buf(ctx), _ct.c_size_t(len(ctx)), self._pk_arg(pk),
                            _ct.c_int(alg))
        return rc == 0

    def verify_mu(self, mu, sig, pk):
        role = self.via('verify_mu')
        sl = (_ct.c_size_t(len(sig)),) if self.abi == 'mldsa-native-v1' else ()
        if role == 'verify_mu':
            return self._fn[role](self._sig_arg(sig), *sl, _buf(mu),
                                  self._pk_arg(pk)) == 0
        if role == 'verify_internal':
            return self._fn[role](self._sig_arg(sig), *sl, _buf(mu), _ct.c_size_t(len(mu)),
                                  _buf(b''), _ct.c_size_t(0), self._pk_arg(pk),
                                  _ct.c_int(1)) == 0
        raise NotApplicable("no external-mu verification entry point")

    # ---- the edge-case backend (pq_verify.edge.run_dsa) -------------------

    def verify(self, pk, msg, sig, ctx):
        return self.verify_pure(msg, ctx, sig, pk)

    def sign(self, seed, msg, mu, ctx, rnd):
        pk, sk = self.keygen(seed)
        r = bytes.fromhex(rnd) if rnd is not None else bytes(32)
        if mu is not None and msg is None:
            return pk, self.sign_mu(bytes.fromhex(mu), r, sk)
        return pk, self.sign_pure(bytes.fromhex(msg), ctx, r, sk)


# ─────────────────────────────── the audit ───────────────────────────────

_ROUTES = {   # NIST group -> (stage, operation)
    ('sigGen', 'internal', False): ('sigGenInternal', 'sign_internal'),
    ('sigGen', 'internal', True):  ('sigGenMu', 'sign_mu'),
    ('sigGen', 'pure', None):      ('sigGenPure', 'sign_pure'),
    ('sigGen', 'preHash', None):   ('sigGenPreHash', 'sign_prehash'),
    ('sigVer', 'internal', False): ('sigVerInternal', 'verify_internal'),
    ('sigVer', 'internal', True):  ('sigVerMu', 'verify_mu'),
    ('sigVer', 'pure', None):      ('sigVerPure', 'verify_pure'),
    ('sigVer', 'preHash', None):   ('sigVerPreHash', 'verify_prehash'),
}


def _route(mode, g):
    if g.get('signatureInterface') == 'internal':
        return _ROUTES[(mode, 'internal', bool(g.get('externalMu')))]
    return _ROUTES[(mode, g.get('preHash', 'pure'), None)]


def _passed(v):
    return v if isinstance(v, bool) else str(v).lower() == 'true'


def run_acvp(v, load):
    """NIST's keyGen/sigGen/sigVer for v.param_set. Returns
    (tally {stage: [p, t]}, na {stage: [count, reason]}, failures [...])."""
    from .core import _SLHDSA_PREHASH as PREHASH
    tally, na, failures = {}, {}, []

    def rec(stage, ok, why=None, tc=None):
        p, t = tally.get(stage, (0, 0))
        tally[stage] = (p + int(ok), t + 1)
        if not ok and len(failures) < 50:
            failures.append({'stage': stage, 'tcId': tc, 'detail': why})

    def skip(stage, reason):
        c, _ = na.get(stage, (0, reason))
        na[stage] = (c + 1, reason)

    # keyGen
    p, e = load('ML-DSA-keyGen-FIPS204')
    exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
    for g in p['testGroups']:
        if g.get('parameterSet') != v.param_set:
            continue
        for t in g['tests']:
            ref = exp[str(t['tcId'])]
            try:
                pk, sk = v.keygen(bytes.fromhex(t['seed']))
            except NotApplicable as ex:
                skip('keyGen', str(ex))
                continue
            except VendorError as ex:
                rec('keyGen', False, f"keypair: {ex}", t['tcId'])
                continue
            ok = pk.hex().upper() == ref['pk'].upper() and sk.hex().upper() == ref['sk'].upper()
            rec('keyGen', ok, None if ok else "pk or sk differs from NIST", t['tcId'])

    for mode in ('sigGen', 'sigVer'):
        p, e = load(f'ML-DSA-{mode}-FIPS204')
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        for g in p['testGroups']:
            if g.get('parameterSet') != v.param_set:
                continue
            stage, op = _route(mode, g)
            for t in g['tests']:
                ref = exp[str(t['tcId'])]
                try:
                    ok, why = _one(v, mode, op, g, t, ref, PREHASH)
                except NotApplicable as ex:
                    skip(stage, str(ex))
                    continue
                rec(stage, ok, why, t['tcId'])
    return tally, na, failures


def _one(v, mode, op, g, t, ref, PREHASH):
    h = bytes.fromhex
    ctx = h(t.get('context', ''))
    if mode == 'sigGen':
        rnd = bytes(32) if g.get('deterministic') else h(t['rnd'])
        sk = h(t['sk'])
        try:
            if op == 'sign_internal':
                sig = v.sign_internal(b'', h(t['message']), rnd, sk)
            elif op == 'sign_mu':
                sig = v.sign_mu(h(t['mu']), rnd, sk)
            elif op == 'sign_pure':
                sig = v.sign_pure(h(t['message']), ctx, rnd, sk)
            else:
                arc, ph = PREHASH[t['hashAlg']]
                sig = v.sign_prehash(ph(h(t['message'])),
                                     h('06096086480165030402') + bytes([arc]),
                                     t['hashAlg'], ctx, rnd, sk)
        except VendorError as ex:
            return False, f"{v.entry(op)} {ex}"
        ok = sig.hex().upper() == ref['signature'].upper()
        return ok, None if ok else "signature differs from NIST"
    pk, sig = h(t['pk']), h(t['signature'])
    if op == 'verify_internal':
        got = v.verify_internal(b'', h(t['message']), sig, pk)
    elif op == 'verify_mu':
        got = v.verify_mu(h(t['mu']), sig, pk)
    elif op == 'verify_pure':
        got = v.verify_pure(h(t['message']), ctx, sig, pk)
    else:
        arc, ph = PREHASH[t['hashAlg']]
        got = v.verify_prehash(ph(h(t['message'])), h('06096086480165030402') + bytes([arc]),
                               t['hashAlg'], ctx, sig, pk)
    want = _passed(ref['testPassed'])
    return got == want, None if got == want else (
        f"{'accepted' if got else 'rejected'} a signature NIST marks "
        f"{'valid' if want else 'invalid'}")


def run_accumulated(v, param_set, n, tally, na):
    """CCTV's accumulated keygen + deterministic-signing cases through v
    (VendorDSA, or any object with its keygen / sign_pure / verify_pure).
    Records stage 'accumulated' in tally, or its reason in na."""
    if not n:
        return None
    from . import accumulated as _acc
    try:
        ok, why = _acc.run_dsa(v, param_set, n)
    except NotApplicable as exc:
        na['accumulated'] = (1, f"CCTV accumulated vectors: {exc}")
        return None
    except VendorError as exc:
        ok, why = False, f"refused a valid input: {exc}"
    tally['accumulated'] = (int(ok), 1)
    return {'cases': n, 'ok': ok, 'detail': why,
            'source': _acc.source(param_set, n)}


_OP_OF_STAGE = {
    'keyGen': 'keygen',
    'sigGenInternal': 'sign_internal', 'sigGenPure': 'sign_pure',
    'sigGenPreHash': 'sign_prehash', 'sigGenMu': 'sign_mu',
    'sigVerInternal': 'verify_internal', 'sigVerPure': 'verify_pure',
    'sigVerPreHash': 'verify_prehash', 'sigVerMu': 'verify_mu',
}


def pqverify_audit_dsa(so_path, param_set='ML-DSA-65', abi=None, symbols=None,
                       prompt_dir=None, vector_dir=None, live=False, verbose=True,
                       edge=True, accumulated=10_000, prefix=None):
    """Audit a third-party ML-DSA library end to end; see the module docstring.

    Returns None when the library cannot be audited at all (an ambiguous
    symbol, or no entry point for any stage). Otherwise a dict with
    'detail' {stage: (p, t)}, 'not_applicable' {stage: (count, reason)},
    'via' {stage: symbol}, 'failures', 'rng' findings and 'edge'.
    """
    v = VendorDSA(so_path, param_set, abi=abi, symbols=symbols, prefix=prefix)
    try:
        return _audit_dsa(v, param_set, prompt_dir, vector_dir, live, verbose, edge,
                          accumulated)
    finally:
        v.close()


def _audit_dsa(v, param_set, prompt_dir, vector_dir, live, verbose, edge, accumulated):
    from .core import (DEGRADED, _load_vector_json, _pkg_dir, _vector_label,
                       _ACVP_BASE)
    import json as _j
    if v.ambiguous:
        from .symbols import ambiguity_message
        print(ambiguity_message(v.path, v.ambiguous, _ROLES, "--dsa-symbol ROLE=SYMBOL"))
        DEGRADED['skipped_checks'].append(f'DSA audit ({param_set})')
        return None
    if not any(v.via(op) for op in set(_OP_OF_STAGE.values())):
        print(f"  Cannot audit {v.path}: no ML-DSA entry point found for "
              f"{param_set}.")
        hint = [e for e in exported_symbols(v.path)
                if any(k in e.lower() for k in ('sign', 'keypair', 'verify'))][:8]
        if hint:
            print(f"    exported: {hint}")
        DEGRADED['skipped_checks'].append(f'DSA audit ({param_set})')
        return None

    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _os.path.join(_pkg_dir(), "vectors")
    dirs = ('ML-DSA-keyGen-FIPS204', 'ML-DSA-sigGen-FIPS204', 'ML-DSA-sigVer-FIPS204')

    def load(d):
        if _local:
            base = _os.path.join(_local, d)
            return (_load_vector_json(_os.path.join(base, "prompt.json"), f"{d}/prompt.json"),
                    _load_vector_json(_os.path.join(base, "expectedResults.json"),
                                      f"{d}/expectedResults.json"))
        import urllib.request
        g = lambda f: _j.loads(urllib.request.urlopen(_ACVP_BASE + d + "/" + f,
                                                      timeout=60).read())
        return g("prompt.json"), g("expectedResults.json")

    via = {s: v.entry(op) for s, op in _OP_OF_STAGE.items()}
    if verbose:
        print("=" * 68)
        print(f"  THIRD-PARTY ML-DSA AUDIT — {param_set}")
        print(f"  library : {v.name}   (calling convention: {v.abi})")
        _rng = ("liboqs's OQS_randombytes_custom_algorithm hook: randomised APIs audited"
                if isinstance(v._rng, _OQSRNG) else
                "pqv_randombytes linked: randomised APIs audited" if v.has('rng') else
                "not linked: seed-taking APIs only")
        print(f"  harness : {_rng}")
        print(f"  vectors : {_vector_label(_local, *dirs)}")
        print("=" * 68)

    tally, na, failures = run_acvp(v, load)

    edge_res = None
    if edge:
        from .edge import run_dsa, sources as _edge_sources
        edge_res = run_dsa(v, param_set)
        edge_res['vectors'] = _edge_sources()
        for stage, (p, t) in edge_res['stages'].items():
            tally['edge:' + stage] = (p, t)

    acc_res = run_accumulated(v, param_set, accumulated, tally, na)

    p_all = sum(p for p, _ in tally.values())
    t_all = sum(t for _, t in tally.values())
    na_all = sum(c for c, _ in na.values()) + (edge_res or {}).get('not_applicable', 0)
    verified = p_all == t_all and t_all > 0 and not v.rng_findings
    if verbose:
        for s in STAGES:
            if s in tally:
                p, t = tally[s]
                print(f"  {'PASS' if p == t else 'FAIL'}  {s:15s} {p}/{t}   via {via[s]}")
            if s in na:
                c, why = na[s]
                print(f"  n/a   {s:15s} {c} vector(s): {why}")
        if edge_res is not None:
            print(f"  edge cases: {edge_res['vectors']}")
            for s in EDGE_STAGES:
                if s in edge_res['stages']:
                    p, t = edge_res['stages'][s]
                    print(f"  {'PASS' if p == t else 'FAIL'}  edge:{s:10s} {p}/{t}")
            if edge_res.get('not_applicable'):
                print(f"  n/a   edge        {edge_res['not_applicable']} vector(s) the API "
                      f"cannot express (fixed-size or out-of-range arguments)")
        if acc_res:
            print(f"  {'PASS' if acc_res['ok'] else 'FAIL'}  accumulated     "
                  f"{int(acc_res['ok'])}/1   {acc_res['detail']}")
        elif 'accumulated' in na:
            print(f"  n/a   accumulated     {na['accumulated'][1]}")
        for f in (failures + (edge_res or {}).get('failures', []))[:5]:
            print(f"        ✗ {f.get('stage')} {f.get('tcId') or f.get('case')}: "
                  f"{f.get('detail')}")
        for r in v.rng_findings[:3]:
            print(f"        ✗ randomness: {r}")
        print("=" * 68)
        status = ('VERIFIED' if verified else
                  'FINDINGS PRESENT' if t_all else 'CANNOT VERIFY')
        print(f"  RESULT: {p_all}/{t_all} — {status}"
              + (f"   ({na_all} not applicable to this API)" if na_all else ""))
        print("  This audits the vendor's OWN keygen/sign/verify against NIST's")
        print("  vectors and Wycheproof's edge cases. It is not a side-channel review.")
        print("=" * 68)
    return {'verified': verified, 'passed': p_all, 'total': t_all,
            'detail': tally, 'not_applicable': {k: list(x) for k, x in na.items()},
            'not_applicable_total': na_all, 'via': via, 'abi': v.abi,
            'harness': v.has('rng'), 'failures': failures,
            'rng': list(v.rng_findings), 'edge': edge_res, 'library': v.path,
            'accumulated': acc_res,
            'vectors': _vector_label(_local, *dirs),
            'symbols': {k: s for k, s in v.sym.items() if s}}
