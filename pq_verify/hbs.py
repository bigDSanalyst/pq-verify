"""Stateful hash-based signatures: LMS/HSS and XMSS/XMSS^MT.

pq-verify's own implementation of

    RFC 8554     Leighton-Micali (LM-OTS, LMS, HSS)
    RFC 8391     XMSS and XMSS^MT (WOTS+)
    SP 800-208   NIST's profile of both: SHA-256/192, SHAKE256/256 and
                 SHAKE256/192 parameter sets, and pseudorandom key generation

written from the specifications for one purpose: to be an independent
reference that vendor output and published vectors are checked against.
Verification is complete for every parameter set either standard defines.
Key generation and signing build the whole Merkle tree (2^h leaves), so they
are practical in pure Python for small trees only; `keygen_cost` says how many
hash calls a tree costs, and the suites use it to decide what runs by default.

CNSA 2.0 requires LMS or XMSS for firmware and software signing now, ahead of
ML-DSA. Neither scheme is safe to use if a one-time key is ever used twice:
that is a property of the signer's state handling, which no vector can show.
"""
import hashlib
import struct

u32 = lambda x: struct.pack('>I', x)
u16 = lambda x: struct.pack('>H', x)
u8 = lambda x: struct.pack('>B', x)


class InvalidSignature(Exception):
    """Raised internally; verify() returns False."""


# ═══════════════════════════════ LMS / LM-OTS ═══════════════════════════════

def _sha256_n(n):
    return lambda data: hashlib.sha256(data).digest()[:n]


def _shake256_n(n):
    return lambda data: hashlib.shake_256(data).digest(n)


# typecode -> (name, hash, n, w)                 RFC 8554 §4.1, SP 800-208 §4
LMOTS = {}
for _base, _fam, _n in ((0x01, 'SHA256', 32), (0x05, 'SHA256', 24),
                        (0x09, 'SHAKE', 32), (0x0D, 'SHAKE', 24)):
    for _k, _w in enumerate((1, 2, 4, 8)):
        LMOTS[_base + _k] = (f"LMOTS_{_fam}_N{_n}_W{_w}",
                             _sha256_n(_n) if _fam == 'SHA256' else _shake256_n(_n),
                             _n, _w)

# typecode -> (name, hash, m, h)                 RFC 8554 §5.1, SP 800-208 §4
LMS = {}
for _base, _fam, _m in ((0x05, 'SHA256', 32), (0x0A, 'SHA256', 24),
                        (0x0F, 'SHAKE', 32), (0x14, 'SHAKE', 24)):
    for _k, _h in enumerate((5, 10, 15, 20, 25)):
        LMS[_base + _k] = (f"LMS_{_fam}_M{_m}_H{_h}",
                           _sha256_n(_m) if _fam == 'SHA256' else _shake256_n(_m),
                           _m, _h)

LMOTS_BY_NAME = {v[0]: k for k, v in LMOTS.items()}
LMS_BY_NAME = {v[0]: k for k, v in LMS.items()}

D_PBLC, D_MESG, D_LEAF, D_INTR = b'\x80\x80', b'\x81\x81', b'\x82\x82', b'\x83\x83'


def lmots_params(n, w):
    """(p, ls) per RFC 8554 Appendix B."""
    u = -(-8 * n // w)
    v = -(-((((1 << w) - 1) * u).bit_length() - 1 + 1) // w)
    return u + v, 16 - v * w


def _coef(s, i, w):
    return ((1 << w) - 1) & (s[i * w // 8] >> (8 - (w * (i % (8 // w)) + w)))


def _cksm(s, n, w, ls):
    total = sum(((1 << w) - 1) - _coef(s, i, w) for i in range(n * 8 // w))
    return u16((total << ls) & 0xFFFF)


def lmots_sig_len(ots_type):
    _, _, n, w = LMOTS[ots_type]
    p, _ = lmots_params(n, w)
    return 4 + n * (p + 1)


def lmots_pk_from_sig(sig, msg, I, q, ots_type):
    """RFC 8554 Algorithm 4b: the candidate OTS public key Kc."""
    if len(sig) < 4 or struct.unpack('>I', sig[:4])[0] != ots_type:
        raise InvalidSignature("LM-OTS typecode mismatch")
    _, H, n, w = LMOTS[ots_type]
    p, ls = lmots_params(n, w)
    if len(sig) != 4 + n * (p + 1):
        raise InvalidSignature("LM-OTS signature length")
    C = sig[4:4 + n]
    Q = H(I + u32(q) + D_MESG + C + msg)
    Qc = Q + _cksm(Q, n, w, ls)
    z = []
    for i in range(p):
        a = _coef(Qc, i, w)
        tmp = sig[4 + n + i * n:4 + n + (i + 1) * n]
        for j in range(a, (1 << w) - 1):
            tmp = H(I + u32(q) + u16(i) + u8(j) + tmp)
        z.append(tmp)
    return H(I + u32(q) + D_PBLC + b''.join(z))


def lms_verify(pk, msg, sig):
    """RFC 8554 Algorithm 6a. True or False; never raises on bad input."""
    try:
        return _lms_verify(pk, msg, sig)
    except (InvalidSignature, KeyError, struct.error, IndexError):
        return False


def _lms_verify(pk, msg, sig):
    if len(pk) < 8:
        raise InvalidSignature("public key too short")
    pubtype, ots_type = struct.unpack('>II', pk[:8])
    _, H, m, h = LMS[pubtype]
    if ots_type not in LMOTS or len(pk) != 24 + m:
        raise InvalidSignature("public key")
    I, T1 = pk[8:24], pk[24:]
    if len(sig) < 8:
        raise InvalidSignature("signature too short")
    q = struct.unpack('>I', sig[:4])[0]
    otssigtype = struct.unpack('>I', sig[4:8])[0]
    if otssigtype != ots_type:
        raise InvalidSignature("LM-OTS type differs from the public key's")
    ol = lmots_sig_len(ots_type)
    if len(sig) < 4 + ol + 4:
        raise InvalidSignature("signature too short")
    ots = sig[4:4 + ol]
    sigtype = struct.unpack('>I', sig[4 + ol:8 + ol])[0]
    if sigtype != pubtype:
        raise InvalidSignature("LMS type differs from the public key's")
    if q >= (1 << h) or len(sig) != 12 + ol + h * m - 4:
        raise InvalidSignature("leaf index or signature length")
    path = sig[8 + ol:]
    Kc = lmots_pk_from_sig(ots, msg, I, q, ots_type)
    node = (1 << h) + q
    tmp = H(I + u32(node) + D_LEAF + Kc)
    for i in range(h):
        auth = path[i * m:(i + 1) * m]
        if node & 1:
            tmp = H(I + u32(node >> 1) + D_INTR + auth + tmp)
        else:
            tmp = H(I + u32(node >> 1) + D_INTR + tmp + auth)
        node >>= 1
    return tmp == T1


def hss_verify(pk, msg, sig):
    """RFC 8554 Algorithm 6 (HSS). True or False."""
    try:
        L = struct.unpack('>I', pk[:4])[0]
        nspk = struct.unpack('>I', sig[:4])[0]
        if nspk + 1 != L or not 1 <= L <= 8:
            return False
        key, rest = pk[4:], sig[4:]
        for _ in range(nspk):
            s_len = _lms_sig_len_from(rest)
            s, rest = rest[:s_len], rest[s_len:]
            p_len = _lms_pk_len_from(rest)
            pub, rest = rest[:p_len], rest[p_len:]
            if not lms_verify(key, pub, s):
                return False
            key = pub
        return lms_verify(key, msg, rest)
    except (struct.error, KeyError, IndexError, InvalidSignature):
        return False


def _lms_sig_len_from(sig):
    ots = struct.unpack('>I', sig[4:8])[0]
    ol = lmots_sig_len(ots)
    t = struct.unpack('>I', sig[4 + ol:8 + ol])[0]
    _, _, m, h = LMS[t]
    return 8 + ol + h * m


def _lms_pk_len_from(pub):
    t = struct.unpack('>I', pub[:4])[0]
    return 24 + LMS[t][2]


def lmots_keygen_x(I, q, i, seed, H):
    """RFC 8554 Appendix A: x_q[i] = H(I || u32str(q) || u16str(i) || u8str(0xff) || SEED)."""
    return H(I + u32(q) + u16(i) + b'\xff' + seed)


def lmots_pubkey(I, q, seed, ots_type):
    _, H, n, w = LMOTS[ots_type]
    p, _ = lmots_params(n, w)
    ys = []
    for i in range(p):
        tmp = lmots_keygen_x(I, q, i, seed, H)
        for j in range((1 << w) - 1):
            tmp = H(I + u32(q) + u16(i) + u8(j) + tmp)
        ys.append(tmp)
    return H(I + u32(q) + D_PBLC + b''.join(ys))


def lmots_sign(msg, I, q, seed, ots_type, C):
    _, H, n, w = LMOTS[ots_type]
    p, ls = lmots_params(n, w)
    Q = H(I + u32(q) + D_MESG + C + msg)
    Qc = Q + _cksm(Q, n, w, ls)
    y = []
    for i in range(p):
        tmp = lmots_keygen_x(I, q, i, seed, H)
        for j in range(_coef(Qc, i, w)):
            tmp = H(I + u32(q) + u16(i) + u8(j) + tmp)
        y.append(tmp)
    return u32(ots_type) + C + b''.join(y)


def lms_keygen_cost(lms_type, ots_type):
    """Hash calls to build the whole tree: what keyGen and signing cost here."""
    _, _, _, h = LMS[lms_type]
    _, _, n, w = LMOTS[ots_type]
    p, _ = lmots_params(n, w)
    return (1 << h) * (p * ((1 << w) - 1) + 2) + (1 << h)


class LMSTree:
    """The whole LMS tree for (seed, I): its public key, and signatures with
    authentication paths. Pseudorandom key generation per SP 800-208 §4.1
    (RFC 8554 Appendix A)."""

    def __init__(self, lms_type, ots_type, seed, I):
        _, H, m, h = LMS[lms_type]
        self.lms_type, self.ots_type, self.seed, self.I = lms_type, ots_type, seed, I
        self.H, self.m, self.h = H, m, h
        leaves = 1 << h
        T = [None] * (2 * leaves)
        for q in range(leaves):
            K = lmots_pubkey(I, q, seed, ots_type)
            T[leaves + q] = H(I + u32(leaves + q) + D_LEAF + K)
        for r in range(leaves - 1, 0, -1):
            T[r] = H(I + u32(r) + D_INTR + T[2 * r] + T[2 * r + 1])
        self.T = T
        self.public_key = u32(lms_type) + u32(ots_type) + I + T[1]

    def sign(self, msg, q, C):
        node = (1 << self.h) + q
        path = []
        for _ in range(self.h):
            path.append(self.T[node ^ 1])
            node >>= 1
        ots = lmots_sign(msg, self.I, q, self.seed, self.ots_type, C)
        return u32(q) + ots + u32(self.lms_type) + b''.join(path)


# ═══════════════════════════════ XMSS / WOTS+ ═══════════════════════════════

def _pad(x, size):
    return x.to_bytes(size, 'big')


class XMSSParams:
    """One XMSS or XMSS^MT parameter set. `pad` is the length of the domain
    separator: n for RFC 8391's functions, 4 for SP 800-208's 192-bit ones."""

    def __init__(self, name, family, n, h, d=1, pad=None):
        self.name, self.family, self.n, self.h, self.d = name, family, n, h, d
        self.pad = pad if pad is not None else n
        self.w, self.log_w = 16, 4
        self.len1 = -(-8 * n // self.log_w)
        self.len2 = ((self.len1 * (self.w - 1)).bit_length() - 1) // self.log_w + 1
        self.len = self.len1 + self.len2
        self.idx_bytes = 4 if d == 1 else -(-h // 8)

    def _hash(self, data):
        if self.family == 'SHA2':
            return (hashlib.sha256(data).digest()[:self.n] if self.n <= 32
                    else hashlib.sha512(data).digest())
        if self.family == 'SHAKE':          # RFC 8391: SHAKE128 (n=32), SHAKE256 (n=64)
            f = hashlib.shake_128 if self.n == 32 else hashlib.shake_256
            return f(data).digest(self.n)
        return hashlib.shake_256(data).digest(self.n)    # SP 800-208 SHAKE256

    def F(self, key, m):         return self._hash(_pad(0, self.pad) + key + m)
    def Hf(self, key, m):        return self._hash(_pad(1, self.pad) + key + m)
    def H_msg(self, key, m):     return self._hash(_pad(2, self.pad) + key + m)
    def PRF(self, key, m):       return self._hash(_pad(3, self.pad) + key + m)
    def PRF_keygen(self, key, m): return self._hash(_pad(4, self.pad) + key + m)


def _xmss_sets():
    sets = {}
    # RFC 8391 Table 4 / 5 (OIDs) and SP 800-208 Tables 10 / 11
    oid = 1
    for fam, n in (('SHA2', 32), ('SHA2', 64), ('SHAKE', 32), ('SHAKE', 64)):
        for h in (10, 16, 20):
            sets[('XMSS', oid)] = XMSSParams(f"XMSS-{fam}_{h}_{n * 8}", fam, n, h)
            oid += 1
    oid = 0x0D
    for fam, n in (('SHA2', 24), ('SHAKE256', 32), ('SHAKE256', 24)):
        for h in (10, 16, 20):
            sets[('XMSS', oid)] = XMSSParams(f"XMSS-{fam}_{h}_{n * 8}", fam, n, h,
                                             pad=4 if n == 24 else n)
            oid += 1
    mt = ((20, 2), (20, 4), (40, 2), (40, 4), (40, 8), (60, 3), (60, 6), (60, 12))
    oid = 1
    for fam, n in (('SHA2', 32), ('SHA2', 64), ('SHAKE', 32), ('SHAKE', 64)):
        for h, d in mt:
            sets[('XMSSMT', oid)] = XMSSParams(f"XMSSMT-{fam}_{h}/{d}_{n * 8}", fam, n, h, d)
            oid += 1
    oid = 0x21
    for fam, n in (('SHA2', 24), ('SHAKE256', 32), ('SHAKE256', 24)):
        for h, d in mt:
            sets[('XMSSMT', oid)] = XMSSParams(f"XMSSMT-{fam}_{h}/{d}_{n * 8}", fam, n, h, d,
                                               pad=4 if n == 24 else n)
            oid += 1
    return sets


XMSS_SETS = _xmss_sets()
XMSS_BY_NAME = {p.name: k for k, p in XMSS_SETS.items()}


class ADRS:
    """RFC 8391 §2.5: 32-byte hash address."""

    def __init__(self):
        self.w = [0] * 8          # layer, tree(hi), tree(lo), type, w4, w5, w6, keyAndMask

    def copy(self):
        a = ADRS()
        a.w = list(self.w)
        return a

    def bytes(self):
        return b''.join(u32(x) for x in self.w)

    def set_layer(self, l):        self.w[0] = l
    def set_tree(self, t):         self.w[1], self.w[2] = t >> 32, t & 0xFFFFFFFF

    def set_type(self, t):
        self.w[3] = t
        self.w[4] = self.w[5] = self.w[6] = self.w[7] = 0

    def set_ots(self, i):          self.w[4] = i
    def set_chain(self, i):        self.w[5] = i
    def set_hash(self, i):         self.w[6] = i
    def set_ltree(self, i):        self.w[4] = i
    def set_height(self, i):       self.w[5] = i
    def set_index(self, i):        self.w[6] = i
    def get_height(self):          return self.w[5]
    def get_index(self):           return self.w[6]
    def set_km(self, i):           self.w[7] = i


def _base_w(x, w_log, out_len):
    out, total, bits, inp = [], 0, 0, 0
    for _ in range(out_len):
        if bits == 0:
            total = x[inp]
            inp += 1
            bits = 8
        bits -= w_log
        out.append((total >> bits) & ((1 << w_log) - 1))
    return out


def _chain(P, X, i, s, seed, adrs):
    tmp = X
    for j in range(i, i + s):
        adrs.set_hash(j)
        adrs.set_km(0)
        key = P.PRF(seed, adrs.bytes())
        adrs.set_km(1)
        bm = P.PRF(seed, adrs.bytes())
        tmp = P.F(key, bytes(a ^ b for a, b in zip(tmp, bm)))
    return tmp


def _msg_digits(P, M):
    msg = _base_w(M, P.log_w, P.len1)
    csum = sum(P.w - 1 - x for x in msg)
    csum <<= (8 - ((P.len2 * P.log_w) % 8)) % 8
    nbytes = -(-(P.len2 * P.log_w) // 8)
    return msg + _base_w(csum.to_bytes(nbytes, 'big'), P.log_w, P.len2)


def wots_pk_from_sig(P, sig, M, seed, adrs):
    digits = _msg_digits(P, M)
    out = []
    for i in range(P.len):
        adrs.set_chain(i)
        out.append(_chain(P, sig[i * P.n:(i + 1) * P.n], digits[i], P.w - 1 - digits[i],
                          seed, adrs))
    return out


def _rand_hash(P, left, right, seed, adrs):
    adrs.set_km(0)
    key = P.PRF(seed, adrs.bytes())
    adrs.set_km(1)
    bm0 = P.PRF(seed, adrs.bytes())
    adrs.set_km(2)
    bm1 = P.PRF(seed, adrs.bytes())
    return P.Hf(key, bytes(a ^ b for a, b in zip(left, bm0)) +
                bytes(a ^ b for a, b in zip(right, bm1)))


def _ltree(P, pk, seed, adrs):
    pk = list(pk)
    l = P.len
    adrs.set_height(0)
    while l > 1:
        for i in range(l // 2):
            adrs.set_index(i)
            pk[i] = _rand_hash(P, pk[2 * i], pk[2 * i + 1], seed, adrs)
        if l % 2:
            pk[l // 2] = pk[l - 1]
        l = -(-l // 2)
        adrs.set_height(adrs.get_height() + 1)
    return pk[0]


def _root_from_sig(P, idx, sig_ots, auth, M, seed, adrs, hh):
    adrs.set_type(0)
    adrs.set_ots(idx)
    pk = wots_pk_from_sig(P, sig_ots, M, seed, adrs)
    adrs.set_type(1)
    adrs.set_ltree(idx)
    node = _ltree(P, pk, seed, adrs)
    adrs.set_type(2)
    adrs.set_index(idx)
    for k in range(hh):
        adrs.set_height(k)
        a = auth[k * P.n:(k + 1) * P.n]
        if (idx >> k) & 1 == 0:
            adrs.set_index(adrs.get_index() // 2)
            node = _rand_hash(P, node, a, seed, adrs)
        else:
            adrs.set_index((adrs.get_index() - 1) // 2)
            node = _rand_hash(P, a, node, seed, adrs)
    return node


def xmss_verify(pk, msg, sig, mt=None):
    """RFC 8391 Algorithms 14 / 17. `pk` begins with the 4-byte OID; `mt`
    selects XMSS^MT (default: XMSS unless the OID only exists for MT)."""
    try:
        return _xmss_verify(pk, msg, sig, mt)
    except (KeyError, IndexError, struct.error, InvalidSignature):
        return False


def _xmss_verify(pk, msg, sig, mt):
    oid = struct.unpack('>I', pk[:4])[0]
    kind = 'XMSSMT' if mt else 'XMSS'
    P = XMSS_SETS[(kind, oid)]
    n, hh = P.n, P.h // P.d
    if len(pk) != 4 + 2 * n:
        raise InvalidSignature("public key length")
    root, seed = pk[4:4 + n], pk[4 + n:]
    want = P.idx_bytes + n + P.d * (P.len * n + hh * n)
    if len(sig) != want:
        raise InvalidSignature("signature length")
    idx = int.from_bytes(sig[:P.idx_bytes], 'big')
    if idx >= (1 << P.h):
        raise InvalidSignature("index out of range")
    r = sig[P.idx_bytes:P.idx_bytes + n]
    M = P.H_msg(r + root + _pad(idx, n), msg)
    off = P.idx_bytes + n
    adrs = ADRS()
    idx_tree, node = idx >> hh, M
    idx_leaf = idx & ((1 << hh) - 1)
    for layer in range(P.d):
        adrs = ADRS()
        adrs.set_layer(layer)
        adrs.set_tree(idx_tree)
        sig_ots = sig[off:off + P.len * n]
        auth = sig[off + P.len * n:off + P.len * n + hh * n]
        off += P.len * n + hh * n
        node = _root_from_sig(P, idx_leaf, sig_ots, auth, node, seed, adrs, hh)
        idx_leaf = idx_tree & ((1 << hh) - 1)
        idx_tree >>= hh
    return node == root


def xmss_keygen_cost(P):
    return (1 << (P.h // P.d)) * (P.len * (P.w - 1) * 3 + P.len * 3) * P.d


class XMSSTree:
    """A whole single-tree XMSS key: public key and signing. WOTS+ secret
    keys from PRF_keygen(S_XMSS, SEED || ADRS) (SP 800-208 §6.2); pass
    legacy=True for the RFC 8391 / original xmss-reference derivation."""

    def __init__(self, P, s_xmss, sk_prf, seed, legacy=False):
        if P.d != 1:
            raise ValueError("XMSSTree builds single-tree XMSS only")
        self.P, self.s, self.sk_prf, self.seed, self.legacy = P, s_xmss, sk_prf, seed, legacy
        n, h = P.n, P.h
        leaves = []
        for i in range(1 << h):
            adrs = ADRS()
            adrs.set_type(0)
            adrs.set_ots(i)
            pk = [_chain(P, self._sk(i, c), 0, P.w - 1, seed, self._ots(i, c))
                  for c in range(P.len)]
            la = ADRS()
            la.set_type(1)
            la.set_ltree(i)
            leaves.append(_ltree(P, pk, seed, la))
        self.levels = [leaves]
        level = leaves
        for k in range(h):
            nxt = []
            for j in range(len(level) // 2):
                a = ADRS()
                a.set_type(2)
                a.set_height(k)
                a.set_index(j)
                nxt.append(_rand_hash(P, level[2 * j], level[2 * j + 1], seed, a))
            self.levels.append(nxt)
            level = nxt
        self.root = level[0]

    def _ots(self, i, c):
        a = ADRS()
        a.set_type(0)
        a.set_ots(i)
        a.set_chain(c)
        return a

    def _sk(self, i, c):
        P = self.P
        if self.legacy:
            # xmss-reference before SP 800-208: a per-leaf seed expanded by index
            leaf_seed = P.PRF(self.s, self._ots(i, 0).bytes()[:28] + bytes(4))
            return P.PRF(leaf_seed, _pad(c, 32))
        a = self._ots(i, c)
        a.set_hash(0)
        a.set_km(0)
        return P.PRF_keygen(self.s, self.seed + a.bytes())

    def public_key(self, oid):
        return u32(oid) + self.root + self.seed

    def sign(self, msg, idx):
        P, n = self.P, self.P.n
        r = P.PRF(self.sk_prf, _pad(idx, 32))
        M = P.H_msg(r + self.root + _pad(idx, n), msg)
        digits = _msg_digits(P, M)
        ots = b''.join(_chain(P, self._sk(idx, c), 0, digits[c], self.seed,
                              self._ots(idx, c)) for c in range(P.len))
        auth = b''.join(self.levels[k][(idx >> k) ^ 1] for k in range(P.h))
        return u32(idx) + r + ots + auth
