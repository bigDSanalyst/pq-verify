"""
pq_verify.hqc — HQC's error-correcting code, a reference for auditing decoders.

HQC was selected by NIST in March 2025; its standard is not final. Everything
here is its own track ("hqc"), never part of a FIPS 203/204/205 verdict.

Scope: the code layer only -- the concatenation of a Reed-Solomon code over
GF(2^8) (outer) with a duplicated Reed-Muller code RM(1,7) (inner) that HQC's
decryption decodes. Key generation, encryption, sampling and hashing are not
covered. The decoder is audited on its own because a KEM-level test cannot
see it: honest decryptions almost never put more than a couple of errors in
front of the outer decoder, and decapsulation re-encrypts, so a ciphertext
built to reach a corner of the decoder is rejected whatever the decoder did.

    rs_encode(m)        systematic: the k message bytes in the top positions,
                        the parity of x^(n1-k) m(x) mod g(x) below them,
                        g(x) = (x - a)(x - a^2)...(x - a^2delta)
    rs_decode(r)        Berlekamp-Massey, roots over the n1 positions, Forney;
                        None when more than delta symbols are wrong
    rm_encode(c)        each symbol to 128 bits b7 + <b0..b6, j> (j = 0..127),
                        repeated n2/128 times
    rm_decode(w)        maximum likelihood over the 256 codewords: the
                        Walsh-Hadamard transform of the summed copies, the
                        largest |value|, ties to the lowest index -- the rule
                        the submitters' reference implementations follow
    code_encode/decode  the two layers in sequence

Within the outer code's radius (delta symbol errors) and the inner code's
(fewer than 32 * copies bit flips per block) the right answer is forced by the
codes' distances, so the audit compares exact bytes. Beyond the inner radius
the reference decoder is still exact (maximum likelihood, then the tie rule);
beyond the outer radius nothing is specified and only memory safety is checked.

Two code profiles:

    v5     HQC v5.0.0 (2025-08-22), and the 2023-04-30 round-4 submission
           (PQClean): identical code layer -- GF(2^8) mod x^8+x^4+x^3+x^2+1,
           a = x, Reed-Muller bits least-significant first within each byte
    next   the submitters' unreleased next-release branch: GF(2^8) mod
           x^8+x^4+x^3+x+1 with a = x+1 (x alone has order 51 there), and each
           byte of a Reed-Muller codeword stored most-significant bit first

The published generator polynomials and the submitters' own decoder outputs on
pq-verify's vectors are pinned (vectors/HQC_MANIFEST.json); `pq-verify --hqc`
holds this module to both.
"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, "vectors", "HQC_MANIFEST.json")
TRACK_NOTE = ("HQC was selected by NIST in March 2025; its standard is not final. This "
              "is its own track, never part of a FIPS 203/204/205 verdict, and it "
              "covers the error-correcting code only, not the KEM.")

# name: (n1, n2, k, delta) -- Reed-Solomon length, Reed-Muller block length in
# bits (128 x copies), message bytes, Reed-Solomon radius
SETS = {"HQC-1": (46, 384, 16, 15), "HQC-3": (56, 640, 24, 16), "HQC-5": (90, 640, 32, 29)}
ALIASES = {"hqc-1": "HQC-1", "hqc-3": "HQC-3", "hqc-5": "HQC-5",
           "hqc-128": "HQC-1", "hqc-192": "HQC-3", "hqc-256": "HQC-5"}
# profile: (field polynomial, generator a, Reed-Muller bytes stored MSB first)
PROFILES = {"v5": (0x11D, 0x02, False), "next": (0x11B, 0x03, True)}
PROFILE_NOTES = {
    "v5": "HQC v5.0.0 (2025-08-22) code layer, identical in the 2023-04-30 submission",
    "next": "the submitters' unreleased next-release branch (pinned commit)",
}
REV8 = bytes(int(f"{i:08b}"[::-1], 2) for i in range(256))


def set_name(name):
    if name in SETS:
        return name
    if name.lower() in ALIASES:
        return ALIASES[name.lower()]
    raise ValueError(f"unknown HQC parameter set {name!r}; known: {', '.join(SETS)} "
                     f"(or hqc-128/192/256)")


class Field:
    """GF(2^8) by exp/log tables on the profile's generator. A generator that
    does not have order 255 is refused: tables built on it are silently wrong
    (x has order 51 modulo x^8+x^4+x^3+x+1)."""

    def __init__(self, poly, alpha):
        self.poly, self.alpha = poly, alpha
        exp, log, x = [0] * 512, [None] * 256, 1
        for i in range(255):
            if log[x] is not None:
                raise ValueError(f"{alpha:#x} has order {i} modulo {poly:#x}, not 255")
            exp[i], log[x] = x, i
            x = self.slow_mul(x, alpha)
        if x != 1:
            raise ValueError(f"{alpha:#x} does not generate GF(2^8) modulo {poly:#x}")
        for i in range(255, 512):
            exp[i] = exp[i - 255]
        self.exp, self.log = exp, log

    def slow_mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            if a & 0x100:
                a ^= self.poly
            b >>= 1
        return r

    def mul(self, a, b):
        return self.exp[self.log[a] + self.log[b]] if a and b else 0

    def inv(self, a):
        if not a:
            raise ZeroDivisionError("0 has no inverse")
        return self.exp[255 - self.log[a]]

    def det(self, rows):
        """Determinant of a square matrix (Gaussian elimination)."""
        a = [list(r) for r in rows]
        n, d = len(a), 1
        for c in range(n):
            p = next((r for r in range(c, n) if a[r][c]), None)
            if p is None:
                return 0
            a[c], a[p] = a[p], a[c]
            d = self.mul(d, a[c][c])
            ic = self.inv(a[c][c])
            for r in range(c + 1, n):
                if a[r][c]:
                    f = self.mul(a[r][c], ic)
                    a[r] = [x ^ self.mul(f, y) for x, y in zip(a[r], a[c])]
        return d


class Code:
    def __init__(self, name, profile="v5"):
        self.name = set_name(name)
        if profile not in PROFILES:
            raise ValueError(f"unknown HQC profile {profile!r}; known: {', '.join(PROFILES)}")
        self.profile = profile
        self.n1, self.n2, self.k, self.delta = SETS[self.name]
        self.copies = self.n2 // 128
        poly, alpha, self.msb_first = PROFILES[profile]
        self.F = Field(poly, alpha)
        self.g = self.generator()
        self.word_bytes = self.n1 * self.n2 // 8
        # each block's 128 bits as an integer, bit j = codeword position j
        self._cw = [self._rm_bits(b) for b in range(256)]
        self._cw_bytes = [self.block_bytes([c] * self.copies) for c in self._cw]

    # ── Reed-Solomon ────────────────────────────────────────────────────
    def generator(self):
        """g(x) = prod_{i=1..2delta} (x - a^i), coefficients lowest first."""
        g = [1]
        for i in range(1, 2 * self.delta + 1):
            r = self.F.exp[i]
            g = [(g[j - 1] if j else 0) ^ (self.F.mul(r, g[j]) if j < len(g) else 0)
                 for j in range(len(g) + 1)]
        return g

    def rs_encode(self, msg):
        msg = bytes(msg)
        if len(msg) != self.k:
            raise ValueError(f"message is {len(msg)} bytes, not {self.k}")
        r = 2 * self.delta
        p = [0] * r + list(msg)
        for deg in range(self.n1 - 1, r - 1, -1):
            c = p[deg]
            if c:
                for i, gi in enumerate(self.g):
                    p[deg - r + i] ^= self.F.mul(c, gi)
        return bytes(p[:r]) + msg

    def syndromes(self, word):
        F = self.F
        return [_xor_all(F.mul(c, F.exp[(i * j) % 255]) for j, c in enumerate(word))
                for i in range(1, 2 * self.delta + 1)]

    def rs_decode(self, word):
        """The message, or None when no codeword is within delta symbols."""
        F, word = self.F, list(word)
        S = self.syndromes(word)
        if not any(S):
            return bytes(word[2 * self.delta:])
        C, B, L, m, b = [1], [1], 0, 1, 1
        for n in range(2 * self.delta):
            d = S[n]
            for i in range(1, L + 1):
                if i < len(C):
                    d ^= F.mul(C[i], S[n - i])
            if d == 0:
                m += 1
                continue
            f = F.mul(d, F.inv(b))
            T = C[:]
            C = C + [0] * max(0, len(B) + m - len(C))
            for i, bi in enumerate(B):
                C[i + m] ^= F.mul(f, bi)
            if 2 * L <= n:
                L, B, b, m = n + 1 - L, T, d, 1
            else:
                m += 1
        C = C[:L + 1]
        if L > self.delta:
            return None
        roots = [p for p in range(self.n1) if _poly_eval(F, C, F.exp[(255 - p) % 255]) == 0]
        if len(roots) != L:
            return None
        omega = [0] * (2 * self.delta)
        for i, s in enumerate(S):
            for j, c in enumerate(C):
                if i + j < len(omega):
                    omega[i + j] ^= F.mul(s, c)
        deriv = [C[i] if i % 2 else 0 for i in range(1, len(C))]
        for p in roots:
            xi = F.exp[(255 - p) % 255]
            den = _poly_eval(F, deriv, xi)
            if not den:
                return None
            word[p] ^= F.mul(_poly_eval(F, omega, xi), F.inv(den))
        if any(self.syndromes(word)):
            return None
        return bytes(word[2 * self.delta:])

    # ── Reed-Muller ─────────────────────────────────────────────────────
    @staticmethod
    def _rm_bits(b):
        u, top = b & 0x7F, b >> 7
        return sum((top ^ (bin(u & j).count("1") & 1)) << j for j in range(128))

    def block_bytes(self, copies):
        """A block's copies (128-bit integers, bit j = position j) as stored."""
        out = b"".join(c.to_bytes(16, "little") for c in copies)
        return out.translate(REV8) if self.msb_first else out

    def block_copies(self, raw):
        if self.msb_first:
            raw = raw.translate(REV8)
        return [int.from_bytes(raw[16 * c:16 * c + 16], "little") for c in range(self.copies)]

    def codeword(self, b):
        return self._cw[b]

    def rm_encode(self, symbols):
        symbols = bytes(symbols)
        if len(symbols) != self.n1:
            raise ValueError(f"{len(symbols)} symbols, not {self.n1}")
        return b"".join(self._cw_bytes[s] for s in symbols)

    def correlations(self, copies):
        """Y[u] = sum over copies and positions of (-1)^(bit + <u, j>)."""
        y = [0] * 128
        for c in copies:
            for j in range(128):
                y[j] += -1 if (c >> j) & 1 else 1
        h = 1
        while h < 128:
            for i in range(0, 128, 2 * h):
                for j in range(i, i + h):
                    a, b = y[j], y[j + h]
                    y[j], y[j + h] = a + b, a - b
            h *= 2
        return y

    def rm_decode_block(self, copies):
        return _argmax(self.correlations(copies))

    def is_ml(self, copies, b):
        """b's codeword is as close as any (whatever rule breaks ties)."""
        Y = self.correlations(copies)
        return (-1 if b & 0x80 else 1) * Y[b & 0x7F] == max(abs(v) for v in Y)

    def blocks(self, word):
        n = 16 * self.copies
        return [self.block_copies(word[i * n:(i + 1) * n]) for i in range(self.n1)]

    def word(self, blocks):
        return b"".join(self.block_bytes(b) for b in blocks)

    def rm_decode(self, word):
        return bytes(self.rm_decode_block(b) for b in self.blocks(word))

    # ── concatenated ────────────────────────────────────────────────────
    def code_encode(self, msg):
        return self.rm_encode(self.rs_encode(msg))

    def code_decode(self, word):
        return self.rs_decode(self.rm_decode(word))


def _xor_all(it):
    r = 0
    for x in it:
        r ^= x
    return r


def _poly_eval(F, p, x):
    r = 0
    for c in reversed(p):
        r = F.mul(r, x) ^ c
    return r


# ─────────────────────────── built vectors ───────────────────────────

class Stream:
    """Deterministic randomness (SHAKE-256), the same on every Python, so the
    self-check's vectors are the ones the submitters' code was pinned on."""

    def __init__(self, seed):
        self.seed = seed if isinstance(seed, bytes) else str(seed).encode()
        self.buf, self.ctr = b"", 0

    def bytes(self, n):
        while len(self.buf) < n:
            self.buf += hashlib.shake_256(self.seed + self.ctr.to_bytes(8, "big")).digest(4096)
            self.ctr += 1
        out, self.buf = self.buf[:n], self.buf[n:]
        return out

    def below(self, n):
        if n <= 1:
            return 0
        bits = (n - 1).bit_length()
        nb = (bits + 7) // 8
        while True:
            v = int.from_bytes(self.bytes(nb), "big") & ((1 << bits) - 1)
            if v < n:
                return v

    def sample(self, n, k):
        pool = list(range(n))
        for i in range(k):
            j = i + self.below(n - i)
            pool[i], pool[j] = pool[j], pool[i]
        return pool[:k]

    def bits(self, n):
        return int.from_bytes(self.bytes((n + 7) // 8), "little") & ((1 << n) - 1)


def hankel_minor(C, errors, m):
    """det of the m x m leading Hankel matrix of the syndromes of `errors`
    ({position: value}) -- zero exactly when Berlekamp-Massey meets a zero
    discrepancy that a generic error pattern never produces."""
    F = C.F
    S = [_xor_all(F.mul(v, F.exp[(i * p) % 255]) for p, v in errors.items())
         for i in range(1, 2 * m)]
    return F.det([[S[a + b] for b in range(m)] for a in range(m)])


def random_errors(C, s, nu, positions=None):
    pos = positions if positions is not None else s.sample(C.n1, nu)
    return {p: 1 + s.below(255) for p in pos}


def defective_errors(C, s, nu, m, tries=64):
    """nu symbol errors whose m-th leading Hankel minor vanishes (1 <= m < nu).
    The minor is affine in each error value (Cauchy-Binet), so one value is
    solved for: a * e + b = 0."""
    if not 1 <= m < nu:
        raise ValueError("need 1 <= m < nu")
    F = C.F
    for _ in range(tries):
        e = random_errors(C, s, nu)
        j = list(e)[s.below(nu)]
        e[j] = 0
        b = hankel_minor(C, e, m)
        e[j] = 1
        a = hankel_minor(C, e, m) ^ b
        if a and b:
            e[j] = F.mul(b, F.inv(a))
            if hankel_minor(C, e, m) == 0:
                return e
    raise RuntimeError(f"no {nu}-error pattern with a vanishing minor {m} found")


def apply_errors(word, errors):
    w = bytearray(word)
    for p, v in errors.items():
        w[p] ^= v
    return bytes(w)


def flip(C, copies, n, s):
    """Flip n of the block's 128 x copies bits, chosen at random."""
    out = list(copies)
    for q in s.sample(128 * C.copies, n):
        out[q // 128] ^= 1 << (q % 128)
    return out


def between(C, a, b, k, s):
    """A block k bit flips from a's codeword, all of them towards b's (the two
    differ in 64 x copies places): distance k to a, 64 x copies - k to b."""
    ca, cb = C.codeword(a), C.codeword(b)
    diff = [(c, j) for c in range(C.copies) for j in range(128) if (ca ^ cb) >> j & 1]
    out = [ca] * C.copies
    for i in s.sample(len(diff), k):
        c, j = diff[i]
        out[c] ^= 1 << j
    return out


def inversion_word():
    """f(j) = Tr(j^-1) over GF(2^7): nonlinearity 54, its nearest codewords
    tied 14 ways -- a stress for the tie rule."""
    def mul(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            if a & 0x80:
                a ^= 0x83
            b >>= 1
        return r

    def power(a, e):
        r = 1
        while e:
            if e & 1:
                r = mul(r, a)
            a = mul(a, a)
            e >>= 1
        return r

    def trace(x):
        t, y = 0, x
        for _ in range(7):
            t ^= y
            y = mul(y, y)
        return t & 1

    return sum(trace(power(j, 126) if j else 0) << j for j in range(128))


def _pick_pair(s, low_first):
    """Two distinct symbols with different low 7 bits; when low_first the
    first has the lower index."""
    while True:
        a, b = s.below(256), s.below(256)
        if (a & 0x7F) != (b & 0x7F) and ((a & 0x7F) < (b & 0x7F)) == low_first:
            return a, b


def rm_cases(C, s):
    """[(label, copies)] -- inner-code blocks, the right answer from the
    reference (exact maximum likelihood, ties to the lowest index)."""
    M, cases = C.copies, []
    for b in range(256):
        cases.append((f"codeword {b:#04x}", [C.codeword(b)] * M))
    for i in range(C.n1):
        w = s.below(32 * M)
        cases.append((f"{w} flips (radius {32 * M - 1})", flip(C, [C.codeword(s.below(256))] * M, w, s)))
    # between two codewords, nearer the first: every distance up to the radius,
    # with the nearer codeword's index above and below the other's
    for k in (32 * M - 1, 32 * M - 8, 24 * M, 16 * M, 8 * M):
        for low_first in (False, True, False, True):
            a, b = _pick_pair(s, low_first)
            cases.append((f"{k} flips from {a:#04x} towards {b:#04x}", between(C, a, b, k, s)))
    # equidistant from two codewords: a tie
    for a, b in ((0x00, 0x7F), (0x80, 0x01), (0x7F, 0x80)):
        cases.append((f"tie {a:#04x}/{b:#04x}", between(C, a, b, 32 * M, s)))
    for _ in range(9):
        a, b = _pick_pair(s, s.below(2) == 0)
        cases.append((f"tie {a:#04x}/{b:#04x}", between(C, a, b, 32 * M, s)))
    inv = inversion_word()
    for label, w in (("inversion word", inv), ("inversion word, complemented", inv ^ ((1 << 128) - 1)),
                     ("inversion word + a codeword", inv ^ C.codeword(s.below(256))),
                     ("inversion word + a codeword", inv ^ C.codeword(s.below(256)))):
        cases.append((f"{label} (many-way tie)", [w] * M))
    # one exact copy of b against noisy copies of a: the maximum-likelihood
    # answer is b, a decoder that skips that copy answers a
    for c in range(M):
        for _ in range(2):
            cases.append((f"copy {c} decides", _copy_decides(C, c, s)))
    for _ in range(C.n1):
        cases.append(("random block", [s.bits(128) for _ in range(M)]))
    return cases


def _copy_decides(C, c, s):
    M = C.copies
    w = 44 if M == 3 else 56
    while True:
        a, b = s.below(256), s.below(256)
        if (a ^ b) & 0x7F == 0:
            continue
        blk = [_flip_one(C.codeword(a), w, s) for _ in range(M)]
        blk[c] = C.codeword(b)
        others = blk[:c] + blk[c + 1:]       # what a decoder skipping copy c sees
        if C.rm_decode_block(blk) == b and _argmax(C.correlations(others)) != b:
            return blk


def _flip_one(cw, w, s):
    for j in s.sample(128, w):
        cw ^= 1 << j
    return cw


def _argmax(Y):
    best = max(abs(v) for v in Y)
    u = next(i for i, v in enumerate(Y) if abs(v) == best)
    return u | (0x80 if Y[u] < 0 else 0)


def rs_cases(C, s):
    """[(label, errors)] -- outer-code error patterns; within delta the
    decoder must return the message."""
    d, out = C.delta, [("no errors", {})]
    for nu in (1, 2, d - 1, d):
        for _ in range(2):
            out.append((f"{nu} errors", random_errors(C, s, nu)))
    out.append((f"{d} errors in the parity part", random_errors(C, s, d, list(range(d)))))
    out.append((f"{d} errors in the message part",
                random_errors(C, s, d, list(range(C.n1 - d, C.n1)))))
    for nu, ms in ((2, (1,)), (3, (1, 2)), (d, range(1, d))):
        for m in ms:
            out.append((f"{nu} errors, Hankel minor {m} = 0", defective_errors(C, s, nu, m)))
    return out


def beyond_cases(C, s):
    """Patterns past the radius: no answer is specified."""
    return [(f"{C.delta + 1} errors (beyond the radius)", random_errors(C, s, C.delta + 1)),
            (f"{C.n1} errors (every symbol)", random_errors(C, s, C.n1))]


def chunk_blocks(C, cases, s):
    """Pack single-block cases into whole received words (n1 blocks each),
    padding the last with codewords. -> [(word, [labels], expected bytes)]"""
    out = []
    for i in range(0, len(cases), C.n1):
        part = cases[i:i + C.n1]
        while len(part) < C.n1:
            b = s.below(256)
            part.append((f"codeword {b:#04x} (padding)", [C.codeword(b)] * C.copies))
        blocks = [c for _, c in part]
        out.append((C.word(blocks), [lab for lab, _ in part],
                    bytes(C.rm_decode_block(b) for b in blocks)))
    return out


def code_cases(C, s):
    """[(label, word, message)] -- received words for the whole decoder, each
    within both radii, so the message is the only answer."""
    M, out = C.copies, []

    def noisy(sym, budget):
        return [flip(C, [C.codeword(x)] * M, s.below(budget + 1), s) for x in sym]

    for label, errs, inner in (
            ("clean", {}, 0),
            ("inner noise in every block", {}, 32 * M - 1),
            (f"{C.delta} symbol errors through the inner code", random_errors(C, s, C.delta), 0),
            (f"{C.delta} symbol errors and inner noise", random_errors(C, s, C.delta), 32 * M - 1),
            (f"{C.delta} symbol errors, Hankel minor 1 = 0", defective_errors(C, s, C.delta, 1), 16 * M),
            (f"{C.delta} symbol errors, Hankel minor {C.delta // 2} = 0",
             defective_errors(C, s, C.delta, C.delta // 2), 16 * M),
            (f"{C.delta} symbol errors, Hankel minor {C.delta - 1} = 0",
             defective_errors(C, s, C.delta, C.delta - 1), 16 * M)):
        m = s.bytes(C.k)
        sym = apply_errors(C.rs_encode(m), errs)
        out.append((label, C.word(noisy(sym, inner)), m))
    # every block one flip inside the inner radius, all of them aimed at
    # another codeword: still only one answer
    for label, lower in (("every block at the inner radius, towards another codeword", None),
                         ("every block at the inner radius, towards a lower-index codeword", True)):
        m = s.bytes(C.k)
        blocks = []
        for x in C.rs_encode(m):
            while True:
                y = s.below(256)
                if (x ^ y) & 0x7F and (lower is None or (y & 0x7F) < (x & 0x7F) or not x & 0x7F):
                    break
            blocks.append(between(C, x, y, 32 * M - 1, s))
        out.append((label, C.word(blocks), m))
    return out


def suite(C, s):
    """Every input, with the answer a conforming decoder gives."""
    msgs = [bytes(C.k), bytes([0xFF]) * C.k] + [s.bytes(C.k) for _ in range(6)]
    syms = bytes(range(256))
    rm_in = [(syms + bytes(C.n1))[i:i + C.n1] for i in range(0, 256, C.n1)]
    rs = []
    for label, e in rs_cases(C, s):
        m = s.bytes(C.k)
        rs.append((label, apply_errors(C.rs_encode(m), e), m))
    beyond = []
    for label, e in beyond_cases(C, s):
        beyond.append((label, apply_errors(C.rs_encode(s.bytes(C.k)), e), None))
    return {
        "rs_encode": [(m, C.rs_encode(m)) for m in msgs],
        "rm_encode": [(x, C.rm_encode(x)) for x in rm_in],
        "code_encode": [(m, C.code_encode(m)) for m in msgs[:4]],
        "rm_decode": chunk_blocks(C, rm_cases(C, s), s),
        "rs_decode": rs,
        "rs_beyond": beyond,
        "code_decode": code_cases(C, s),
    }


_IO = {"rs_encode": (0, 1), "rm_encode": (0, 1), "code_encode": (0, 1),
       "rm_decode": (0, 2), "rs_decode": (1, 2), "code_decode": (1, 2)}


def suite_digest(cases):
    """sha256 per category over inputs and answers: the pinned fingerprint of
    what the submitters' decoders returned on these inputs."""
    out = {}
    for cat, (i, o) in _IO.items():
        h = hashlib.sha256()
        for item in cases[cat]:
            for part in (item[i], item[o]):
                h.update(len(part).to_bytes(4, "big") + part)
        out[cat] = h.hexdigest()
    return out


SELF_SEED = "pq-verify hqc self-check v1"


def self_suite(name, profile):
    C = Code(name, profile)
    return C, suite(C, Stream(f"{SELF_SEED} {profile} {C.name}"))


# ─────────────────────────── self-check ───────────────────────────

def load_manifest(path=MANIFEST):
    with open(path) as fh:
        return json.load(fh)


def self_check(name, profile, manifest):
    """[(check, ok, detail)] for one set and profile."""
    out = []
    try:
        C, cases = self_suite(name, profile)
    except ValueError as exc:
        return [("field generator has order 255", False, str(exc))]
    poly, alpha, _ = PROFILES[profile]
    out.append((f"{alpha:#x} generates GF(2^8) modulo {poly:#x}", True, ""))
    pub = manifest["published_generator"][profile][C.name]
    out.append(("generator polynomial equals the submitters' RS_POLY_COEFS",
                C.g == pub, "" if C.g == pub else f"computed {C.g[:4]}..., published {pub[:4]}..."))
    pinned = manifest["decoder_outputs"][profile][C.name]
    for cat, digest in suite_digest(cases).items():
        out.append((f"{cat}: answers equal the submitters' code on pq-verify's vectors",
                    digest == pinned.get(cat), "" if digest == pinned.get(cat) else
                    f"{digest[:16]}... vs pinned {str(pinned.get(cat))[:16]}..."))
    # the reference decoders reproduce what was encoded
    bad = [lab for lab, w, m in cases["rs_decode"] if C.rs_decode(w) != m]
    out.append(("rs_decode returns the message within the radius", not bad, ", ".join(bad[:3])))
    bad = [lab for lab, w, m in cases["code_decode"] if C.code_decode(w) != m]
    out.append(("code_decode returns the message within both radii", not bad, ", ".join(bad[:3])))
    return out


def manifest_problems(path=MANIFEST):
    try:
        m = load_manifest(path)
    except (OSError, ValueError) as exc:
        return [f"pinned HQC manifest missing or unreadable: {exc}"]
    out = []
    for key in ("published_generator", "decoder_outputs"):
        for p in PROFILES:
            if set(m.get(key, {}).get(p, {})) != set(SETS):
                out.append(f"the manifest's {key} does not cover every set for profile {p}")
    return out


def sources():
    m = load_manifest()
    return "; ".join(f"{p}: {m['sources'][p]['what']} {m['sources'][p]['commit'][:7]}"
                     for p in PROFILES if p in m["sources"])


def pqverify_hqc(verbose=True, sets=None, profiles=None):
    """The reference against the submitters' published generator polynomials
    and their own decoders' answers on pq-verify's vectors."""
    import time
    t0 = time.time()
    detail, failures = {}, []
    if verbose:
        print("=" * 68)
        print("  HQC code layer — reference self-check — NOT A FIPS STANDARD")
        print("=" * 68)
    problems = manifest_problems()
    detail["pinned manifest covers every set"] = (int(not problems), 1)
    failures += [{"stage": "manifest", "case": p} for p in problems]
    manifest = load_manifest() if not problems else None
    if verbose and manifest:
        print(f"  pinned  : {sources()}")
    for profile in (profiles or PROFILES):
        for name in (sets or SETS):
            if manifest is None:
                break
            t1 = time.time()
            res = self_check(name, profile, manifest)
            ok = sum(1 for _, good, _ in res if good)
            key = f"{set_name(name)} ({profile})"
            detail[key] = (ok, len(res))
            failures += [{"stage": key, "case": f"{c}: {d}".rstrip(": ")}
                         for c, good, d in res if not good]
            if verbose:
                print(f"  {'PASS' if ok == len(res) else 'FAIL'}  {key:16s} {ok}/{len(res)}"
                      f"   ({time.time() - t1:.1f} s)")
    p = sum(a for a, _ in detail.values())
    t = sum(b for _, b in detail.values())
    if verbose:
        for f in failures[:5]:
            print(f"        ✗ {f['stage']}: {f['case']}")
        print("=" * 68)
        print(f"  RESULT: {p}/{t} — {'VERIFIED' if p == t and t else 'FINDINGS PRESENT'}"
              f"   {time.time() - t0:.0f} s")
        print(f"  {TRACK_NOTE}")
        print("=" * 68)
    return {"verified": p == t and t > 0, "passed": p, "total": t, "detail": detail,
            "failures": failures, "vectors": sources() if manifest else None, "track": "hqc",
            "standard": "HQC (selected by NIST; standard not final) — code layer",
            "reference": "pq_verify.hqc"}
