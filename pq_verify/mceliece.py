"""
pq_verify.mceliece — Classic McEliece (round 4), a reference for auditing.

Classic McEliece is not a FIPS standard. It was a NIST round-4 candidate that
NIST did not select (it chose HQC), and it is being standardised by ISO.
Everything here is its own track: never part of a FIPS 203/204/205 verdict,
reported as "classic-mceliece" in every report.

This module is pq-verify's own implementation of the parts an audit needs,
written from the round-4 definitions (the submitters' SUPERCOP-20221025 code
fixes the encodings):

    keygen(delta)   SeededKeyGen: the whole key pair from the 32-byte seed
                    the private key begins with. The private key stores the
                    seed of the attempt that succeeded, so a vendor's key
                    pair is regenerated -- public key included -- from its
                    own private key, with no control over its randomness.
    encode(pk, e)   C = H e for a chosen weight-t error vector
    decode(sk, C)   the Goppa decoder: syndromes (with g^2), Berlekamp-Massey,
                    roots over the support; success only for weight exactly t
                    whose syndrome matches
    decap(sk, C)    K = SHAKE256(1 || e || C) on success, SHAKE256(0 || s || C)
                    otherwise (implicit rejection)

The private key is delta (32) || c (8, the f-variants' pivot set) || g (2t)
|| Benes control bits || s (n/8). The control bits are checked by what they
encode: applied to the identity they must give the permutation keygen derives
(control bits for a permutation are not unique, so their bytes are not
compared). Everything else is compared byte for byte.

Every step is unique given the seed -- the minimal polynomial, the sorted
support, the reduced row echelon form [I | T] and, for the f variants, the
first 32 pivot columns -- so a correct implementation reproduces the vendor's
bytes exactly, whatever elimination order it uses.

Pure Python (exact integers; the native GF(2) engine holds at most 2048
variables and returns solutions, not the reduced matrix, so it is not used
here). The large sets take seconds per key.
"""
import gzip
import hashlib
import json
import os

# name: (m, n, t, F) with F the Goppa-field polynomial's low terms
# {exponent: coefficient} (y^t = sum of them); the field polynomial by m
PARAMS = {
    "mceliece348864":   (12, 3488, 64,  {3: 1, 1: 1, 0: 2}),
    "mceliece460896":   (13, 4608, 96,  {10: 1, 9: 1, 6: 1, 0: 1}),
    "mceliece6688128":  (13, 6688, 128, {7: 1, 2: 1, 1: 1, 0: 1}),
    "mceliece6960119":  (13, 6960, 119, {8: 1, 0: 1}),
    "mceliece8192128":  (13, 8192, 128, {7: 1, 2: 1, 1: 1, 0: 1}),
}
for _s in list(PARAMS):
    PARAMS[_s + "f"] = PARAMS[_s]
SETS = tuple(sorted(PARAMS, key=lambda s: (PARAMS[s][1], s)))
FIELD_POLY = {12: (1 << 12) | (1 << 3) | 1,                          # z^12+z^3+1
              13: (1 << 13) | (1 << 4) | (1 << 3) | (1 << 1) | 1}    # z^13+z^4+z^3+z+1
MU, NU = 32, 64          # the f variants' semi-systematic form

HERE = os.path.dirname(os.path.abspath(__file__))
BUNDLE = os.path.join(HERE, "vectors", "mceliece_kat.json.gz")
MANIFEST = os.path.join(HERE, "vectors", "MCELIECE_MANIFEST.json")
TRACK_NOTE = ("Classic McEliece (round 4) is not a FIPS standard: a NIST round-4 "
              "candidate not selected by NIST, under ISO standardisation. This is "
              "its own track, never part of a FIPS 203/204/205 verdict.")


class Params:
    def __init__(self, name):
        if name not in PARAMS:
            raise ValueError(f"unknown parameter set {name!r}; known: {', '.join(SETS)}")
        self.name = name
        self.m, self.n, self.t, self.F = PARAMS[name]
        self.f = name.endswith("f")
        self.q = 1 << self.m
        self.mt = self.m * self.t
        self.k = self.n - self.mt
        self.row_bytes = (self.k + 7) // 8
        self.synd_bytes = (self.mt + 7) // 8
        self.cond_bytes = (1 << (self.m - 4)) * (2 * self.m - 1)
        self.pk_bytes = self.mt * self.row_bytes
        self.sk_bytes = 40 + 2 * self.t + self.cond_bytes + self.n // 8
        self.ct_bytes = self.synd_bytes
        self.padded = self.mt % 8 != 0 or self.k % 8 != 0
        self._field()

    def _field(self):
        """log/exp tables, with a generator found and checked, not assumed."""
        q, poly = self.q, FIELD_POLY[self.m]

        def mul_slow(a, b):
            r = 0
            while b:
                if b & 1:
                    r ^= a
                b >>= 1
                a <<= 1
                if a & q:
                    a ^= poly
            return r
        for gen in range(2, q):
            exp, x = [0] * (2 * q), 1
            for i in range(q - 1):
                exp[i] = x
                x = mul_slow(x, gen)
                if x == 1 and i < q - 2:
                    break
            else:
                if x == 1:
                    break
        log = [0] * q
        for i in range(q - 1):
            log[exp[i]] = i
        for i in range(q - 1, 2 * q):
            exp[i] = exp[i - (q - 1)]
        self.exp, self.log = exp, log

    # -- GF(2^m) ----------------------------------------------------------
    def mul(self, a, b):
        return 0 if a == 0 or b == 0 else self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        if a == 0:
            raise ZeroDivisionError("inverse of 0 in GF(2^m)")
        return self.exp[(self.q - 1) - self.log[a]]

    def sq(self, a):
        return self.mul(a, a)

    def bitrev(self, a):
        return int(f"{a:0{self.m}b}"[::-1], 2)


# ---------------------------------------------------------------------------
# Key generation
# ---------------------------------------------------------------------------

def _poly_mulmod(P, a, b):
    """a * b in GF(2^m)[y] / F(y), F monic of degree t."""
    t, mul = P.t, P.mul
    prod = [0] * (2 * t - 1)
    for i, ai in enumerate(a):
        if ai:
            la = P.log[ai]
            for j, bj in enumerate(b):
                if bj:
                    prod[i + j] ^= P.exp[la + P.log[bj]]
    for i in range(2 * t - 2, t - 1, -1):
        c = prod[i]
        if c:
            for e, coef in P.F.items():
                prod[i - t + e] ^= mul(c, coef)
    return prod[:t]


def minimal_polynomial(P, beta):
    """g monic of degree t with g(beta) = 0 in GF(2^m)[y]/F, or None if
    beta's minimal polynomial has lower degree."""
    t = P.t
    powers = [[1] + [0] * (t - 1), list(beta)]
    for _ in range(2, t + 1):
        powers.append(_poly_mulmod(P, powers[-1], beta))
    # solve sum_{j<t} g_j beta^j = beta^t: t equations (coefficient i), t unknowns
    rows = [[powers[j][i] for j in range(t)] + [powers[t][i]] for i in range(t)]
    for col in range(t):
        piv = next((r for r in range(col, t) if rows[r][col]), None)
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        iv = P.inv(rows[col][col])
        rows[col] = [P.mul(x, iv) for x in rows[col]]
        pr = rows[col]
        for r in range(t):
            if r != col and rows[r][col]:
                c = rows[r][col]
                lc = P.log[c]
                rows[r] = [x ^ (P.exp[lc + P.log[y]] if y else 0) for x, y in zip(rows[r], pr)]
    return [rows[i][t] for i in range(t)]


def _eval(P, g, x):
    """g (monic, coefficients g_0..g_{t-1}) at x."""
    r = 1
    for c in reversed(g):
        r = P.mul(r, x) ^ c
    return r


def _bits_row(vals, k):
    """The integer whose bit j is bit k of vals[j]."""
    return int(bytes(48 + ((v >> k) & 1) for v in reversed(vals)), 2)


def parity_check(P, g, support):
    """The mt x n matrix H, row i*m + k = bit k of alpha_j^i / g(alpha_j),
    as integers (bit j = column j)."""
    inv = [P.inv(_eval(P, g, a)) for a in support]
    rows = []
    for _ in range(P.t):
        rows.extend(_bits_row(inv, k) for k in range(P.m))
        inv = [P.mul(v, a) for v, a in zip(inv, support)]
    return rows


def _reduce_rows(rows, start, stop):
    """Full reduction with pivot in column r for rows start..stop-1; False if
    a pivot is missing."""
    mt = len(rows)
    for r in range(start, stop):
        bit = 1 << r
        piv = next((k for k in range(r, mt) if rows[k] & bit), None)
        if piv is None:
            return False
        if piv != r:
            rows[r], rows[piv] = rows[piv], rows[r]
        pr = rows[r]
        for k in range(mt):
            if k != r and rows[k] & bit:
                rows[k] ^= pr
    return True


def _swap_bits(x, a, b):
    if ((x >> a) ^ (x >> b)) & 1:
        x ^= (1 << a) | (1 << b)
    return x


def systematic(P, rows, pi):
    """[I | T] in place; for the f variants the semi-systematic form, which
    moves the first 32 pivot columns in [mt-32, mt+32) into place (and the
    permutation with them). Returns (rows, pivot set) or None."""
    mt = P.mt
    if not P.f:
        return (rows, 0xFFFFFFFF) if _reduce_rows(rows, 0, mt) else None
    if not _reduce_rows(rows, 0, mt - MU):
        return None
    base = mt - MU
    sub = [(rows[base + i] >> base) & ((1 << NU) - 1) for i in range(MU)]
    piv = []
    for i in range(MU):
        acc = 0
        for j in range(i, MU):
            acc |= sub[j]
        if acc == 0:
            return None
        s = (acc & -acc).bit_length() - 1          # first column with a 1 left
        piv.append(s)
        if not (sub[i] >> s) & 1:
            j = next(j for j in range(i + 1, MU) if (sub[j] >> s) & 1)
            sub[i] ^= sub[j]
        for j in range(i + 1, MU):
            if (sub[j] >> s) & 1:
                sub[j] ^= sub[i]
    for j, c in enumerate(piv):
        if c != j:
            pi[base + j], pi[base + c] = pi[base + c], pi[base + j]
            for r in range(mt):
                rows[r] = _swap_bits(rows[r], base + j, base + c)
    if not _reduce_rows(rows, base, mt):
        return None
    return rows, sum(1 << c for c in piv)


def public_key(P, rows):
    """T's rows (columns mt..n-1), each packed LSB-first into ceil(k/8) bytes."""
    mt = P.mt
    return b"".join((r >> mt).to_bytes(P.row_bytes, "little") for r in rows)


class KeyPair:
    """Everything keygen derives, for comparison with a vendor's key."""

    def __init__(self, P, delta, c, g, pi, s, pk):
        self.P, self.delta, self.c, self.g, self.pi, self.s, self.pk = (
            P, delta, c, g, pi, s, pk)

    def sk_fields(self):
        P = self.P
        return {"delta": self.delta, "c": self.c.to_bytes(8, "little"),
                "g": b"".join(x.to_bytes(2, "little") for x in self.g), "s": self.s}


def keygen(P, delta, max_attempts=1):
    """SeededKeyGen from the 32-byte seed. A seed taken from a private key
    succeeds on the first attempt (the key stores the seed that did), so
    max_attempts=1 is a check, not a limit: None means the seed cannot have
    produced a key."""
    seed = bytes(delta)
    for _ in range(max_attempts):
        E = hashlib.shake_256(b"\x40" + seed).digest(P.n // 8 + 4 * P.q + 2 * P.t + 32)
        nxt = E[-32:]
        f_off = len(E) - 32 - 2 * P.t
        p_off = f_off - 4 * P.q
        beta = [int.from_bytes(E[f_off + 2 * i:f_off + 2 * i + 2], "little") & (P.q - 1)
                for i in range(P.t)]
        g = minimal_polynomial(P, beta)
        if g is not None:
            a = [int.from_bytes(E[p_off + 4 * i:p_off + 4 * i + 4], "little")
                 for i in range(P.q)]
            if len(set(a)) == P.q:
                pi = [i for _, i in sorted(zip(a, range(P.q)))]
                support = [P.bitrev(pi[i]) for i in range(P.n)]
                rows = parity_check(P, g, support)
                got = systematic(P, rows, pi)
                if got is not None:
                    rows, c = got
                    return KeyPair(P, seed, c, g, pi, E[:P.n // 8], public_key(P, rows))
        seed = nxt
    return None


# ---------------------------------------------------------------------------
# The private key
# ---------------------------------------------------------------------------

def split_sk(P, sk):
    if len(sk) != P.sk_bytes:
        raise ValueError(f"private key is {len(sk)} bytes, {P.name} needs {P.sk_bytes}")
    o = 40 + 2 * P.t
    return {"delta": sk[:32], "c": sk[32:40], "g": sk[40:o],
            "cond": sk[o:o + P.cond_bytes], "s": sk[o + P.cond_bytes:]}


def permutation_from_control_bits(P, cond):
    """Apply the Benes network to the identity: layers of stride 1, 2, ...,
    2^(m-1), 2^(m-2), ..., 1, each n/2 control bits (LSB first), the bit
    deciding whether positions i+j and i+j+stride swap."""
    q, w = P.q, P.m
    p = list(range(q))
    idx = 0
    for s in list(range(w)) + list(range(w - 2, -1, -1)):
        stride = 1 << s
        for i in range(0, q, 2 * stride):
            for j in range(stride):
                if (cond[idx >> 3] >> (idx & 7)) & 1:
                    a, b = i + j, i + j + stride
                    p[a], p[b] = p[b], p[a]
                idx += 1
    return p


def support_from_sk(P, sk):
    f = split_sk(P, sk)
    g = [int.from_bytes(f["g"][2 * i:2 * i + 2], "little") & (P.q - 1) for i in range(P.t)]
    pi = permutation_from_control_bits(P, f["cond"])
    return g, [P.bitrev(pi[i]) for i in range(P.n)], f["s"]


# ---------------------------------------------------------------------------
# Encapsulation with a chosen error vector, decoding, decapsulation
# ---------------------------------------------------------------------------

def e_bytes(P, positions):
    v = 0
    for i in positions:
        v |= 1 << i
    return v.to_bytes(P.n // 8, "little")


def encode(P, pk, e):
    """C = H e with H = [I | T], from the public key; e as n/8 bytes."""
    ev = int.from_bytes(e, "little")
    head, tail = ev & ((1 << P.mt) - 1), ev >> P.mt
    c = head
    for i in range(P.mt):
        row = int.from_bytes(pk[i * P.row_bytes:(i + 1) * P.row_bytes], "little")
        if bin(row & tail).count("1") & 1:
            c ^= 1 << i
    return c.to_bytes(P.synd_bytes, "little")


def padding_zero(P, C):
    return (int.from_bytes(C, "little") >> P.mt) == 0


def _syndromes(P, positions, g, support):
    """S_j = sum over positions of alpha^j / g(alpha)^2, j < 2t (field
    arithmetic inlined: this and root finding are the decoder's hot loops)."""
    exp, log, q1 = P.exp, P.log, P.q - 1
    S = [0] * (2 * P.t)
    for i in positions:
        a = support[i]
        w = P.inv(P.sq(_eval(P, g, a)))
        if a == 0:
            S[0] ^= w                     # 0^0 = 1; every higher power is 0
            continue
        la, lw = log[a], log[w]
        for j in range(2 * P.t):
            S[j] ^= exp[lw]
            lw += la
            if lw >= q1:
                lw -= q1
    return S


def _berlekamp_massey(P, S):
    C, B, L, m, b = [1], [1], 0, 1, 1
    for n in range(len(S)):
        d = S[n]
        for i in range(1, L + 1):
            if i < len(C):
                d ^= P.mul(C[i], S[n - i])
        if d == 0:
            m += 1
            continue
        coef = P.mul(d, P.inv(b))
        T = list(C)
        shifted = [0] * m + [P.mul(coef, x) for x in B]
        if len(shifted) > len(C):
            C = C + [0] * (len(shifted) - len(C))
        for i, x in enumerate(shifted):
            C[i] ^= x
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, T, d, 1
        else:
            m += 1
    return C + [0] * (L + 1 - len(C)), L


def locate(P, sk, C):
    """(error positions the locator's roots give, the syndrome of C): the
    algebra of decoding, before any acceptance check."""
    g, support, _ = support_from_sk(P, sk)
    cv = int.from_bytes(C, "little") & ((1 << P.mt) - 1)
    pos = [i for i in range(P.mt) if (cv >> i) & 1]
    S = _syndromes(P, pos, g, support)
    sigma, L = _berlekamp_massey(P, S)
    if L > P.t:
        return None, S
    rev = list(reversed(sigma[:L + 1]))          # x^L sigma(1/x): roots are the locators
    hi_first = list(reversed(rev))
    exp, log = P.exp, P.log
    err = []
    for i, a in enumerate(support):
        if a == 0:
            r = rev[0]
        else:
            la, r = log[a], 0
            for c in hi_first:
                r = (exp[log[r] + la] if r else 0) ^ c
        if r == 0:
            err.append(i)
    return err, S


def decode(P, sk, C):
    """The error vector e (n/8 bytes) with He = C and weight exactly t, or
    None. The ciphertext's padding bits, if any, are ignored here; decap
    deals with them."""
    err, S = locate(P, sk, C)
    if err is None or len(err) != P.t:
        return None
    g, support, _ = support_from_sk(P, sk)
    if _syndromes(P, err, g, support) != S:
        return None
    return e_bytes(P, err)


def shared_key(b, x, C):
    return hashlib.shake_256(bytes([b]) + x + C).digest(32)


def decap(P, sk, C):
    """(status, key, how): how is 'decoded', 'rejected' (implicit rejection)
    or 'padding' (nonzero padding bits: the submitters' reference refuses)."""
    if not padding_zero(P, C):
        return "refuse", None, "padding"
    e = decode(P, sk, C)
    if e is not None:
        return "ok", shared_key(1, e, C), "decoded"
    return "ok", shared_key(0, split_sk(P, sk)["s"], C), "rejected"


# ---------------------------------------------------------------------------
# Comparing a private key with what its seed derives
# ---------------------------------------------------------------------------

def check_key(P, pk, sk, kp=None):
    """[(name, ok, detail)]: the vendor's (pk, sk) against keygen from the
    seed sk begins with."""
    f = split_sk(P, sk)
    kp = kp or keygen(P, f["delta"])
    if kp is None:
        return [("keygen from the private key's seed", False,
                 "the seed in the private key does not produce a key on its first "
                 "attempt, so it is not the seed this key came from")]
    out = [("public key = regenerated public key", pk == kp.pk,
            "" if pk == kp.pk else f"differs in {_first_diff(pk, kp.pk)}")]
    want = kp.sk_fields()
    for name in ("c", "g", "s"):
        out.append((f"private key {name} = regenerated", f[name] == want[name],
                    "" if f[name] == want[name] else "differs"))
    perm = permutation_from_control_bits(P, f["cond"])
    out.append(("control bits encode the regenerated permutation", perm == kp.pi,
                "" if perm == kp.pi else
                f"{sum(a != b for a, b in zip(perm, kp.pi))} positions differ"))
    return out


def _first_diff(a, b):
    if len(a) != len(b):
        return f"length ({len(a)} vs {len(b)} bytes)"
    i = next(i for i in range(len(a)) if a[i] != b[i])
    return f"byte {i} (row {i // max(1, len(a) // max(1, len(a)))})"


# ---------------------------------------------------------------------------
# Self-check against the pinned KATs
# ---------------------------------------------------------------------------

def load_vectors():
    with gzip.open(BUNDLE, "rt", encoding="utf-8") as fh:
        bundle = json.load(fh)
    with open(MANIFEST) as fh:
        manifest = json.load(fh)
    return bundle, manifest


def kat_text(seed, pk, sk, ct, ss):
    """PQClean's nistkat output, the text its META.yml nistkat-sha256 hashes."""
    def h(b):
        return b.hex().upper()
    return (f"count = 0\nseed = {h(seed)}\npk = {h(pk)}\nsk = {h(sk)}\n"
            f"ct = {h(ct)}\nss = {h(ss)}\n").encode()


def self_check(name, entry, published):
    """[(check, ok, detail)] for one pinned KAT entry: the public key is not
    pinned, so pq-verify's keygen must regenerate it exactly -- the rebuilt KAT
    must hash to the sha256 PQClean publishes."""
    P = Params(name)
    seed, sk, ct, ss = (bytes.fromhex(entry[k]) for k in ("seed", "sk", "ct", "ss"))
    kp = keygen(P, sk[:32])
    if kp is None:
        return [("keygen from the KAT seed", False, "no key on the first attempt")]
    out = [("KAT rebuilt with pq-verify's public key hashes to META.yml's nistkat-sha256",
            hashlib.sha256(kat_text(seed, kp.pk, sk, ct, ss)).hexdigest() == published,
            f"published {published[:16]}...")]
    out.extend(check_key(P, kp.pk, sk, kp))
    e = decode(P, sk, ct)
    out.append(("decode(ct) has weight t", e is not None, ""))
    if e is not None:
        out.append(("encode(pk, e) = ct", encode(P, kp.pk, e) == ct, ""))
        out.append(("decap(ct) = ss", shared_key(1, e, ct) == ss, ""))
    return out


def bundle_problems():
    """The bundle is the file the manifest names, covering every set."""
    out = []
    try:
        with open(MANIFEST) as fh:
            manifest = json.load(fh)
        with open(BUNDLE, "rb") as fh:
            raw = fh.read()
    except OSError as exc:
        return [f"pinned Classic McEliece vectors missing: {exc}"]
    if hashlib.sha256(raw).hexdigest() != manifest.get("bundle_sha256"):
        out.append("mceliece_kat.json.gz does not match MCELIECE_MANIFEST.json")
    if set(manifest.get("published_nistkat_sha256", {})) != set(SETS):
        out.append("the manifest does not publish a KAT hash for every set")
    return out


def sources():
    with open(MANIFEST) as fh:
        s = json.load(fh)["source"]
    return (f"PQClean {s['commit'][:7]} ({s['date']}), {s['implementation']}: NIST KAT "
            f"first records, each matching PQClean's published nistkat-sha256")


def pqverify_mceliece(verbose=True, sets=None):
    """The reference against the pinned KATs, every parameter set (or `sets`).
    The public keys are not pinned: each is regenerated from the private
    key's seed, and the rebuilt KAT must hash to PQClean's published value."""
    import time
    t0 = time.time()
    detail, failures = {}, []
    if verbose:
        print("=" * 68)
        print("  Classic McEliece (round 4) — reference self-check — NOT A FIPS STANDARD")
        print(f"  vectors : {sources()}")
        print("=" * 68)
    problems = bundle_problems()
    detail["pinned vectors match their manifest"] = (int(not problems), 1)
    failures += [{"stage": "pinned vectors", "case": p} for p in problems]
    bundle, manifest = load_vectors()
    for name in (sets or SETS):
        t1 = time.time()
        res = self_check(name, bundle[name], manifest["published_nistkat_sha256"][name])
        ok = sum(1 for _, good, _ in res if good)
        detail[name] = (ok, len(res))
        failures += [{"stage": name, "case": f"{c}: {d}".rstrip(": ")}
                     for c, good, d in res if not good]
        if verbose:
            print(f"  {'PASS' if ok == len(res) else 'FAIL'}  {name:18s} {ok}/{len(res)}"
                  f"   KAT rebuilt with a regenerated public key ({time.time() - t1:.1f} s)")
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
            "failures": failures, "vectors": sources(), "track": "classic-mceliece",
            "standard": "Classic McEliece round 4 (not a FIPS standard)",
            "reference": "pq_verify.mceliece"}
