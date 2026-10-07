"""
pq_verify.fndsa — FN-DSA (Falcon) signature verification, ahead of FIPS 206.

DRAFT TRACK. FIPS 206 is not published as a final standard. What is checked
here is Falcon as submitted to round 3 of NIST's process (specification
v1.2, the scheme FIPS 206 standardises), against vectors that PQClean's
reference code reproduces byte-for-byte. Nothing in this module contributes
to a FIPS 203/204/205 verdict, and every report labels it as draft.

Verification is the part of Falcon least likely to move between round 3 and
the final FIPS 206: it is integer arithmetic modulo q = 12289 --

    c  = HashToPoint(nonce || message)                SHAKE256, rejection-sampled
    s1 = c - s2 * h   mod (q, x^n + 1)                one NTT product
    accept iff ||(s1, s2)||^2 <= beta^2               the l2 bound

What the final standard may still change is framing: the signature and key
headers, how the message is bound to a context, padding. All of that lives in
the "framing" section below and nowhere else, so the final text needs that
section updated, not the arithmetic.

Signing is not checked here. It depends on floating-point FFT arithmetic and
a discrete Gaussian sampler, which is where Falcon implementations go wrong,
and auditing it needs the final standard's test vectors.
"""

import gzip
import hashlib
import json
import os

Q = 12289
NONCE_LEN = 40

# logn -> (name, n, beta^2, public key bytes, padded signature bytes, max
# compressed signature bytes). beta^2 are the round-3 bounds floor(beta^2).
PARAMS = {
    9:  ("FN-DSA-512",  512,  34034726,  897,  666,  752),
    10: ("FN-DSA-1024", 1024, 70265242, 1793, 1280, 1462),
}
BY_NAME = {v[0]: k for k, v in PARAMS.items()}


class Reject(Exception):
    """The input is not a valid encoding (distinct from a failed norm check)."""


# ---------------------------------------------------------------------------
# Arithmetic modulo q: the negacyclic NTT over Z_q[x]/(x^n + 1)
# ---------------------------------------------------------------------------

def _generator():
    # q - 1 = 2^12 * 3: g generates Z_q^* iff g^((q-1)/2) != 1 and g^((q-1)/3) != 1
    for g in range(2, Q):
        if pow(g, (Q - 1) // 2, Q) != 1 and pow(g, (Q - 1) // 3, Q) != 1:
            return g
    raise AssertionError("unreachable")


GENERATOR = _generator()


def _bitrev(x, bits):
    r = 0
    for _ in range(bits):
        r = (r << 1) | (x & 1)
        x >>= 1
    return r


_ZETAS = {}


def zetas(logn):
    """psi^bitrev(i) for i < n, psi a primitive 2n-th root of unity mod q."""
    if logn not in _ZETAS:
        n = 1 << logn
        psi = pow(GENERATOR, (Q - 1) // (2 * n), Q)
        _ZETAS[logn] = [pow(psi, _bitrev(i, logn), Q) for i in range(n)]
    return _ZETAS[logn]


def ntt_layers(f, logn):
    """Forward negacyclic NTT, returning the state after every layer.

    Cooley-Tukey, bit-reversed twiddles, one layer per halving of the span:
    logn layers, n/2 butterflies each. Returns [f, after layer 0, ...].
    """
    n = 1 << logn
    z = zetas(logn)
    a = [x % Q for x in f]
    states = [list(a)]
    k, span = 1, n // 2
    while span >= 1:
        for start in range(0, n, 2 * span):
            w = z[k]
            k += 1
            for j in range(start, start + span):
                t = w * a[j + span] % Q
                a[j + span] = (a[j] - t) % Q
                a[j] = (a[j] + t) % Q
        states.append(list(a))
        span //= 2
    return states


def layer_butterflies(logn, layer):
    """(j, j + span, zeta) for every butterfly of one layer, in order."""
    n = 1 << logn
    z = zetas(logn)
    span = n >> (layer + 1)
    k = 1 << layer
    out = []
    for start in range(0, n, 2 * span):
        w = z[k]
        k += 1
        out.extend((j, j + span, w) for j in range(start, start + span))
    return out


def ntt(f, logn):
    return ntt_layers(f, logn)[-1]


def intt(fh, logn):
    """Inverse of ntt (Gentleman-Sande, the same twiddles inverted)."""
    n = 1 << logn
    z = zetas(logn)
    a = list(fh)
    k, span = n - 1, 1
    while span < n:
        for start in range(n - 2 * span, -1, -2 * span):
            w = pow(z[k], Q - 2, Q)
            k -= 1
            for j in range(start, start + span):
                u, v = a[j], a[j + span]
                a[j] = (u + v) % Q
                a[j + span] = (u - v) * w % Q
        span *= 2
    n_inv = pow(n, Q - 2, Q)
    return [x * n_inv % Q for x in a]


def poly_mul(a, b, logn):
    """a * b in Z_q[x]/(x^n + 1), through the NTT."""
    ah, bh = ntt(a, logn), ntt(b, logn)
    return intt([x * y % Q for x, y in zip(ah, bh)], logn)


def poly_mul_schoolbook(a, b):
    """a * b in Z_q[x]/(x^n + 1) by definition: the NTT's independent check."""
    n = len(a)
    out = [0] * n
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            k = i + j
            if k < n:
                out[k] += ai * bj
            else:
                out[k - n] -= ai * bj
    return [x % Q for x in out]


# ---------------------------------------------------------------------------
# Encodings (Falcon round 3, section 3.11)
# ---------------------------------------------------------------------------

def decode_public_key(pk):
    """h from header byte 0x00 + logn, then n coefficients of 14 bits each."""
    if not pk:
        raise Reject("empty public key")
    logn = pk[0]
    if pk[0] & 0xF0 or logn not in PARAMS:
        raise Reject(f"public key header 0x{pk[0]:02x} names no FN-DSA parameter set")
    n, want = PARAMS[logn][1], PARAMS[logn][3]
    if len(pk) != want:
        raise Reject(f"public key is {len(pk)} bytes, {PARAMS[logn][0]} needs {want}")
    acc = int.from_bytes(pk[1:], "big")
    bits = 8 * (len(pk) - 1)
    h = []
    for i in range(n):
        w = (acc >> (bits - 14 * (i + 1))) & 0x3FFF
        if w >= Q:
            raise Reject(f"public key coefficient {i} is {w}, not below q = {Q}")
        h.append(w)
    if bits - 14 * n and acc & ((1 << (bits - 14 * n)) - 1):
        raise Reject("public key has nonzero padding bits")
    return logn, h


def decompress(buf, n):
    """s2 from Falcon's compressed encoding; Reject if non-canonical.

    Each coefficient: a sign bit, the low 7 bits of |x|, then |x| >> 7 in
    unary (zeros ended by a one). Rejected, as the reference rejects them:
    |x| > 2047, "-0", running out of input, and nonzero bits after the last
    coefficient in its final byte. Returns (s2, bytes consumed).
    """
    bits = "".join(f"{b:08b}" for b in buf)
    pos, out = 0, []
    for i in range(n):
        if pos + 8 > len(bits):
            raise Reject(f"signature ends inside coefficient {i}")
        sign = bits[pos] == "1"
        low = int(bits[pos + 1:pos + 8], 2)
        pos += 8
        high = 0
        while True:
            if pos >= len(bits):
                raise Reject(f"signature ends inside coefficient {i}")
            if bits[pos] == "1":
                pos += 1
                break
            pos += 1
            high += 1
            if (high << 7) + low > 2047:
                raise Reject(f"coefficient {i} exceeds 2047 in magnitude")
        mag = (high << 7) + low
        if sign and mag == 0:
            raise Reject(f"coefficient {i} is encoded as -0")
        out.append(-mag if sign else mag)
    used = (pos + 7) // 8
    if bits[pos:used * 8].strip("0"):
        raise Reject("nonzero bits after the last coefficient")
    return out, used


def compress(s, slen=None):
    """Inverse of decompress (used to build adversarial inputs)."""
    bits = []
    for x in s:
        m = abs(x)
        bits.append(("1" if x < 0 else "0") + f"{m & 127:07b}" + "0" * (m >> 7) + "1")
    b = "".join(bits)
    b += "0" * (-len(b) % 8)
    raw = bytes(int(b[i:i + 8], 2) for i in range(0, len(b), 8))
    if slen is not None:
        if len(raw) > slen:
            return None
        raw += bytes(slen - len(raw))
    return raw


def hash_to_point(nonce, message, n):
    """c in Z_q^n: SHAKE256(nonce || message), 16-bit samples below 5q kept."""
    xof = hashlib.shake_256(bytes(nonce) + bytes(message))
    need, c, length = n, [], 4 * n
    while True:
        stream = xof.digest(length)
        c.clear()
        for i in range(0, len(stream) - 1, 2):
            w = (stream[i] << 8) | stream[i + 1]
            if w < 5 * Q:
                c.append(w % Q)
                if len(c) == need:
                    return c
        length *= 2


# ---------------------------------------------------------------------------
# Verification core: the arithmetic FIPS 206 keeps from round 3
# ---------------------------------------------------------------------------

def _centre(w):
    return w - Q if w > Q // 2 else w


def verify_core(logn, h, nonce, message, s2):
    """(accepted, squared norm) for decoded inputs."""
    n, beta2 = PARAMS[logn][1], PARAMS[logn][2]
    c = hash_to_point(nonce, message, n)
    s2h = poly_mul([x % Q for x in s2], h, logn)
    s1 = [_centre((ci - pi) % Q) for ci, pi in zip(c, s2h)]
    norm = sum(x * x for x in s1) + sum(x * x for x in s2)
    return norm <= beta2, norm


# ---------------------------------------------------------------------------
# Framing (round 3 / PQClean). The section FIPS 206's final text may change.
# ---------------------------------------------------------------------------

def _body(logn, body):
    """s2 from the signature body after header and nonce: compressed, or
    compressed and zero-padded to the fixed padded length."""
    padded = PARAMS[logn][4] - 1 - NONCE_LEN
    if not body:
        raise Reject("empty signature body")
    s2, used = decompress(body, PARAMS[logn][1])
    if used != len(body):
        if len(body) != padded or any(body[used:]):
            raise Reject("bytes after the compressed signature")
    return s2


def verify(pk, message, sig):
    """Detached signature: 0x30 + logn || nonce (40) || compressed s2.

    Returns (accepted, reason). An encoding the reference rejects is a
    rejection, with the reason.
    """
    try:
        logn, h = decode_public_key(pk)
        if len(sig) < 2 + NONCE_LEN or len(sig) > PARAMS[logn][5]:
            raise Reject(f"signature length {len(sig)} out of range")
        if sig[0] != 0x30 + logn:
            raise Reject(f"signature header 0x{sig[0]:02x}, expected 0x{0x30 + logn:02x}")
        s2 = _body(logn, sig[1 + NONCE_LEN:])
        ok, norm = verify_core(logn, h, sig[1:1 + NONCE_LEN], message, s2)
        return ok, (f"norm^2 {norm} <= {PARAMS[logn][2]}" if ok
                    else f"norm^2 {norm} exceeds {PARAMS[logn][2]}")
    except Reject as exc:
        return False, str(exc)


def open_signed(pk, sm):
    """NIST-API signed message: len (2) || nonce || message || 0x20 + logn || s2.

    Returns (message or None, reason).
    """
    try:
        logn, h = decode_public_key(pk)
        if len(sm) < 3 + NONCE_LEN:
            raise Reject("signed message too short")
        slen = (sm[0] << 8) | sm[1]
        if slen < 2 or slen > len(sm) - NONCE_LEN - 2:
            raise Reject(f"signature length field {slen} out of range")
        mlen = len(sm) - NONCE_LEN - 2 - slen
        if sm[2 + NONCE_LEN + mlen] != 0x20 + logn:
            raise Reject(f"signature header 0x{sm[2 + NONCE_LEN + mlen]:02x}, "
                         f"expected 0x{0x20 + logn:02x}")
        message = sm[2 + NONCE_LEN:2 + NONCE_LEN + mlen]
        s2 = _body(logn, sm[3 + NONCE_LEN + mlen:])
        ok, norm = verify_core(logn, h, sm[2:2 + NONCE_LEN], message, s2)
        if not ok:
            return None, f"norm^2 {norm} exceeds {PARAMS[logn][2]}"
        return bytes(message), f"norm^2 {norm} <= {PARAMS[logn][2]}"
    except Reject as exc:
        return None, str(exc)


# ---------------------------------------------------------------------------
# Pinned vectors
# ---------------------------------------------------------------------------

_VEC = os.path.join(os.path.dirname(__file__), "vectors")
BUNDLE = os.path.join(_VEC, "fndsa_vectors.json.gz")
MANIFEST = os.path.join(_VEC, "FNDSA_MANIFEST.json")


def _parse_rsp(text):
    """NIST .rsp: blank-line separated records of 'key = value'."""
    out, cur = [], {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            if cur:
                out.append(cur)
                cur = {}
            continue
        k, _, v = line.partition(" = ")
        cur[k] = v
    if cur:
        out.append(cur)
    return [r for r in out if "pk" in r]


def load_vectors():
    """[(set name, source label, kind, pk, message, signed blob)].

    kind: 'sm' (NIST-API signed message) or 'sig' (detached signature).
    PQClean's testvectors output repeats (pk, sk, sm, sig) per message; the
    message is the one sm carries, and both signatures are over it.
    """
    with gzip.open(BUNDLE, "rt", encoding="utf-8") as fh:
        bundle = json.load(fh)
    with open(MANIFEST) as fh:
        manifest = json.load(fh)
    out = []
    for key in sorted(bundle):
        meta = manifest["files"][key]
        name, label = meta["set"], meta["label"]
        if meta["kind"] == "nistkat":
            for r in _parse_rsp(bundle[key]):
                out.append((name, label, "sm", bytes.fromhex(r["pk"]),
                            bytes.fromhex(r["msg"]), bytes.fromhex(r["sm"])))
        else:
            lines = bundle[key].split()
            for i in range(0, len(lines), 4):
                pk, _sk, sm, sig = (bytes.fromhex(x) for x in lines[i:i + 4])
                slen = (sm[0] << 8) | sm[1]
                msg = sm[2 + NONCE_LEN:len(sm) - slen]
                out.append((name, label, "sm", pk, msg, sm))
                out.append((name, label, "sig", pk, msg, sig))
    return out


def check_vector(kind, pk, message, blob):
    if kind == "sm":
        got, why = open_signed(pk, blob)
        return got == message, why if got == message or got is None else "message mismatch"
    return verify(pk, message, blob)


# ---------------------------------------------------------------------------
# The suite: pinned vectors, required rejections, the NTT on the native engine
# ---------------------------------------------------------------------------

DRAFT_NOTE = ("DRAFT TRACK: FIPS 206 is not final. Checked against Falcon round 3 "
              "(the scheme FIPS 206 standardises); not part of any FIPS 203/204/205 verdict.")


class _Tally:
    def __init__(self):
        self.detail, self.failures = {}, []

    def rec(self, stage, ok, what=None):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        if not ok and len(self.failures) < 50:
            self.failures.append({"stage": stage, "case": what})

    def totals(self):
        return (sum(p for p, _ in self.detail.values()),
                sum(t for _, t in self.detail.values()))


def bundle_problems():
    """Offline: each pinned file hashes to its manifest digest and to the
    digest PQClean publishes for it (tools/pin_fndsa_vectors.py --check)."""
    with gzip.open(BUNDLE, "rt", encoding="utf-8") as fh:
        bundle = json.load(fh)
    with open(MANIFEST) as fh:
        manifest = json.load(fh)
    published = manifest["sources"]["pqclean"]["published"]
    problems = []
    if set(bundle) != set(manifest["files"]):
        problems.append("bundle and FNDSA_MANIFEST.json list different files")
    for key in sorted(set(bundle) & set(manifest["files"])):
        f = manifest["files"][key]
        got = hashlib.sha256(bundle[key].encode("ascii")).hexdigest()
        if not (got == f["sha256"] == published[f["set"]][f["kind"]]):
            problems.append(f"{key}: does not hash to PQClean's published sha256")
    return problems


def sources():
    with open(MANIFEST) as fh:
        s = json.load(fh)["sources"]["pqclean"]
    return f"PQClean {s['commit'][:7]} ({s['date']}), outputs match META.yml sha256"


def _mutants(pk, message, sig):
    """(what, encoding, pk, message, sig) a verifier must reject, from one
    valid detached signature. encoding: the rejection must come from the
    decoder, before any arithmetic -- for these the norm check would often
    reject too, which would hide a decoder that accepts them."""
    logn = sig[0] - 0x30
    n, padded = PARAMS[logn][1], PARAMS[logn][4]
    body = sig[1 + NONCE_LEN:]
    s2, used = decompress(body, n)
    out = [
        ("message bit flipped", False, pk, bytes([message[0] ^ 1]) + message[1:]
         if message else b"\x00", sig),
        ("nonce bit flipped", False, pk, message, sig[:1] + bytes([sig[1] ^ 0x80]) + sig[2:]),
        ("header names the other parameter set", True, pk, message,
         bytes([0x30 + (19 - logn)]) + sig[1:]),
    ]
    bumped = list(s2)
    bumped[0] += 1 if bumped[0] < 2047 else -1
    out.append(("s2[0] changed by one", False, pk, message,
                sig[:1 + NONCE_LEN] + compress(bumped)))
    if 0 in s2:
        i = s2.index(0)
        enc = compress(s2)
        bits = "".join(f"{b:08b}" for b in enc)
        pos = sum(8 + (abs(x) >> 7) + 1 for x in s2[:i])
        bits = bits[:pos] + "1" + bits[pos + 1:]
        out.append(("a zero coefficient encoded as -0", True, pk, message,
                    sig[:1 + NONCE_LEN] + bytes(int(bits[j:j + 8], 2)
                                               for j in range(0, len(bits), 8))))
    tail = sig[-1]
    spare = (8 - sum(8 + (abs(x) >> 7) + 1 for x in s2) % 8) % 8
    if spare:
        out.append(("nonzero bit after the last coefficient", True, pk, message,
                    sig[:-1] + bytes([tail | 1])))
    out.append(("trailing garbage byte", True, pk, message, sig + b"\x01"))
    if len(sig) < padded:
        out.append(("padded to the fixed length with a nonzero byte", True, pk, message,
                    sig + bytes(padded - len(sig) - 1) + b"\x01"))
    # A coefficient w re-encoded as w + q: the same key mod q, so a decoder
    # that skips the range check verifies the signature anyway. Only the
    # decoder can reject it -- an out-of-range value that also changed the
    # key would be caught by the norm check, hiding a missing range check.
    _, h = decode_public_key(pk)
    i = next(j for j, w in enumerate(h) if w + Q < 1 << 14)
    acc = int.from_bytes(pk[1:], "big") + (Q << (8 * (len(pk) - 1) - 14 * (i + 1)))
    out.append(("public key coefficient >= q (w + q: same key mod q)", True,
                pk[:1] + acc.to_bytes(len(pk) - 1, "big"), message, sig))
    out.append(("public key one byte short", True, pk[:-1], message, sig))
    return out


_ZQ = None


def native_zq():
    """The native Z_q engine (core.ZQ_C, unchanged), built alone. None when
    no compiler is available."""
    global _ZQ
    if _ZQ is None:
        import ctypes
        from . import core
        wd = core._pqv_workdir()
        c_path, so_path = os.path.join(wd, "pqv_zq.c"), os.path.join(wd, "libpqv_zq.so")
        if not os.path.exists(so_path):
            with open(c_path, "w") as fh:
                fh.write(core.ZQ_C)
            proc = core._cc("gcc", "-O3 -shared -fPIC -lm", so_path, c_path)
            if proc.returncode:
                _ZQ = False
                if "zq" not in core.DEGRADED["engines"]:
                    core.DEGRADED["engines"].append("zq")
                core.ENGINE_ERRORS["zq"] = (proc.stderr or proc.stdout or "")[-1500:]
                return None
        lib = ctypes.CDLL(so_path)
        P16 = ctypes.POINTER(ctypes.c_uint16)
        lib.zq_batch_butterfly.argtypes = [P16, P16, P16, P16, P16,
                                           ctypes.POINTER(ctypes.c_uint8),
                                           ctypes.c_int, ctypes.c_uint16]
        lib.zq_batch_butterfly.restype = ctypes.c_int
        _ZQ = lib
    return _ZQ or None


def _native_layers(lib, logn, f):
    """Every butterfly of every layer of the NTT of f, checked by the native
    engine's Montgomery arithmetic. Returns (layers ok, butterflies checked)."""
    import ctypes
    states = ntt_layers(f, logn)
    ok, total = 0, 0
    for layer in range(logn):
        bfs = layer_butterflies(logn, layer)
        src, dst = states[layer], states[layer + 1]
        m = len(bfs)
        A = (ctypes.c_uint16 * m)(*(src[j] for j, _, _ in bfs))
        B = (ctypes.c_uint16 * m)(*(src[k] for _, k, _ in bfs))
        W = (ctypes.c_uint16 * m)(*(w for _, _, w in bfs))
        E = (ctypes.c_uint16 * m)(*(dst[j] for j, _, _ in bfs))
        O = (ctypes.c_uint16 * m)(*(dst[k] for _, k, _ in bfs))
        flags = (ctypes.c_uint8 * m)()
        ok += lib.zq_batch_butterfly(A, B, W, E, O, flags, m, Q) == 0
        total += m
    return ok == logn, total


def pqverify_fndsa(verbose=True):
    """FN-DSA verification on the draft track; see the module docstring."""
    import random
    import time
    T = _Tally()
    t0 = time.time()
    if verbose:
        print("=" * 68)
        print("  FN-DSA (Falcon) verification — FIPS 206 DRAFT TRACK")
        print(f"  vectors : {sources()}")
        print("=" * 68)

    problems = bundle_problems()
    T.rec("pinned vectors match PQClean's published sha256", not problems,
          "; ".join(problems) or None)

    # ---- the pinned vectors verify; their mutants do not
    for name, _label, kind, pk, msg, blob in load_vectors():
        ok, why = check_vector(kind, pk, msg, blob)
        T.rec(f"{name} verify ({'NIST-API signed message' if kind == 'sm' else 'detached'})",
              ok, f"{len(msg)}-byte message: {why}")
        if kind != "sig":
            continue
        logn = blob[0] - 0x30
        padded = PARAMS[logn][4]
        if len(blob) < padded:
            ok, why = verify(pk, msg, blob + bytes(padded - len(blob)))
            T.rec(f"{name} verify (zero-padded to {padded} bytes)", ok, why)
        for what, encoding, mpk, mmsg, msig in _mutants(pk, msg, blob):
            ok, why = verify(mpk, mmsg, msig)
            # a decoder rejection never reports a norm; a norm rejection always does
            right = not ok and (why.startswith("norm^2") != encoding)
            T.rec(f"{name} rejects: {what}", right,
                  f"accepted: {why}" if ok else f"rejected for the wrong reason: {why}"
                  if not right else why)

    # ---- the arithmetic: NTT mod 12289 against the definition, and on the
    # native Z_q engine butterfly by butterfly
    rng = random.Random(206)
    lib = native_zq()
    for logn in sorted(PARAMS):
        name, n = PARAMS[logn][0], PARAMS[logn][1]
        z = zetas(logn)
        psi = z[_bitrev(1, logn)]
        T.rec(f"{name} NTT root", pow(psi, n, Q) == Q - 1 and pow(psi, 2 * n, Q) == 1,
              f"psi = {psi}: psi^n = -1 and psi^2n = 1 mod {Q}")
        a = [rng.randrange(Q) for _ in range(n)]
        b = [rng.randrange(Q) for _ in range(n)]
        T.rec(f"{name} NTT product = negacyclic definition",
              poly_mul(a, b, logn) == poly_mul_schoolbook(a, b), f"n = {n}")
        T.rec(f"{name} inverse NTT", intt(ntt(a, logn), logn) == a, f"n = {n}")
        if lib:
            good, count = _native_layers(lib, logn, a)
            T.rec(f"{name} NTT on the native Z_q engine", good,
                  f"{logn} layers, {count} butterflies")

    p_all, t_all = T.totals()
    if verbose:
        for s, (p, t) in T.detail.items():
            print(f"  {'PASS' if p == t else 'FAIL'}  {s:58s} {p}/{t}")
        if not lib:
            print("  ----  NTT on the native Z_q engine: not run (no working gcc)")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']}: {f['case']}")
        print("=" * 68)
        print(f"  RESULT: {p_all}/{t_all} — "
              f"{'VERIFIED (draft)' if p_all == t_all and t_all else 'FINDINGS PRESENT'}"
              f"   {time.time() - t0:.0f} s")
        print(f"  {DRAFT_NOTE}")
        print("  Signing is not checked: it needs the final standard's vectors.")
        print("=" * 68)
    return {"verified": p_all == t_all and t_all > 0, "passed": p_all, "total": t_all,
            "detail": T.detail, "failures": T.failures, "vectors": sources(),
            "native_engine": bool(lib), "track": "draft", "standard": "FIPS 206 (draft)",
            "reference": "pq_verify.fndsa"}
