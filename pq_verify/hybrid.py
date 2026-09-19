"""
pq_verify.hybrid — RFC 10024 hybrid key-agreement conformance.

Nothing in production negotiates bare ML-KEM. Every deployment that has
actually turned post-quantum TLS on runs a *hybrid* group: X25519MLKEM768 is
what Chrome, Firefox, OpenSSL, BoringSSL and the large CDNs agree on today.

The ML-KEM half of that handshake is covered by ``--acvp`` and ``--audit-kem``.
The *composition* is not — and the composition is where the bugs are, because
RFC 10024 does not use one order. It uses three:

    group                 key share            shared secret
    X25519MLKEM768        ML-KEM ‖ ECDHE       ML-KEM ‖ ECDHE
    SecP256r1MLKEM768     ECDHE  ‖ ML-KEM      ECDHE  ‖ ML-KEM
    SecP384r1MLKEM1024    ECDHE  ‖ ML-KEM      ECDHE  ‖ ML-KEM

The first row is reversed relative to its own name. The RFC says so itself:

    "The group name X25519MLKEM768 does not adhere to the naming convention
     outlined in Section 3.2 of RFC9954.  Specifically, the order of shares
     in the concatenation has been reversed.  This is due to historical
     reasons."

So an implementation can pass every ACVP vector byte-for-byte and still be
wrong, because ACVP never sees the concatenation. The failure is silent in the
worst way: two peers that make the same mistake interoperate happily with each
other and with nobody else, and a peer that got it right sees only a
decrypt_error with no indication of which side is at fault.

This module verifies the part ACVP cannot reach:

    pq-verify --emit-hybrid-prompt X25519MLKEM768 -o q.json
        writes what to supply, with the pinned layout and the RFC citation
        for every field. No secrets are requested that are not needed.

    pq-verify --verify-hybrid transcript.json
        checks the lengths, the component split, the FIPS 203 encapsulation
        key check the RFC makes a MUST, the ECDHE point validity, the X25519
        all-zero check, and — where a private scalar is supplied — recomputes
        the ECDHE shared secret and compares it byte-for-byte at the pinned
        offset.

and, when a check fails, it tests the *other* order explicitly. "Your ECDHE
half is byte-identical to the correct one, at the wrong offset" is a one-line
root cause for a bug that otherwise costs days.

Binding, as everywhere else in this tool: a transcript is data someone sent.
No binary is loaded, so the report says ``artifact: none`` and means it.

  ⚠  The X25519 and ECDH code in this module is a *reference* written for
     checking someone else's answers offline. It is not constant time and
     must never be used for real key agreement. pq-verify does not observe
     timing or power behaviour — see the side_channel field on every report.
"""

import datetime
import hashlib
import json
import os

from .core import DEGRADED, VERSION

PROMPT_SCHEMA = "pq-verify/hybrid-prompt"
TRANSCRIPT_SCHEMA = "pq-verify/hybrid-transcript"
SCHEMA_VERSION = "1.0"

# ----------------------------------------------------------------------
# Pinned from RFC 10024, "Post-Quantum Traditional (PQ/T) Hybrid Key
# Agreement Mechanisms for TLS 1.3" (draft-ietf-tls-ecdhe-mlkem, as adopted).
#
# Source used to pin these values, recorded so the numbers can be traced:
#   https://raw.githubusercontent.com/tlswg/tls-ecdhe-mlkem/main/
#       draft-ietf-tls-ecdhe-mlkem.md
#   sha256 08d94801b4d2f1513fdc8676944176b177feecb3326978d99dec13fceec7fd69
#
# Every length below is stated explicitly in that document rather than derived
# here, and the totals are cross-checked against the component sizes at import
# (see _check_registry). A length that does not add up is a typo in this file,
# and it fails loudly rather than mis-scoring someone's transcript.
# ----------------------------------------------------------------------

RFC = "RFC 10024"

# component sizes, from FIPS 203 (ML-KEM) and RFC 9846 §4.3.8.2 (ECDHE point)
_KEM_SIZES = {          # (encapsulation key, ciphertext, shared secret)
    "ML-KEM-768":  (1184, 1088, 32),
    "ML-KEM-1024": (1568, 1568, 32),
}
_ECDH_SIZES = {         # (public share, shared secret, private scalar)
    "X25519": (32, 32, 32),
    "P-256":  (65, 32, 32),
    "P-384":  (97, 48, 48),
}

GROUPS = {
    "X25519MLKEM768": {
        "codepoint": 0x11EC,
        "kem": "ML-KEM-768",
        "ecdh": "X25519",
        # RFC 10024 "Client Share": "the concatenation of the client's
        # ML-KEM-768 encapsulation key and the client's X25519 ephemeral
        # share", 1216 bytes.
        "client_share": ("kem_ek", "ecdh_pub"),
        "client_share_size": 1216,
        # "Server Share": "the concatenation of an ML-KEM ciphertext ... and
        # the server's ephemeral X25519 share", 1120 bytes.
        "server_share": ("kem_ct", "ecdh_pub"),
        "server_share_size": 1120,
        # "Shared Secret": "the concatenation of the ML-KEM shared secret and
        # the X25519 shared secret", 64 bytes.
        "shared_secret": ("kem_ss", "ecdh_ss"),
        "shared_secret_size": 64,
        "note": ("the order is reversed relative to the group name — RFC 10024 "
                 "says so explicitly, and calls it historical"),
        "recommended": True,
    },
    "SecP256r1MLKEM768": {
        "codepoint": 0x11EB,
        "kem": "ML-KEM-768",
        "ecdh": "P-256",
        # "the concatenation of the secp256r1 ephemeral share and ML-KEM-768
        # encapsulation key", 1249 bytes.
        "client_share": ("ecdh_pub", "kem_ek"),
        "client_share_size": 1249,
        # "the server's ephemeral secp256r1 share ... and an ML-KEM
        # ciphertext", 1153 bytes.
        "server_share": ("ecdh_pub", "kem_ct"),
        "server_share_size": 1153,
        # "the concatenation of the ECDHE and ML-KEM shared secrets", 64 bytes.
        "shared_secret": ("ecdh_ss", "kem_ss"),
        "shared_secret_size": 64,
        "note": "ECDHE first — the opposite of X25519MLKEM768",
        "recommended": False,
    },
    "SecP384r1MLKEM1024": {
        "codepoint": 0x11ED,
        "kem": "ML-KEM-1024",
        "ecdh": "P-384",
        "client_share": ("ecdh_pub", "kem_ek"),
        "client_share_size": 1665,
        "server_share": ("ecdh_pub", "kem_ct"),
        "server_share_size": 1665,
        "shared_secret": ("ecdh_ss", "kem_ss"),
        "shared_secret_size": 80,
        "note": ("ECDHE first; client and server shares are the same size "
                 "because ML-KEM-1024 ek and ct are both 1568 bytes"),
        "recommended": False,
    },
}

_PART_SIZE = {          # component -> which size table entry it reads
    "kem_ek": 0, "kem_ct": 1, "kem_ss": 2,
}


def part_size(group, part):
    """Byte length of one component of `group`, from the pinned tables."""
    g = GROUPS[group]
    if part in _PART_SIZE:
        return _KEM_SIZES[g["kem"]][_PART_SIZE[part]]
    if part == "ecdh_pub":
        return _ECDH_SIZES[g["ecdh"]][0]
    if part == "ecdh_ss":
        return _ECDH_SIZES[g["ecdh"]][1]
    if part == "ecdh_priv":
        return _ECDH_SIZES[g["ecdh"]][2]
    raise KeyError(part)


def layout(group, field):
    """[(part, offset, size), …] for 'client_share'|'server_share'|'shared_secret'."""
    off, out = 0, []
    for part in GROUPS[group][field]:
        n = part_size(group, part)
        out.append((part, off, n))
        off += n
    return out


def _check_registry():
    """The pinned totals must equal the sum of the pinned component sizes.

    RFC 10024 states both, so they are two independent numbers that must
    agree. Transcribing either one wrongly is caught here, at import, rather
    than by silently splitting someone's transcript at the wrong offset.
    """
    for name, g in GROUPS.items():
        for field in ("client_share", "server_share", "shared_secret"):
            total = sum(part_size(name, p) for p in g[field])
            if total != g[field + "_size"]:
                raise AssertionError(
                    f"{name}: {field} components sum to {total}, but "
                    f"{RFC} states {g[field + '_size']}")
        if set(g["client_share"]) != {"kem_ek", "ecdh_pub"}:
            raise AssertionError(f"{name}: client share must carry ek + ECDHE")
        if set(g["server_share"]) != {"kem_ct", "ecdh_pub"}:
            raise AssertionError(f"{name}: server share must carry ct + ECDHE")
        if set(g["shared_secret"]) != {"kem_ss", "ecdh_ss"}:
            raise AssertionError(f"{name}: shared secret must carry both halves")


_check_registry()


# ----------------------------------------------------------------------
# X25519 — RFC 7748 §5. Reference only; NOT constant time.
# ----------------------------------------------------------------------

_P25519 = (1 << 255) - 19
_A24 = 121665


def x25519(scalar, u):
    """RFC 7748 §5 X25519(k, u). `scalar` and `u` are 32 bytes each."""
    if len(scalar) != 32 or len(u) != 32:
        raise ValueError("X25519 takes 32-byte inputs")
    k = bytearray(scalar)
    k[0] &= 248
    k[31] &= 127
    k[31] |= 64
    k = int.from_bytes(bytes(k), "little")
    # RFC 7748: the most significant bit of the u-coordinate is masked off.
    x1 = int.from_bytes(u, "little") & ((1 << 255) - 1)

    p = _P25519
    x2, z2, x3, z3, swap = 1, 0, x1, 1, 0
    for t in range(254, -1, -1):
        kt = (k >> t) & 1
        swap ^= kt
        if swap:
            x2, x3 = x3, x2
            z2, z3 = z3, z2
        swap = kt
        a = (x2 + z2) % p
        aa = a * a % p
        b = (x2 - z2) % p
        bb = b * b % p
        e = (aa - bb) % p
        c = (x3 + z3) % p
        d = (x3 - z3) % p
        da = d * a % p
        cb = c * b % p
        x3 = (da + cb) % p
        x3 = x3 * x3 % p
        z3 = (da - cb) % p
        z3 = z3 * z3 % p * x1 % p
        x2 = aa * bb % p
        z2 = e * (aa + _A24 * e % p) % p
    if swap:
        x2, x3 = x3, x2
        z2, z3 = z3, z2
    return (x2 * pow(z2, p - 2, p) % p).to_bytes(32, "little")


# ----------------------------------------------------------------------
# P-256 / P-384 ECDH — short Weierstrass, a = -3. Reference only; NOT
# constant time. The parameters are checked at import against three
# independent properties (see _check_curve), so a mistyped constant cannot
# survive to mis-score a transcript.
# ----------------------------------------------------------------------

class _Curve(object):
    def __init__(self, name, p, b, gx, gy, n, flen):
        self.name, self.p, self.b, self.n, self.flen = name, p, b, n, flen
        self.g = (gx, gy)

    def on_curve(self, pt):
        if pt is None:
            return False
        x, y = pt
        if not (0 <= x < self.p and 0 <= y < self.p):
            return False
        return (y * y - (x * x * x - 3 * x + self.b)) % self.p == 0

    def add(self, pt1, pt2):
        if pt1 is None:
            return pt2
        if pt2 is None:
            return pt1
        p = self.p
        x1, y1 = pt1
        x2, y2 = pt2
        if x1 == x2:
            if (y1 + y2) % p == 0:
                return None
            lam = (3 * x1 * x1 - 3) * pow(2 * y1 % p, p - 2, p) % p
        else:
            lam = (y2 - y1) * pow((x2 - x1) % p, p - 2, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    def mul(self, k, pt):
        r, acc = None, pt
        while k:
            if k & 1:
                r = self.add(r, acc)
            acc = self.add(acc, acc)
            k >>= 1
        return r

    def decode_point(self, blob):
        """Uncompressed point per RFC 9846 §4.3.8.2, or None if invalid."""
        f = self.flen
        if len(blob) != 1 + 2 * f or blob[0] != 0x04:
            return None
        pt = (int.from_bytes(blob[1:1 + f], "big"),
              int.from_bytes(blob[1 + f:], "big"))
        if not self.on_curve(pt):
            return None
        return pt

    def ecdh(self, priv, peer_blob):
        """RFC 9846 §7.4.2: the x-coordinate, big-endian, field-length bytes."""
        pt = self.decode_point(peer_blob)
        if pt is None:
            raise ValueError("peer point is not a valid uncompressed point")
        d = int.from_bytes(priv, "big")
        if not 1 <= d < self.n:
            raise ValueError("private scalar out of range")
        r = self.mul(d, pt)
        if r is None:
            raise ValueError("ECDH produced the point at infinity")
        return r[0].to_bytes(self.flen, "big")


CURVES = {
    "P-256": _Curve(
        "P-256",
        p=0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
        b=0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b,
        gx=0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
        gy=0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5,
        n=0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551,
        flen=32),
    "P-384": _Curve(
        "P-384",
        p=int("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"
              "ffffffff0000000000000000ffffffff", 16),
        b=int("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875a"
              "c656398d8a2ed19d2a85c8edd3ec2aef", 16),
        gx=int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a38"
               "5502f25dbf55296c3a545e3872760ab7", 16),
        gy=int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c0"
               "0a60b1ce1d7e819d7a431d7c90ea0e5f", 16),
        n=int("ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf"
              "581a0db248b0a77aecec196accc52973", 16),
        flen=48),
}


def _check_curve(c):
    """Three properties that no mistyped constant survives.

    A wrong b, Gx or Gy puts the base point off the curve. A wrong n leaves
    n*G somewhere other than infinity. A wrong p breaks both. Together they
    pin the parameters without needing to trust this file's transcription.
    """
    if not c.on_curve(c.g):
        raise AssertionError(f"{c.name}: base point is not on the curve")
    if c.mul(c.n, c.g) is not None:
        raise AssertionError(f"{c.name}: n*G is not the point at infinity")
    if c.p % 4 != 3:
        raise AssertionError(f"{c.name}: p is not 3 mod 4")


for _c in CURVES.values():
    _check_curve(_c)


# ----------------------------------------------------------------------
# FIPS 203 §7.2 encapsulation key check — RFC 10024 makes this a MUST for
# the server, so a transcript can be checked against it without any vendor
# code at all.
# ----------------------------------------------------------------------

_Q = 3329


def ek_modulus_check(ek, kem):
    """True when every 12-bit coefficient of the encapsulation key is < q.

    FIPS 203 §7.2: ek must satisfy ByteEncode_12(ByteDecode_12(ek)) == ek,
    which holds exactly when no 12-bit field is >= q. Random bytes pass with
    probability (3329/4096)**(128*k), which is below 2**-140 for k=3 — so
    this doubles as a reliable test of whether a byte range *is* an
    encapsulation key, which is what makes the wrong-order diagnostic
    definitive rather than a guess.
    """
    k = {"ML-KEM-768": 3, "ML-KEM-1024": 4}[kem]
    if len(ek) != _KEM_SIZES[kem][0]:
        return False
    body = ek[:384 * k]                       # trailing 32 bytes are rho
    for i in range(0, len(body), 3):
        trio = body[i] | (body[i + 1] << 8) | (body[i + 2] << 16)
        if (trio & 0xFFF) >= _Q or (trio >> 12) >= _Q:
            return False
    return True


# ----------------------------------------------------------------------
# self-test — the reference above is checked against published vectors
# before it is used to judge anyone else's answers
# ----------------------------------------------------------------------

# RFC 7748 §5.2 (scalar multiplication) and §6.1 (Diffie-Hellman).
_RFC7748_SCALARMULT = (
    ("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
     "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
     "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"),
    ("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
     "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
     "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"),
    ("0900000000000000000000000000000000000000000000000000000000000000",
     "0900000000000000000000000000000000000000000000000000000000000000",
     "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"),
)
_RFC7748_DH = (
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a",
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
    "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f",
    "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742",
)
# NIST CAVS 14.1, ECC CDH primitive (SP 800-56A):
# (private, peer public point, expected shared secret)
_CAVS_ECDH = {
    "P-256": (
        "7d7dc5f71eb29ddaf80d6214632eeae03d9058af1fb6d22ed80badb62bc1a534",
        "04700c48f77f56584c5cc632ca65640db91b6bacce3a4df6b42ce7cc838833d287"
        "db71e509e3fd9b060ddb20ba5c51dcc5948d46fbf640dfe0441782cab85fa4ac",
        "46fc62106420ff012e54a434fbdd2d25ccc5852060561e68040dd7778997bd7b"),
    "P-384": (
        "3cc3122a68f0d95027ad38c067916ba0eb8c38894d22e1b15618b6818a661774"
        "ad463b205da88cf699ab4d43c9cf98a1",
        "04a7c76b970c3b5fe8b05d2838ae04ab47697b9eaf52e764592efda27fe75132"
        "72734466b400091adbf2d68c58e0c50066"
        "ac68f19f2e1cb879aed43a9969b91a0839c4c38a49749b661efedf243451915e"
        "d0905a32b060992b468c64766fc8437a",
        "5f9d29dc5e31a163060356213669c8ce132e22f57c9a04f40ba7fcead493b457"
        "e5621e766c40a2e3d4d6a04b25e533f1"),
}
_X25519_BASE = b"\x09" + b"\x00" * 31


def selftest():
    """Check this module's own reference against published vectors.

    Returns (passed, total, failures). Called before every verification: a
    verifier whose own arithmetic is wrong would score a correct transcript
    as broken, and that is a worse outcome than not running.
    """
    ok, total, bad = 0, 0, []

    for k, u, want in _RFC7748_SCALARMULT:
        total += 1
        got = x25519(bytes.fromhex(k), bytes.fromhex(u)).hex()
        if got == want:
            ok += 1
        else:
            bad.append(f"RFC 7748 §5.2 scalarmult: got {got[:16]}…")

    priv, pub, peer, shared = (bytes.fromhex(h) for h in _RFC7748_DH)
    total += 1
    if x25519(priv, _X25519_BASE) == pub:
        ok += 1
    else:
        bad.append("RFC 7748 §6.1: public key from private scalar")
    total += 1
    if x25519(priv, peer) == shared:
        ok += 1
    else:
        bad.append("RFC 7748 §6.1: shared secret")

    for name, (d, peer_pt, want) in _CAVS_ECDH.items():
        total += 1
        try:
            got = CURVES[name].ecdh(bytes.fromhex(d),
                                    bytes.fromhex(peer_pt)).hex()
        except ValueError as exc:
            got = f"error: {exc}"
        if got == want:
            ok += 1
        else:
            bad.append(f"CAVS ECC CDH {name}: got {str(got)[:16]}…")

    return ok, total, bad


# ----------------------------------------------------------------------
# prompt — what to supply, with the citation for every field
# ----------------------------------------------------------------------

_HOW_TO_RESPOND = [
    "Run one hybrid handshake (or one offline key agreement) for this group "
    "with your own implementation and record the wire bytes.",
    "Fill in the fields below as lowercase hex. Omit any field you cannot "
    "produce — an omitted field is reported as NOT CHECKED, never as a pass.",
    "The ECDHE private scalars are optional. Supplying one lets pq-verify "
    "recompute the ECDHE shared secret and compare it byte-for-byte at the "
    "offset this group pins; without one, only structure and length are "
    "checked. Use ephemeral test keys, never production keys.",
    "pq-verify does not need, and will not read, the ML-KEM decapsulation "
    "key. Supply mlkemSharedSecret only if you want the ML-KEM half of the "
    "combined secret checked for placement.",
    "Send the completed file back and run: pq-verify --verify-hybrid FILE",
]


def _field_docs(group):
    g = GROUPS[group]
    ec, kem = g["ecdh"], g["kem"]
    docs = {
        "clientShare": {
            "required": False,
            "bytes": g["client_share_size"],
            "layout": [{"component": p, "offset": o, "bytes": n}
                       for p, o, n in layout(group, "client_share")],
            "cite": f"{RFC}, Client Share",
        },
        "serverShare": {
            "required": False,
            "bytes": g["server_share_size"],
            "layout": [{"component": p, "offset": o, "bytes": n}
                       for p, o, n in layout(group, "server_share")],
            "cite": f"{RFC}, Server Share",
        },
        "sharedSecret": {
            "required": False,
            "bytes": g["shared_secret_size"],
            "layout": [{"component": p, "offset": o, "bytes": n}
                       for p, o, n in layout(group, "shared_secret")],
            "cite": f"{RFC}, Shared Secret",
        },
        "clientEcdhPrivate": {
            "required": False,
            "bytes": part_size(group, "ecdh_priv"),
            "note": f"{ec} private scalar used for the client share (optional)",
        },
        "serverEcdhPrivate": {
            "required": False,
            "bytes": part_size(group, "ecdh_priv"),
            "note": f"{ec} private scalar used for the server share (optional)",
        },
        "mlkemSharedSecret": {
            "required": False,
            "bytes": part_size(group, "kem_ss"),
            "note": f"the {kem} shared secret K, if you want its placement checked",
        },
    }
    return docs


def build_hybrid_prompt(group):
    if group not in GROUPS:
        raise ValueError(
            f"unknown group {group!r} — known: {', '.join(sorted(GROUPS))}")
    g = GROUPS[group]
    return {
        "schema": PROMPT_SCHEMA,
        "schemaVersion": SCHEMA_VERSION,
        "toolVersion": VERSION,
        "generated": datetime.datetime.now(
            datetime.timezone.utc).isoformat(timespec="seconds"),
        "group": group,
        "codepoint": f"0x{g['codepoint']:04X}",
        "specification": RFC,
        "components": {"kem": g["kem"], "ecdh": g["ecdh"]},
        "orderNote": g["note"],
        "howToRespond": _HOW_TO_RESPOND,
        "fields": _field_docs(group),
        "response": {
            "schema": TRANSCRIPT_SCHEMA,
            "group": group,
            "clientShare": "",
            "serverShare": "",
            "sharedSecret": "",
            "clientEcdhPrivate": "",
            "serverEcdhPrivate": "",
            "mlkemSharedSecret": "",
            "implementation": "",
        },
    }


def emit_hybrid_prompt(group, out_path=None, verbose=True):
    doc = build_hybrid_prompt(group)
    path = out_path or f"pq-verify-hybrid-prompt-{group}.json"
    d = os.path.dirname(os.path.abspath(path))
    if d:
        os.makedirs(d, exist_ok=True)
    with open(path, "w") as fh:
        json.dump(doc, fh, indent=2)
    if verbose:
        g = GROUPS[group]
        print("=" * 68)
        print(f"  HYBRID PROMPT — {group}  (0x{g['codepoint']:04X}, {RFC})")
        print("=" * 68)
        print(f"  components : {g['kem']} + {g['ecdh']}")
        for field in ("client_share", "server_share", "shared_secret"):
            parts = " ‖ ".join(f"{p}({n})" for p, _o, n in layout(group, field))
            print(f"  {field:14s}: {parts} = {g[field + '_size']} bytes")
        print(f"  note       : {g['note']}")
        print("-" * 68)
        print(f"  wrote {path}")
        print("  Fill in what you can. An omitted field is NOT CHECKED, and")
        print("  is reported as such — it is never counted as a pass.")
        print("=" * 68)
    return path, doc


# ----------------------------------------------------------------------
# verification
# ----------------------------------------------------------------------

_MAX_LISTED = 25


def _hex(v, want_len=None):
    """Bytes from a hex field, or None if it is absent or not usable."""
    if not isinstance(v, str):
        return None
    s = "".join(v.split())
    if s[:2].lower() == "0x":
        s = s[2:]
    if not s or len(s) % 2:
        return None
    try:
        b = bytes.fromhex(s)
    except ValueError:
        return None
    if want_len is not None and len(b) != want_len:
        return b          # caller reports the length mismatch
    return b


def _artifact_field(meta):
    """The binding. A transcript is bytes someone sent; nothing was loaded."""
    claimed = None
    a = meta.get("artifact")
    if isinstance(a, dict):
        claimed = a.get("sha256")
    elif isinstance(a, str):
        claimed = a
    summary = "none — vendor-supplied transcript"
    if isinstance(claimed, str) and claimed.strip():
        summary += (f" (vendor asserts sha256 {claimed.strip()}, "
                    f"not verified by pq-verify)")
    else:
        claimed = None
    return {"bound": False, "sha256": None, "path": None, "summary": summary,
            "vendor_asserted_sha256": claimed,
            "detail": ("No binary was loaded. A passing transcript shows that "
                       "the bytes compose the way RFC 10024 requires; it does "
                       "not identify the code that produced them.")}


class _Res(object):
    """Accumulates checks. A check that could not run is SKIPPED, not passed."""

    def __init__(self):
        self.checks = []
        self.findings = []

    def ok(self, name, detail=""):
        self.checks.append({"name": name, "passed": True, "detail": detail})

    def fail(self, name, detail):
        self.checks.append({"name": name, "passed": False, "detail": detail})
        self.findings.append(f"hybrid: {name} — {detail}")

    def skip(self, name, reason):
        """Not run because the transcript did not supply what it needs."""
        self.checks.append({"name": name, "passed": None, "detail": reason,
                            "skipped": True, "kind": "no_input"})

    def na(self, name, reason):
        """Not run because this group has no such check to run.

        Kept apart from a skip deliberately. A missing input means the
        transcript could say more than it does, and the verdict should stay
        PARTIAL until it does. A check that does not exist for this group is
        not a gap in the transcript, and holding the verdict at PARTIAL over
        it would train a reader to ignore PARTIAL.
        """
        self.checks.append({"name": name, "passed": None, "detail": reason,
                            "skipped": True, "kind": "not_applicable"})

    def tally(self):
        run = [c for c in self.checks if not c.get("skipped")]
        return sum(1 for c in run if c["passed"]), len(run)


def _offset(group, field, part):
    for p, off, _n in layout(group, field):
        if p == part:
            return off
    return None


def _slice(group, field, blob, part):
    for p, off, n in layout(group, field):
        if p == part:
            return blob[off:off + n]
    return None


def _other_slice(group, field, blob, part):
    """The bytes at the offset this component would have in the OTHER order.

    RFC 10024 uses both orders across its three groups, so "wrong order" is
    the single most likely composition bug. Reading the other offset turns a
    bare mismatch into a named root cause.
    """
    parts = list(GROUPS[group][field])
    if len(parts) != 2 or part not in parts:
        return None
    swapped = [parts[1], parts[0]]
    off = 0
    for p in swapped:
        n = part_size(group, p)
        if p == part:
            return blob[off:off + n]
        off += n
    return None


def verify_hybrid(transcript_path, verbose=True):
    """Check a hybrid transcript against RFC 10024's pinned composition."""
    res = {
        "group": None, "codepoint": None, "specification": RFC,
        "transcript_file": transcript_path, "transcript_sha256": None,
        "implementation": None, "status": "CANNOT VERIFY", "verified": False,
        "passed": 0, "total": 0, "skipped": 0, "not_applicable": 0,
        "checks": [], "findings": [], "layout": {},
        "artifact": _artifact_field({}),
    }

    def _stop(msg):
        res["findings"].append(f"cannot verify: {msg}")
        DEGRADED["skipped_checks"].append(f"hybrid transcript ({msg})")
        if verbose:
            _print(res)
        return res

    # ---- read ------------------------------------------------------------
    try:
        with open(transcript_path, "rb") as fh:
            raw = fh.read()
    except OSError as exc:
        return _stop(f"transcript unreadable ({exc})")
    res["transcript_sha256"] = hashlib.sha256(raw).hexdigest()
    try:
        doc = json.loads(raw.decode("utf-8"))
    except UnicodeDecodeError:
        return _stop("transcript is not UTF-8 text")
    except ValueError as exc:
        return _stop(f"transcript is not valid JSON ({exc})")
    except RecursionError:
        # RecursionError is a RuntimeError, not a ValueError: it would
        # otherwise traceback out of the CLI.
        return _stop("transcript is nested too deeply to parse safely")
    if not isinstance(doc, dict):
        return _stop("transcript is not a JSON object")

    group = doc.get("group")
    if not isinstance(group, str) or group not in GROUPS:
        return _stop(
            f"unknown or missing group {group!r} — known: "
            f"{', '.join(sorted(GROUPS))}")
    g = GROUPS[group]
    res["group"] = group
    res["codepoint"] = f"0x{g['codepoint']:04X}"
    res["artifact"] = _artifact_field(doc)
    impl = doc.get("implementation")
    res["implementation"] = impl if isinstance(impl, str) and impl else None
    res["layout"] = {f: [{"component": p, "offset": o, "bytes": n}
                         for p, o, n in layout(group, f)]
                     for f in ("client_share", "server_share", "shared_secret")}

    # ---- our own arithmetic, before we judge anyone else's ---------------
    st_ok, st_total, st_bad = selftest()
    if st_ok != st_total:
        for b in st_bad:
            res["findings"].append(f"cannot verify: pq-verify's own reference "
                                   f"failed its published vectors — {b}")
        DEGRADED["skipped_checks"].append("hybrid reference self-test")
        if verbose:
            _print(res)
        return res

    r = _Res()
    ec_name, kem_name = g["ecdh"], g["kem"]
    curve = CURVES.get(ec_name)

    # ---- lengths ---------------------------------------------------------
    blobs = {}
    for field, key in (("client_share", "clientShare"),
                       ("server_share", "serverShare"),
                       ("shared_secret", "sharedSecret")):
        want = g[field + "_size"]
        b = _hex(doc.get(key))
        name = f"{key} length"
        if b is None:
            r.skip(name, "not supplied")
            continue
        if len(b) != want:
            r.fail(name, f"{len(b)} bytes, {RFC} pins {want} for {group}")
            continue
        r.ok(name, f"{want} bytes")
        blobs[field] = b

    if not blobs:
        return _stop("transcript supplied none of clientShare, serverShare "
                     "or sharedSecret — there is nothing to check")

    # ---- client share: the encapsulation key must pass FIPS 203 §7.2 -----
    name = f"clientShare {kem_name} encapsulation key (FIPS 203 §7.2)"
    if "client_share" in blobs:
        ek = _slice(group, "client_share", blobs["client_share"], "kem_ek")
        ek_off = _offset(group, "client_share", "kem_ek")
        if ek_modulus_check(ek, kem_name):
            r.ok(name, "every 12-bit coefficient < q")
        else:
            other = _other_slice(group, "client_share",
                                 blobs["client_share"], "kem_ek")
            if other is not None and ek_modulus_check(other, kem_name):
                r.fail(name, (
                    f"there is no valid encapsulation key at offset {ek_off}, "
                    f"but there IS one at the offset the other order gives — "
                    f"the components are concatenated the wrong way round. "
                    f"{RFC} pins {' ‖ '.join(g['client_share'])} for {group}"))
            else:
                r.fail(name, (
                    "a 12-bit coefficient is >= 3329, so this is not a valid "
                    f"{kem_name} encapsulation key. {RFC} makes this check a "
                    "MUST for the server, with an illegal_parameter alert"))
    else:
        r.skip(name, "clientShare not supplied")

    # ---- ECDHE public shares must be well-formed -------------------------
    for field, key in (("client_share", "clientShare"),
                       ("server_share", "serverShare")):
        name = f"{key} {ec_name} share well-formed"
        if field not in blobs:
            r.skip(name, f"{key} not supplied")
            continue
        pub = _slice(group, field, blobs[field], "ecdh_pub")
        if ec_name == "X25519":
            # Every 32-byte string is a valid X25519 u-coordinate, so there is
            # nothing here to check beyond the length, and saying otherwise
            # would be inventing a check.
            r.na(name, "X25519 accepts any 32-byte u-coordinate — there is "
                       "no structural check to run, and inventing one would "
                       "report a check that did not happen")
            continue
        if curve.decode_point(pub) is not None:
            r.ok(name, f"uncompressed point on {ec_name} (RFC 9846 §4.3.8.2)")
        else:
            other = _other_slice(group, field, blobs[field], "ecdh_pub")
            if other is not None and curve.decode_point(other) is not None:
                r.fail(name, (
                    f"not a valid point here, but a valid one IS at the "
                    f"offset the other order gives — the components are "
                    f"concatenated the wrong way round. {RFC} pins "
                    f"{' ‖ '.join(GROUPS[group][field])} for {group}"))
            else:
                r.fail(name, ("not an uncompressed point on the curve "
                              "(RFC 9846 §4.3.8.2 requires 0x04 ‖ x ‖ y with "
                              "the point on the curve)"))

    # ---- X25519 contributory check ---------------------------------------
    name = "sharedSecret X25519 half is non-zero"
    if ec_name != "X25519":
        r.na(name, f"{ec_name} — {RFC} scopes the all-zero check to X25519")
    elif "shared_secret" not in blobs:
        r.skip(name, "sharedSecret not supplied")
    else:
        half = _slice(group, "shared_secret", blobs["shared_secret"], "ecdh_ss")
        if any(half):
            r.ok(name, "non-zero")
        else:
            r.fail(name, (
                f"all zero. {RFC}: both peers MUST perform the all-zero "
                "shared secret check for X25519 and abort with "
                "illegal_parameter — a low-order peer point forces this"))

    # ---- recompute the ECDHE half and compare at the pinned offset -------
    priv_key = {"client_share": "clientEcdhPrivate",
                "server_share": "serverEcdhPrivate"}
    peer_of = {"client_share": "server_share", "server_share": "client_share"}
    recomputed = {}
    for field, key in priv_key.items():
        side = "client" if field == "client_share" else "server"
        name = f"{side} {ec_name} shared secret recomputed"
        priv = _hex(doc.get(key))
        peer_field = peer_of[field]
        if priv is None:
            r.skip(name, f"{key} not supplied")
            continue
        if len(priv) != part_size(group, "ecdh_priv"):
            r.fail(name, f"{key} is {len(priv)} bytes, expected "
                         f"{part_size(group, 'ecdh_priv')}")
            continue
        if peer_field not in blobs:
            r.skip(name, f"needs the peer's share, and "
                         f"{'serverShare' if peer_field == 'server_share' else 'clientShare'}"
                         f" was not supplied")
            continue
        peer_pub = _slice(group, peer_field, blobs[peer_field], "ecdh_pub")
        try:
            got = (x25519(priv, peer_pub) if ec_name == "X25519"
                   else curve.ecdh(priv, peer_pub))
        except ValueError as exc:
            r.fail(name, f"could not complete the key agreement: {exc}")
            continue
        recomputed[side] = got
        if "shared_secret" not in blobs:
            r.skip(name, "computed, but sharedSecret was not supplied to "
                         "compare against")
            recomputed[side] = got
            continue
        want = _slice(group, "shared_secret", blobs["shared_secret"], "ecdh_ss")
        if got == want:
            r.ok(name, f"matches the {ec_name} half byte-for-byte")
        else:
            other = _other_slice(group, "shared_secret",
                                 blobs["shared_secret"], "ecdh_ss")
            if other is not None and got == other:
                r.fail(name, (
                    f"the {ec_name} half is byte-identical to the recomputed "
                    f"value but sits at the OTHER offset — the two halves of "
                    f"the shared secret are swapped. {RFC} pins "
                    f"{' ‖ '.join(g['shared_secret'])} for {group}"))
            else:
                r.fail(name, (
                    f"recomputed {got.hex()[:24]}…, transcript has "
                    f"{want.hex()[:24]}… at the offset {RFC} pins"))

    # ---- both scalars supplied: the two sides must agree -----------------
    name = f"client and server derive the same {ec_name} secret"
    if len(recomputed) == 2:
        if recomputed["client"] == recomputed["server"]:
            r.ok(name, "the two independent derivations agree")
        else:
            r.fail(name, "the two sides derive different secrets — the shares "
                         "and the private scalars do not belong to the same "
                         "exchange")
    else:
        r.skip(name, "needs both private scalars and both shares")

    # ---- ML-KEM half placement -------------------------------------------
    name = f"sharedSecret {kem_name} half placement"
    kss = _hex(doc.get("mlkemSharedSecret"))
    if kss is None:
        r.skip(name, "mlkemSharedSecret not supplied")
    elif len(kss) != part_size(group, "kem_ss"):
        r.fail(name, f"mlkemSharedSecret is {len(kss)} bytes, expected "
                     f"{part_size(group, 'kem_ss')}")
    elif "shared_secret" not in blobs:
        r.skip(name, "sharedSecret not supplied")
    else:
        want = _slice(group, "shared_secret", blobs["shared_secret"], "kem_ss")
        if kss == want:
            r.ok(name, f"present at the offset {RFC} pins")
        else:
            other = _other_slice(group, "shared_secret",
                                 blobs["shared_secret"], "kem_ss")
            if other is not None and kss == other:
                r.fail(name, (
                    f"the {kem_name} secret is in the combined secret but at "
                    f"the OTHER offset — the two halves are swapped. {RFC} "
                    f"pins {' ‖ '.join(g['shared_secret'])} for {group}"))
            else:
                r.fail(name, (
                    f"the supplied {kem_name} secret does not appear at the "
                    f"offset {RFC} pins"))

    # ---- verdict ---------------------------------------------------------
    p, t = r.tally()
    res["checks"] = r.checks
    res["findings"] = r.findings
    res["passed"], res["total"] = p, t
    res["skipped"] = sum(1 for c in r.checks
                         if c.get("kind") == "no_input")
    res["not_applicable"] = sum(1 for c in r.checks
                                if c.get("kind") == "not_applicable")
    if t == 0:
        res["status"] = "CANNOT VERIFY"
        res["findings"].append(
            "cannot verify: the transcript supplied nothing this group can be "
            "checked against")
    elif p < t:
        res["status"] = "FINDINGS PRESENT"
    elif res["skipped"]:
        res["status"] = "PARTIAL"
    else:
        res["status"] = "VERIFIED"
    res["verified"] = (res["status"] == "VERIFIED")
    if res["skipped"]:
        DEGRADED["skipped_checks"].append(
            f"hybrid {group} ({res['skipped']} check(s) had no input)")

    if verbose:
        _print(res)
    return res


def _print(res):
    group = res["group"] or "(unknown group)"
    print("=" * 68)
    print(f"  HYBRID COMPOSITION — {group}")
    print("=" * 68)
    print(f"  transcript: {os.path.basename(res['transcript_file'])}")
    print(f"  sha256    : {res['transcript_sha256'] or '(unreadable)'}")
    print(f"  spec      : {res['specification']}"
          + (f"   codepoint {res['codepoint']}" if res["codepoint"] else ""))
    if res.get("implementation"):
        print(f"  claimed   : {res['implementation']}")
    print(f"  artifact  : {res['artifact']['summary']}")
    if res["checks"]:
        print("-" * 68)
        for c in res["checks"]:
            if c.get("kind") == "not_applicable":
                mark = "N/A"
            elif c.get("skipped"):
                mark = "NOT CHECKED"
            elif c["passed"]:
                mark = "PASS"
            else:
                mark = "**FAIL**"
            print(f"  {mark:12s} {c['name']}")
            if c["detail"]:
                print(f"               {c['detail']}")
    print("-" * 68)
    print(f"  checked   : {res['passed']} of {res['total']} runnable checks"
          + (f"   ({res['skipped']} not checked — no input)"
             if res["skipped"] else "")
          + (f"   ({res['not_applicable']} N/A for this group)"
             if res.get("not_applicable") else ""))
    if res["findings"]:
        print("-" * 68)
        for f in res["findings"][:_MAX_LISTED]:
            print(f"    - {f}")
        if len(res["findings"]) > _MAX_LISTED:
            print(f"    … and {len(res['findings']) - _MAX_LISTED} more")
    print("=" * 68)
    print(f"  RESULT: {res['status']}")
    print("  SCOPE: this checks how the two components are composed, against")
    print(f"  {RFC}. It does not re-derive the ML-KEM half — use --acvp or")
    print("  --audit-kem for that. No binary was loaded, so the result is not")
    print("  bound to any artifact.")
    print("=" * 68)
