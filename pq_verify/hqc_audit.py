"""Audit a THIRD-PARTY HQC decoder (the code layer; HQC's standard is not final).

The library's own compiled encoder and decoder functions are called directly
and judged by pq_verify.hqc, the reference held to the submitters' published
generator polynomials and to their own decoders' answers (`pq-verify --hqc`):

    encode       reed_solomon_encode, reed_muller_encode and code_encode,
                 byte for byte
    rm-decode    the inner decoder on built blocks, each answer exact: every
                 codeword; noise up to the radius; blocks between two
                 codewords at every distance up to the radius, the nearer one
                 sometimes the higher index; ties (equidistant blocks, and the
                 GF(2^7) inversion word, tied 14 ways) broken to the lowest
                 index as the submitters' code does; one exact copy outvoting
                 noisy ones; random blocks (maximum likelihood)
    rs-decode    the outer decoder within its radius: random errors, all in
                 the parity or the message part, and patterns whose leading
                 Hankel minors vanish -- the Berlekamp-Massey branch a random
                 pattern essentially never reaches. Past the radius nothing is
                 specified and only the bounds are checked
    code-decode  whole received words within both radii -> the message
    bounds       no call writes outside its output buffer

Why the functions and not the KEM: honest decryptions put almost no errors in
front of the outer decoder, and decapsulation re-encrypts, so a ciphertext
built to reach a corner of the decoder is rejected whatever the decoder did. A
library whose shared object hides these symbols (liboqs builds them with
hidden visibility) cannot be audited this way; build its sources with default
visibility.

Calling convention, by symbol name, for every known version: f(out, in), with
the 2023 submission's uint8_t and the 2025 code's uint64_t pointers laid out
the same; buffers are 64-byte aligned. Names as PQClean exports them
(PQCLEAN_HQC128_CLEAN_code_decode), as the submitters' build does (code_decode)
or namespaced (PQCHQC_HQC1_C_code_decode). An ambiguous role is never guessed
(--hqc-symbol, --symbol-prefix).
"""
import ctypes as _ct
import os
import re as _re

from . import hqc as H

STAGES = ("encode", "rm-decode", "rs-decode", "code-decode", "bounds")
_ROLES = {
    "rs_encode": r"reed_solomon_encode$",
    "rs_decode": r"reed_solomon_decode$",
    "rm_encode": r"reed_muller_encode$",
    "rm_decode": r"reed_muller_decode$",
    "code_encode": r"(?:^|_)code_encode$",
    "code_decode": r"(?:^|_)code_decode$",
}
_MARK = {"128": "HQC-1", "1": "HQC-1", "192": "HQC-3", "3": "HQC-3", "256": "HQC-5", "5": "HQC-5"}
GUARD = 64


def exported_symbols(so_path):
    from .symbols import exported_functions
    return exported_functions(so_path)


def _matches_set(name, param_set):
    """A name that carries a parameter-set marker must carry this set's; a
    name with none (the submitters' own build, one set per library) fits any."""
    m = _re.search(r"hqc[_-]?(128|192|256|1|3|5)(?![0-9])", name.lower())
    return m is None or _MARK[m.group(1)] == param_set


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


class _Buf:
    """64-byte aligned, with GUARD bytes of a known pattern on each side."""
    FILL = 0xA5

    def __init__(self, data=b"", size=None):
        size = len(data) if size is None else size
        self.size = size
        self.raw = _ct.create_string_buffer(bytes([self.FILL]) * (size + 2 * GUARD + 64))
        base = _ct.addressof(self.raw)
        self.addr = base + (-(base + GUARD) % 64) + GUARD
        if data:
            _ct.memmove(self.addr, bytes(data), len(data))

    @property
    def ptr(self):
        return _ct.c_void_p(self.addr)

    def value(self):
        return _ct.string_at(self.addr, self.size)

    def intact(self):
        pat = bytes([self.FILL]) * GUARD
        return (_ct.string_at(self.addr - GUARD, GUARD) == pat
                and _ct.string_at(self.addr + self.size, GUARD) == pat)


class VendorHQC:
    def __init__(self, so_path, param_set, symbols=None, prefix=None):
        self.path = os.path.abspath(so_path)
        self.name = os.path.basename(so_path)
        self.param_set = H.set_name(param_set)
        self.lib = _ct.CDLL(self.path)
        self.sym, self.ambiguous = resolve_symbols(exported_symbols(self.path),
                                                   self.param_set, symbols, prefix)
        self.fn = {}
        for role, s in self.sym.items():
            if s:
                f = getattr(self.lib, s)
                f.restype, f.argtypes = None, [_ct.c_void_p, _ct.c_void_p]
                self.fn[role] = f

    def has(self, role):
        return role in self.fn

    def call(self, role, data, out_len):
        """-> (output bytes, wrote only its output). The input is padded with
        zeros to a whole number of 64-bit words plus a guard."""
        inp = _Buf(bytes(data) + bytes(GUARD))
        out = _Buf(size=out_len)
        self.fn[role](out.ptr, inp.ptr)
        return out.value(), out.intact()


class _Tally:
    def __init__(self):
        self.detail, self.failures = {}, []

    def rec(self, stage, ok, case, detail=""):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        if not ok and len(self.failures) < 50:
            self.failures.append({"stage": stage, "case": case, "detail": detail})


def _other_profile(C, role, inp, got):
    """A hint when an encoder computes the other profile's code."""
    for p in H.PROFILES:
        if p == C.profile:
            continue
        D = H.Code(C.name, p)
        want = {"rs_encode": D.rs_encode, "rm_encode": D.rm_encode,
                "code_encode": D.code_encode}[role](inp)
        if want == got:
            return f"; it matches profile {p!r} ({H.PROFILE_NOTES[p]}) -- try --hqc-profile {p}"
    return ""


def run(v, C, cases):
    T = _Tally()

    def call(role, data, n, case):
        got, intact = v.call(role, data, n)
        T.rec("bounds", intact, f"{role}: {case}",
              "" if intact else f"wrote outside its {n}-byte output")
        return got

    for role, items in (("rs_encode", cases["rs_encode"]), ("rm_encode", cases["rm_encode"]),
                        ("code_encode", cases["code_encode"])):
        if not v.has(role):
            continue
        n = C.n1 if role == "rs_encode" else C.word_bytes
        for inp, want in items:
            got = call(role, inp, n, inp[:4].hex() + "...")
            ok = got == want
            T.rec("encode", ok, f"{role}({inp[:6].hex()}...)",
                  "" if ok else f"differs from byte {next(i for i in range(n) if got[i] != want[i])}"
                  + _other_profile(C, role, inp, got))
    if v.has("rm_decode"):
        for word, labels, want in cases["rm_decode"]:
            got = call("rm_decode", word, C.n1, labels[0])
            blocks = C.blocks(word)
            for i, (lab, g, w) in enumerate(zip(labels, got, want)):
                if g == w:
                    T.rec("rm-decode", True, lab)
                elif C.is_ml(blocks[i], g):
                    T.rec("rm-decode", False, lab, f"returned {g:#04x}, as near as the "
                          f"reference's {w:#04x} but the tie broken differently (lowest index)")
                else:
                    T.rec("rm-decode", False, lab, f"returned {g:#04x}; {w:#04x}'s codeword "
                          f"is nearer (not maximum likelihood)")
    if v.has("rs_decode"):
        for lab, word, m in cases["rs_decode"]:
            got = call("rs_decode", word, C.k, lab)
            T.rec("rs-decode", got == m, lab, "" if got == m else "wrong message")
        for lab, word, _ in cases["rs_beyond"]:
            call("rs_decode", word, C.k, lab)
    if v.has("code_decode"):
        for lab, word, m in cases["code_decode"]:
            got = call("code_decode", word, C.k, lab)
            T.rec("code-decode", got == m, lab, "" if got == m else "wrong message")
    return T


def pqverify_audit_hqc(so_path, param_set="HQC-1", symbols=None, verbose=True,
                       prefix=None, profile="v5", seed=None):
    """Audit a third-party HQC decoder; see the module docstring.

    Returns None when it cannot be audited (an ambiguous symbol, no decoder
    entry point). Otherwise {'detail': {stage: (p, t)}, 'via', 'failures',
    'seed', ...}. The vectors are fresh each run unless `seed` is given; the
    seed is reported so a finding can be replayed."""
    from .core import DEGRADED
    name = H.set_name(param_set)
    v = VendorHQC(so_path, name, symbols=symbols, prefix=prefix)
    if v.ambiguous:
        from .symbols import ambiguity_message
        print(ambiguity_message(v.path, v.ambiguous, _ROLES, "--hqc-symbol ROLE=SYMBOL"))
        DEGRADED["skipped_checks"].append(f"HQC decoder audit ({name})")
        return None
    if not any(v.has(r) for r in ("rm_decode", "rs_decode", "code_decode")):
        print(f"  Cannot audit {v.path}: no HQC decoder entry point "
              f"(reed_muller_decode, reed_solomon_decode, code_decode) for {name}.")
        hint = [e for e in exported_symbols(v.path) if "hqc" in e.lower()][:8]
        if hint:
            print(f"    exported: {hint}")
        print("    (liboqs builds these with hidden visibility; build the sources with "
              "default visibility to audit them)")
        DEGRADED["skipped_checks"].append(f"HQC decoder audit ({name})")
        return None
    seed = seed or os.urandom(16).hex()
    C = H.Code(name, profile)
    cases = H.suite(C, H.Stream(f"pq-verify hqc audit {seed}"))
    if verbose:
        print("=" * 68)
        print(f"  THIRD-PARTY HQC DECODER AUDIT — {name} — code layer only")
        print(f"  library : {v.name}   profile: {profile} ({H.PROFILE_NOTES[profile]})")
        print(f"  reference: pq_verify.hqc   seed: {seed}")
        print("=" * 68)
    T = run(v, C, cases)
    p_all = sum(p for p, _ in T.detail.values())
    t_all = sum(t for _, t in T.detail.values())
    verified = p_all == t_all and t_all > 0
    via = {"encode": ", ".join(v.sym[r] for r in ("rs_encode", "rm_encode", "code_encode")
                               if v.sym.get(r)) or None,
           "rm-decode": v.sym.get("rm_decode"), "rs-decode": v.sym.get("rs_decode"),
           "code-decode": v.sym.get("code_decode"), "bounds": "every call"}
    missing = [r for r in _ROLES if not v.has(r)]
    if verbose:
        for s in STAGES:
            if s in T.detail:
                p, t = T.detail[s]
                print(f"  {'PASS' if p == t else 'FAIL'}  {s:11s} {p}/{t}   via {via[s]}")
        if missing:
            print(f"  not exported (not audited): {', '.join(missing)}")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']} {f['case']}: {f['detail']}")
        print("=" * 68)
        status = "VERIFIED" if verified else ("FINDINGS PRESENT" if t_all else "CANNOT VERIFY")
        print(f"  RESULT: {p_all}/{t_all} — {status}")
        print(f"  {H.TRACK_NOTE}")
        print("  Not a side-channel review.")
        print("=" * 68)
    return {"verified": verified, "passed": p_all, "total": t_all, "detail": T.detail,
            "via": via, "not_exported": missing, "failures": T.failures,
            "library": v.path, "profile": profile, "seed": seed,
            "parameter_set": name, "track": "hqc",
            "standard": "HQC code layer (selected by NIST; standard not final)",
            "symbols": {k: s for k, s in v.sym.items() if s}}
