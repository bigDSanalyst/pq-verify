"""Audit a THIRD-PARTY LMS/HSS or XMSS/XMSS^MT library (SP 800-208).

The library is loaded through a pqv_hbs adapter (pq_verify/harness/hbs/
pqv_hbs.h): five C functions mapping its own API onto one encoding.
Adapters for cisco/hash-sigs and xmss-reference ship with pq-verify; another
library needs one small C file. The audit then drives the library with:

    verify      every pinned verification vector: NIST's LMS sigVer and
                sigGen signatures, post-quantum-cryptography/KAT's LMS and
                XMSS, liboqs's XMSS, XMSS^MT and HSS, RFC 8554 Appendix F
    keyGen      seed -> public key, byte-exact (NIST and pqc-kat)
    sigGen      seed + leaf index + message -> signature, byte-exact
                (pqc-kat; LMS with the ACVP randomizer derivation)
    malformed   signatures derived from valid ones, each wrong in exactly
                one field: the leaf index (out of range, or another leaf),
                the typecodes, the randomizer, the first and last chain
                values, the first and last authentication-path nodes, one
                byte short or long, another message, another key. Each is
                confirmed rejected by pq-verify's own verifier first; the
                library must reject it too.

What the library's adapter says it cannot do (a hash family it lacks, key
generation it does not expose) is not applicable, with the reason. Key
generation and signing build whole trees, so they run within a hash budget
and, by default, for at most `per_group` cases per parameter set; the rest
are reported as not run. None of these is ever counted as a pass.
"""
import ctypes as _ct
import json as _json
import os as _os
import struct as _struct

from . import hbs as H
from .hbs_suite import _bundle, _c_arrays, _rsp, _xmss_sig, sources as _sources

LMS, XMSS, XMSSMT = 1, 2, 3
CAN_VERIFY, CAN_KEYGEN, CAN_SIGN = 1, 2, 4
SCHEME_NAME = {LMS: "LMS", XMSS: "XMSS", XMSSMT: "XMSS^MT"}

DEFAULT_BUDGET = 10_000_000       # hash calls per tree: every height-10 tree (C is fast)
DEFAULT_PER_GROUP = 2             # keyGen/sigGen cases per parameter set
FULL_BUDGET = 300_000_000         # height 16 and LMS height 15 (C is fast)


class AdapterError(Exception):
    pass


class HBSAdapter:
    """A library built with a pqv_hbs version-1 adapter."""

    def __init__(self, so_path):
        self.path = _os.path.abspath(_os.path.expanduser(so_path))
        if not _os.path.exists(self.path):
            raise FileNotFoundError(self.path)
        self.lib = L = _ct.CDLL(self.path)
        for f in ("pqv_hbs_abi", "pqv_hbs_name", "pqv_hbs_supports", "pqv_hbs_verify",
                  "pqv_hbs_keygen", "pqv_hbs_sign"):
            if not hasattr(L, f):
                raise AdapterError(f"{self.path} has no {f}: not built with a pqv_hbs adapter "
                                   f"(pq_verify/harness/hbs/pqv_hbs.h)")
        U32, SZ, P, PSZ = _ct.c_uint32, _ct.c_size_t, _ct.c_char_p, _ct.POINTER(_ct.c_size_t)
        # Every argument typed: an untyped size_t is passed as a 32-bit int,
        # and the callee reads garbage in the upper half.
        L.pqv_hbs_abi.argtypes, L.pqv_hbs_abi.restype = [], _ct.c_int
        L.pqv_hbs_name.argtypes, L.pqv_hbs_name.restype = [], _ct.c_char_p
        L.pqv_hbs_supports.argtypes = [U32, U32, U32]
        L.pqv_hbs_supports.restype = _ct.c_int
        L.pqv_hbs_verify.argtypes = [U32, P, SZ, P, SZ, P, SZ]
        L.pqv_hbs_verify.restype = _ct.c_int
        L.pqv_hbs_keygen.argtypes = [U32, U32, U32, P, SZ, P, PSZ]
        L.pqv_hbs_keygen.restype = _ct.c_int
        L.pqv_hbs_sign.argtypes = [U32, U32, U32, P, SZ, _ct.c_uint64, P, SZ, P, PSZ]
        L.pqv_hbs_sign.restype = _ct.c_int
        abi = L.pqv_hbs_abi()
        if abi != 1:
            raise AdapterError(f"pqv_hbs ABI {abi}; this pq-verify speaks version 1")
        self.name = L.pqv_hbs_name().decode(errors="replace")

    def supports(self, scheme, typ, ots=0):
        return self.lib.pqv_hbs_supports(scheme, typ, ots)

    def verify(self, scheme, pk, msg, sig):
        return self.lib.pqv_hbs_verify(scheme, pk, len(pk), msg, len(msg), sig, len(sig)) == 0

    def keygen(self, scheme, typ, ots, seed):
        pk, n = _ct.create_string_buffer(512), _ct.c_size_t(512)
        rc = self.lib.pqv_hbs_keygen(scheme, typ, ots, seed, len(seed), pk, _ct.byref(n))
        return None if rc else pk.raw[:n.value]

    def sign(self, scheme, typ, ots, seed, index, msg):
        cap = 1 << 20
        sig, n = _ct.create_string_buffer(cap), _ct.c_size_t(cap)
        rc = self.lib.pqv_hbs_sign(scheme, typ, ots, seed, len(seed), index, msg, len(msg),
                                   sig, _ct.byref(n))
        return None if rc else sig.raw[:n.value]


# ───────────────────────────── vectors, uniformly ─────────────────────────────

def _hss_pk(pk):
    return H.u32(1) + pk


def _hss_sig(sig):
    return H.u32(0) + sig


def _lms_names(pk):
    """(LMS type, LM-OTS type) of an HSS public key's top tree."""
    t, o = _struct.unpack('>II', pk[4:12])
    return t, o


def cases():
    """Every pinned vector as a uniform case dict:
       kind: verify | keygen | sign; scheme; source; typ; ots; label; cost;
       and pk/msg/sig/want, or seed/index/msg/want."""
    from .core import _load_bundle
    out = []
    nist = _load_bundle()

    # NIST ACVP LMS
    for d in ("LMS-keyGen-1.0", "LMS-sigGen-1.0", "LMS-sigGen-SP800-208",
              "LMS-sigVer-1.0", "LMS-sigVer-SP800-208"):
        mode = d.split('-')[1]
        p, e = nist[f"{d}/prompt.json"], nist[f"{d}/expectedResults.json"]
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        egrp = {str(g['tgId']): g for g in e['testGroups']}
        for g in p['testGroups']:
            lt, ot = H.LMS_BY_NAME[g['lmsMode']], H.LMOTS_BY_NAME[g['lmOtsMode']]
            name = f"{g['lmsMode']}/{g['lmOtsMode']}"
            for t in g['tests']:
                ref, label = exp[str(t['tcId'])], f"NIST {d} tcId {t['tcId']}"
                base = dict(scheme=LMS, source="NIST", typ=lt, ots=ot, set=name, label=label)
                if mode == 'keyGen':
                    out.append(dict(base, kind='keygen', seed=bytes.fromhex(t['seed'] + t['i']),
                                    want=_hss_pk(bytes.fromhex(ref['publicKey'])),
                                    cost=H.lms_keygen_cost(lt, ot)))
                elif mode == 'sigVer':
                    tp = ref['testPassed']
                    out.append(dict(base, kind='verify', pk=_hss_pk(bytes.fromhex(g['publicKey'])),
                                    msg=bytes.fromhex(t['message']),
                                    sig=_hss_sig(bytes.fromhex(t['signature'])),
                                    want=tp if isinstance(tp, bool) else str(tp) == 'True'))
                else:
                    out.append(dict(base, kind='verify',
                                    pk=_hss_pk(bytes.fromhex(egrp[str(g['tgId'])]['publicKey'])),
                                    msg=bytes.fromhex(t['message']),
                                    sig=_hss_sig(bytes.fromhex(ref['signature'])), want=True))

    b = _bundle()
    # post-quantum-cryptography/KAT LMS
    for key in sorted(k for k in b if k.startswith('pqc-kat/LMS/')):
        mode = key.split('/')[2].split('-')[1]
        for g in _json.loads(b[key])['testGroups']:
            lt, ot = H.LMS_BY_NAME[g['lmsMode']], H.LMOTS_BY_NAME[g['lmOtsMode']]
            base = dict(scheme=LMS, source="pqc-kat", typ=lt, ots=ot,
                        set=f"{g['lmsMode']}/{g['lmOtsMode']}")
            cost = H.lms_keygen_cost(lt, ot)
            for t in g['tests']:
                label = f"{key} tcId {t['tcId']}"
                if mode == 'keyGen':
                    out.append(dict(base, kind='keygen', label=label, cost=cost,
                                    seed=bytes.fromhex(t['seed'] + t['i']),
                                    want=_hss_pk(bytes.fromhex(t['publicKey']))))
                elif mode == 'sigVer':
                    out.append(dict(base, kind='verify', label=label,
                                    pk=_hss_pk(bytes.fromhex(g['publicKey'])),
                                    msg=bytes.fromhex(t['message']),
                                    sig=_hss_sig(bytes.fromhex(t['signature'])),
                                    want=str(t['testPassed']).lower() == 'true'))
                else:
                    pk, msg = _hss_pk(bytes.fromhex(g['publicKey'])), bytes.fromhex(t['message'])
                    sig = _hss_sig(bytes.fromhex(t['signature']))
                    out.append(dict(base, kind='verify', label=label, pk=pk, msg=msg, sig=sig,
                                    want=True))
                    out.append(dict(base, kind='sign', label=label, cost=cost,
                                    seed=bytes.fromhex(g['seed'] + g['i']), index=int(t['q']),
                                    msg=msg, want=sig))

    # post-quantum-cryptography/KAT XMSS
    for key in sorted(k for k in b if k.startswith('pqc-kat/XMSS/') and k.endswith('prompt.json')):
        mode = key.split('/')[2].split('-')[1]
        p = _json.loads(b[key])
        e = _json.loads(b[key.replace('prompt.json', 'expectedResults.json')])
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        for g in p['testGroups']:
            oid = int(g['OID'])
            P = H.XMSS_SETS[('XMSS', oid)]
            base = dict(scheme=XMSS, source="pqc-kat", typ=oid, ots=0, set=P.name)
            cost = H.xmss_keygen_cost(P)
            for t in g['tests']:
                label, ref = f"{key} tcId {t['tcId']}", exp[str(t['tcId'])]
                if mode == 'keyGen':
                    if 'seed' in t:
                        seed = bytes.fromhex(t['seed'])[:3 * P.n]
                    else:
                        seed = bytes.fromhex(t['S_XMSS'] + t['SK_PRF'] + t['I'])
                    want = bytes.fromhex(ref['publicKey'])
                    if len(want) == 2 * P.n:            # one file omits the OID
                        want = H.u32(oid) + want
                    out.append(dict(base, kind='keygen', label=label, cost=cost, seed=seed,
                                    want=want))
                elif mode == 'sigVer':
                    msg = bytes.fromhex(t['message'])
                    sig = _xmss_sig(bytes.fromhex(t['signature']), msg, P)
                    if sig is None:
                        continue
                    out.append(dict(base, kind='verify', label=label,
                                    pk=bytes.fromhex(g['publicKey']), msg=msg, sig=sig,
                                    want=str(ref['testPassed']).lower() == 'true'))
                else:
                    msg = bytes.fromhex(t['message'])
                    sig = _xmss_sig(bytes.fromhex(ref['signature']), msg, P)
                    pk = H.u32(oid) + bytes.fromhex(g['PK_root'] + g['I'])
                    out.append(dict(base, kind='verify', label=label, pk=pk, msg=msg, sig=sig,
                                    want=True))
                    out.append(dict(base, kind='sign', label=label, cost=cost,
                                    seed=bytes.fromhex(g['S_XMSS'] + g['SK_PRF'] + g['I']),
                                    index=int.from_bytes(sig[:4], 'big'), msg=msg, want=sig))

    # liboqs KATs
    for key in sorted(k for k in b if k.startswith('liboqs/')):
        d = _rsp(b[key])
        name = key.rsplit('/', 1)[1][:-4]
        pk, msg, sm = bytes.fromhex(d['pk']), bytes.fromhex(d['msg']), bytes.fromhex(d['sm'])
        label = f"liboqs {name}"
        if '/xmss/' in key:
            mt = name.startswith('XMSSMT')
            oid = int.from_bytes(pk[:4], 'big')
            P = H.XMSS_SETS[('XMSSMT' if mt else 'XMSS', oid)]
            out.append(dict(kind='verify', scheme=XMSSMT if mt else XMSS, source="liboqs",
                            typ=oid, ots=0, set=P.name, label=label, pk=pk, msg=msg,
                            sig=_xmss_sig(sm, msg, P), want=True))
        else:
            first = int.from_bytes(pk[:4], 'big')
            if first in H.LMS and len(pk) == 24 + H.LMS[first][2]:
                pk, sm = _hss_pk(pk), _hss_sig(sm)
            lt, ot = _lms_names(pk)
            out.append(dict(kind='verify', scheme=LMS, source="liboqs", typ=lt, ots=ot,
                            set=f"{H.LMS[lt][0]}/{H.LMOTS[ot][0]}", label=label,
                            pk=pk, msg=msg, sig=sm, want=True))

    # RFC 8554 Appendix F
    for i, c in enumerate(_c_arrays(b['hash-sigs/test_testvector.c']), 1):
        lt, ot = _lms_names(c['public_key'])
        out.append(dict(kind='verify', scheme=LMS, source="RFC 8554", typ=lt, ots=ot,
                        set=f"{H.LMS[lt][0]}/{H.LMOTS[ot][0]}", label=f"RFC 8554 test case {i}",
                        pk=c['public_key'], msg=c['message'], sig=c['signature'], want=True))
    return out


# ───────────────────────────── malformations ─────────────────────────────

def _flip(b, i, bit=1):
    b = bytearray(b)
    b[i] ^= bit
    return bytes(b)


def malformed(case):
    """Signatures wrong in exactly one field, from one valid verify case.
    Yields (what, pk, msg, sig); each must be rejected."""
    pk, msg, sig = case['pk'], case['msg'], case['sig']
    if case['scheme'] == LMS:
        if _struct.unpack('>I', sig[:4])[0] != 0:
            return                           # one-level keys only: offsets below
        _, _, n, w = H.LMOTS[case['ots']]
        p, _ = H.lmots_params(n, w)
        _, _, m, h = H.LMS[case['typ']]
        s = 4                                 # LMS signature inside the HSS form
        q, ots, C, y0 = s, s + 4, s + 8, s + 8 + n
        ylast, ltype = s + 8 + n * p - 1, s + 8 + n * (p + 1)
        path0, pathlast = ltype + 4, len(sig) - 1
        qv = _struct.unpack('>I', sig[q:q + 4])[0]
        other_ots = next(o for o in H.LMOTS if o != case['ots'])
        other_lms = next(t for t in H.LMS if t != case['typ'])
        yield "Nspk = 1 for a one-level key", pk, msg, H.u32(1) + sig[4:]
        yield "leaf index q = 2^h", pk, msg, sig[:q] + H.u32(1 << h) + sig[q + 4:]
        yield "another leaf index", pk, msg, sig[:q] + H.u32(qv ^ 1) + sig[q + 4:]
        yield "LM-OTS typecode changed", pk, msg, sig[:ots] + H.u32(other_ots) + sig[ots + 4:]
        yield "randomizer C changed", pk, msg, _flip(sig, C)
        yield "first chain value changed", pk, msg, _flip(sig, y0)
        yield "last chain value changed", pk, msg, _flip(sig, ylast, 0x80)
        yield "LMS typecode changed", pk, msg, sig[:ltype] + H.u32(other_lms) + sig[ltype + 4:]
        yield "first path node changed", pk, msg, _flip(sig, path0)
        yield "last path node changed", pk, msg, _flip(sig, pathlast, 0x80)
        yield "public key: L = 2", H.u32(2) + pk[4:], msg, sig
        yield "public key root changed", _flip(pk, len(pk) - 1), msg, sig
    else:
        mt = case['scheme'] == XMSSMT
        P = H.XMSS_SETS[('XMSSMT' if mt else 'XMSS', case['typ'])]
        ib = P.idx_bytes
        idx = int.from_bytes(sig[:ib], 'big')
        yield "leaf index = 2^h", pk, msg, (1 << P.h).to_bytes(ib + 1, 'big')[-ib:] + sig[ib:] \
            if (1 << P.h) < (1 << (8 * ib)) else sig[:ib - 1] + b'\xff' + sig[ib:]
        yield "another leaf index", pk, msg, (idx ^ 1).to_bytes(ib, 'big') + sig[ib:]
        yield "randomizer r changed", pk, msg, _flip(sig, ib)
        yield "first WOTS+ chain changed", pk, msg, _flip(sig, ib + P.n)
        yield "last WOTS+ chain changed", pk, msg, _flip(sig, ib + P.n + P.len * P.n - 1, 0x80)
        yield "last authentication node changed", pk, msg, _flip(sig, len(sig) - 1, 0x80)
        yield "public key root changed", _flip(pk, 4), msg, sig
        yield "public key SEED changed", _flip(pk, len(pk) - 1), msg, sig
    yield "one byte short", pk, msg, sig[:-1]
    yield "one byte long", pk, msg, sig + b'\x00'
    yield "another message", pk, msg + b'\x00', sig


def _reference_verify(scheme, pk, msg, sig):
    if scheme == LMS:
        return H.hss_verify(pk, msg, sig)
    return H.xmss_verify(pk, msg, sig, mt=scheme == XMSSMT)


# ───────────────────────────── the audit ─────────────────────────────

class _T:
    def __init__(self):
        self.detail, self.na, self.not_run, self.failures = {}, {}, {}, []

    def rec(self, stage, ok, label, why=None):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        # at most 10 examples per stage, so one noisy stage cannot hide another
        if not ok and (t - p) < 10:
            self.failures.append({'stage': stage, 'case': label, 'detail': why})

    def bump(self, table, stage, reason):
        c, _ = table.get(stage, (0, reason))
        table[stage] = (c + 1, reason)


def pqverify_audit_hbs(so_path, budget=None, per_group=None, full=False, verbose=True):
    """Audit an LMS/XMSS library built with a pqv_hbs adapter; see the module
    docstring. full=True lifts the per-group cap and raises the budget."""
    budget = budget if budget is not None else (FULL_BUDGET if full else DEFAULT_BUDGET)
    per_group = per_group if per_group is not None else (None if full else DEFAULT_PER_GROUP)
    v = HBSAdapter(so_path)
    T = _T()
    if verbose:
        print("=" * 72)
        print(f"  THIRD-PARTY LMS/XMSS AUDIT — {v.name}")
        print(f"  library : {_os.path.basename(v.path)}   (pqv_hbs adapter, ABI 1)")
        print(f"  vectors : NIST ACVP-Server 2972def (LMS); {_sources()}")
        print(f"  budget  : {budget:,} hash calls per tree"
              + (f", {per_group} keyGen/sigGen case(s) per parameter set" if per_group else ""))
        print("=" * 72)
    groups = {}
    malformed_done = set()
    unsupported, implemented = {}, set()
    for c in cases():
        sch = SCHEME_NAME[c['scheme']]
        stage = f"{sch} {c['kind'] if c['kind'] != 'sign' else 'sigGen'}".replace('keygen', 'keyGen')
        key = f"{stage} [{c['source']}]"
        caps = v.supports(c['scheme'], c['typ'], c['ots'])
        need = {'verify': CAN_VERIFY, 'keygen': CAN_KEYGEN, 'sign': CAN_SIGN}[c['kind']]
        if not caps & need:
            unsupported.setdefault(stage, set()).add(c['set'])
            T.bump(T.na, stage, None)
            continue
        implemented.add(c['scheme'])
        if c['kind'] == 'verify':
            ok = v.verify(c['scheme'], c['pk'], c['msg'], c['sig'])
            T.rec(key, ok == c['want'], c['label'],
                  None if ok == c['want'] else
                  f"{'accepted' if ok else 'rejected'} a signature the vector marks "
                  f"{'valid' if c['want'] else 'invalid'}")
            # malformations from the first valid signature of each parameter set
            if c['want'] and ok and c['set'] not in malformed_done:
                malformed_done.add(c['set'])
                mstage = f"{sch} malformed"
                for what, pk, msg, sig in malformed(c):
                    if _reference_verify(c['scheme'], pk, msg, sig):
                        continue                  # not malformed after all; never scored
                    got = v.verify(c['scheme'], pk, msg, sig)
                    T.rec(mstage, not got, f"{c['set']}: {what}",
                          None if not got else "accepted")
            continue
        if c['cost'] > budget:
            T.bump(T.not_run, stage, f"tree over budget (up to {c['cost']:,} hash calls)")
            continue
        gk = (stage, c['set'])
        if per_group is not None and groups.get(gk, 0) >= per_group:
            T.bump(T.not_run, stage, f"sampled: {per_group} per parameter set "
                                     f"(--audit-hbs-full runs all)")
            continue
        groups[gk] = groups.get(gk, 0) + 1
        if c['kind'] == 'keygen':
            got = v.keygen(c['scheme'], c['typ'], c['ots'], c['seed'])
        else:
            got = v.sign(c['scheme'], c['typ'], c['ots'], c['seed'], c['index'], c['msg'])
        T.rec(key, got == c['want'], c['label'],
              None if got == c['want'] else
              ("the library refused" if got is None else "output differs from the vector"))

    # One reason per stage: the scheme is absent from the library, or which
    # parameter sets its adapter reports no support for.
    for stage, sets in unsupported.items():
        sch = next(k for k, n in SCHEME_NAME.items() if stage.startswith(n + " "))
        what = stage.split(" ", 1)[1]
        if sch not in implemented:
            why = f"{v.name} does not implement {SCHEME_NAME[sch]}"
        else:
            why = (f"{v.name} has no {what} for {len(sets)} parameter set(s), e.g. "
                   + ", ".join(sorted(sets)[:2]))
        T.na[stage] = (T.na[stage][0], why)
    p_all = sum(p for p, _ in T.detail.values())
    t_all = sum(t for _, t in T.detail.values())
    na_all = sum(c for c, _ in T.na.values())
    nr_all = sum(c for c, _ in T.not_run.values())
    verified = p_all == t_all and t_all > 0
    if verbose:
        for s, (p, t) in sorted(T.detail.items()):
            print(f"  {'PASS' if p == t else 'FAIL'}  {s:40s} {p}/{t}")
        for s, (c, why) in sorted(T.na.items()):
            print(f"  n/a   {s:40s} {c}: {why}")
        for s, (c, why) in sorted(T.not_run.items()):
            print(f"  ----  {s:40s} {c} not run: {why}")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']}: {f['case']}: {f['detail']}")
        print("=" * 72)
        print(f"  RESULT: {p_all}/{t_all} — "
              f"{'VERIFIED' if verified else 'FINDINGS PRESENT' if t_all else 'CANNOT VERIFY'}"
              + (f"   ({na_all} not applicable, {nr_all} not run)" if na_all or nr_all else ""))
        print("  This audits the library's own verify/keygen/sign against the pinned")
        print("  vectors. No vector can show state handling: a one-time key used")
        print("  twice breaks both schemes. It is not a side-channel review.")
        print("=" * 72)
    return {'verified': verified, 'passed': p_all, 'total': t_all, 'detail': T.detail,
            'not_applicable': {k: list(x) for k, x in T.na.items()},
            'not_applicable_total': na_all,
            'not_run': {k: list(x) for k, x in T.not_run.items()}, 'not_run_total': nr_all,
            'failures': T.failures, 'library': v.path, 'name': v.name,
            'budget': budget, 'per_group': per_group,
            'vectors': f"NIST ACVP-Server 2972def (LMS); {_sources()}"}
