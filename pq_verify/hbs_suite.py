"""LMS/HSS and XMSS/XMSS^MT conformance suites (RFC 8554, RFC 8391, SP 800-208).

Two suites, kept apart because their vectors have different standing:

pqverify_lms_acvp()   NIST's ACVP LMS vectors (pinned with the other NIST
                      files): keyGen byte-exact, sigVer verdicts, and every
                      sigGen signature verified under its published key.
                      Part of --acvp-all.

pqverify_hbs()        Everything else, each labelled by source:
                      post-quantum-cryptography/KAT (every SP 800-208 family,
                      LMS and XMSS), liboqs's KATs (XMSS^MT, the RFC 8391
                      SHA-512/SHAKE128 sets, two-level HSS), and RFC 8554's
                      own HSS test cases via cisco/hash-sigs.

Verification is cheap at any height and always runs. Key generation and
byte-exact signing build the whole tree (2^h leaves); a case whose tree costs
more hash calls than the budget is reported as not run, with its cost, never
as a pass. budget=None runs the default (seconds); full=True runs every tree
of height 10 or less (budget FULL_BUDGET).
"""
import gzip as _gz
import json as _json
import os as _os
import re as _re
import time as _time

from . import hbs as H

DEFAULT_BUDGET = 100_000          # hash calls per tree: every LMS h=5 tree up to w=4 (~10 s)
FULL_BUDGET = 4_000_000           # every LMS and XMSS tree of height 10 (w <= 4)

NIST_DIRS = ("LMS-keyGen-1.0", "LMS-sigGen-1.0", "LMS-sigGen-SP800-208",
             "LMS-sigVer-1.0", "LMS-sigVer-SP800-208")

_SOURCE_LABEL = {
    "pqc-kat": "post-quantum-cryptography/KAT (third party, not NIST)",
    "liboqs": "liboqs KATs (third party, not NIST)",
    "hash-sigs": "RFC 8554 Appendix F, via cisco/hash-sigs",
}


def _passed(v):
    return v if isinstance(v, bool) else str(v).lower() == 'true'


def _h(x):
    return bytes.fromhex(x)


class _Tally:
    def __init__(self):
        self.detail, self.not_run, self.failures = {}, {}, []

    def rec(self, stage, ok, what=None):
        p, t = self.detail.get(stage, (0, 0))
        self.detail[stage] = (p + int(bool(ok)), t + 1)
        if not ok and len(self.failures) < 50:
            self.failures.append({'stage': stage, 'case': what})

    def skip(self, stage, count, cost):
        c, worst = self.not_run.get(stage, (0, 0))
        self.not_run[stage] = (c + count, max(worst, cost))

    def totals(self):
        return (sum(p for p, _ in self.detail.values()),
                sum(t for _, t in self.detail.values()),
                sum(c for c, _ in self.not_run.values()))


# ─────────────────────────────── NIST ACVP ───────────────────────────────

def pqverify_lms_acvp(prompt_dir=None, verbose=True, live=False, vector_dir=None):
    """NIST ACVP LMS (SP 800-208): 9 keyGen byte-exact, 16 sigVer verdicts,
    62 sigGen signatures verified under the published public key. NIST's
    sigGen vectors carry no private key (the IUT generates its own), so the
    signatures can be verified but not regenerated. No dependency beyond
    hashlib."""
    from .core import _load_vector_json, _pkg_dir, _vector_label, _ACVP_BASE
    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _os.path.join(_pkg_dir(), "vectors")

    def load(d, f):
        if _local:
            return _load_vector_json(_os.path.join(_local, d, f), f"{d}/{f}")
        import urllib.request
        return _json.loads(urllib.request.urlopen(_ACVP_BASE + d + "/" + f,
                                                  timeout=60).read())

    T = _Tally()
    if verbose:
        print("=" * 64)
        print("  NIST ACVP LMS (SP 800-208)")
        print(f"  vectors: {_vector_label(_local, *NIST_DIRS)}")
        print("  reference: pq_verify.hbs (RFC 8554 / SP 800-208, hashlib only)")
        print("=" * 64)
    for d in NIST_DIRS:
        mode = d.split('-')[1]
        p, e = load(d, "prompt.json"), load(d, "expectedResults.json")
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        egrp = {str(g['tgId']): g for g in e['testGroups']}
        for g in p['testGroups']:
            stage = f"{mode}/{g['lmsMode']}/{g['lmOtsMode']}"
            lt, ot = H.LMS_BY_NAME[g['lmsMode']], H.LMOTS_BY_NAME[g['lmOtsMode']]
            for t in g['tests']:
                ref = exp[str(t['tcId'])]
                tc = f"{d} tcId {t['tcId']}"
                if mode == 'keyGen':
                    pk = H.LMSTree(lt, ot, _h(t['seed']), _h(t['i'])).public_key
                    T.rec(stage, pk.hex().upper() == ref['publicKey'].upper(), tc)
                elif mode == 'sigVer':
                    got = H.lms_verify(_h(g['publicKey']), _h(t['message']), _h(t['signature']))
                    T.rec(stage, got == _passed(ref['testPassed']), tc)
                else:
                    pk = _h(egrp[str(g['tgId'])]['publicKey'])
                    T.rec(stage, H.lms_verify(pk, _h(t['message']), _h(ref['signature'])), tc)
    p_all, t_all, _ = T.totals()
    if verbose:
        for s, (p, t) in sorted(T.detail.items()):
            print(f"  {'PASS' if p == t else 'FAIL'}      {s:52s} {p}/{t}")
        print("=" * 64)
        print(f"  ACVP RESULT: {p_all}/{t_all} NIST LMS vectors verified")
        print("  sigGen: NIST publishes no private key, so each signature is")
        print("          verified under its key rather than regenerated")
        print("=" * 64)
    return {'verified': p_all == t_all and t_all > 0, 'passed': p_all, 'total': t_all,
            'detail': T.detail, 'failures': T.failures,
            'vectors': _vector_label(_local, *NIST_DIRS),
            'reference': 'pq_verify.hbs'}


# ─────────────────────────────── other sources ───────────────────────────────

def _bundle():
    from .core import _pkg_dir
    with _gz.open(_os.path.join(_pkg_dir(), "vectors", "hbs_vectors.json.gz"), "rt") as fh:
        return _json.load(fh)


def _manifest():
    from .core import _pkg_dir
    with open(_os.path.join(_pkg_dir(), "vectors", "HBS_MANIFEST.json")) as fh:
        return _json.load(fh)


def sources():
    m = _manifest()
    return ", ".join(f"{k} {s['commit'][:7]}" for k, s in sorted(m['sources'].items()))


def _rsp(text):
    d = {}
    for line in text.splitlines():
        if ' = ' in line and not line.lstrip().startswith('#'):
            k, v = line.split(' = ', 1)
            d[k.strip()] = v.strip().strip('"')
    return d


def _c_arrays(text):
    """{name: bytes} for each `static const unsigned char name[] = {...}`,
    grouped by the test function that declares it."""
    out, fn = [], None
    for m in _re.finditer(r'bool (test_testvector_\d+)\(void\)|'
                          r'unsigned char (\w+)\[\] = \{([^}]*)\}', text):
        if m.group(1):
            fn = {}
            out.append(fn)
        elif fn is not None:
            fn[m.group(2)] = bytes(int(x, 16) for x in _re.findall(r'0x([0-9a-fA-F]{2})',
                                                                  m.group(3)))
    return out


def _xmss_sig(sig, msg, P):
    """Strip an appended message (the signed-message form sig || M that
    xmss-reference's xmss_sign emits). Returns the bare signature, or None
    when the appended copy differs from M."""
    n, hh = P.n, P.h // P.d
    bare = P.idx_bytes + n + P.d * (P.len * n + hh * n)
    if len(sig) == bare + len(msg):
        return sig[:bare] if sig[bare:] == msg else None
    return sig


def pqverify_hbs(full=False, budget=None, verbose=True):
    """The non-NIST LMS/HSS and XMSS/XMSS^MT vectors; see the module docstring."""
    budget = budget if budget is not None else (FULL_BUDGET if full else DEFAULT_BUDGET)
    b = _bundle()
    T = _Tally()
    t0 = _time.time()
    if verbose:
        print("=" * 68)
        print("  LMS/HSS + XMSS/XMSS^MT (RFC 8554, RFC 8391, SP 800-208)")
        print(f"  vectors : {sources()}")
        print(f"  budget  : {budget:,} hash calls per tree "
              f"({'full' if full else 'default; --lms-xmss-full runs every height-10 tree'})")
        print("=" * 68)

    # ---- pqc-kat LMS (internalProjection: inputs and answers together)
    for key in sorted(k for k in b if k.startswith('pqc-kat/LMS/')):
        mode = key.split('/')[2].split('-')[1]
        doc = _json.loads(b[key])
        for g in doc['testGroups']:
            lt, ot = H.LMS_BY_NAME[g['lmsMode']], H.LMOTS_BY_NAME[g['lmOtsMode']]
            fam = g['lmsMode'].split('_')[1] + '_' + g['lmsMode'].split('_')[2]
            stage = f"pqc-kat LMS {mode} {fam}"
            cost = H.lms_keygen_cost(lt, ot)
            if mode == 'sigVer':
                pk = _h(g['publicKey'])
                for t in g['tests']:
                    got = H.lms_verify(pk, _h(t['message']), _h(t['signature']))
                    T.rec(stage, got == _passed(t['testPassed']), f"{key} tcId {t['tcId']}")
            elif mode == 'keyGen':
                if cost > budget:
                    T.skip(stage, len(g['tests']), cost)
                    continue
                for t in g['tests']:
                    tree = H.LMSTree(lt, ot, _h(t['seed']), _h(t['i']))
                    T.rec(stage, tree.public_key.hex().upper() == t['publicKey'].upper(),
                          f"{key} tcId {t['tcId']}")
            else:
                pk = _h(g['publicKey'])
                tree = None
                if cost <= budget:
                    seed, I = _h(g['seed']), _h(g['i'])
                    tree = H.LMSTree(lt, ot, seed, I)
                    if tree.public_key != pk:
                        tree = False
                else:
                    T.skip(stage + " (byte-exact)", len(g['tests']), cost)
                n = H.LMOTS[ot][2]
                for t in g['tests']:
                    sig, msg = _h(t['signature']), _h(t['message'])
                    T.rec(stage + " (verify)", H.lms_verify(pk, msg, sig),
                          f"{key} tcId {t['tcId']}")
                    if tree is None:
                        continue
                    if tree is False:
                        T.rec(stage + " (byte-exact)", False,
                              f"{key} tgId {g['tgId']}: public key from seed differs")
                        continue
                    # The randomizer C is derived, as hash-sigs does:
                    # H(I || u32(q) || u16(0xFFFD) || u8(0xFF) || SEED)
                    q = int(t['q'])
                    C = H.LMOTS[ot][1](tree.I + H.u32(q) + H.u16(0xFFFD) + b'\xff' + tree.seed)
                    T.rec(stage + " (byte-exact)", tree.sign(msg, q, C) == sig,
                          f"{key} tcId {t['tcId']}")

    # ---- pqc-kat XMSS (prompt + expectedResults)
    for key in sorted(k for k in b if k.startswith('pqc-kat/XMSS/') and k.endswith('prompt.json')):
        mode = key.split('/')[2].split('-')[1]
        p = _json.loads(b[key])
        e = _json.loads(b[key.replace('prompt.json', 'expectedResults.json')])
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        for g in p['testGroups']:
            oid = int(g['OID'])
            P = H.XMSS_SETS[('XMSS', oid)]
            stage = f"pqc-kat XMSS {mode} {P.name}"
            cost = H.xmss_keygen_cost(P)
            if mode == 'sigVer':
                pk = _h(g['publicKey'])
                for t in g['tests']:
                    msg = _h(t['message'])
                    sig = _xmss_sig(_h(t['signature']), msg, P)
                    got = sig is not None and H.xmss_verify(pk, msg, sig)
                    T.rec(stage, got == _passed(exp[str(t['tcId'])]['testPassed']),
                          f"{key} tcId {t['tcId']} ({t.get('comment', '')})")
            elif mode == 'keyGen':
                if cost > budget:
                    T.skip(stage, len(g['tests']), cost)
                    continue
                for t in g['tests']:
                    if 'seed' in t:
                        sd = _h(t['seed'])
                        s_x, prf, seed = sd[:P.n], sd[P.n:2 * P.n], sd[2 * P.n:3 * P.n]
                    else:
                        s_x, prf, seed = _h(t['S_XMSS']), _h(t['SK_PRF']), _h(t['I'])
                    tree = H.XMSSTree(P, s_x, prf, seed)
                    want = exp[str(t['tcId'])]['publicKey'].upper()
                    got = tree.public_key(oid).hex().upper()
                    # one upstream file omits the 4-byte OID from its keys
                    T.rec(stage, want in (got, got[8:]), f"{key} tcId {t['tcId']}")
            else:
                root, seed = _h(g['PK_root']), _h(g['I'])
                pk = H.u32(oid) + root + seed
                tree = None
                if cost <= budget:
                    tree = H.XMSSTree(P, _h(g['S_XMSS']), _h(g['SK_PRF']), seed)
                else:
                    T.skip(stage + " (byte-exact)", len(g['tests']), cost)
                for t in g['tests']:
                    msg = _h(t['message'])
                    sig = _xmss_sig(_h(exp[str(t['tcId'])]['signature']), msg, P)
                    T.rec(stage + " (verify)", sig is not None and H.xmss_verify(pk, msg, sig),
                          f"{key} tcId {t['tcId']}")
                    if tree is not None:
                        idx = int.from_bytes(sig[:4], 'big') if sig else -1
                        ok = (sig is not None and tree.root == root and
                              tree.sign(msg, idx) == sig)
                        T.rec(stage + " (byte-exact)", ok, f"{key} tcId {t['tcId']}")

    # ---- liboqs KATs: XMSS / XMSS^MT / LMS / HSS, verification
    for key in sorted(k for k in b if k.startswith('liboqs/')):
        d = _rsp(b[key])
        name = key.rsplit('/', 1)[1][:-4]
        pk, msg, sm = _h(d['pk']), _h(d['msg']), _h(d['sm'])
        if '/xmss/' in key:
            mt = name.startswith('XMSSMT')
            P = H.XMSS_SETS[('XMSSMT' if mt else 'XMSS', int.from_bytes(pk[:4], 'big'))]
            sig = _xmss_sig(sm, msg, P)
            stage = f"liboqs {'XMSS^MT' if mt else 'XMSS'} verify"
            T.rec(stage, sig is not None and H.xmss_verify(pk, msg, sig, mt=mt), name)
        else:
            hss = len(pk) != 24 + H.LMS[int.from_bytes(pk[:4], 'big')][2] \
                if int.from_bytes(pk[:4], 'big') in H.LMS else True
            stage = f"liboqs {'HSS' if hss else 'LMS'} verify"   # HSS: L = 1 or 2
            ok = H.hss_verify(pk, msg, sm) if hss else H.lms_verify(pk, msg, sm)
            T.rec(stage, ok, name)

    # ---- RFC 8554 Appendix F (two-level HSS), via hash-sigs
    for i, case in enumerate(_c_arrays(b['hash-sigs/test_testvector.c']), 1):
        T.rec("RFC 8554 HSS verify",
              H.hss_verify(case['public_key'], case['message'], case['signature']),
              f"RFC 8554 test case {i}")

    p_all, t_all, nr = T.totals()
    not_run = {k: [c, f"tree over budget (up to {w:,} hash calls)"]
               for k, (c, w) in T.not_run.items()}
    if verbose:
        for s, (p, t) in sorted(T.detail.items()):
            print(f"  {'PASS' if p == t else 'FAIL'}  {s:56s} {p}/{t}")
        for s, (c, why) in sorted(not_run.items()):
            print(f"  ----  {s:56s} {c} not run: {why}")
        for f in T.failures[:5]:
            print(f"        ✗ {f['stage']}: {f['case']}")
        print("=" * 68)
        print(f"  RESULT: {p_all}/{t_all} — "
              f"{'VERIFIED' if p_all == t_all and t_all else 'FINDINGS PRESENT'}"
              + (f"   ({nr} key generation/signing case(s) over budget, not run)" if nr else "")
              + f"   {_time.time() - t0:.0f} s")
        print("  These vectors are not NIST's; see `--acvp-all` for NIST's LMS set.")
        print("  Neither scheme is safe if a one-time key is used twice: state")
        print("  handling is the signer's, and no vector can show it.")
        print("=" * 68)
    return {'verified': p_all == t_all and t_all > 0, 'passed': p_all, 'total': t_all,
            'detail': T.detail, 'not_run': not_run,
            'not_run_total': nr, 'failures': T.failures, 'budget': budget,
            'vectors': sources(), 'reference': 'pq_verify.hbs'}
