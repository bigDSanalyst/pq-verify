"""Edge-case vectors: C2SP Wycheproof and CCTV, pinned and offline.

NIST's ACVP vectors are mostly well-formed inputs. The bugs that ship sit at
the edges, and these two projects collect them, each labelled with the bug it
targets:

  ML-KEM  ciphertexts whose re-encryption differs only after a zero byte
          (strcmp in Decaps), seeds that force unusually many XOF reads
          (unlucky SampleNTT), every coefficient value q..4095 at every
          position of an encapsulation key (modulus check), decapsulation
          keys with a corrupted H(ek) or embedded ek, malleated ciphertexts
          that must take the implicit-rejection path, wrong lengths.
  ML-DSA  out-of-order and over-limit hints, z at the norm bound, contexts of
          255 and 256 bytes, signing that needs many rejection rounds,
          wrong key and signature lengths.

Results are reported in stages, the same shape --audit-kem uses:

  edgeValid   a valid vector must produce exactly the recorded bytes
  edgeEk      an invalid encapsulation key must be refused (FIPS 203 §7.2)
  edgeDk      an invalid decapsulation key must be refused (FIPS 203 §7.3)
  edgeLength  a wrong-length input must be refused (Python APIs only: a C
              entry point takes fixed-size buffers, so it cannot be asked)
  sigVerify   ML-DSA: verify must accept exactly the valid signatures
  sigGen      ML-DSA: deterministic signing must reproduce the signature

Sources and commits: pq_verify/vectors/EDGE_MANIFEST.json.
"""
import gzip
import json
import os

_VEC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vectors")
BUNDLE = os.path.join(_VEC, "edge_vectors.json.gz")
MANIFEST = os.path.join(_VEC, "EDGE_MANIFEST.json")

KEM_SETS = ("ML-KEM-512", "ML-KEM-768", "ML-KEM-1024")
DSA_SETS = ("ML-DSA-44", "ML-DSA-65", "ML-DSA-87")
KEM_STAGES = ("edgeValid", "edgeEk", "edgeDk", "edgeLength")
DSA_STAGES = ("sigVerify", "sigGen", "edgeLength")

_bundle_cache = None

# Defects in the pinned reference versions (constraints-reference.txt) that
# these vectors expose. They are reported, never masked: a run against these
# versions is FINDINGS PRESENT. tools/doctor.py compares each run with this
# table, so a new disagreement is a BLOCK and a fixed one is flagged for
# removal.
KNOWN_REFERENCE_DEFECTS = {
    ("dilithium-py", "1.4.0"): {
        "stage": "sigVerify",
        "cases": {"ML-DSA-44": "mldsa_44_verify #18 ",
                  "ML-DSA-65": "mldsa_65_verify #19 ",
                  "ML-DSA-87": "mldsa_87_verify #21 "},
        "summary": ("accepts a signature whose hint list repeats an index; "
                    "FIPS 204 Algorithm 21 (HintBitUnpack) requires strictly "
                    "increasing indices, so the signature is malleable"),
        "upstream": ("fixed in GiacomoPope/dilithium-py bd9b552 (2026-06-09, "
                     "`<` became `<=`); no release contains it yet"),
    },
}


def _reference_version(name):
    try:
        from importlib import metadata
        return metadata.version(name)
    except Exception:
        return None


def known_defect(reference, param_set, failure):
    """The KNOWN_REFERENCE_DEFECTS entry this failure matches, or None."""
    d = KNOWN_REFERENCE_DEFECTS.get((reference, _reference_version(reference)))
    if not d or failure["stage"] != d["stage"]:
        return None
    frag = d["cases"].get(param_set)
    return d if frag and frag in failure["case"] + " " else None


def _bundle():
    global _bundle_cache
    if _bundle_cache is None:
        with gzip.open(BUNDLE, "rt", encoding="utf-8") as fh:
            _bundle_cache = json.load(fh)
    return _bundle_cache


def sources():
    """'Wycheproof 3fa63dd, CCTV 50a8ecf' -- what a report cites."""
    with open(MANIFEST) as fh:
        s = json.load(fh)["sources"]
    return f"Wycheproof {s['wycheproof']['commit'][:7]}, CCTV {s['cctv']['commit'][:7]}"


def _h(x):
    return bytes.fromhex(x) if x else b""


def _cctv_records(text):
    """CCTV .txt: 'name = hex' lines; a blank line ends a record."""
    recs, cur = [], {}
    for line in text.splitlines():
        line = line.strip()
        if not line:
            if cur:
                recs.append(cur); cur = {}
            continue
        if " = " in line:
            k, v = line.split(" = ", 1)
            cur[k.strip()] = v.strip()
    if cur:
        recs.append(cur)
    return recs


# ───────────────────────── ML-KEM case generation ─────────────────────────
#
# Each case is (stage, case_id, flags, kind, args, expected):
#   kind 'keygen'  args (d, z)          expected (ek, dk or None)
#   kind 'encaps'  args (ek, m)         expected (c, K) or None (must refuse)
#   kind 'decaps'  args (dk, c)         expected K or None (must refuse)

def kem_cases(param_set):
    level = param_set.rsplit("-", 1)[1]
    b = _bundle()
    out = []

    wp = json.loads(b[f"wycheproof/testvectors_v1/mlkem_{level}_test.json"])
    for g in wp["testGroups"]:
        src = g["source"]["name"]
        for t in g["tests"]:
            cid = f"wycheproof mlkem_{level}_test #{t['tcId']} ({src})"
            fl = tuple(t.get("flags", ()))
            seed, c = _h(t["seed"]), _h(t["c"])
            if t["result"] == "valid":
                d, z = seed[:32], seed[32:]
                out.append(("edgeValid", cid, fl, "keygen", (d, z),
                            (_h(t["ek"]) if t.get("ek") else None, None)))
                out.append(("edgeValid", cid, fl, "decaps_seed", (d, z, c), _h(t["K"])))
            else:
                # 'Private key too short/long', 'Ciphertext too short/long'
                out.append(("edgeLength", cid, fl, "decaps_seed_len",
                            (seed, c), None))

    wp = json.loads(b[f"wycheproof/testvectors_v1/mlkem_{level}_encaps_test.json"])
    for g in wp["testGroups"]:
        src = g["source"]["name"]
        for t in g["tests"]:
            cid = f"wycheproof mlkem_{level}_encaps_test #{t['tcId']} ({src})"
            fl = tuple(t.get("flags", ()))
            ek, m = _h(t["ek"]), _h(t["m"])
            if t["result"] == "valid":
                out.append(("edgeValid", cid, fl, "encaps", (ek, m), (_h(t["c"]), _h(t["K"]))))
            elif "ModulusOverflow" in fl or "not reduced" in t.get("comment", ""):
                # Wycheproof's own "Public key not reduced" cases carry no flag
                out.append(("edgeEk", cid, fl, "encaps", (ek, m), None))
            else:
                out.append(("edgeLength", cid, fl, "encaps", (ek, m), None))

    wp = json.loads(b[f"wycheproof/testvectors_v1/mlkem_{level}_semi_expanded_decaps_test.json"])
    for g in wp["testGroups"]:
        for t in g["tests"]:
            cid = f"wycheproof mlkem_{level}_semi_expanded_decaps_test #{t['tcId']}"
            fl = tuple(t.get("flags", ()))
            dk, c = _h(t["dk"]), _h(t["c"])
            if t["result"] == "valid":
                out.append(("edgeValid", cid, fl, "decaps", (dk, c), _h(t["K"])))
            elif "InvalidDecapsulationKey" in fl:
                out.append(("edgeDk", cid, fl, "decaps", (dk, c), None))
            else:
                out.append(("edgeLength", cid, fl, "decaps", (dk, c), None))

    for r in _cctv_records(b[f"cctv/ML-KEM/strcmp/ML-KEM-{level}.txt"]):
        out.append(("edgeValid", f"cctv strcmp ML-KEM-{level}", ("Strcmp",),
                    "decaps", (_h(r["dk"]), _h(r["c"])), _h(r["K"])))

    for r in _cctv_records(b[f"cctv/ML-KEM/unluckysample/ML-KEM-{level}.txt"]):
        cid = f"cctv unluckysample ML-KEM-{level}"
        # No keygen check: CCTV derived these keys with FIPS 203 ipd's G(d),
        # not the final G(d || k), so the recorded ek/dk are not what a
        # conforming KeyGen produces from d. Encaps with the recorded ek
        # still expands the unlucky matrix, which is what the vector is for.
        out.append(("edgeValid", cid, ("UnluckySample",), "encaps",
                    (_h(r["ek"]), _h(r["m"])), (_h(r["c"]), _h(r["K"]))))
        out.append(("edgeValid", cid, ("UnluckySample",), "decaps",
                    (_h(r["dk"]), _h(r["c"])), _h(r["K"])))

    m = bytes(32)
    lines = [ln for ln in b[f"cctv/ML-KEM/modulus/ML-KEM-{level}.txt"].splitlines() if ln.strip()]
    for i, ln in enumerate(lines):
        out.append(("edgeEk", f"cctv modulus ML-KEM-{level} line {i + 1}",
                    ("ModulusOverflow",), "encaps", (_h(ln.strip()), m), None))
    return out


# ────────────────────────────── KEM backends ──────────────────────────────

class ReferenceKEM:
    """kyber-py, the reference pq-verify's ACVP checks trust."""
    name = "kyber-py"
    fixed_buffers = False

    def __init__(self, param_set):
        from kyber_py import ml_kem
        self.k = getattr(ml_kem, param_set.replace("-", "_"))

    def keygen(self, d, z):
        return self.k._keygen_internal(d, z)

    def keygen_seed(self, seed):
        return self.k.key_derive(seed)

    def encaps(self, ek, m):
        K, c = self.k._encaps_internal(ek, m)
        return c, K

    def decaps(self, dk, c):
        return self.k.decaps(dk, c)


class VendorKEM:
    """A vendor library's *_keypair_derand / *_enc_derand / *_dec via ctypes.
    A nonzero return code is a refusal."""
    fixed_buffers = True

    def __init__(self, keypair, encaps, decaps, sizes, name="vendor"):
        self.kp, self.en, self.de = keypair, encaps, decaps
        self.ek_n, self.dk_n, self.ct_n = sizes
        self.name = name

    def keygen(self, d, z):
        import ctypes
        ek = ctypes.create_string_buffer(self.ek_n)
        dk = ctypes.create_string_buffer(self.dk_n)
        rc = self.kp(ek, dk, ctypes.create_string_buffer(d + z, 64))
        if rc != 0:
            raise ValueError(f"keypair_derand returned {rc}")
        return ek.raw, dk.raw

    def keygen_seed(self, seed):
        return self.keygen(seed[:32], seed[32:])

    def encaps(self, ek, m):
        import ctypes
        ct = ctypes.create_string_buffer(self.ct_n)
        ss = ctypes.create_string_buffer(32)
        rc = self.en(ct, ss, ctypes.create_string_buffer(ek, len(ek)),
                     ctypes.create_string_buffer(m, 32))
        if rc != 0:
            raise ValueError(f"enc_derand returned {rc}")
        return ct.raw, ss.raw

    def decaps(self, dk, c):
        import ctypes
        ss = ctypes.create_string_buffer(32)
        rc = self.de(ss, ctypes.create_string_buffer(c, len(c)),
                     ctypes.create_string_buffer(dk, len(dk)))
        if rc != 0:
            raise ValueError(f"dec returned {rc}")
        return ss.raw


def _kem_lengths_ok(backend, kind, args, param_set):
    """Can this input be put to a fixed-buffer C entry point at all?"""
    accepts = getattr(backend, "accepts", None)
    if accepts is not None and not accepts(kind, args):
        return False
    if not backend.fixed_buffers:
        return True
    from .core import _KEM_SIZES
    ek_n, dk_n, ct_n = _KEM_SIZES[param_set][:3]
    if kind == "encaps":
        return len(args[0]) == ek_n and len(args[1]) == 32
    if kind == "decaps":
        return len(args[0]) == dk_n and len(args[1]) == ct_n
    if kind == "decaps_seed_len":
        return False          # a C entry point takes a fixed-size seed
    if kind == "decaps_seed":
        return len(args[2]) == ct_n
    return True


def _run_kem_case(backend, kind, args, expected):
    """Returns (ok, detail)."""
    try:
        if kind == "keygen":
            ek, dk = backend.keygen(*args)
            want_ek, want_dk = expected
            if want_ek is not None and ek != want_ek:
                return False, "ek differs"
            if want_dk is not None and dk != want_dk:
                return False, "dk differs"
            return True, ""
        if kind == "decaps_seed":
            d, z, c = args
            _, dk = backend.keygen(d, z)
            K = backend.decaps(dk, c)
            return (K == expected), ("" if K == expected else "K differs")
        if kind == "decaps_seed_len":
            seed, c = args
            _, dk = backend.keygen_seed(seed)
            backend.decaps(dk, c)
            return False, "wrong-length input accepted"
        if kind == "encaps":
            c, K = backend.encaps(*args)
            if expected is None:
                return False, "invalid encapsulation key accepted"
            if (c, K) != expected:
                return False, "c differs" if c != expected[0] else "K differs"
            return True, ""
        if kind == "decaps":
            K = backend.decaps(*args)
            if expected is None:
                return False, "invalid input accepted"
            return (K == expected), ("" if K == expected else "K differs")
    except Exception as e:  # a refusal
        if expected is None or kind == "decaps_seed_len":
            return True, ""
        return False, f"refused a valid input: {type(e).__name__}: {str(e)[:80]}"
    raise ValueError(kind)


def run_kem(backend, param_set, max_failures=20):
    stages = {s: [0, 0] for s in KEM_STAGES}
    failures, na = [], 0
    for stage, cid, flags, kind, args, expected in kem_cases(param_set):
        if not _kem_lengths_ok(backend, kind, args, param_set):
            na += 1
            continue
        ok, why = _run_kem_case(backend, kind, args, expected)
        stages[stage][1] += 1
        stages[stage][0] += ok
        if not ok and len(failures) < max_failures:
            failures.append({"stage": stage, "case": cid, "flags": list(flags),
                             "detail": why})
    stages = {k: v for k, v in stages.items() if v[1]}
    return {"stages": stages, "failures": failures, "not_applicable": na}


# ─────────────────────────────── ML-DSA ───────────────────────────────

def dsa_cases(param_set):
    level = param_set.rsplit("-", 1)[1]
    b = _bundle()
    out = []
    wp = json.loads(b[f"wycheproof/testvectors_v1/mldsa_{level}_verify_test.json"])
    for g in wp["testGroups"]:
        pk = _h(g["publicKey"])
        src = g["source"]["name"]
        for t in g["tests"]:
            fl = tuple(t.get("flags", ()))
            stage = "edgeLength" if any(f in fl for f in (
                "IncorrectPublicKeyLength", "IncorrectSignatureLength")) else "sigVerify"
            out.append((stage, f"wycheproof mldsa_{level}_verify #{t['tcId']} ({src})",
                        fl, "verify",
                        (pk, _h(t.get("msg", "")), _h(t["sig"]), _h(t.get("ctx", "")),
                         "ctx" in t),
                        t["result"] == "valid"))
    wp = json.loads(b[f"wycheproof/testvectors_v1/mldsa_{level}_sign_seed_test.json"])
    for g in wp["testGroups"]:
        seed, pk = _h(g["privateSeed"]), _h(g["publicKey"])
        src = g["source"]["name"]
        for t in g["tests"]:
            fl = tuple(t.get("flags", ()))
            cid = f"wycheproof mldsa_{level}_sign_seed #{t['tcId']} ({src})"
            if t["result"] != "valid":
                stage = "edgeLength" if "IncorrectPrivateKeyLength" in fl else "sigGen"
                out.append((stage, cid, fl, "sign",
                            (seed, pk, t.get("msg"), t.get("mu"), _h(t.get("ctx", "")),
                             t.get("rnd")), None))
            else:
                out.append(("sigGen", cid, fl, "sign",
                            (seed, pk, t.get("msg"), t.get("mu"), _h(t.get("ctx", "")),
                             t.get("rnd")), _h(t["sig"])))
    return out


class ReferenceDSA:
    name = "dilithium-py"

    def __init__(self, param_set):
        from dilithium_py import ml_dsa
        self.d = getattr(ml_dsa, param_set.replace("-", "_"))

    def verify(self, pk, msg, sig, ctx):
        return bool(self.d.verify(pk, msg, sig, ctx))

    def sign(self, seed, msg, mu, ctx, rnd):
        pk, sk = self.d.key_derive(seed)
        if mu is not None and msg is None:
            # Sign_internal with an external mu, deterministic unless rnd given
            if rnd is None:
                return pk, self.d.sign_external_mu(sk, _h(mu), deterministic=True)
            raise NotImplementedError("external mu with rnd")
        if len(ctx) > 255:
            raise ValueError("ctx longer than 255 bytes")
        m_prime = bytes([0, len(ctx)]) + ctx + _h(msg)
        r = _h(rnd) if rnd is not None else bytes(32)
        return pk, self.d._sign_internal(sk, m_prime, r)


def run_dsa(backend, param_set, max_failures=20):
    stages = {s: [0, 0] for s in DSA_STAGES}
    failures = []
    na = 0
    for stage, cid, flags, kind, args, expected in dsa_cases(param_set):
        try:
            if kind == "verify":
                pk, msg, sig, ctx, _ = args
                got = backend.verify(pk, msg, sig, ctx)
                ok, why = (got == expected), ("" if got == expected else
                                               f"verify returned {got}, expected {expected}")
            else:
                seed, pk, msg, mu, ctx, rnd = args
                got_pk, sig = backend.sign(seed, msg, mu, ctx, rnd)
                if expected is None:
                    ok, why = False, "invalid signing input accepted"
                elif got_pk != pk:
                    ok, why = False, "public key from seed differs"
                else:
                    ok, why = (sig == expected), ("" if sig == expected else "signature differs")
        except NotImplementedError:
            # The backend cannot express this case (a fixed-size argument, a
            # mode it lacks). Counted, never scored as a pass.
            na += 1
            continue
        except Exception as e:
            if kind == "verify":
                ok = expected is False
            else:
                ok = expected is None
            why = "" if ok else f"raised {type(e).__name__}: {str(e)[:80]}"
        stages[stage][1] += 1
        stages[stage][0] += ok
        if not ok and len(failures) < max_failures:
            failures.append({"stage": stage, "case": cid, "flags": list(flags),
                             "detail": why})
    stages = {k: v for k, v in stages.items() if v[1]}
    return {"stages": stages, "failures": failures, "not_applicable": na}


# ─────────────────────────────── entry point ───────────────────────────────

def pqverify_edge(param_sets=None, verbose=True):
    """Run the pinned edge-case vectors against pq-verify's own references
    (kyber-py, dilithium-py). Returns a result dict; None when neither
    reference is installed.

    A finding here is a finding about a library pq-verify trusts to grade
    everyone else, so it is reported, never hidden.
    """
    sets = list(param_sets or (KEM_SETS + DSA_SETS))
    results, missing = {}, []
    for ps in sets:
        try:
            if ps.startswith("ML-KEM"):
                results[ps] = run_kem(ReferenceKEM(ps), ps)
                results[ps]["reference"] = "kyber-py"
            else:
                results[ps] = run_dsa(ReferenceDSA(ps), ps)
                results[ps]["reference"] = "dilithium-py"
        except ImportError as e:
            missing.append(str(e).split("'")[1] if "'" in str(e) else str(e))
            continue
        for f in results[ps]["failures"]:
            d = known_defect(results[ps]["reference"], ps, f)
            if d:
                f["known_defect"] = f"{d['summary']}; {d['upstream']}"
    if not results:
        if verbose:
            print("  edge vectors: CANNOT VERIFY -- neither kyber-py nor dilithium-py "
                  "is installed (pip install \"pq-verify[full]\")")
        return None
    passed = sum(v[0] for r in results.values() for v in r["stages"].values())
    total = sum(v[1] for r in results.values() for v in r["stages"].values())
    status = "VERIFIED" if passed == total else "FINDINGS PRESENT"
    out = {"status": status, "verified": passed == total, "passed": passed,
           "total": total, "sets": results, "vectors": sources(),
           "missing": sorted(set(missing))}
    if verbose:
        _print(out)
    return out


_REFERENCE_RUN = []


def reference_run():
    """pqverify_edge() over every set, quietly, computed once per process:
    the installed references cannot change while it runs (tools/doctor.py
    and the tests call this repeatedly)."""
    if not _REFERENCE_RUN:
        _REFERENCE_RUN.append(pqverify_edge(verbose=False))
    return _REFERENCE_RUN[0]


def _print(out):
    print(f"\n  EDGE-CASE VECTORS  ({out['vectors']})")
    for ps, r in out["sets"].items():
        cells = "  ".join(f"{k} {v[0]}/{v[1]}" for k, v in r["stages"].items())
        mark = "✅" if all(v[0] == v[1] for v in r["stages"].values()) else "❌"
        na = f"  ({r['not_applicable']} n/a)" if r["not_applicable"] else ""
        print(f"  {mark} {ps:12s} [{r['reference']}]  {cells}{na}")
        for f in r["failures"][:5]:
            print(f"       ✗ {f['stage']}: {f['case']} {f['flags']} -- {f['detail']}")
            if f.get("known_defect"):
                print(f"         known {r['reference']} {_reference_version(r['reference'])} "
                      f"defect: {f['known_defect']}")
        if len(r["failures"]) > 5:
            print(f"       ... {len(r['failures']) - 5} more")
    if out["missing"]:
        print(f"  ⏭  not run: {', '.join(out['missing'])} not installed")
    print(f"  {out['status']}: {out['passed']}/{out['total']}")
