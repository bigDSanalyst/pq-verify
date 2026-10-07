"""A Crucible-protocol harness over kyber-py and dilithium-py, for tests.

    python crucible_ref_harness.py [FAULT]

FAULT plants one defect so pq-verify's harness audit can be shown to catch
it (or to refuse to score it):
  no-ek-check    Encaps accepts an encapsulation key with a coefficient >= q
  seedless       KeyGen ignores its seed (as some real harnesses do)
  external       ML_DSA_Sign and ML_DSA_Verify both treat "message" as M with
                 an empty context (FIPS 204 external), as Crucible's CIRCL and
                 liboqs harnesses do, instead of the protocol's M'
  external-sign  only ML_DSA_Sign does: sign and verify disagree
  sigma-only     ML_DSA_Verify reads the signature from "sigma" only, as
                 Crucible's battery sends it and its CIRCL harness reads it
  seed-dk        keeps decapsulation keys as the seed d || z, as Go's
                 crypto/mlkem does (correct; FIPS 203 §7.1 allows it)
  crash-after=N  exits after N requests
  hang-after=N   stops answering after N requests
  lie-unsupported  answers "unsupported" for Decaps, which it advertises
"""
import json
import os
import sys
import time

from kyber_py.ml_kem import ML_KEM_512, ML_KEM_768, ML_KEM_1024
from dilithium_py.ml_dsa import ML_DSA_44, ML_DSA_65, ML_DSA_87

FAULT = sys.argv[1] if len(sys.argv) > 1 else ""
KEM = {512: ML_KEM_512, 768: ML_KEM_768, 1024: ML_KEM_1024}
DSA = {44: ML_DSA_44, 65: ML_DSA_65, 87: ML_DSA_87}
KEM_BY_EK = {384 * k + 32: v for k, v in ((2, ML_KEM_512), (3, ML_KEM_768),
                                          (4, ML_KEM_1024))}
KEM_BY_DK = {768 * k + 96: v for k, v in ((2, ML_KEM_512), (3, ML_KEM_768),
                                          (4, ML_KEM_1024))}
DSA_BY_PK = {1312: ML_DSA_44, 1952: ML_DSA_65, 2592: ML_DSA_87}
DSA_BY_SK = {2560: ML_DSA_44, 4032: ML_DSA_65, 4896: ML_DSA_87}


def out(obj):
    sys.stdout.write(json.dumps(obj) + "\n")
    sys.stdout.flush()


def handle(req):
    fn, i, p = req["function"], {k: bytes.fromhex(v) for k, v in req["inputs"].items()}, \
        req.get("params", {})
    if fn == "ML_KEM_KeyGen":
        r = os.urandom(64) if FAULT == "seedless" else i["randomness"]
        ek, dk = KEM[p["param_set"]]._keygen_internal(r[:32], r[32:])
        return {"ek": ek, "dk": r if FAULT == "seed-dk" else dk}
    if fn == "ML_KEM_Encaps":
        kem = KEM_BY_EK.get(len(i["ek"]))
        if kem is None:
            raise ValueError("bad ek length")
        if FAULT == "no-ek-check":
            # A lax decoder: reduce every 12-bit coefficient mod q and go on,
            # as a library without FIPS 203's modulus check does.
            ek, t = i["ek"], int.from_bytes(i["ek"][:-32], "little")
            n = (len(ek) - 32) * 8 // 12
            red = sum(((t >> (12 * j)) & 0xFFF) % 3329 << (12 * j) for j in range(n))
            reduced = red.to_bytes(len(ek) - 32, "little") + ek[-32:]
            K, r = kem._G(i["randomness"] + kem._H(ek))
            c = kem._k_pke_encrypt(reduced, i["randomness"], r)
        else:
            K, c = kem._encaps_internal(i["ek"], i["randomness"])
        return {"c": c, "K": K}
    if fn == "ML_KEM_Decaps":
        if FAULT == "lie-unsupported":
            return None
        dk = i["dk"]
        if FAULT == "seed-dk":
            if len(dk) != 64:
                raise ValueError("dk must be the 64-byte seed")
            kem = {1088: ML_KEM_768, 768: ML_KEM_512, 1568: ML_KEM_1024}[len(i["c"])]
            dk = kem._keygen_internal(dk[:32], dk[32:])[1]
        kem = KEM_BY_DK.get(len(dk))
        if kem is None:
            raise ValueError("bad dk length")
        return {"K": kem._decaps_internal(dk, i["c"])}
    if fn == "ML_DSA_KeyGen":
        seed = os.urandom(32) if FAULT == "seedless" else i["seed"]
        pk, sk = DSA[p["param_set"]]._keygen_internal(seed)
        return {"pk": pk, "sk": sk}
    if fn == "ML_DSA_Sign":
        dsa = DSA_BY_SK.get(len(i["sk"]))
        if dsa is None:
            raise ValueError("bad sk length")
        m = (b"\x00\x00" + i["message"]) if FAULT in ("external", "external-sign") \
            else i["message"]
        return {"signature": dsa._sign_internal(i["sk"], m, i["rnd"])}
    if fn == "ML_DSA_Verify":
        dsa = DSA_BY_PK.get(len(i["pk"]))
        if dsa is None:
            raise ValueError("bad pk length")
        sig = i["sigma"] if FAULT == "sigma-only" else i["signature"]
        m = (b"\x00\x00" + i["message"]) if FAULT == "external" else i["message"]
        ok = dsa._verify_internal(i["pk"], m, sig)
        return {"valid": b"\x01" if ok else b"\x00"}
    return None


def main():
    out({"implementation": f"pq-verify reference harness{' (' + FAULT + ')' if FAULT else ''}",
         "functions": ["ML_KEM_KeyGen", "ML_KEM_Encaps", "ML_KEM_Decaps",
                       "ML_DSA_KeyGen", "ML_DSA_Sign", "ML_DSA_Verify"]})
    n = 0
    for line in sys.stdin:
        if not line.strip():
            break
        n += 1
        if FAULT.startswith("crash-after=") and n > int(FAULT.split("=")[1]):
            os._exit(3)
        if FAULT.startswith("hang-after=") and n > int(FAULT.split("=")[1]):
            time.sleep(3600)
        try:
            res = handle(json.loads(line))
        except Exception as exc:              # a refusal, as the protocol says
            out({"error": f"{type(exc).__name__}: {exc}"})
            continue
        if res is None:
            out({"unsupported": True})
        else:
            out({"outputs": {k: v.hex() for k, v in res.items()}})


if __name__ == "__main__":
    main()
