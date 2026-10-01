"""General proofs shipped with pq-verify, checked by Coq on request.

pq_verify/coq/ holds theorems that quantify over EVERY input, not the inputs
a run happens to test:

  Reduce.v  montgomery_reduce (ML-KEM and ML-DSA), barrett_reduce (ML-KEM,
            all 65,536 int16 inputs), reduce32 (ML-DSA): congruent to the
            input and within the stated bound, for every input in range; no
            intermediate overflows its C type.
  NTT.v     the FIPS 203 and FIPS 204 forward NTT equal the Chinese-remainder
            map they are defined to compute, for every 256-coefficient input.

`pq-verify --proofs` compiles each file with coqc and requires every theorem
to print "Closed under the global context": an Admitted proof or an added
axiom fails, although coqc itself would accept it.
"""
import os
import shutil
import tempfile
import time

FILES = ("Reduce.v", "NTT.v")


def _coq_dir():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "coq")


def theorems(path):
    with open(path) as fh:
        return [ln.split()[2].rstrip(".") for ln in fh
                if ln.startswith("Print Assumptions ")]


def pqverify_proofs(verbose=True, timeout=1200, files=FILES, coq_dir=None):
    """Check the shipped proofs. Returns a result dict; status is VERIFIED,
    FINDINGS PRESENT (a file failed), or CANNOT VERIFY (no coqc)."""
    import subprocess
    from .core import coq_check
    src = coq_dir or _coq_dir()
    if shutil.which("coqc") is None:
        if verbose:
            print("  proofs: CANNOT VERIFY -- coqc not in PATH (apt install coq)")
        return {"status": "CANNOT VERIFY", "verified": False, "passed": 0,
                "total": len(files), "files": {}}
    results = {}
    with tempfile.TemporaryDirectory(prefix="pqv-proofs-") as work:
        for name in files:
            path = os.path.join(work, name)
            shutil.copy(os.path.join(src, name), path)
            t0 = time.perf_counter()
            try:
                ok, detail = coq_check(path, timeout=timeout)
            except subprocess.TimeoutExpired:
                ok, detail = False, f"coqc timed out after {timeout}s"
            results[name] = {"ok": ok, "detail": detail,
                             "theorems": theorems(path),
                             "seconds": round(time.perf_counter() - t0, 1)}
            if verbose:
                mark = "✅" if ok else "❌"
                print(f"  {mark} {name:9s} {len(results[name]['theorems'])} theorems  "
                      f"{detail}  ({results[name]['seconds']}s)")
    passed = sum(r["ok"] for r in results.values())
    status = "VERIFIED" if passed == len(files) else "FINDINGS PRESENT"
    if verbose:
        print(f"  PROOFS {status}: {passed}/{len(files)} files")
    return {"status": status, "verified": passed == len(files), "passed": passed,
            "total": len(files), "files": results}
