#!/usr/bin/env python3
"""
pq-verify — VENDOR AUDIT TEMPLATE
==================================
Audit the NTT that your compiled ML-KEM or ML-DSA library exports, and get
pq-verify's JSON report. This file runs one command:

    pq-verify --audit-so <library> <symbol> --json pqverify_vendor_report.json

pq-verify loads the library in a child process with a timeout, checks its NTT
against the FIPS 203 or FIPS 204 definition, and binds the verdict to the
sha256 of every shared object that ran. Only the library's own code is judged.

The NTT is one function of the scheme. To audit a whole ML-KEM or ML-DSA
implementation against NIST's ACVP vectors, run `pq-verify --audit-kem` or
`pq-verify --audit-dsa` on it (README.md).

USAGE (Linux, Python 3.9+, gcc):
    1. Install:           pip install pq-verify
    2. Edit the CONFIG block below (3 lines).
    3. Run this file:     python vendor_audit_template.py

Output: pq-verify's console report, pqverify_vendor_report.json, and its exit
code: 0 verified; 1 not verified (findings, or an NTT that could not be run:
a symbol not found, which the report answers with the library's NTT symbols,
a crash or a hang); 2 not audited (the library could not be read or loaded).

Auditing a library runs its code. Audit one you do not trust inside a
container or a VM (SECURITY.md).
"""

import os
import subprocess
import sys

# ============================================================
# CONFIG — edit these three lines
# ============================================================
SO_PATH    = "./libkyber_ntt.so"   # path to your compiled library
NTT_SYMBOL = "ntt"                 # its exported NTT: nm -D <library> | grep -i ntt
SCHEME     = "ML-KEM"              # "ML-KEM" or "ML-DSA"

REPORT = "pqverify_vendor_report.json"

_SCHEMES = {"ML-KEM": "mlkem", "ML-DSA": "mldsa"}


def scheme_problem(so_path, symbol, scheme):
    """Why --audit-so would audit this NTT as the other scheme, or None.

    --audit-so tells ML-DSA from ML-KEM by name: for ML-DSA, the symbol or
    the library's path must contain mldsa, ml_dsa, ml-dsa, dilithium or
    fips204, and any other name is audited as ML-KEM. The two differ in more
    than the modulus: ML-DSA's coefficients are int32 and ML-KEM's int16, so
    an ML-DSA NTT read as ML-KEM writes past the buffer it is given. This asks
    the function --audit-so itself uses."""
    from pq_verify.core import _detect_scheme
    if scheme not in _SCHEMES:
        return f"SCHEME must be 'ML-KEM' or 'ML-DSA', not {scheme!r}"
    seen = _detect_scheme(symbol, os.path.abspath(os.path.expanduser(so_path))) or "mlkem"
    if seen != _SCHEMES[scheme]:
        other = "ML-DSA" if seen == "mldsa" else "ML-KEM"
        return (f"--audit-so would audit {symbol} in {so_path} as {other}, not "
                f"{scheme}: it tells the two apart by name. Name the library or the "
                f"symbol so that it contains {_SCHEMES[scheme]}")
    return None


def main():
    try:
        why = scheme_problem(SO_PATH, NTT_SYMBOL, SCHEME)
    except ImportError:
        print("  pq-verify is not installed: pip install pq-verify")
        return 2
    if why:
        print(f"  cannot audit: {why}")
        return 2
    # This script's own output from an earlier run would otherwise be taken
    # for the report of a run that wrote none.
    if os.path.exists(REPORT):
        os.remove(REPORT)
    code = subprocess.call([sys.executable, "-m", "pq_verify.cli",
                            "--audit-so", SO_PATH, NTT_SYMBOL, "--json", REPORT])
    if os.path.exists(REPORT):
        print(f"  report: {REPORT} (exit code {code})")
    else:
        print(f"  no report: the library was not audited (exit code {code})")
    return code


if __name__ == "__main__":
    sys.exit(main())
