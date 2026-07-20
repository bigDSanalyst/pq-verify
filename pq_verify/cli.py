"""
pq-verify command-line interface.

    pq-verify                      run the 160-test self-suite
    pq-verify --quick              fast subset of the self-suite
    pq-verify --acvp               full NIST ACVP (all 12 ML-KEM groups)
    pq-verify --params SET         parameter security (e.g. ML-KEM-1024)
    pq-verify --kem K              native full-KEM at module rank K (2/3/4)
    pq-verify --leakage            per-layer protection-allocation table
    pq-verify --audit-so PATH SYM  audit an NTT in a compiled .so
    pq-verify --version
"""
import argparse
import sys

from . import __version__
from .core import (
    main as run_selftest,
    pqverify_acvp,
    pqverify_mldsa_acvp,
    pqverify_acvp_all,
    pqverify_params,
    pqverify_kem,
    pqverify_leakage,
    pqverify_load_so,
    pqverify_scan,
)


def build_parser():
    p = argparse.ArgumentParser(
        prog="pq-verify",
        description="Independent verification for ML-KEM / ML-DSA implementations.",
    )
    p.add_argument("--version", action="version",
                   version=f"pq-verify {__version__}")
    p.add_argument("--quick", action="store_true",
                   help="run a fast subset of the self-suite")
    p.add_argument("--acvp", action="store_true",
                   help="full NIST ACVP end-to-end ML-KEM (all 12 groups)")
    p.add_argument("--mldsa-acvp", action="store_true",
                   help="full NIST ACVP end-to-end ML-DSA (FIPS 204, 615 vectors)")
    p.add_argument("--acvp-all", action="store_true",
                   help="both ACVP suites: ML-KEM + ML-DSA (855 vectors)")
    p.add_argument("--params", metavar="SET",
                   help="parameter security check (e.g. ML-KEM-512/768/1024)")
    p.add_argument("--kem", metavar="K", type=int, choices=(2, 3, 4),
                   help="native full-KEM verification at module rank K")
    p.add_argument("--leakage", action="store_true",
                   help="per-layer side-channel protection-allocation table")
    p.add_argument("--audit-so", nargs=2, metavar=("PATH", "SYM"),
                   help="audit an NTT symbol SYM inside compiled library PATH")
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)

    # If a specific task is requested, run just that task.
    ran_task = False
    if args.acvp:
        pqverify_acvp(); ran_task = True
    if getattr(args, "mldsa_acvp", False):
        pqverify_mldsa_acvp(); ran_task = True
    if getattr(args, "acvp_all", False):
        pqverify_acvp_all(); ran_task = True
    if args.params:
        pqverify_params(args.params); ran_task = True
    if args.kem:
        pqverify_kem(k=args.kem); ran_task = True
    if args.leakage:
        pqverify_leakage(); ran_task = True
    if args.audit_so:
        path, sym = args.audit_so
        ntt = pqverify_load_so(path, sym)
        pqverify_scan(ntt); ran_task = True

    # Default: run the self-suite.
    if not ran_task:
        run_selftest(quick=args.quick)

    return 0


if __name__ == "__main__":
    sys.exit(main())
