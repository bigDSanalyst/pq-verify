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
                   help="full NIST ACVP end-to-end ML-KEM (all groups)")
    p.add_argument("--mldsa-acvp", action="store_true",
                   help="full NIST ACVP end-to-end ML-DSA (FIPS 204, 615 vectors)")
    p.add_argument("--acvp-all", action="store_true",
                   help="both ACVP suites: ML-KEM + ML-DSA (855 pinned vectors)")
    p.add_argument("--live", action="store_true",
                   help="fetch NIST's CURRENT vectors instead of the pinned "
                        "bundle (needs network; results may change between runs)")
    p.add_argument("--vector-dir", metavar="DIR",
                   help="verify against your own local ACVP vector directory")
    p.add_argument("--params", metavar="SET",
                   help="parameter security check (e.g. ML-KEM-512/768/1024)")
    p.add_argument("--kem", metavar="K", type=int, choices=(2, 3, 4),
                   help="native full-KEM verification at module rank K")
    p.add_argument("--leakage", action="store_true",
                   help="per-layer side-channel protection-allocation table")
    p.add_argument("--audit-so", nargs=2, metavar=("PATH", "SYM"),
                   help="audit an NTT symbol SYM inside compiled library PATH")
    p.add_argument("--json", metavar="FILE",
                   help="write results to FILE in pq-verify's native schema")
    p.add_argument("--sarif", metavar="FILE",
                   help="write SARIF 2.1.0 to FILE — ingested natively by GitHub "
                        "Code Scanning, DefectDojo, Snyk, AWS Security Hub")
    p.add_argument("--fail-on-finding", action="store_true",
                   help="exit non-zero if any finding is reported (CI gating)")
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)

    # If a specific task is requested, run just that task.
    ran_task = False
    _vsrc = dict(live=getattr(args, "live", False),
                 vector_dir=getattr(args, "vector_dir", None))
    if args.acvp:
        pqverify_acvp(**_vsrc); ran_task = True
    if getattr(args, "mldsa_acvp", False):
        pqverify_mldsa_acvp(**_vsrc); ran_task = True
    if getattr(args, "acvp_all", False):
        pqverify_acvp_all(**_vsrc); ran_task = True
    if args.params:
        pqverify_params(args.params); ran_task = True
    if args.kem:
        pqverify_kem(k=args.kem); ran_task = True
    if args.leakage:
        pqverify_leakage(); ran_task = True
    scan_results = None
    if args.audit_so:
        path, sym = args.audit_so
        ntt = pqverify_load_so(path, sym)
        scan_results = pqverify_scan(ntt); ran_task = True

    # Default: run the self-suite.
    if not ran_task:
        run_selftest(quick=args.quick)

    # ---- machine-readable output --------------------------------------
    exit_code = 0
    if scan_results is not None and (args.json or args.sarif or args.fail_on_finding):
        from .report import to_json, to_sarif, write
        from .core import VERSION
        if args.json:
            write(args.json, to_json(scan_results))
            print(f"  wrote {args.json}")
        if args.sarif:
            write(args.sarif, to_sarif(scan_results, tool_version=VERSION))
            print(f"  wrote {args.sarif}")
        findings = sum(len(r.get("findings", [])) for r in scan_results)
        if args.fail_on_finding and findings:
            print(f"  FAILING: {findings} finding(s)")
            exit_code = 1

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
