"""
pq-verify command-line interface.

    pq-verify                      run the 160-test self-suite
    pq-verify --quick              fast subset of the self-suite
    pq-verify --acvp               full NIST ACVP (all 12 ML-KEM groups)
    pq-verify --params SET         parameter security (e.g. ML-KEM-1024)
    pq-verify --kem K              native full-KEM at module rank K (2/3/4)
    pq-verify --leakage            per-layer protection-allocation table
    pq-verify --audit-so PATH SYM  audit an NTT in a compiled .so
    pq-verify --emit-prompt SET    write the ACVP questions for SET
    pq-verify --verify-response F  check a response against the pinned answers
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
    pqverify_audit_kem,
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
    p.add_argument("--audit-kem", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="audit a full ML-KEM implementation (keygen/encaps/decaps) "
                        "in PATH against NIST vectors, e.g. "
                        "--audit-kem lib.so ML-KEM-768")
    p.add_argument("--emit-prompt", metavar="PARAM_SET",
                   help="write the ACVP question set for PARAM_SET (e.g. "
                        "ML-DSA-65) to a file, for implementations that cannot "
                        "be dlopen'd \u2014 HSMs, sealed vendor binaries. No "
                        "answers are included. Pass 'list' for the available "
                        "parameter sets")
    p.add_argument("--prompt-out", metavar="FILE",
                   help="where --emit-prompt writes (default "
                        "pq-verify-prompt-<PARAM_SET>.json; .gz is honoured)")
    p.add_argument("--verify-response", metavar="FILE",
                   help="check a response file against the pinned expected "
                        "answers, byte-exact and per test case. The result is "
                        "NOT bound to any artifact and says so")
    p.add_argument("--json", metavar="FILE",
                   help="write results to FILE in pq-verify's native schema")
    p.add_argument("--sarif", metavar="FILE",
                   help="write SARIF 2.1.0 to FILE — ingested natively by GitHub "
                        "Code Scanning, DefectDojo, Snyk, AWS Security Hub")
    p.add_argument("--require-full-coverage", action="store_true",
                   help="exit non-zero if any engine or dependency was missing "
                        "(prevents a degraded run from reporting green in CI)")
    p.add_argument("--fail-on-finding", action="store_true",
                   help="exit non-zero if any finding is reported (CI gating)")
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)

    # If a specific task is requested, run just that task.
    ran_task = False
    acvp_results = {}
    _vsrc = dict(live=getattr(args, "live", False),
                 vector_dir=getattr(args, "vector_dir", None))
    if args.acvp:
        acvp_results["ML-KEM (FIPS 203)"] = pqverify_acvp(**_vsrc)
        ran_task = True
    if getattr(args, "mldsa_acvp", False):
        acvp_results["ML-DSA (FIPS 204)"] = pqverify_mldsa_acvp(**_vsrc)
        ran_task = True
    if getattr(args, "acvp_all", False):
        _all = pqverify_acvp_all(**_vsrc)
        acvp_results["ML-KEM (FIPS 203)"] = _all.get("ml_kem")
        acvp_results["ML-DSA (FIPS 204)"] = _all.get("ml_dsa")
        if _all.get("slh_dsa"):
            acvp_results["SLH-DSA (FIPS 205)"] = _all["slh_dsa"]
        ran_task = True
    if args.params:
        pqverify_params(args.params); ran_task = True
    if args.kem:
        pqverify_kem(k=args.kem); ran_task = True
    if args.leakage:
        pqverify_leakage(); ran_task = True
    response_result = None
    if getattr(args, "emit_prompt", None):
        from .response import emit_prompt, available_parameter_sets
        ran_task = True
        if args.emit_prompt.lower() in ("list", "?"):
            sets = available_parameter_sets(**_vsrc)
            print("  parameter sets available from the pinned bundle:")
            for s_ in sets:
                print(f"    {s_}")
            return 0
        try:
            emit_prompt(args.emit_prompt, out_path=args.prompt_out, **_vsrc)
        except ValueError as exc:
            print(f"  {exc}")
            return 2
    if getattr(args, "verify_response", None):
        from .response import verify_response
        response_result = verify_response(args.verify_response, **_vsrc)
        ran_task = True

    from .report import artifact_bound

    scan_results = None
    kem_result = kem_ran = kem_reason = None
    kem_artifact = scan_artifact = None
    if getattr(args, "audit_kem", None):
        from .core import pqverify_audit_kem
        _p, _ps = args.audit_kem
        kem_ran = _ps
        ran_task = True
        # Bind first: the hash is of the file we were pointed at, and it holds
        # whether or not the audit can run. Binding and verdict are separate
        # facts, so a library that cannot be audited is still bound to.
        try:
            kem_artifact = artifact_bound(_p)
        except OSError as exc:
            print(f"  cannot audit {_p}: {exc}")
            return 2
        print(f"  artifact: {kem_artifact['summary']}")
        try:
            kem_result = pqverify_audit_kem(_p, _ps)
        except OSError as exc:
            # Not loadable by the dynamic linker: cannot verify, not a failure.
            kem_result = None
            kem_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {kem_reason}")
    if args.audit_so:
        path, sym = args.audit_so
        # Compile the engines first. Without them pqverify_scan silently omits
        # the Freivalds check and reports 2/2 instead of 3/3 -- a skip that
        # looks like a pass, which is the failure mode this tool exists to
        # prevent in other people's code.
        from .core import compile_all, bind_all
        _eng = compile_all()
        bind_all(_eng)
        ran_task = True
        try:
            scan_artifact = artifact_bound(path)
            print(f"  artifact: {scan_artifact['summary']}")
            ntt = pqverify_load_so(path, sym)
        except (OSError, ValueError) as exc:
            # An unloadable file or a refused width/field mismatch is an input
            # error, not a verification outcome: say so and stop rather than
            # emitting a report about a target that was never audited.
            print(f"  cannot audit {path}: {exc}")
            return 2
        scan_results = pqverify_scan(ntt, ns={"engines": _eng})

    # Default: run the self-suite.
    if not ran_task:
        run_selftest(quick=args.quick)

    # ---- machine-readable output --------------------------------------
    # One native report per invocation, chosen most-specific-first, so two
    # tasks in one command cannot silently overwrite each other's file. The
    # exit code still reflects EVERY task that ran, not just the reported one.
    from .report import (to_json, to_json_acvp, to_json_kem, to_json_response,
                         to_sarif, artifact_unbound, write)
    from .core import VERSION

    exit_code = 0
    json_doc = sarif_doc = None
    reported = None

    if scan_results is not None:
        from .core import integrity_report as _ir
        _f, _g = _ir(verbose=False)
        json_doc = to_json(scan_results,
                           extra={"coverage": {"full": _f, "gaps": _g}},
                           artifact=scan_artifact)
        sarif_doc = to_sarif(scan_results, tool_version=VERSION,
                             artifact=scan_artifact)
        reported = "--audit-so"
        findings = sum(len(r.get("findings", [])) for r in scan_results)
        if args.fail_on_finding and findings:
            print(f"  FAILING: {findings} finding(s)")
            exit_code = 1

    if kem_ran is not None:
        doc = to_json_kem(kem_result, artifact=kem_artifact, param_set=kem_ran,
                          library=args.audit_kem[0], reason=kem_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-kem"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_kem[0]}:{kem_ran}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=kem_artifact)
        # A KEM audit that found faults, or that could not run at all, must
        # not exit 0 under a CI gate. The old code set a variable nothing read.
        if args.fail_on_finding and not doc["verified"]:
            print(f"  FAILING: KEM audit {doc['status']}")
            exit_code = 1

    if response_result is not None:
        doc = to_json_response(response_result)
        if json_doc is None:
            json_doc, reported = doc, "--verify-response"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{response_result.get('parameter_set')}:response",
                  "passed": response_result.get("passed", 0),
                  "total": response_result.get("total", 0),
                  "findings": response_result.get("findings", [])}],
                tool_version=VERSION, artifact=response_result.get("artifact"))
        # INCOMPLETE and CANNOT VERIFY are both "did not verify".
        if args.fail_on_finding and not response_result["verified"]:
            print(f"  FAILING: {response_result['status']}")
            exit_code = 1

    if acvp_results:
        doc = to_json_acvp(acvp_results)
        if json_doc is None:
            json_doc, reported = doc, "ACVP"
        if args.fail_on_finding and not doc["verified"]:
            print(f"  FAILING: ACVP {doc['status']} "
                  f"({doc['summary']['checks_passed']}/"
                  f"{doc['summary']['checks_total']})")
            exit_code = 1

    if args.json:
        if json_doc is not None:
            write(args.json, json_doc)
            print(f"  wrote {args.json}  (report for {reported}; "
                  f"artifact: {json_doc['artifact']['summary']})")
        else:
            print(f"  note: --json wrote nothing — this task emits no "
                  f"machine-readable report")
    if args.sarif:
        if sarif_doc is not None:
            write(args.sarif, sarif_doc)
            print(f"  wrote {args.sarif}")
        else:
            print(f"  note: --sarif wrote nothing — this task emits no "
                  f"machine-readable report")

    # ---- integrity: did this run cover what the tool claims? -----------
    # Reported LAST, after every task, so it reflects the whole run.
    from .core import integrity_report
    _full, _gaps = integrity_report()
    if getattr(args, "require_full_coverage", False) and not _full:
        print("  FAILING: degraded run and --require-full-coverage was set")
        exit_code = 1

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
