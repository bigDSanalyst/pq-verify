"""
pq-verify command-line interface.

    pq-verify                      run the 160-check self-suite
    pq-verify --quick              fast subset of the self-suite
    pq-verify --acvp               full NIST ACVP (all 12 ML-KEM groups)
    pq-verify --acvp-all           ML-KEM + ML-DSA + SLH-DSA + LMS (1566 vectors)
    pq-verify --lms-xmss           LMS/HSS + XMSS/XMSS^MT, every SP 800-208 family
    pq-verify --fndsa              FN-DSA (Falcon) verification, FIPS 206 draft track
    pq-verify --mceliece           Classic McEliece reference vs the KATs (not FIPS)
    pq-verify --hqc                HQC code layer vs the submitters' code (not final)
    pq-verify --slhdsa-siggen      SLH-DSA sigGen, 624 signatures (~30 min)
    pq-verify --params SET         parameter security (e.g. ML-KEM-1024)
    pq-verify --kem K              native full-KEM at module rank K (2/3/4)
    pq-verify --leakage            per-layer algebraic protection allocation
    pq-verify --audit-so PATH SYM  audit an NTT in a compiled .so
    pq-verify --audit-dsa PATH SET audit an ML-DSA library (keygen/sign/verify)
    pq-verify --audit-hbs PATH     audit an LMS/XMSS library (pqv_hbs adapter)
    pq-verify --audit-fndsa PATH SET  audit an FN-DSA library (FIPS 206 draft track)
    pq-verify --audit-mceliece PATH SET  audit a Classic McEliece library (not FIPS)
    pq-verify --audit-hqc PATH SET       audit an HQC decoder (code layer)
    pq-verify --audit-harness CMD SET  audit through a Crucible-protocol harness
    pq-verify --check-no-harness PATH   fail if PATH is an audit/test build
    pq-verify --emit-prompt SET    write the ACVP questions for SET
                                   (--fresh-key K: fresh, unpublished ones)
    pq-verify --verify-response F  check a response against the pinned answers
    pq-verify --emit-hybrid-prompt G   write what to supply for hybrid group G
    pq-verify --verify-hybrid F    check a hybrid transcript against RFC 10024
    pq-verify --version

Exit status: 0 verified, 1 a task found problems or could not verify,
2 bad input. Pass --no-fail to report without gating.
"""
import argparse
import sys

from . import __version__
from .core import (
    main as run_selftest,
    pqverify_acvp,
    pqverify_mldsa_acvp,
    pqverify_acvp_all,
    pqverify_slhdsa_acvp,
    pqverify_params,
    pqverify_kem,
    pqverify_leakage,
    pqverify_load_so,
    pqverify_scan,
    pqverify_audit_kem,
)


def _audit_so_task(path, sym):
    """--audit-so, as one call so it can run in the isolated child: build the
    engines, load the symbol, scan it. An input error comes back as
    ('input', message) rather than an exception."""
    from .core import compile_all, bind_all, integrity_report
    # Compile the engines first. Without them pqverify_scan silently omits
    # the Freivalds check and reports 2/2 instead of 3/3 -- a skip that looks
    # like a pass, which is the failure mode this tool exists to prevent in
    # other people's code.
    eng = compile_all()
    bind_all(eng)
    try:
        ntt = pqverify_load_so(path, sym)
    except (OSError, ValueError) as exc:
        return ("input", str(exc))
    results = pqverify_scan(ntt, ns={"engines": eng})
    full, gaps = integrity_report(verbose=False)
    return ("ok", results, full, gaps)


# Symbols only pq-verify's audit harnesses define. A shipped binary carrying
# either is a test build: pqv_rng_* replaces randombytes() with a queue of
# caller-chosen bytes (every key and nonce predictable), and a pqv_hbs adapter
# signs at whatever leaf index it is handed, with no one-time-use state.
_RNG_HARNESS = ("deterministic randombytes() harness (pq_verify/harness/"
                "pqv_randombytes.c): every key and nonce comes from the caller")
_HBS_ADAPTER = ("pqv_hbs audit adapter: signs at a caller-chosen leaf index, "
                "bypassing one-time-signature state")
_HARNESS_MARKERS = {b"pqv_rng_set": _RNG_HARNESS, b"pqv_rng_overrun": _RNG_HARNESS,
                    b"pqv_hbs_abi": _HBS_ADAPTER, b"pqv_hbs_sign": _HBS_ADAPTER}


def check_no_harness(path):
    """(clean, [what was found]). Scans the file's bytes, so it works on a
    static archive or a stripped object as well as a shared library."""
    with open(path, "rb") as fh:
        blob = fh.read()
    found = sorted({why for sym, why in _HARNESS_MARKERS.items()
                    if sym + b"\0" in blob})
    return not found, found


def _isolated(args, module, func, *a, **kw):
    """Run an audit through pq_verify.isolate; (result, loaded, failure)."""
    from .isolate import run, IsolatedFailure
    timeout = args.audit_timeout
    if timeout is None:
        timeout = 6 * 3600 if getattr(args, "audit_hbs_full", False) else 3600
    try:
        res, loaded = run(module, func, a, kw, timeout=timeout or None)
        return res, loaded, None
    except IsolatedFailure as exc:
        return None, None, str(exc)


def _bind_loaded(artifact, loaded):
    """Add what the audit actually mapped to the artifact binding. Returns a
    reason string if the audited file is not the file that was hashed."""
    from .isolate import environment, in_process
    import os as _os
    artifact["isolation"] = ("in-process (PQV_IN_PROCESS=1)" if in_process()
                             else "child process")
    env = environment()
    if env:
        artifact["loader_environment"] = env
    if loaded is None:
        return None
    artifact["loaded_objects"] = loaded
    me = _os.path.realpath(artifact["path"])
    for obj in loaded:
        if _os.path.realpath(obj["path"]) == me and obj["sha256"] != artifact["sha256"]:
            return ("the library file changed while it was being audited (sha256 "
                    f"{obj['sha256']} after, {artifact['sha256']} before)")
    return None


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
                   help="every ACVP suite: ML-KEM + ML-DSA + SLH-DSA keyGen and "
                        "sigVer + LMS (1566 pinned NIST vectors, about a minute)")
    p.add_argument("--lms-acvp", action="store_true",
                   help="NIST ACVP LMS (SP 800-208) alone: keyGen, sigGen, sigVer "
                        "(87 vectors)")
    p.add_argument("--lms-xmss", action="store_true",
                   help="LMS/HSS and XMSS/XMSS^MT against every pinned non-NIST "
                        "source (every SP 800-208 family, RFC 8554's test cases, "
                        "XMSS^MT); key generation and signing within a hash budget")
    p.add_argument("--lms-xmss-full", action="store_true",
                   help="--lms-xmss with every tree of height 10 or less built and "
                        "signed byte-exactly (about ten minutes)")
    p.add_argument("--fndsa", action="store_true",
                   help="FN-DSA (Falcon) verification, DRAFT TRACK ahead of FIPS 206: "
                        "PQClean's Falcon-512/1024 vectors (pinned to its published "
                        "sha256), the encodings a verifier must reject, and the NTT "
                        "mod 12289 on the native Z_q engine. Not part of any FIPS "
                        "203/204/205 result")
    p.add_argument("--mceliece", action="store_true",
                   help="Classic McEliece (round 4; NOT a FIPS standard): pq-verify's "
                        "reference regenerates each pinned KAT's public key from its "
                        "private key, and the rebuilt KAT must hash to the value "
                        "PQClean publishes; all ten parameter sets")
    p.add_argument("--hqc", action="store_true",
                   help="HQC's error-correcting code (HQC's standard is not final; "
                        "never part of a FIPS verdict): pq-verify's Reed-Solomon / "
                        "Reed-Muller reference against the submitters' published "
                        "generator polynomials and their own decoders' answers on "
                        "built vectors, both code profiles, every parameter set")
    p.add_argument("--slhdsa-acvp", action="store_true",
                   help="NIST ACVP SLH-DSA (FIPS 205) alone: keyGen and sigVer, "
                        "all 12 parameter sets (624 vectors)")
    p.add_argument("--slhdsa-siggen", action="store_true",
                   help="add SLH-DSA sigGen: 624 byte-exact signatures, "
                        "deterministic and randomised, about 30 min. Extends "
                        "--acvp-all, or runs the SLH-DSA suite on its own")
    p.add_argument("--edge-cases", nargs="?", const="all", metavar="SET",
                   help="pinned Wycheproof/CCTV edge-case vectors against pq-verify's "
                        "own references (kyber-py, dilithium-py); SET limits it to "
                        "one parameter set, e.g. ML-DSA-65")
    p.add_argument("--proofs", action="store_true",
                   help="check the shipped Coq proofs (pq_verify/coq): reductions "
                        "and the NTT, proved for every input; needs coqc, ~2 min")
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
                   help="per-layer algebraic protection allocation: which NTT "
                        "layers are worth masking, computed from the "
                        "transform's structure. Nothing is measured")
    p.add_argument("--audit-so", nargs=2, metavar=("PATH", "SYM"),
                   help="audit an NTT symbol SYM inside compiled library PATH")
    p.add_argument("--audit-kem", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="audit a full ML-KEM implementation (keygen/encaps/decaps) "
                        "in PATH against NIST vectors, e.g. "
                        "--audit-kem lib.so ML-KEM-768. Includes NIST's invalid "
                        "keys, which the library must refuse")
    p.add_argument("--audit-dsa", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="audit a full ML-DSA implementation (keygen/sign/verify) in "
                        "PATH against every NIST ACVP vector and Wycheproof's edge "
                        "cases, e.g. --audit-dsa lib.so ML-DSA-65. Each interface "
                        "(internal, pure, pre-hash, external mu) goes through the "
                        "library's own entry point for it")
    p.add_argument("--audit-hbs", metavar="PATH",
                   help="audit an LMS/HSS or XMSS/XMSS^MT library built with a pqv_hbs "
                        "adapter (pq_verify/harness/hbs): every pinned verification "
                        "vector, byte-exact key generation and signing, signatures "
                        "malformed in one field, and -- where the adapter has the "
                        "optional state functions -- the library's own key state: "
                        "no leaf issued twice, state durable before a signature "
                        "leaves, refusal once the key is exhausted")
    p.add_argument("--audit-fndsa", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="DRAFT TRACK, ahead of FIPS 206: audit an FN-DSA (Falcon) "
                        "library in PATH through its own entry points, e.g. "
                        "--audit-fndsa lib.so FN-DSA-512. Pinned signatures verify, "
                        "malformed ones are refused, its keys are canonical and "
                        "match their secret keys, its signatures verify under "
                        "pq-verify's verifier and never reuse a nonce")
    p.add_argument("--audit-mceliece", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="NOT A FIPS STANDARD: audit a Classic McEliece library in PATH "
                        "through its own entry points, e.g. --audit-mceliece lib.so "
                        "mceliece348864. Its keys regenerated from their own seed, its "
                        "ciphertexts decoded, ciphertexts built against its key "
                        "(weight t, t-1, t+1, random, another key's) decapsulated to "
                        "the exact expected key, padding refused")
    p.add_argument("--audit-hqc", nargs=2, metavar=("PATH", "PARAM_SET"),
                   help="audit an HQC decoder in PATH through its own encoder and "
                        "decoder functions (reed_solomon_*, reed_muller_*, code_*), "
                        "e.g. --audit-hqc libhqc.so HQC-1: every codeword, blocks "
                        "between two codewords up to the radius, ties, Hankel-built "
                        "error patterns, whole received words -- each answer exact. "
                        "The code layer only, not the KEM")
    p.add_argument("--audit-harness", nargs=2, metavar=("COMMAND", "PARAM_SET"),
                   help="audit an ML-KEM or ML-DSA implementation in any language "
                        "through a harness speaking Crucible's JSON-line protocol "
                        "(github.com/symbolicsoft/crucible): NIST's vectors, its "
                        "invalid keys and the Wycheproof/CCTV edge cases, e.g. "
                        "--audit-harness './harness-circl' ML-KEM-768. COMMAND is "
                        "split like a shell command line")
    p.add_argument("--constant-time", action="store_true",
                   help="with --audit-kem or --audit-mceliece: run Encaps and Decaps "
                        "under Valgrind memcheck with the secret inputs marked, and fail "
                        "on any branch or memory access that depends on them (Linux, "
                        "needs valgrind). Not a measurement of timing, power or EM")
    p.add_argument("--accumulated", type=int, metavar="N",
                   help="with --audit-kem / --audit-dsa / --audit-harness: run N of C2SP "
                        "CCTV's accumulated cases (seeded random keygen/encaps/decaps or "
                        "keygen/sign, hashed and compared with CCTV's published digest). "
                        "Default 10000; 100 for a quick ML-DSA run; 0 to skip")
    p.add_argument("--mceliece-symbol", action="append", default=[], metavar="ROLE=SYM",
                   help="with --audit-mceliece: bind ROLE (keypair, enc, dec) to SYM; "
                        "repeatable")
    p.add_argument("--hqc-symbol", action="append", default=[], metavar="ROLE=SYM",
                   help="with --audit-hqc: bind ROLE (rs_encode, rs_decode, rm_encode, "
                        "rm_decode, code_encode, code_decode) to SYM; repeatable")
    p.add_argument("--hqc-profile", choices=("v5", "next"),
                   help="with --audit-hqc: the code the library implements -- v5 "
                        "(HQC v5.0.0 and the 2023 round-4 submission; the default) or "
                        "next (the submitters' unreleased next-release branch)")
    p.add_argument("--hqc-seed", metavar="SEED",
                   help="with --audit-hqc: build the vectors from SEED instead of fresh "
                        "randomness, to replay a reported finding")
    p.add_argument("--fndsa-symbol", action="append", default=[], metavar="ROLE=SYM",
                   help="with --audit-fndsa: bind ROLE (keypair, sign, verify, open) "
                        "to SYM; repeatable")
    p.add_argument("--audit-hbs-full", action="store_true",
                   help="with --audit-hbs: every key generation and signing case up to "
                        "height 16, not a sample")
    p.add_argument("--check-no-harness", metavar="PATH",
                   help="release gate: exit 1 if PATH contains pq-verify's "
                        "deterministic randombytes() harness or a pqv_hbs adapter "
                        "-- test scaffolding that must never ship")
    p.add_argument("--audit-timeout", metavar="SECONDS", type=int,
                   help="with --audit-*: give up on the library after SECONDS "
                        "(default 3600; 6 h with --audit-hbs-full; 0 = never). "
                        "Each audit runs in a child process, so a hang or a crash "
                        "is reported instead of taking pq-verify down with it")
    p.add_argument("--symbol-prefix", metavar="PREFIX",
                   help="with --audit-kem, --audit-dsa, --audit-fndsa, --audit-mceliece "
                        "or --audit-hqc: consider only "
                        "symbols starting with PREFIX, for a library that exports "
                        "more than one implementation (liboqs: OQS_KEM_ml_kem_768_ "
                        "for its public API, PQCP_MLKEM_NATIVE_MLKEM768_X86_64_ for "
                        "one backend). An ambiguity within it is still refused")
    p.add_argument("--dsa-abi", choices=("pqcrystals", "mldsa-native", "mldsa-native-v1", "oqs"),
                   help="with --audit-dsa: the calling convention, when "
                        "auto-detection from the symbol names is wrong")
    p.add_argument("--dsa-symbol", action="append", default=[], metavar="ROLE=SYM",
                   help="with --audit-dsa: bind ROLE (keypair, keypair_seed, "
                        "sign_internal, verify_internal, sign_ctx, verify_ctx, sign, "
                        "verify, sign_mu, verify_mu, sign_prehash, verify_prehash) "
                        "to SYM; repeatable")
    for _role, _ex in (("keypair", "keypair_derand"), ("encaps", "enc_derand"),
                       ("decaps", "dec")):
        p.add_argument(f"--kem-{_role}", metavar="SYM",
                       help=f"with --audit-kem: the {_role} symbol, when "
                            f"auto-detection of *_{_ex} finds none or several")
    p.add_argument("--emit-prompt", metavar="PARAM_SET",
                   help="write the ACVP question set for PARAM_SET (e.g. "
                        "ML-DSA-65) to a file, for implementations that cannot "
                        "be dlopen'd \u2014 HSMs, sealed vendor binaries. No "
                        "answers are included. Pass 'list' for the available "
                        "parameter sets")
    p.add_argument("--fresh-key", metavar="FILE",
                   help="with --emit-prompt: pose FRESH questions, derived from a "
                        "new random seed written to FILE (kept by the auditor, "
                        "never sent). Their answers are published nowhere, so a "
                        "correct response had to be computed. With "
                        "--verify-response: the key to recompute the answers from")
    p.add_argument("--fresh-count", metavar="N", type=int,
                   help="with --emit-prompt --fresh-key: tests per group "
                        "(default 8 ML-KEM, 4 ML-DSA, 1 SLH-DSA, 2 LMS; "
                        "LMS sigGen and sigVer get four times that)")
    p.add_argument("--prompt-out", metavar="FILE",
                   help="where --emit-prompt writes (default "
                        "pq-verify-prompt-<PARAM_SET>.json; .gz is honoured)")
    p.add_argument("--verify-response", metavar="FILE",
                   help="check a response file against the pinned expected "
                        "answers, byte-exact and per test case. The result is "
                        "NOT bound to any artifact and says so")
    p.add_argument("--emit-hybrid-prompt", metavar="GROUP",
                   help="write the fields needed to check a hybrid key "
                        "agreement for GROUP (e.g. X25519MLKEM768) against "
                        "RFC 10024. Pass 'list' for the known groups")
    p.add_argument("--verify-hybrid", metavar="FILE",
                   help="check a hybrid transcript against RFC 10024: "
                        "component order, lengths, the FIPS 203 \u00a77.2 "
                        "encapsulation key check, ECDHE point validity, and "
                        "the recomputed ECDHE shared secret")
    p.add_argument("--json", metavar="FILE",
                   help="write results to FILE in pq-verify's native schema")
    p.add_argument("--sarif", metavar="FILE",
                   help="write SARIF 2.1.0 to FILE — ingested natively by GitHub "
                        "Code Scanning, DefectDojo, Snyk, AWS Security Hub")
    p.add_argument("--require-full-coverage", action="store_true",
                   help="exit non-zero if any engine or dependency was missing "
                        "(prevents a degraded run from reporting green in CI)")
    p.add_argument("--fail-on-finding", action="store_true",
                   help="exit 1 if any task did not verify. This is the default "
                        "since 2.10.0; the flag is kept so existing pipelines "
                        "keep working")
    p.add_argument("--no-fail", action="store_true",
                   help="report only: exit 0 even when a task found problems or "
                        "could not verify (input errors still exit 2)")
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)

    # A modifier without the task it modifies used to be ignored, so a typo'd
    # pipeline ran something other than what it asked for and said nothing.
    for _flag, _set, _needs in (
            ("--audit-hbs-full", args.audit_hbs_full, args.audit_hbs),
            ("--dsa-abi", args.dsa_abi, args.audit_dsa),
            ("--symbol-prefix", args.symbol_prefix,
             args.audit_kem or args.audit_dsa or args.audit_fndsa or args.audit_mceliece
             or args.audit_hqc),
            ("--mceliece-symbol", args.mceliece_symbol, args.audit_mceliece),
            ("--hqc-symbol", args.hqc_symbol, args.audit_hqc),
            ("--hqc-profile", args.hqc_profile, args.audit_hqc),
            ("--hqc-seed", args.hqc_seed, args.audit_hqc),
            ("--dsa-symbol", args.dsa_symbol, args.audit_dsa),
            ("--fndsa-symbol", args.fndsa_symbol, args.audit_fndsa),
            ("--constant-time", args.constant_time, args.audit_kem or args.audit_mceliece),
            ("--accumulated", args.accumulated is not None,
             args.audit_kem or args.audit_dsa or args.audit_harness),
            ("--kem-keypair", args.kem_keypair, args.audit_kem),
            ("--kem-encaps", args.kem_encaps, args.audit_kem),
            ("--kem-decaps", args.kem_decaps, args.audit_kem),
            ("--fresh-key", args.fresh_key,
             args.emit_prompt or args.verify_response),
            ("--fresh-count", args.fresh_count, args.fresh_key),
            ("--audit-timeout", args.audit_timeout is not None,
             args.audit_kem or args.audit_dsa or args.audit_hbs or args.audit_so
             or args.audit_fndsa or args.audit_mceliece or args.audit_hqc
             or args.audit_harness)):
        if _set and not _needs:
            _parent = {"--audit-hbs-full": "--audit-hbs",
                       "--fndsa-symbol": "--audit-fndsa",
                       "--symbol-prefix": "--audit-kem, --audit-dsa, --audit-fndsa, "
                                          "--audit-mceliece or --audit-hqc",
                       "--mceliece-symbol": "--audit-mceliece",
                       "--hqc-symbol": "--audit-hqc",
                       "--hqc-profile": "--audit-hqc",
                       "--hqc-seed": "--audit-hqc",
                       "--accumulated": "--audit-kem, --audit-dsa or --audit-harness",
                       "--constant-time": "--audit-kem or --audit-mceliece",
                       "--fresh-key": "--emit-prompt or --verify-response",
                       "--fresh-count": "--fresh-key",
                       "--audit-timeout": "an --audit-* task"}.get(
                _flag, "--audit-dsa" if _flag.startswith("--dsa") else "--audit-kem")
            print(f"  {_flag} does nothing without {_parent}")
            return 2
    # --accumulated N must be a count CCTV publishes a digest for, for every
    # parameter set this run audits: an unpublished count checks nothing.
    from .accumulated import counts as _acc_counts, DEFAULT as _ACC_DEFAULT

    def _acc_n(ps):
        return _ACC_DEFAULT if args.accumulated is None else args.accumulated
    for _ps_req in [x[1] for x in (args.audit_kem, args.audit_dsa, args.audit_harness) if x]:
        _n = _acc_n(_ps_req)
        if _n and _acc_counts(_ps_req) and _n not in _acc_counts(_ps_req):
            print(f"  --accumulated {_n}: CCTV publishes no {_n}-case digest for "
                  f"{_ps_req}; available: {', '.join(map(str, _acc_counts(_ps_req))) or 'none'}"
                  f" (0 to skip)")
            return 2
    if args.no_fail and args.fail_on_finding:
        print("  --no-fail and --fail-on-finding contradict each other")
        return 2

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
    _siggen = getattr(args, "slhdsa_siggen", False)
    if getattr(args, "acvp_all", False):
        _all = pqverify_acvp_all(slhdsa_siggen=_siggen, **_vsrc)
        acvp_results["ML-KEM (FIPS 203)"] = _all.get("ml_kem")
        acvp_results["ML-DSA (FIPS 204)"] = _all.get("ml_dsa")
        # Listed even when it could not run: a requested suite that is absent
        # from the report reads as one that was never asked for.
        acvp_results["SLH-DSA (FIPS 205)"] = _all.get("slh_dsa")
        acvp_results["LMS (SP 800-208)"] = _all.get("lms")
        ran_task = True
    elif getattr(args, "slhdsa_acvp", False) or _siggen:
        acvp_results["SLH-DSA (FIPS 205)"] = pqverify_slhdsa_acvp(siggen=_siggen,
                                                                   **_vsrc)
        ran_task = True
    if getattr(args, "lms_acvp", False) and not getattr(args, "acvp_all", False):
        from .hbs_suite import pqverify_lms_acvp
        acvp_results["LMS (SP 800-208)"] = pqverify_lms_acvp(**_vsrc)
        ran_task = True
    if getattr(args, "check_no_harness", None):
        try:
            clean, found = check_no_harness(args.check_no_harness)
        except OSError as exc:
            print(f"  cannot check {args.check_no_harness}: {exc}")
            return 2
        if clean:
            print(f"  OK: {args.check_no_harness} carries no pq-verify audit harness")
        else:
            for f in found:
                print(f"  HARNESS PRESENT in {args.check_no_harness}: {f}")
            print("  FAILING: this is a test build; never ship it")
            return 0 if args.no_fail else 1
        if not any(getattr(args, a, None) for a in (
                "acvp", "mldsa_acvp", "acvp_all", "slhdsa_acvp", "slhdsa_siggen",
                "lms_acvp", "lms_xmss", "lms_xmss_full", "fndsa", "mceliece", "proofs",
                "edge_cases", "audit_mceliece", "hqc", "audit_hqc",
                "params", "kem", "leakage", "emit_prompt", "verify_response",
                "emit_hybrid_prompt", "verify_hybrid", "audit_kem", "audit_dsa", "audit_fndsa",
                "audit_harness",
                "audit_hbs", "audit_so")):
            return 0
    hbs_result = None
    if getattr(args, "lms_xmss", False) or getattr(args, "lms_xmss_full", False):
        from .hbs_suite import pqverify_hbs
        hbs_result = pqverify_hbs(full=getattr(args, "lms_xmss_full", False))
        ran_task = True
    fndsa_result = None
    if getattr(args, "fndsa", False):
        from .fndsa import pqverify_fndsa
        fndsa_result = pqverify_fndsa()
        ran_task = True
    mce_result = None
    if getattr(args, "mceliece", False):
        from .mceliece import pqverify_mceliece
        mce_result = pqverify_mceliece()
        ran_task = True
    hqc_result = None
    if getattr(args, "hqc", False):
        from .hqc import pqverify_hqc
        hqc_result = pqverify_hqc()
        ran_task = True
    proofs_result = None
    if getattr(args, "proofs", False):
        from .proofs import pqverify_proofs
        print("\n  PROOFS (pq_verify/coq): every theorem must be closed -- no axioms, "
              "no Admitted")
        proofs_result = pqverify_proofs()
        ran_task = True
    edge_result = None
    if getattr(args, "edge_cases", None):
        from .edge import pqverify_edge, KEM_SETS, DSA_SETS
        _sets = None if args.edge_cases == "all" else [args.edge_cases]
        if _sets and _sets[0] not in KEM_SETS + DSA_SETS:
            print(f"  unknown parameter set {_sets[0]!r}; choose from "
                  f"{', '.join(KEM_SETS + DSA_SETS)}")
            return 2
        edge_result = pqverify_edge(_sets)
        if edge_result is None:
            edge_result = {"status": "CANNOT VERIFY", "verified": False,
                           "passed": 0, "total": 0, "sets": {}}
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
            emit_prompt(args.emit_prompt, out_path=args.prompt_out,
                        fresh_key=args.fresh_key, fresh_count=args.fresh_count,
                        **_vsrc)
        except ValueError as exc:
            print(f"  {exc}")
            return 2
    if getattr(args, "verify_response", None):
        from .response import verify_response
        response_result = verify_response(args.verify_response,
                                          fresh_key=args.fresh_key, **_vsrc)
        ran_task = True
    hybrid_result = None
    if getattr(args, "emit_hybrid_prompt", None):
        from .hybrid import emit_hybrid_prompt, GROUPS as _HG
        ran_task = True
        if args.emit_hybrid_prompt.lower() in ("list", "?"):
            print("  hybrid groups known to this build (RFC 10024):")
            for name in sorted(_HG, key=lambda k: _HG[k]["codepoint"]):
                g = _HG[name]
                print(f"    0x{g['codepoint']:04X}  {name:20s} "
                      f"{g['kem']} + {g['ecdh']}")
            return 0
        try:
            emit_hybrid_prompt(args.emit_hybrid_prompt,
                               out_path=args.prompt_out)
        except ValueError as exc:
            print(f"  {exc}")
            return 2
    if getattr(args, "verify_hybrid", None):
        from .hybrid import verify_hybrid
        hybrid_result = verify_hybrid(args.verify_hybrid)
        ran_task = True

    from .report import artifact_bound

    scan_results = None
    kem_result = kem_ran = kem_reason = None
    kem_artifact = scan_artifact = None
    if getattr(args, "audit_kem", None):
        from .core import pqverify_audit_kem
        _p, _ps = args.audit_kem
        from .core import _KEM_SIZES
        if _ps not in _KEM_SIZES:
            # A typo is an input error, not a finding: exit 2 like every other
            # bad argument, never 1 (which CI reads as "the library is faulty").
            print(f"  unknown parameter set {_ps!r} for --audit-kem — known: "
                  f"{', '.join(sorted(_KEM_SIZES))}")
            return 2
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
            kem_result, _loaded, kem_reason = _isolated(
                args, "pq_verify.core", "pqverify_audit_kem", _p, _ps,
                keypair=args.kem_keypair, encaps=args.kem_encaps,
                decaps=args.kem_decaps, accumulated=_acc_n(_ps),
                constant_time=args.constant_time, prefix=args.symbol_prefix)
            _bound = _bind_loaded(kem_artifact, _loaded)
            kem_reason = kem_reason or _bound
            if kem_reason:
                kem_result = None
                print(f"  cannot verify: {kem_reason}")
        except OSError as exc:
            # Not loadable by the dynamic linker: cannot verify, not a failure.
            kem_result = None
            kem_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {kem_reason}")
    dsa_result = dsa_ran = dsa_reason = dsa_artifact = None
    if getattr(args, "audit_dsa", None):
        from .dsa_audit import pqverify_audit_dsa, DSA_SIZES, _ROLES
        _p, _ps = args.audit_dsa
        if _ps not in DSA_SIZES:
            print(f"  unknown parameter set {_ps!r} for --audit-dsa — known: "
                  f"{', '.join(sorted(DSA_SIZES))}")
            return 2
        _syms = {}
        for item in args.dsa_symbol:
            role, _, sym = item.partition("=")
            if role not in _ROLES or not sym:
                print(f"  bad --dsa-symbol {item!r}: use ROLE=SYMBOL with ROLE one "
                      f"of {', '.join(_ROLES)}")
                return 2
            _syms[role] = sym
        dsa_ran = _ps
        ran_task = True
        try:
            dsa_artifact = artifact_bound(_p)
        except OSError as exc:
            print(f"  cannot audit {_p}: {exc}")
            return 2
        print(f"  artifact: {dsa_artifact['summary']}")
        try:
            dsa_result, _loaded, dsa_reason = _isolated(
                args, "pq_verify.dsa_audit", "pqverify_audit_dsa", _p, _ps,
                abi=args.dsa_abi, symbols=_syms, accumulated=_acc_n(_ps),
                prefix=args.symbol_prefix, **_vsrc)
            _bound = _bind_loaded(dsa_artifact, _loaded)
            dsa_reason = dsa_reason or _bound
            if dsa_reason:
                dsa_result = None
                print(f"  cannot verify: {dsa_reason}")
        except OSError as exc:
            dsa_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {dsa_reason}")
    fna_result = fna_ran = fna_reason = fna_artifact = None
    if getattr(args, "audit_fndsa", None):
        from .fndsa_audit import SETS as _FN_SETS, _ROLES as _FN_ROLES
        _p, _ps = args.audit_fndsa
        if _ps not in _FN_SETS:
            print(f"  unknown parameter set {_ps!r} for --audit-fndsa — known: "
                  f"{', '.join(sorted(_FN_SETS))}")
            return 2
        _syms = {}
        for item in args.fndsa_symbol:
            role, _, sym = item.partition("=")
            if role not in _FN_ROLES or not sym:
                print(f"  bad --fndsa-symbol {item!r}: use ROLE=SYMBOL with ROLE one "
                      f"of {', '.join(_FN_ROLES)}")
                return 2
            _syms[role] = sym
        fna_ran = _ps
        ran_task = True
        try:
            fna_artifact = artifact_bound(_p)
        except OSError as exc:
            print(f"  cannot audit {_p}: {exc}")
            return 2
        print(f"  artifact: {fna_artifact['summary']}")
        try:
            fna_result, _loaded, fna_reason = _isolated(
                args, "pq_verify.fndsa_audit", "pqverify_audit_fndsa", _p, _ps,
                symbols=_syms, prefix=args.symbol_prefix)
            _bound = _bind_loaded(fna_artifact, _loaded)
            fna_reason = fna_reason or _bound
            if fna_reason:
                fna_result = None
                print(f"  cannot verify: {fna_reason}")
        except OSError as exc:
            fna_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {fna_reason}")
    mca_result = mca_ran = mca_reason = mca_artifact = None
    if getattr(args, "audit_mceliece", None):
        from .mceliece import SETS as _MC_SETS
        from .mceliece_audit import _ROLES as _MC_ROLES
        _p, _ps = args.audit_mceliece
        if _ps not in _MC_SETS:
            print(f"  unknown parameter set {_ps!r} for --audit-mceliece — known: "
                  f"{', '.join(_MC_SETS)}")
            return 2
        _syms = {}
        for item in args.mceliece_symbol:
            role, _, sym = item.partition("=")
            if role not in _MC_ROLES or not sym:
                print(f"  bad --mceliece-symbol {item!r}: use ROLE=SYMBOL with ROLE one "
                      f"of {', '.join(_MC_ROLES)}")
                return 2
            _syms[role] = sym
        mca_ran = _ps
        ran_task = True
        try:
            mca_artifact = artifact_bound(_p)
        except OSError as exc:
            print(f"  cannot audit {_p}: {exc}")
            return 2
        print(f"  artifact: {mca_artifact['summary']}")
        try:
            mca_result, _loaded, mca_reason = _isolated(
                args, "pq_verify.mceliece_audit", "pqverify_audit_mceliece", _p, _ps,
                symbols=_syms, prefix=args.symbol_prefix,
                constant_time_check=args.constant_time)
            _bound = _bind_loaded(mca_artifact, _loaded)
            mca_reason = mca_reason or _bound
            if mca_reason:
                mca_result = None
                print(f"  cannot verify: {mca_reason}")
        except OSError as exc:
            mca_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {mca_reason}")
    hqa_result = hqa_ran = hqa_reason = hqa_artifact = None
    if getattr(args, "audit_hqc", None):
        from .hqc import set_name as _hqc_set
        from .hqc_audit import _ROLES as _HQ_ROLES
        _p, _ps = args.audit_hqc
        try:
            _ps = _hqc_set(_ps)
        except ValueError as exc:
            print(f"  {exc}")
            return 2
        _syms = {}
        for item in args.hqc_symbol:
            role, _, sym = item.partition("=")
            if role not in _HQ_ROLES or not sym:
                print(f"  bad --hqc-symbol {item!r}: use ROLE=SYMBOL with ROLE one "
                      f"of {', '.join(_HQ_ROLES)}")
                return 2
            _syms[role] = sym
        hqa_ran = _ps
        ran_task = True
        try:
            hqa_artifact = artifact_bound(_p)
        except OSError as exc:
            print(f"  cannot audit {_p}: {exc}")
            return 2
        print(f"  artifact: {hqa_artifact['summary']}")
        try:
            hqa_result, _loaded, hqa_reason = _isolated(
                args, "pq_verify.hqc_audit", "pqverify_audit_hqc", _p, _ps,
                symbols=_syms, prefix=args.symbol_prefix,
                profile=args.hqc_profile or "v5", seed=args.hqc_seed)
            _bound = _bind_loaded(hqa_artifact, _loaded)
            hqa_reason = hqa_reason or _bound
            if hqa_reason:
                hqa_result = None
                print(f"  cannot verify: {hqa_reason}")
        except OSError as exc:
            hqa_reason = f"the dynamic linker could not load it ({exc})"
            print(f"  cannot audit: {hqa_reason}")
    har_result = har_artifact = None
    if getattr(args, "audit_harness", None):
        import shlex as _shlex
        from .harness_audit import (KEM_SETS as _HK, DSA_SETS as _HD,
                                    harness_executable, pqverify_audit_harness)
        from .report import artifact_harness
        _cmd, _ps = args.audit_harness
        if _ps not in _HK + _HD:
            print(f"  unknown parameter set {_ps!r} for --audit-harness — known: "
                  f"{', '.join(_HK + _HD)}")
            return 2
        try:
            _argv = _shlex.split(_cmd)
        except ValueError as exc:
            print(f"  cannot parse the harness command: {exc}")
            return 2
        if not _argv:
            print("  --audit-harness needs a command")
            return 2
        ran_task = True
        har_artifact = artifact_harness(harness_executable(_argv), _argv)
        print(f"  artifact: {har_artifact['summary']}  (the harness)")
        _t = args.audit_timeout
        har_result = pqverify_audit_harness(
            _argv, _ps, timeout=60 if _t is None else (_t or None),
            accumulated=_acc_n(_ps))
    hbsa_result = hbsa_reason = hbsa_artifact = None
    hbsa_ran = bool(getattr(args, "audit_hbs", None))
    if hbsa_ran:
        from .hbs_audit import pqverify_audit_hbs, AdapterError
        ran_task = True
        try:
            hbsa_artifact = artifact_bound(args.audit_hbs)
        except OSError as exc:
            print(f"  cannot audit {args.audit_hbs}: {exc}")
            return 2
        print(f"  artifact: {hbsa_artifact['summary']}")
        try:
            hbsa_result, _loaded, hbsa_reason = _isolated(
                args, "pq_verify.hbs_audit", "pqverify_audit_hbs", args.audit_hbs,
                full=args.audit_hbs_full)
            _bound = _bind_loaded(hbsa_artifact, _loaded)
            hbsa_reason = hbsa_reason or _bound
            if hbsa_reason:
                hbsa_result = None
                print(f"  cannot verify: {hbsa_reason}")
        except (OSError, AdapterError) as exc:
            hbsa_reason = str(exc)
            print(f"  cannot audit: {hbsa_reason}")
    scan_coverage = None
    if args.audit_so:
        path, sym = args.audit_so
        ran_task = True
        try:
            scan_artifact = artifact_bound(path)
        except OSError as exc:
            print(f"  cannot audit {path}: {exc}")
            return 2
        print(f"  artifact: {scan_artifact['summary']}")
        out, _loaded, why = _isolated(args, "pq_verify.cli", "_audit_so_task",
                                      path, sym)
        _bound = _bind_loaded(scan_artifact, _loaded)
        why = why or _bound
        if why:
            # Still a report: a target that crashed or hung gets the same
            # JSON/SARIF a failing one does, with nothing counted as passed.
            print(f"  cannot verify {path}: {why}")
            scan_results = [{"name": f"{path}:{sym}", "passed": 0, "total": 0,
                             "findings": [f"cannot verify: {why}"]}]
        elif out[0] == "input":
            # An unloadable file or a refused width/field mismatch is an input
            # error, not a verification outcome: say so and stop rather than
            # emitting a report about a target that was never audited.
            print(f"  cannot audit {path}: {out[1]}")
            return 2
        else:
            _, scan_results, _full, _gaps = out
            scan_coverage = {"full": _full, "gaps": _gaps}

    # Default: run the self-suite.
    selftest_results = None
    if not ran_task:
        selftest_results = run_selftest(quick=args.quick)

    # ---- machine-readable output --------------------------------------
    # One native report per invocation, chosen most-specific-first, so two
    # tasks in one command cannot silently overwrite each other's file. The
    # exit code still reflects EVERY task that ran, not just the reported one.
    from .report import (to_json, to_json_acvp, to_json_hybrid, to_json_kem,
                         to_json_dsa, to_json_hbs_audit, to_json_response, to_sarif,
                         artifact_unbound, write)
    from .core import VERSION

    exit_code = 0
    json_doc = sarif_doc = None
    reported = None
    # Gating is the default. A verifier whose failures exit 0 unless a flag is
    # remembered reports green from a failed job -- the GitHub Action did
    # exactly that for --acvp-all until 2.10.0.
    gate = not args.no_fail

    if selftest_results is not None:
        _rows = [t for r in selftest_results for t in r.tests]
        _failed = [t["name"] for t in _rows
                   if not t.get("skipped") and t["passed"] is not True]
        if gate and _failed:
            print(f"  FAILING: self-suite, {len(_failed)} check(s) failed: "
                  f"{', '.join(_failed[:5])}{', ...' if len(_failed) > 5 else ''}")
            exit_code = 1

    if scan_results is not None:
        json_doc = to_json(scan_results, extra={"coverage": scan_coverage},
                           artifact=scan_artifact)
        sarif_doc = to_sarif(scan_results, tool_version=VERSION,
                             artifact=scan_artifact)
        reported = "--audit-so"
        findings = sum(len(r.get("findings", [])) for r in scan_results)
        if gate and not json_doc["summary"]["verified"]:
            print(f"  FAILING: {findings} finding(s)" if findings else
                  "  FAILING: the scan did not verify")
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
        if gate and not doc["verified"]:
            print(f"  FAILING: KEM audit {doc['status']}")
            exit_code = 1

    if dsa_ran is not None:
        doc = to_json_dsa(dsa_result, artifact=dsa_artifact, param_set=dsa_ran,
                          library=args.audit_dsa[0], reason=dsa_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-dsa"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_dsa[0]}:{dsa_ran}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=dsa_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: ML-DSA audit {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print(f"  FAILING: ML-DSA audit scope is partial and "
                  f"--require-full-coverage was set")
            exit_code = 1

    if hbsa_ran:
        doc = to_json_hbs_audit(hbsa_result, artifact=hbsa_artifact,
                                library=args.audit_hbs, reason=hbsa_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-hbs"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_hbs}:LMS/XMSS",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=hbsa_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: LMS/XMSS audit {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print(f"  FAILING: LMS/XMSS audit scope is partial and "
                  f"--require-full-coverage was set")
            exit_code = 1

    if har_result is not None:
        from .report import to_json_harness_audit
        doc = to_json_harness_audit(har_result, artifact=har_artifact)
        if json_doc is None:
            json_doc, reported = doc, "--audit-harness"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_harness[0]}:{args.audit_harness[1]}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=har_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: harness audit {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print("  FAILING: harness audit scope is partial and "
                  "--require-full-coverage was set")
            exit_code = 1

    if fna_ran is not None:
        from .report import to_json_fndsa_audit
        doc = to_json_fndsa_audit(fna_result, artifact=fna_artifact, param_set=fna_ran,
                                  library=args.audit_fndsa[0], reason=fna_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-fndsa"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_fndsa[0]}:{fna_ran}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=fna_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: FN-DSA audit (draft) {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print(f"  FAILING: FN-DSA audit scope is partial and "
                  f"--require-full-coverage was set")
            exit_code = 1

    if mca_ran is not None:
        from .report import to_json_mceliece_audit
        doc = to_json_mceliece_audit(mca_result, artifact=mca_artifact, param_set=mca_ran,
                                     library=args.audit_mceliece[0], reason=mca_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-mceliece"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_mceliece[0]}:{mca_ran}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=mca_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: Classic McEliece audit {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print(f"  FAILING: Classic McEliece audit scope is partial and "
                  f"--require-full-coverage was set")
            exit_code = 1

    if hqa_ran is not None:
        from .report import to_json_hqc_audit
        doc = to_json_hqc_audit(hqa_result, artifact=hqa_artifact, param_set=hqa_ran,
                                library=args.audit_hqc[0], reason=hqa_reason)
        if json_doc is None:
            json_doc, reported = doc, "--audit-hqc"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{args.audit_hqc[0]}:{hqa_ran}",
                  "passed": doc["summary"]["checks_passed"],
                  "total": doc["summary"]["checks_total"],
                  "findings": doc["findings"]}],
                tool_version=VERSION, artifact=hqa_artifact)
        if doc.get("scope"):
            print(f"  SCOPE: {doc['scope']['statement']}")
        if gate and not doc["verified"]:
            print(f"  FAILING: HQC decoder audit {doc['status']}")
            exit_code = 1
        elif (gate and getattr(args, "require_full_coverage", False)
              and doc.get("scope") and not doc["scope"]["complete"]):
            print("  FAILING: HQC decoder audit scope is partial and "
                  "--require-full-coverage was set")
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
        if gate and not response_result["verified"]:
            print(f"  FAILING: {response_result['status']}")
            exit_code = 1

    if hybrid_result is not None:
        doc = to_json_hybrid(hybrid_result)
        if json_doc is None:
            json_doc, reported = doc, "--verify-hybrid"
        if sarif_doc is None:
            sarif_doc = to_sarif(
                [{"name": f"{hybrid_result.get('group')}:hybrid",
                  "passed": hybrid_result.get("passed", 0),
                  "total": hybrid_result.get("total", 0),
                  "findings": hybrid_result.get("findings", [])}],
                tool_version=VERSION, artifact=hybrid_result.get("artifact"))
        # PARTIAL and CANNOT VERIFY are both "did not verify".
        if gate and not hybrid_result["verified"]:
            print(f"  FAILING: hybrid {hybrid_result['status']}")
            exit_code = 1

    if proofs_result is not None:
        doc = {"schema": "pq-verify/proofs-report", "tool_version": VERSION,
               "status": proofs_result["status"], "verified": proofs_result["verified"],
               "summary": {"checks_passed": proofs_result["passed"],
                           "checks_total": proofs_result["total"]},
               "files": proofs_result["files"],
               "artifact": {"summary": "pq-verify's shipped Coq proofs"}}
        if json_doc is None:
            json_doc, reported = doc, "--proofs"
        if gate and not proofs_result["verified"]:
            print(f"  FAILING: proofs {proofs_result['status']}")
            exit_code = 1

    if edge_result is not None:
        doc = {"schema": "pq-verify/edge-report", "tool_version": VERSION,
               "status": edge_result["status"], "verified": edge_result["verified"],
               "vectors": edge_result.get("vectors"),
               "summary": {"checks_passed": edge_result["passed"],
                           "checks_total": edge_result["total"]},
               "sets": edge_result["sets"],
               "artifact": {"summary": "pq-verify's reference implementations"}}
        if json_doc is None:
            json_doc, reported = doc, "--edge-cases"
        if gate and not edge_result["verified"]:
            print(f"  FAILING: edge cases {edge_result['status']} "
                  f"({edge_result['passed']}/{edge_result['total']})")
            exit_code = 1

    if hbs_result is not None:
        from .report import to_json_hbs
        doc = to_json_hbs(hbs_result)
        if json_doc is None:
            json_doc, reported = doc, "--lms-xmss"
        if gate and not doc["verified"]:
            print(f"  FAILING: LMS/XMSS {doc['status']} "
                  f"({doc['summary']['checks_passed']}/{doc['summary']['checks_total']})")
            exit_code = 1

    if mce_result is not None:
        from .report import to_json_mceliece
        doc = to_json_mceliece(mce_result)
        if json_doc is None:
            json_doc, reported = doc, "--mceliece"
        if gate and not doc["verified"]:
            print(f"  FAILING: Classic McEliece {doc['status']} "
                  f"({doc['summary']['checks_passed']}/{doc['summary']['checks_total']})")
            exit_code = 1

    if hqc_result is not None:
        from .report import to_json_hqc
        doc = to_json_hqc(hqc_result)
        if json_doc is None:
            json_doc, reported = doc, "--hqc"
        if gate and not doc["verified"]:
            print(f"  FAILING: HQC code layer {doc['status']} "
                  f"({doc['summary']['checks_passed']}/{doc['summary']['checks_total']})")
            exit_code = 1

    if fndsa_result is not None:
        from .report import to_json_fndsa
        doc = to_json_fndsa(fndsa_result)
        if json_doc is None:
            json_doc, reported = doc, "--fndsa"
        if gate and not doc["verified"]:
            print(f"  FAILING: FN-DSA (draft) {doc['status']} "
                  f"({doc['summary']['checks_passed']}/{doc['summary']['checks_total']})")
            exit_code = 1

    if acvp_results:
        doc = to_json_acvp(acvp_results)
        if json_doc is None:
            json_doc, reported = doc, "ACVP"
        if gate and not doc["verified"]:
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
    # A self-suite-only run has already printed this inside its summary; the
    # gate below still uses it, but printing it twice reads as two reports.
    _full, _gaps = integrity_report(verbose=ran_task)
    if getattr(args, "require_full_coverage", False) and not _full:
        print("  FAILING: degraded run and --require-full-coverage was set")
        exit_code = 1

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
