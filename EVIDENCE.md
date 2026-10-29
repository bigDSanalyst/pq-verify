# Evidence: each claim, and how to check it

Each claim pq-verify makes, with the command that reproduces it, the CI job
that re-runs it, what it is pinned to, and what it does not show. None of it
is a certificate: a CMVP certificate is issued by NIST and the Canadian Centre
for Cyber Security after an accredited laboratory has tested the module.

**Verdicts.** A check ends VERIFIED, FINDINGS PRESENT or CANNOT VERIFY. CANNOT
VERIFY means a tool or input was missing, or a check did not decide; it is
never a pass. In the self-suite, a check whose optional dependency is missing
reports ⊘ SKIPPED, which is never a pass either.

**The audits' checks are shown to fail.** Each audit's checks are shown
failing on planted defects, in the run itself or in CI, so a pass is one they
could have refused:
- self-tests inside a run: CBMC's own, and each exhaustive test's control;
- mutants in CI: one planted bug each, which the audit must catch in the
  stage its row names;
- reachability checks: a false assertion at the end of each CBMC harness
  must fail.

CI's vendor-audit jobs run on every change to the audit code and weekly; a
row whose result differs from the one recorded fails the job.

## The claims

| Claim | Reproduce | Re-run in CI | Pinned to | Does not show |
|---|---|---|---|---|
| pq-verify's own references pass every NIST ACVP vector of the default run: ML-KEM 240, ML-DSA 615, SLH-DSA 624, LMS 87, 1,566 in all | `pq-verify --acvp-all`, offline, about a minute | `tests.yml`: each `py3.x` job and `macOS (Apple silicon)`; all four suites must run | the vectors shipped in `pq_verify/vectors/`, checked by `tools/doctor.py` in the `py3.x` jobs; `watch-nist-vectors.yml` checks NIST for changes weekly | anything about another implementation. These are the references every verdict rests on |
| SLH-DSA signature generation matches NIST byte for byte: 624 signatures | `pq-verify --slhdsa-siggen`, about 30 minutes | `slhdsa-siggen.yml`, weekly and on changes to it | the same vectors | as above |
| The self-suite: 160 checks, 54 of them on PQC | `pq-verify` | `tests.yml`, `self-suite (base)`, `(dev)` and `(full)`: the total is 160, none fail, every skip names its dependency, and the missing set is exactly the profile's | `constraints-reference.txt` for the reference packages | anything from the other 106 checks (the harness, classical and research engines), which are never PQC evidence |
| Coq proofs, for every input: FIPS 203's and FIPS 204's forward NTTs equal the CRT map they are defined to compute; `montgomery_reduce`, `barrett_reduce` and `reduce32` are congruent to their input and within bound, with no intermediate overflow | `pq-verify --proofs`, which needs `coqc` | `tests.yml`, `self-suite (full)`, which installs Coq. Every theorem must print "Closed under the global context", and tests plant a wrong NTT spec, a false Montgomery range and an `Admitted` proof, each of which must be refused | `pq_verify/coq/NTT.v`, `Reduce.v` | anything about compiled code: these are the algorithms as written in Coq ([LIMITS.md](LIMITS.md#proofs-and-tests)) |
| Each third-party library's result in [AUDITS.md](AUDITS.md): ML-KEM, ML-DSA, LMS/XMSS, FN-DSA (draft), Classic McEliece, HQC | `python3 tools/vendor_audit.py`, or `--only` one scheme | `vendor-audits.yml`, `vendor audits (pinned libraries)`: each library rebuilt and re-audited, and each mutant listed for a row must fail | each library's commit in `tools/vendor_audits.json`; the reference packages in `constraints-reference.txt` | another version, build, compiler or CPU than the one pinned; behaviour when not under test ([LIMITS.md](LIMITS.md#what-a-pass-is-about)) |
| Constant time (`--constant-time`): no branch or memory address depends on a secret, in ML-KEM's Encaps and Decaps, ML-DSA's key generation and signing (in a build carrying its own annotations), and Classic McEliece's Encaps and Decaps | `pq-verify --audit-kem LIB.so ML-KEM-768 --constant-time`, and the same with `--audit-dsa` and `--audit-mceliece` | the vendor-audit rows above, including planted leaks that must be reported | as above, run under Valgrind memcheck | a proof for all inputs: it sees the runs it makes. Nor instruction timing, the values computed, prefetches, or other builds ([LIMITS.md](LIMITS.md#side-channels)) |
| CBMC proves PQClean's ML-KEM and ML-DSA NTT and reduction code free of undefined behaviour on every input FIPS 203 or 204 allows, with each output in its bound; the reductions are tested on every input their contracts allow, and the zeta tables and ML-DSA's rounding in full | `pq-verify --audit-source DIR`; as CI runs it, `python3 tools/source_audit.py --scheme ml-kem` (or `ml-dsa`) | `vendor-audits.yml`, four `source audit` jobs: all six parameter sets VERIFIED, and all 7 ML-KEM and 12 ML-DSA mutants caught | PQClean at `0586a824`; Kissat at commit `8af8e56`, its 4.0.4 release; CBMC 5.95.1 and Z3 4.8.12 from Ubuntu 24.04's packages | that the NTTs compute the standard's transform, any other function, `poly_chknorm`'s decision, strict aliasing, timing ([SOURCE-AUDIT.md](SOURCE-AUDIT.md#what-this-does-not-show)) |
| LMS/HSS and XMSS/XMSS^MT: pq-verify's references agree with every other pinned source | `pq-verify --lms-xmss`; every height-10 tree with `--lms-xmss-full` | `tests.yml` at the default budget; `lms-xmss-full.yml` weekly, in full | the pinned vectors in `pq_verify/vectors/` | anything about a library: that is `--audit-hbs`, in the vendor audits |
| FN-DSA (draft FIPS 206), Classic McEliece (not a FIPS standard) and HQC's code layer (standard not final): the references against their pinned vectors | `pq-verify --fndsa`, `--mceliece`, `--hqc` | `tests.yml`, each `py3.x` job | the pinned KATs and upstream outputs in `pq_verify/vectors/` | a FIPS 203, 204 or 205 verdict: each is its own track. HQC's covers its error-correcting code, not the KEM |
| An implementation that cannot be loaded (an HSM, a service) can be given fresh ACVP questions, whose answers exist nowhere until pq-verify computes them | `pq-verify --emit-prompt SET --fresh-key K`, then `--verify-response` | `tests.yml` tests: a computing responder passes; a prompt carries no answer; one wrong byte is a finding; published answers do not pass a fresh prompt | the auditor's key | which code answered: such a report says `artifact: none` ([LIMITS.md](LIMITS.md#what-a-pass-is-about)) |
| A library verdict is bound to the SHA-256 of every shared object that ran | any library audit with `--json FILE` | `tests.yml` tests: the binding is the file's own digest; a hash the vendor asserts is not a binding; a prompt/response result is never bound | — | that the binary behaves the same when it is not under test |
| Hybrid groups (RFC 10024), such as X25519MLKEM768: component order, offsets and lengths, checked from the wire bytes | `pq-verify --verify-hybrid TRANSCRIPT` | `tests.yml` steps: prompts are emitted and round-trip; an unparseable transcript fails a gate | — | the security of the combination, or of either component's implementation |
| Implementations in any language, audited through a Crucible-protocol harness | `python3 tools/harness_audit.py` | `vendor-audits.yml`, `harness audits (Crucible protocol, pinned)` | each harness's commit in `tools/harness_audits.json` | that the harness speaks for the library, which cannot be proved across a process boundary |
| Each release is built by CI, with SLSA provenance and an SBOM attested | `gh attestation verify pq_verify-<version>-py3-none-any.whl --repo bigDSanalyst/pq-verify` | `release.yml`, run by the maintainer | — | anything about correctness: provenance says where a file came from |
| CI's workflows pin each action to a commit and are checked for unsafe patterns | `zizmor .` | `zizmor.yml`, with zizmor 1.31.1, on every push and pull request | each action's commit | — |

## Not re-run by CI

AUDITS.md's first sections predate the pinned vendor audits. These are the
symbol audits of liboqs, PQClean and the pq-crystals reference, the BoringSSL
vector cross-check, and the negative control. pq-verify v2.6.4 produced them
on 2026-08-08, against the commits each section names, and gives the commands
to repeat them. CI does not repeat them; the full-scheme audits of the same
libraries, which it does, are in the tables below them.

## Reproducing the results

The checks of pq-verify itself need Python 3.9 or later and `gcc`, and run
offline:

```bash
pip install "pq-verify[full]"
pq-verify                  # the self-suite
pq-verify --acvp-all       # 1,566 NIST ACVP vectors
pq-verify --proofs         # the Coq proofs, with coqc installed
```

The vendor audits rebuild each pinned library, so they also need `cmake`,
`libssl-dev` and, for constant time, `valgrind`. The source audit needs `cbmc`
and, for ML-DSA, `z3` and Kissat; [SOURCE-AUDIT.md](SOURCE-AUDIT.md) says how
to build Kissat. From a checkout:

```bash
python3 tools/vendor_audit.py
python3 tools/source_audit.py --scheme ml-kem
python3 tools/source_audit.py --scheme ml-dsa
```

What pq-verify cannot check is in [LIMITS.md](LIMITS.md), and what it has
found in public libraries is in [AUDITS.md](AUDITS.md).
