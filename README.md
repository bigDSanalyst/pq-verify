# pq-verify v2.20.0 — PQC Implementation Verification

[![PyPI](https://img.shields.io/pypi/v/pq-verify.svg)](https://pypi.org/project/pq-verify/)
![license](https://img.shields.io/badge/license-MIT-green)
[![tests](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml/badge.svg)](https://github.com/bigDSanalyst/pq-verify/actions/workflows/tests.yml)
![self-suite](https://img.shields.io/badge/self--suite-160%20checks-brightgreen)
![ACVP-KEM](https://img.shields.io/badge/ML--KEM%20ACVP-240%2F240-brightgreen)
![ACVP-DSA](https://img.shields.io/badge/ML--DSA%20ACVP-615%2F615-brightgreen)
![ACVP-SLH](https://img.shields.io/badge/SLH--DSA%20ACVP-1248%2F1248-brightgreen)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24433273.svg)](https://doi.org/10.5281/zenodo.24433273)

**Independent verification for ML-KEM (Kyber), ML-DSA (Dilithium), SLH-DSA (SPHINCS+), LMS/HSS and XMSS/XMSS^MT implementations.**

You deploy post-quantum cryptography. pq-verify checks that **your** implementation computes the standard correctly, three ways:

- **A library you can load** (`--audit-kem`, `--audit-dsa`, `--audit-slhdsa`, `--audit-hbs`, `--audit-so`): pq-verify drives the vendor's own entry points with every NIST ACVP vector, Wycheproof's edge cases where they exist, and malformed inputs, in a child process with a timeout, and binds the verdict to the sha256 of every shared object that ran.
- **An implementation you cannot load** — an HSM, a sealed binary, a remote service (`--emit-prompt SET --fresh-key K`): fresh ACVP questions derived from a seed only the auditor holds, in NIST's own format. Their answers exist nowhere until pq-verify computes them, so a correct response had to be computed, not copied.
- **pq-verify itself**: its reference chain passes every pinned NIST ACVP vector: the 1566 of its default run (ML-KEM, ML-DSA, SLH-DSA, LMS), and SLH-DSA's 624 sigGen vectors on request. The FIPS 203 and FIPS 204 forward NTTs and their modular reductions carry Coq proofs over every input in range, about the algorithms as written in Coq ([what is proved, and what is only tested](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#proofs-and-tests)). This is what makes its verdicts on your code worth trusting; it is not a verdict on your code.

Results are evidence toward FIPS 140-3 / CMVP readiness and CNSA 2.0, not a certificate: a CMVP certificate is issued by NIST and the Canadian Centre for Cyber Security, after an accredited laboratory has tested the module.

It is a verification tool, not a cryptographic library to deploy: it checks the implementations that do the work, from liboqs and Bouncy Castle to your own code; [those audited so far](#implementations-pq-verify-has-audited) are listed below.

pq-verify is written with AI assistance (Claude) and directed by its
maintainer. None of its claims rest on that: the pinned-library audits in
[AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md) are re-run by CI, with planted bugs they must
catch, and [EVIDENCE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/EVIDENCE.md) gives the command and the CI job
behind each claim, and lists what CI does not re-run.

## Which document to read

| To | Read |
|---|---|
| run it on a library | [Quick start](#quick-start), then [QUICKSTART.md](https://github.com/bigDSanalyst/pq-verify/blob/main/QUICKSTART.md) |
| see what it found in real libraries, and the commands that reproduce it | [AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md) |
| know what it cannot check | [LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md) |
| trace a claim to the command and the CI job behind it | [EVIDENCE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/EVIDENCE.md) |
| constant time and side channels | [CONSTANT-TIME.md](https://github.com/bigDSanalyst/pq-verify/blob/main/CONSTANT-TIME.md); [Side channels are not measured](#side-channels-are-not-measured) |
| FN-DSA, Classic McEliece and HQC | [docs/SCHEMES.md](https://github.com/bigDSanalyst/pq-verify/blob/main/docs/SCHEMES.md) |
| put it in CI | [Use it in CI](#use-it-in-ci) |
| hybrid key agreement (RFC 10024) | [HYBRID.md](https://github.com/bigDSanalyst/pq-verify/blob/main/HYBRID.md) |
| see how it works | [ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md) |
| report a vulnerability in pq-verify | [SECURITY.md](https://github.com/bigDSanalyst/pq-verify/blob/main/SECURITY.md) |

---

## What you get

Layers of an audit:

| Layer | Question answered | How |
|-------|-------------------|-----|
| **Correctness** | Does the NTT compute the FIPS definition? | Field-native verification + non-circular KAT |
| **NIST vectors** | Does it match NIST's published vectors? | ML-KEM 240/240 + ML-DSA 615/615 + SLH-DSA 624/624 (keyGen and sigVer) + LMS 87/87 = 1566/1566 ACVP vectors (pinned); SLH-DSA sigGen 624/624 opt-in |
| **Parameters** | What does the lattice estimator give these parameters? | ML-KEM: the lattice-estimator's primal-uSVP cost, pinned; custom parameters: a calibrated primal-uSVP + hybrid estimate. Not a cryptanalysis ([limits](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#parameter-security)) |
| **Composition** | Do the two halves of a hybrid agreement fit together? | RFC 10024 component order, offsets and lengths, per group |

Every result is **reproducible**: the vectors are pinned by SHA-256, a report
on a library names that file by its SHA-256, and your own auditors can re-run
it.

---

## Results

- **In real libraries**: four findings in pinned upstream code — PQClean's
  ML-KEM accepts NIST's invalid keys; xmss-reference has two key-state
  defects; the HQC submitters' AVX2 Reed–Muller decoder has two defects; and
  PQClean's Falcon, built with GCC 13.3, branches on a secret in `fpr_floor`,
  a line whose source has no branch — and every planted bug caught, in each
  library audited
  ([which libraries, and how to reproduce each result](#implementations-pq-verify-has-audited))
- **NIST ACVP**, every vector passing: ML-KEM 240/240, ML-DSA 615/615,
  SLH-DSA 1248/1248 across all 12 parameter sets, LMS 87/87. The default run
  (`--acvp-all`) checks 1566 of them; SLH-DSA's 624 sigGen vectors run with
  `--slhdsa-siggen`
- **LMS/HSS and XMSS/XMSS^MT** (SP 800-208, CNSA 2.0's firmware-signing
  schemes) against every other pinned source, `--lms-xmss`
- **Coq proofs** (`pq-verify --proofs`) that the FIPS 203 and FIPS 204
  forward NTTs compute the map they are defined to and that their modular
  reductions stay in bound, over every input in range. They are about the
  algorithms as written in Coq, not about compiled code; the rest is tested
  ([LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#proofs-and-tests))
- **pq-verify's own self-suite, 160/160**, across 6 field-native engines, of which **54 verify
  PQC directly**; the others check the harness itself or are classical and
  research engines, never counted as PQC evidence
  ([how the checks are tracked](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#engines-and-where-they-are-heading)).
  A check whose optional dependency is missing reports `⊘ SKIPPED`, never a
  pass and never a failure

All of it on commodity hardware (Google Colab CPU); each item in full, with
the native full-KEM, non-circular KAT and lattice-estimator results, is in
[ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#proven-in-detail).

---

## Quick start

```bash
pip install "pq-verify[full]"
pq-verify --acvp-all            # 1566/1566, offline, no configuration, ~1 min
pq-verify --slhdsa-siggen      # + SLH-DSA sigGen, 624 signatures, ~30 min
pq-verify --fndsa              # FN-DSA verification, FIPS 206 DRAFT track, ~1 s
pq-verify --mceliece           # Classic McEliece reference vs the KATs, NOT a FIPS standard
pq-verify --hqc                # HQC's error-correcting code vs the submitters' decoders, ~2 s
```

That is the whole installation. It is a command-line tool and runs offline: no
notebook, no network, no service. The commands above need Python 3.9+ and the
packages `[full]` installs, nothing more, except `--fndsa`, which builds a
small C engine with `gcc` for one of its checks. The self-suite needs `gcc`
and `g++`; [Requirements](#requirements) has the rest. The NIST vectors ship
inside the package, so air-gapped environments work out of the box.

Edge cases, offline: C2SP's [Wycheproof](https://github.com/C2SP/wycheproof)
and [CCTV](https://github.com/C2SP/CCTV) vectors (`strcmp` traps, unlucky
sampling, every out-of-range ek coefficient, malformed ML-DSA hints) are pinned
to exact commits and run by `--audit-kem` and `--audit-dsa` against a vendor
library, and by
`pq-verify --edge-cases` against pq-verify's own references. Against
dilithium-py 1.5.1, the version CI pins and `pip install "pq-verify[full]"`
installs today, the latter reports no finding. dilithium-py 1.4.0 accepts a
repeated hint index; with it installed, the run reports that, as a known
defect of 1.4.0.

To audit a compiled library (this runs the library's code as your user, so
audit a binary you do not trust in a container or a VM):

```bash
pq-verify --audit-so build/libmlkem768.so PQCLEAN_MLKEM768_CLEAN_ntt
pq-verify --audit-kem build/libmlkem768.so ML-KEM-768     # the whole KEM
pq-verify --audit-contained build/libmlkem768.so ML-KEM-768   # the KEM, scored apart from the library
pq-verify --audit-dsa build/libmldsa65.so ML-DSA-65       # the whole signature scheme
pq-verify --audit-slhdsa build/libslhdsa.so SLH-DSA-SHA2-128f   # SLH-DSA, all three interfaces
pq-verify --audit-hbs build/libhashsigs.so                # LMS/XMSS, via a pqv_hbs adapter
```

**The minimal audit.** If you run one command against an ML-KEM library,
run this one: NIST, Wycheproof and CCTV vectors, the FIPS 203 input checks,
10 000 accumulated cases and the constant-time check, with a JSON report
bound to the library's SHA-256, and (the default) a nonzero exit on any
finding:

```bash
pq-verify --audit-kem build/libmlkem768.so ML-KEM-768 --constant-time --json report.json
```

For ML-DSA, the same with `--audit-dsa`. Its `--constant-time` needs one more
thing: Sign's rejection loop branches on secret-derived values by design, so
only the library's own declarations of what is public can tell those branches
from a leak. Build the library with them compiled in and pq-verify's shim in
front of them; any other build is reported CANNOT VERIFY, never a pass
([CONSTANT-TIME.md](https://github.com/bigDSanalyst/pq-verify/blob/main/CONSTANT-TIME.md)). For mldsa-native:

```bash
H=$(python3 -c 'import os, pq_verify; print(os.path.join(os.path.dirname(pq_verify.__file__), "harness"))')
cc -O2 -g -fPIC -shared -DMLD_CONFIG_PARAMETER_SET=65 -DMLD_CONFIG_CT_TESTING_ENABLED \
   -I "$H/ct" -I mldsa mldsa/mldsa_native.c "$H/ct/pqv_ct_shim.c" "$H/pqv_randombytes.c" \
   -o libmldsa65-ct.so
pq-verify --audit-dsa libmldsa65-ct.so ML-DSA-65 --constant-time --json report.json
```

**liboqs.** A library can hold more than one implementation: liboqs exports
its public `OQS_*` API and, beside it, every backend it dispatches to
(mlkem-native's and mldsa-native's portable C and x86-64 code). pq-verify
refuses to guess between them, lists them, and audits the one you name:

```bash
pq-verify --audit-kem   liboqs.so ML-KEM-768 --symbol-prefix OQS_KEM_ml_kem_768_ --constant-time
pq-verify --audit-dsa   liboqs.so ML-DSA-65  --symbol-prefix OQS_SIG_ml_dsa_65_
pq-verify --audit-fndsa liboqs.so FN-DSA-512 --symbol-prefix OQS_SIG_falcon_512_   # draft track
pq-verify --audit-slhdsa liboqs.so SLH-DSA-SHA2-128f   # its pure and 12 HashSLH-DSA algorithms
```

The public API is what your application calls; a backend's prefix
(`PQCP_MLKEM_NATIVE_MLKEM768_C_`, for one) audits the code a CPU without
AVX2 runs. liboqs 0.16.0 passes all of it, per implementation, rebuilt and
re-audited in CI ([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md)).

For an implementation that cannot be loaded — an HSM, a sealed vendor binary,
a build with the transform inlined — ask it the questions instead:

```bash
pq-verify --emit-prompt ML-DSA-65 --prompt-out prompt.json   # 205 questions, no answers
#   ... the implementer runs them, wherever it lives, and returns a response ...
pq-verify --verify-response response.json                    # byte-exact, per test case
```

**This route is weaker than `--audit-so`, and the report says so:** a passing
response shows the standard was computed correctly, not *which binary* computed
it, so the result carries `artifact: none` ([below](#what-a-result-is-bound-to)).
Use it when the alternative is no verification at all, not when you can point
at a file.

A hybrid TLS key agreement such as X25519MLKEM768 joins ML-KEM to ECDH, and
ACVP's algorithm-level vectors do not cover how the two halves are put
together. To check that part:

```bash
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
#   ... fill in the wire bytes from one handshake ...
pq-verify --verify-hybrid hybrid.json                        # RFC 10024 composition
```

`DEMO.ipynb` runs the same thing in Colab if you prefer a notebook.

The Python API, and the other install routes, are in
[ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#public-api).

---

## What a result is bound to

Every report states its binding as a field, not as prose:

| Path | `artifact` |
|------|-----------|
| `--audit-so`, `--audit-kem`, `--audit-dsa`, `--audit-slhdsa`, `--audit-hbs` | `sha256 <hash>` — that file performed the computation |
| `--audit-contained` | `sha256 <hash>` — a sealed in-memory copy of that file, hashed as it was copied, performed the computation |
| `--verify-response` | `none — vendor-supplied response` |
| `--verify-hybrid` | `none — vendor-supplied transcript` |
| `--acvp`, `--acvp-all` | `none — reference-chain conformance, no vendor binary loaded` |

The binding is recorded independently of the verdict, because they are
different facts. A library that exposes no derandomised entry points is
`artifact: sha256 <hash>` (the file was read) with status `CANNOT VERIFY` (no
vector was ever driven through it). In SARIF the hash is emitted as the run's
`artifacts[].hashes.sha-256`, which is where a security platform already looks
for "this exact file was analysed".

**Isolation and what actually ran.** Each `--audit-*` that loads a library
runs it in a child process (`--audit-timeout`, default one hour). A library
that crashes on a test vector or hangs is reported — `CANNOT VERIFY`, with the
signal or the limit — instead of taking pq-verify and its report down with it.
The child leads a process group of its own, and the group (the child and the
processes the library starts) is stopped at the deadline and when the audit
ends. A process that leaves the group, as a daemon does, is not stopped.
The child is **not a sandbox**: it scores the results in the same process as
the library, with your user's privileges, so a library that corrupts memory or
is built to deceive the audit can change its own verdict. A harness
(`--audit-harness`) is a process of its own, with your user's privileges too.
Audit a binary you do not trust in a container or a VM
([SECURITY.md](https://github.com/bigDSanalyst/pq-verify/blob/main/SECURITY.md#what-pq-verify-does-on-purpose)). The child records
every shared object the audit mapped (`artifact.loaded_objects`: path, inode,
sha256), so the binding covers the vendor library *and* what it pulled in — a
libcrypto, a dependency found through `LD_LIBRARY_PATH` — plus any
`LD_PRELOAD`/`LD_LIBRARY_PATH` in effect (`artifact.loader_environment`). The
audited file is hashed before the run and again after it; if they differ, the
verdict is `CANNOT VERIFY` ([LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md) says what that cannot catch).

**A library kept away from its verdict.** `pq-verify --audit-contained
build/libmlkem768.so ML-KEM-768` runs an ML-KEM library somewhere else: in a
worker process that is sent inputs and returns what the library wrote. The
vectors, the expected answers and the scoring stay in pq-verify's own process,
whose memory the worker cannot open while the audit runs, so a library that
corrupts memory corrupts the worker's and not its verdict. The library is
loaded from a sealed in-memory copy of the file, hashed as it was copied, so
what was hashed is what runs, whatever happens to the file on disk. Before the
library is mapped, the worker drops its privileges and installs a seccomp
filter, and pq-verify confirms both from `/proc`. The filter stops the library
starting a process, running another program, opening a socket, opening a file
for writing or changing one, and signalling or tracing another process: a
library that tries is killed by the kernel and reported
(`ISO-SECCOMP-VIOLATION`), and so is a process left behind (`ISO-ESCAPEE`).

The worker can still read any file you can, and NIST's answers are files:
they are published, and this package ships them. So a contained audit also
asks **fresh questions**, drawn from a seed made for the run and scored against
answers pq-verify's reference computes; the seed is in the report, and
`--fresh-seed` replays it. A planted library that cannot compute ML-KEM and
answers from a table of NIST's vectors passes all 80 of them and fails the
fresh ones. The checks are `--audit-kem`'s, without `--constant-time`; on
PQClean's ML-KEM-1024 the two paths agree stage by stage. Linux on x86-64,
with a C compiler; anywhere else the result is `CANNOT VERIFY`. It is **not a
sandbox**, and it does not catch a library that computes correctly only while
it is being audited
([SECURITY.md](https://github.com/bigDSanalyst/pq-verify/blob/main/SECURITY.md#what-pq-verify-does-on-purpose),
[LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#the-contained-worker)).

**Never ship a test build.** The randomness harness and the pqv_hbs adapters
make a library deterministic and stateless on purpose. `pq-verify
--check-no-harness lib.so` exits 1 if either is present; put it in the release
job of anything audited this way.

**Ask fresh questions.** NIST's published questions have published answers:
NIST ships `expectedResults.json` beside every prompt, and so does this
package. A response to them that matches shows only that the answers were
obtained.
For an audit through `--emit-prompt`, pose questions derived from a seed only
you hold:

```bash
pq-verify --emit-prompt ML-DSA-65 --fresh-key audit.key      # send the prompt, keep the key
pq-verify --verify-response response.json --fresh-key audit.key
```

How fresh questions are derived and checked, LMS key-reuse detection, the
`scope` field, and how incomplete or unanswerable runs are reported:
[ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#what-a-result-is-bound-to-in-depth).

---

## Use it in CI

A few lines in any repository that builds a post-quantum library. Findings
appear as annotations on the pull request, and the build fails on any result
that did not verify — including one that could not run.

```yaml
- uses: bigDSanalyst/pq-verify@v2.20.0
  with:
    audit: dsa                       # kem | dsa | slhdsa | fndsa | hbs | ntt
    library: build/libmldsa65.so
    param-set: ML-DSA-65
```

With no library at all, it runs the NIST ACVP suites against pq-verify's own
reference chain:

```yaml
- uses: bigDSanalyst/pq-verify@v2.20.0
```

| Input | Default | Purpose |
|---|---|---|
| `audit` | — | `kem`, `dsa`, `slhdsa` (v2.16.0 and later), `fndsa` (FIPS 206 draft track), `hbs` (pqv_hbs adapter) or `ntt` |
| `library` | — | the compiled `.so` to audit. It runs inside the job, with the job's permissions and secrets |
| `param-set` | — | with `kem`, `dsa`, `slhdsa` or `fndsa`: e.g. `ML-KEM-768`, `ML-DSA-65`, `SLH-DSA-SHA2-128f`, `FN-DSA-512` |
| `symbol` | — | with `ntt`: the exported NTT symbol (`nm -D lib.so \| grep -i ntt`) |
| `acvp` | `true` | run ACVP suites; `live` fetches NIST's current vectors |
| `slhdsa` | `false` | `siggen` adds SLH-DSA's 624 sigGen vectors to the ACVP suites (about 30 minutes) |
| `hybrid-transcript` | — | transcript to check against RFC 10024 (see `--emit-hybrid-prompt`) |
| `fail-on-finding` | `true` | fail the step on any result that did not verify; `false` reports only |
| `sarif-file`, `json-file` | `pq-verify.sarif`, `pq-verify.json` | where the library audit's SARIF 2.1.0 and JSON reports go |
| `version` | the Action's own release | the pq-verify to install. By default the release the Action belongs to, so a workflow pinned to a release keeps that release's pq-verify (from v2.17.0; v2.16.0 and earlier install the newest). `latest` installs the newest release on PyPI at every run, so the code that audits your library can change without your workflow changing; a version such as `2.20.0` installs that release; and `git:<ref>` installs a ref from source |

Outputs: `verified` (true only if every task that ran verified; with
`acvp: false` and no library or transcript nothing runs, and the step fails
with `verified` false), `findings`, `sarif-file`. Every input reaches the shell through the environment, never by
template substitution, and every action the Action uses is pinned to a commit.
So is every action in this repository's own workflows, and a zizmor job fails
CI on any workflow finding. CI also runs the Action itself, as a workflow
would, on GitHub's runner: the NIST suites and an audit of PQClean's NTT with
its SARIF uploaded to code scanning, and a hybrid transcript written to set the
`verified` output through the runner's workflow commands, which must set
nothing.
Pin the Action itself to a full release tag, as the examples above do, or to a
commit SHA. Do not use `@v1`: it marks the first upload and does not move to
new releases. On v2.16.0 or earlier, also set `version` (for example
`version: '2.16.0'`): those releases of the Action install the newest
pq-verify otherwise.

The library runs inside the job, with the job's permissions and any secrets in
its environment, and it can make the audit report a pass it did not earn
([LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#what-a-pass-is-about)). Audit only a build the job would
run anyway, and never a pull request's build under `pull_request_target`.

**Exit status** of the CLI, since 2.10.0: `0` verified, `1` a task found
problems or could not verify, `2` bad input. Gating is the default;
`--no-fail` reports without gating. Before 2.10.0 every task exited 0 unless
`--fail-on-finding` was passed, which the Action did not pass for its ACVP
step. A complete workflow is in
[`example-workflow.yml`](https://github.com/bigDSanalyst/pq-verify/blob/main/example-workflow.yml).

---

## Machine-readable output

```bash
pq-verify --audit-so build/libmlkem768.so PQCLEAN_MLKEM768_CLEAN_ntt \
          --sarif results.sarif --json results.json --fail-on-finding
```

The native JSON report names its schema and version, the pq-verify version
that wrote it (`tool`), when it ran, and what it is bound to (`artifact`).

**SARIF 2.1.0** is imported directly by GitHub Code Scanning (the
[Action](#use-it-in-ci) uploads it) and DefectDojo, so findings land in the
security tooling a team already runs rather than in a terminal someone has to
read. AWS Security Hub takes its own format (ASFF), so it needs a
SARIF-to-ASFF conversion step.

| Rule | Meaning |
|---|---|
| `PQV001` | NTT output diverges from the FIPS reference |
| `PQV002` | Freivalds probabilistic check failed |
| `PQV003` | Root of unity has the wrong multiplicative order |
| `PQV004` | Non-circular known-answer test failed |
| `PQV005` | Boundary/edge-case vector failed |
| `PQV006` | Vendor answer differs from the pinned NIST value |
| `PQV007` | Hybrid key agreement does not compose the way RFC 10024 pins it |
| `PQV008` | ML-DSA library output or verdict differs from NIST, Wycheproof or FIPS 204 |
| `PQV009` | LMS/XMSS library output or verdict differs from the pinned vectors |
| `PQV010` | Undefined behaviour, an overflow or a wrong reduction in the C source |
| `PQV011` | The library did what the contained worker's filter forbids, or left a process behind |
| `PQV012` | An integer division is reachable from a secret-input entry point (note; a review pointer, not a timing verdict) |
| `PQV000` | The run could not verify this — not a pass and not a failure |

`--fail-on-finding` exits non-zero, so it can gate a merge.

---

## Implementations pq-verify has audited

pq-verify has been run against upstream projects, each pinned to a commit,
with planted bugs (mutants) that CI requires it to catch: liboqs 0.16.0,
PQClean, mlkem-native, mldsa-native, the pq-crystals reference code, Bouncy
Castle 1.86 (Java), slhdsa-c, cisco/hash-sigs, xmss-reference and BoringSSL,
and Classic McEliece (PQClean, liboqs) and HQC (PQClean, the submitters' code).
Four have findings:

- PQClean's ML-KEM accepts NIST's invalid keys;
- xmss-reference has two key-state defects;
- the HQC submitters' AVX2 Reed–Muller decoder has two defects;
- PQClean's clean Falcon (FN-DSA, draft track), built with GCC 13.3, branches
  on a secret in `fpr_floor`: the source is branch-free, the compiler adds the
  branch.

The rest verify clean, and every mutant is caught. The table by library, the
exact commits, the build commands and the per-check output are in
[AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md#by-library).

---

## More audit modes

### C source: CBMC, on every input FIPS 203 and 204 allow

`pq-verify --audit-source DIR` checks an ML-KEM or ML-DSA library's C source,
not its binary, and annotates nothing in it.
- **ML-KEM:** CBMC proves that `poly_reduce`, the NTT, the NTT-domain
  multiplication and `poly_frommsg` have no undefined behaviour on any input
  FIPS 203 allows them, and that the NTT and the multiplication never
  overflow an int16 coefficient. `barrett_reduce` and `montgomery_reduce` are
  tested on every input they accept, and the zeta table against FIPS 203's
  definition.
- **ML-DSA:** CBMC proves the NTT, its inverse, the NTT-domain
  multiplication, `poly_reduce` and `poly_chknorm` free of undefined
  behaviour and int32 overflow on every input FIPS 204 gives them, the first
  four with their output bounds. With an exhaustive test of every low word,
  it also proves `montgomery_reduce` correct on every input of its contract.
  `caddq` is tested on all 2³² inputs, and `reduce32` and `freeze` on every
  input their contract allows (2³² − 2²² of them). The zeta table is checked
  against FIPS 204, and `power2round`, `decompose` and `use_hint` against
  FIPS 204's own algorithms on every r in [0, q).

Undefined behaviour covers out-of-bounds accesses, signed overflow and bad
shifts. CBMC's own self-test and each check's control must catch a planted
defect first, or the run is CANNOT VERIFY. So is a run that calls a function
whose body is not in the source given, which CBMC would take to do nothing,
and source holding CBMC directives or inline assembly. One of PQClean's
parameter sets takes about 8 minutes for ML-KEM and 23 for ML-DSA. It needs
`cbmc` and a C compiler, and for ML-DSA `z3` and Kissat. What it proves and
what it does not is in [SOURCE-AUDIT.md](https://github.com/bigDSanalyst/pq-verify/blob/main/SOURCE-AUDIT.md).

### Accumulated vectors: 10 000 random cases, one digest

Every `--audit-kem`, `--audit-dsa` and `--audit-harness` run also drives
10 000 seeded random cases through the library and compares a SHAKE-128
digest of every output with a pinned value -- the way Go and BoringSSL test
themselves. Fixed vectors cover the edge cases someone thought of; these
reach the ones nobody did (a planted bug that fires on 1 ciphertext in 8 192
passes every NIST, Wycheproof and CCTV vector and is caught here). Coverage is
probabilistic: bugs rarer than about 1 in 10 000 operations may not be hit.
ML-DSA digests are C2SP CCTV's; ML-KEM's are Go's, because CCTV's published
ML-KEM digests turn out to be the FIPS 203 draft
([details](https://github.com/bigDSanalyst/pq-verify/blob/main/pq_verify/accumulated.py)). `--accumulated 0` skips them.

### Any language: Crucible-protocol harnesses

**A harness result is not bound to a library.** pq-verify hashes the
harness executable, not the library behind it, so a harness audit says what
*something answering through that harness* computes. It is not
artifact-bound evidence about a specific binary, of the kind a CMVP-style
review needs; for that, load the library (`--audit-kem`, `--audit-dsa`).

`pq-verify --audit-harness './harness-go-stdlib' ML-KEM-768` audits an
implementation in any language through a harness speaking
[Crucible](https://github.com/symbolicsoft/crucible)'s JSON-line protocol,
with pq-verify's own vectors and verdicts — only the wire format is
Crucible's. Go's `crypto/mlkem` and Cloudflare CIRCL (ML-KEM and ML-DSA) are
VERIFIED through Crucible's unmodified harnesses, rebuilt and re-audited in CI.
So is Bouncy Castle's Java provider, through pq-verify's own harness
(`pq_verify/harness/bouncycastle/`), which feeds it NIST's seeds through the
API users call and names the jar it loaded, with its sha256; CI pins that jar
by sha256 and plants five bugs in its sources, all caught
([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md#bouncy-castle-java-through-pq-verifys-harness)).
A harness is untrusted: its message convention is settled against NIST, its
determinism is tested, and a crash, or a reply that is not the protocol's, is
CANNOT VERIFY, never a refusal. The
library behind a harness is not hashed, and the report says so
([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md#any-language-through-crucible-protocol-harnesses)).

### FN-DSA, Classic McEliece and HQC

Three schemes outside FIPS 203, 204 and 205, each checked as far as its
specification allows: FN-DSA (`--audit-fndsa`, the FIPS 206 draft), Classic
McEliece (`--audit-mceliece`, not a FIPS standard) and HQC's error-correcting
code (`--audit-hqc`, its standard not final). What each checks, its results on
the pinned libraries and what it cannot see are in
[docs/SCHEMES.md](https://github.com/bigDSanalyst/pq-verify/blob/main/docs/SCHEMES.md).

---

## Hybrid key agreement (RFC 10024)

A **hybrid** TLS group joins ML-KEM to ECDH, and ACVP never sees how its two
halves are concatenated. RFC 10024 does not use one order:

| Group | Codepoint | Key share | Shared secret |
|---|---|---|---|
| `X25519MLKEM768` | `0x11EC` | ML-KEM ‖ ECDHE | ML-KEM ‖ ECDHE |
| `SecP256r1MLKEM768` | `0x11EB` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |
| `SecP384r1MLKEM1024` | `0x11ED` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |

The first row is reversed relative to its own name. The RFC says so itself,
and calls it historical. So an implementation can pass **every ACVP vector
byte-for-byte** and still be wrong, because ACVP never sees the concatenation.

`--verify-hybrid` checks one handshake's wire bytes: every length, the FIPS 203
§7.2 encapsulation-key check, the ECDHE point, the X25519 all-zero check and,
given ephemeral test keys, both halves of the shared secret recomputed. When a
check fails it tests the other order and names the root cause. Commands are in
the [Quick start](#quick-start); what is checked, and how, is in
[HYBRID.md](https://github.com/bigDSanalyst/pq-verify/blob/main/HYBRID.md).

---

## Scope

pq-verify verifies the **algebraic substance** of ML-KEM/ML-DSA (NTT, module-LWE relations, parameter security) natively in Z₃₃₂₉ / Z₈₃₈₀₄₁₇. The **non-algebraic layers** (SHAKE/SHA3 hashing, sampling, compression, the FO transform) are bit/byte operations verified by NIST ACVP end-to-end testing, not native field solving.

The forward NTTs and the modular reductions are proved in Coq, over every input in range. Everything else, end to end, is tested byte for byte against NIST's pinned vectors, which shows agreement on those inputs, not on every input ([LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#proofs-and-tests)). Each claim here says which of the two it rests on.

pq-verify also prints a per-layer algebraic protection allocation: which NTT
layers would expose the secret if observed, computed from the transform's
structure. That is a design input for masking, not a measurement of any
implementation.

Everything pq-verify does not check — schemes, side channels, parameter
security, which paths are proved and which are only tested — is collected in
[LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md).

### Side channels are not measured

pq-verify compares values. It never executes an implementation under
measurement, collects no traces, and observes no timing, power or
electromagnetic behaviour. **It cannot detect an implementation that computes
the correct answer and leaks the key while doing it.**

This is not hypothetical. KyberSlash and Clangover were byte-exact correct
against every vector and still recovered secret material through timing. A
tool that checked only values would have passed both.

**`--audit-kem ... --constant-time` closes part of that gap, and says exactly
which part.** It runs the vendor's own Encaps (m secret) and Decaps (the
secret key and z secret, on a valid and on a random ciphertext) under
Valgrind memcheck with the secret bytes marked, and fails on every branch and
every memory address that depends on them, naming the function -- the
technique mlkem-native and BoringSSL use on themselves. It catches the
Clangover class (a compiler-introduced branch on a secret bit) and
cache-timing table lookups; three such leaks planted in PQClean, each leaving
every output correct, are caught in CI. It does **not** see instruction
timing -- KyberSlash's secret division -- so the report lists the library's
integer divisions for a reviewer instead, marking those reachable from Encaps
or Decaps by call-graph reachability (the note-level rule `PQV012`, a pointer
and not a verdict; a KyberSlash-class division put back into ML-KEM's
compression is caught as reachable from Decaps while every memcheck stage stays
green); it cannot check key generation (the public matrix seed is derived from
the secret seed); and it measures nothing physical. The report records exactly that scope, and without the flag
claims nothing ([the report fields](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#side-channel-report-fields)).

**`--audit-dsa ... --constant-time` does the same for ML-DSA's key generation
and signing**, where it needs more: Sign branches on secret-derived values by
design, at points where FIPS 204 lets a value be public. pq-verify therefore
judges a build with the library's own declarations of what is public compiled
in, through a shim that logs each one with its call site. memcheck and the log
each cover what the other cannot see. memcheck still reports a branch or
address on any value derived from a secret the library has not declared public,
however plausible its declarations are. A declaration blinds memcheck to what
it releases, so the log judges each one: it must be at a known site, of its
length, in its place in the attempt, and equal to the value the public key and
signature determine wherever they determine it. Where they determine nothing,
as for a rejection flag, the value cannot be checked against them; its site,
length and place still are. Six controls planted in mldsa-native (a branch on a
coefficient's sign, declassifications too early or of the wrong value, a secret
table read, a hardware division) give exactly their specified results in CI. A
build without those declarations is CANNOT VERIFY.
[CONSTANT-TIME.md](https://github.com/bigDSanalyst/pq-verify/blob/main/CONSTANT-TIME.md) is the specification, with its scope: it
does not see the values a computation produces, the leak Berzati et al.
exploited on ML-DSA's signing.

**`--audit-fndsa ... --constant-time` checks FN-DSA's signing.** Falcon
declares nothing public, so the branches its signer takes by design are
matched by function and source line instead, which needs the library's
debug information and its source. That is how it finds the jump GCC 13
compiles PQClean's `fpr_floor` into. It does not check key generation.
`--leakage` is not an exception: it is a design input computed from the NTT's
structure, not an observation of execution.

---

## Verifying a release

Releases are built by `.github/workflows/release.yml` on GitHub's runners, from
a reviewed commit, after the full suite and all 1566 NIST ACVP vectors pass on
Python 3.9 through 3.14. Each artifact carries **SLSA build provenance** and an
attested **SPDX SBOM**. Check them yourself, trusting nothing this repository
says:

```bash
gh attestation verify pq_verify-2.20.0-py3-none-any.whl --repo bigDSanalyst/pq-verify
```

That tells you which workflow built the file, from which commit, on whose
runners — not that we assert it, but that GitHub signed it. Provenance cannot
be added to an artifact after the fact, which is why a release built anywhere
else can never have it.

The SBOM is short: **pq-verify has no unconditional runtime dependencies.**
`kyber-py`, `dilithium-py`, `sympy` and `slh-dsa` are optional extras used to
cross-check against independent implementations; the package itself installs
with none of them. So the SBOM lists pq-verify itself, with its licence, its
purl and each file the wheel installs with its SHA-256, and no dependency.
2.12.1 is the first release whose SBOM does: the SBOMs attached to 2.11.0 and
2.12.0 are empty, and name only the build folder that was scanned.

---

## How it works

[ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md) holds what is not needed to run an audit:

- [Engines and where they are heading](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#engines-and-where-they-are-heading):
  the PQC, harness, classical and research tracks, and why only the first is
  PQC evidence
- [The six field-native engines](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#architecture--six-field-native-engines)
  and the [specification front-end](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#specification-front-end)
- [Deterministic by default](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#deterministic-by-default): the
  pinned NIST vectors and how they are re-pinned
- [The Python API](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#public-api)
- [What a result is bound to, in depth](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#what-a-result-is-bound-to-in-depth)
  and the [side-channel report fields](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#side-channel-report-fields)
- [What's in this package](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#whats-in-this-package)

Third-party audit results, build commands and every planted bug are in
[AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md); hybrid composition in [HYBRID.md](https://github.com/bigDSanalyst/pq-verify/blob/main/HYBRID.md).

---

## Requirements

**Minimum (core engines; self-suite checks that need the packages below report as skipped):**
- Python 3.9+ — **every version of the declared range (3.9, 3.10, 3.11, 3.12,
  3.13, 3.14) runs the full test suite and all 1566 ACVP vectors in CI.** The floor is
  3.9 rather than 3.8 because `pq-verify[full]` cannot resolve below it:
  `kyber-py` and `dilithium-py` both require `>=3.9`. `requires-python` and the
  code are held together mechanically — a module that stops parsing at the
  declared floor fails the suite, and widening the floor fails it too.
- gcc and g++ (the C/C++ engines compile at runtime); on macOS, Xcode's
  command-line tools (Apple clang) — every engine still builds with
  `-march=native`, falling back to `-mcpu=native`
- Linux (x86-64) or macOS (Apple silicon); both run the full suite in CI

**For the full 160/160 self-suite and the 1566/1566 ACVP claim:**
- `kyber-py` — **required** for `pqverify_acvp()` (the byte-exact NIST reference) and the FIPS 203 roundtrip tests
- `dilithium-py` — **required** for `pqverify_mldsa_acvp()` (the 615 ML-DSA vectors)
- `slh-dsa` — **required** for the 624 SLH-DSA vectors and the live roundtrip (parameters still validate without it)
- `coq` — required for the Coq certificate verification tests and
  `--proofs`. CI checks the proofs with Coq 8.18.0, the version Ubuntu 24.04
  packages; no other version is tested
- `sympy` — required for the Engine-6 Conjecture 7 exact-rational test (without it that check reports as skipped, not failed)
- `cryptominisat` — the CMS5 speed-comparison benchmark (without it that check reports as skipped)

```bash
apt-get install -y coq cryptominisat gcc g++
pip install "pq-verify[full]"   # kyber-py, dilithium-py, sympy, slh-dsa
```

**For `--constant-time`:** Valgrind with its headers (`valgrind/memcheck.h`;
`apt install valgrind`) and a C compiler, which builds the small driver that
runs the library under memcheck. For FN-DSA, the library also needs its debug
information (`-g`), and its source where that information says.

**For `--audit-contained`:** Linux on x86-64 with seccomp and `/proc`, and a C
compiler, which builds the worker when the audit runs. `kyber-py` computes the
answers to the fresh questions; without it they are not applicable, and the
report says so.

**For `--audit-source`:** `cbmc` (`apt install cbmc`) and a C compiler, and
for ML-DSA also `z3` and Kissat, which solves the NTT proofs. Ubuntu does not
package Kissat; [SOURCE-AUDIT.md](https://github.com/bigDSanalyst/pq-verify/blob/main/SOURCE-AUDIT.md) says how to build it.
Without it, ML-KEM's NTT runs with CBMC's built-in MiniSat, more slowly.

**Optional:**
- network access — `pqverify_acvp()` fetches NIST vectors from GitHub live; for air-gapped use the pinned vectors are used by default, or pass `vector_dir=` pointing at your own local vector set

**Deliberately NOT required** (a deployment advantage):
- No numpy, scipy, or PyTorch — pure Python + ctypes + inline C
- No SageMath — the `pqverify_params` lattice estimator is self-contained (ML-KEM's lattice-estimator values are pinned; custom parameters use a calibrated formula, [close but not exact](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#parameter-security))

---

## Enterprise audits and pre-CMVP readiness

pq-verify is open source and free to run yourself. Its maintainer also runs
audits with it for teams that want the evidence before a certification lab,
a customer or a deployment sees their code:

- **Library audit**: ML-KEM, ML-DSA and SLH-DSA libraries through their own
  entry points, LMS/HSS and XMSS through a small adapter, and HSMs and sealed
  binaries through fresh ACVP questions. Each audit runs the checks
  that apply: NIST's ACVP vectors, Wycheproof and CCTV edge cases, malformed
  inputs, key-state handling for LMS and XMSS, and constant time for ML-KEM
  and, in a build with its own annotations compiled in, ML-DSA.
- **Pre-CMVP gap assessment**: the ACVP algorithm tests a CMVP submission
  depends on, run beforehand, with each failure traced to its cause.
- **Hybrid TLS review**: RFC 10024 groups such as `X25519MLKEM768`, checked
  from the wire bytes, where ACVP never looks.
- **Remediation verification**: the same audit re-run on the fixed build,
  bound to its sha256.
- **CI integration**: the GitHub Action gates merges on the result, and SARIF
  2.1.0 carries the findings to GitHub Code Scanning or DefectDojo.
- **CNSA 2.0**: its post-quantum algorithms, ML-KEM-1024, ML-DSA-87 and
  LMS/XMSS for firmware signing, are all covered.

The deliverable is evidence, not certification: a CMVP certificate is issued
by NIST and the Canadian Centre for Cyber Security, after an accredited
laboratory has tested the module. What pq-verify has found in public
libraries is in [AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md); what it cannot check is in
[LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md); how each requirement maps to a check is in
[ARCHITECTURE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/ARCHITECTURE.md#mapping-to-requirements); and each claim,
with the command that reproduces it and the CI job that re-runs it, is in
[EVIDENCE.md](https://github.com/bigDSanalyst/pq-verify/blob/main/EVIDENCE.md). To discuss an audit, see [Contact](#contact).

---

## License

MIT. Audits and commercial support: see [Enterprise audits and pre-CMVP readiness](#enterprise-audits-and-pre-cmvp-readiness).

## Citing this software

Archived on Zenodo with a citable DOI:

> Maino, N. C. (2026). *pq-verify: Independent verification for post-quantum
> cryptography implementations* (v2.20.0). Zenodo. https://doi.org/10.5281/zenodo.24433273

```bibtex
@software{maino_pqverify_2026,
  author    = {Maino, Nicholas Clifford},
  title     = {pq-verify: Independent verification for post-quantum cryptography implementations},
  version   = {2.20.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.24433273},
  url       = {https://doi.org/10.5281/zenodo.24433273}
}
```

The DOI above resolves to this specific release. To cite pq-verify as a
whole, whatever the version, use the all-versions DOI,
[10.5281/zenodo.21739510](https://doi.org/10.5281/zenodo.21739510): it always
resolves to the latest release. The companion paper is
[10.5281/zenodo.19302050](https://doi.org/10.5281/zenodo.19302050).

`CITATION.cff` names the version deposited on Zenodo. When a release is newer
than the last deposit, the version citation lags on purpose until a new one
exists — a DOI that does not resolve to the version printed beside it would be
worse than one a release behind. The all-versions DOI never lags. For the
current version see
[Releases](https://github.com/bigDSanalyst/pq-verify/releases) or the PyPI
badge at the top.

## Contact

Nicholas Maino (iamweare) · maiknown@gmail.com · https://github.com/bigDSanalyst
Zenodo: https://doi.org/10.5281/zenodo.19302050