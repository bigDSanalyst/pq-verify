# Limits

What pq-verify does not check, in one place. Each item is also stated where
the check it limits is documented; this page collects them so a reader can
see the edges before reading a result. A pass means what the check that
produced it says, and nothing on this page.

---

## What a pass is about

- **The binary you gave it, behaving as it did under test.** A library built
  to recognise pq-verify could behave differently when it is not being
  audited. That is the limit of any black-box test. The answers are a build
  you control, and the prompt/response path below
  ([ARCHITECTURE.md](ARCHITECTURE.md#what-a-result-is-bound-to-in-depth)).
- **Not a library written to deceive the audit.** A library audit
  (`--audit-kem`, `--audit-dsa` and the rest) computes its verdict in the
  process that has loaded the library, so a library written to deceive
  pq-verify can make it report a pass, in the JSON and the SARIF alike.
  pq-verify does not defend against that, and a container or a VM does not
  either: it protects your machine, not the verdict. Through
  `--audit-harness` the scoring runs in pq-verify's own process, apart from
  the library, which then has to answer the questions; it still runs as your
  user and can change any file you can, the report included.
  `--audit-contained` is that path with a harness of pq-verify's own, for an
  ML-KEM library, and it narrows this: the library cannot open pq-verify's
  memory, a seccomp filter stops it writing to files, starting processes and
  reaching the network, and it is asked fresh questions as well as NIST's
  ([below](#the-contained-worker)). None of that helps against the point
  above, a library that computes correctly whenever it is audited. Where a
  hostile library is the threat, audit a build you made from source you
  reviewed, or use the prompt/response path, which runs none of the vendor's
  code ([SECURITY.md](SECURITY.md#what-pq-verify-does-on-purpose)).
- **Not a file swapped during the audit and put back.** pq-verify hashes the
  library before the audit and again, by the same path, after it; if the two
  differ, the result is `CANNOT VERIFY`. Someone who can write to the file
  while the audit runs could replace it after the first hash and restore it
  before the second, and the report would name the restored file. Where that
  matters, audit the library from a read-only mount, so nothing can change it
  during the run ([SECURITY.md](SECURITY.md#what-pq-verify-does-on-purpose)).
  `--audit-contained` does not have this gap for the library itself: it runs
  a sealed in-memory copy made from the same open file that was hashed, and
  says so if the file on disk changed meanwhile. A library the loader pulls
  in with it (a libcrypto) is still hashed by its path, after the load.
- **The code path this machine took.** A library that picks its code at run
  time (liboqs's distribution build chooses AVX2 or portable code from the
  CPU's features) is audited on the path the auditing CPU selects. Another
  CPU, compiler or set of flags is another binary: the submitters' HQC AVX2
  decoder gets every block's sign right at `-O3` and wrong at GCC 13's `-O2`
  ([AUDITS.md](AUDITS.md#hqc-decoder-audit--standard-not-final-with-mutants)).
- **Not which binary answered, on the prompt/response path.** An
  implementation with no loadable entry points (an HSM, a remote service) can
  answer pq-verify's questions instead. A passing fresh response proves that
  the responder computed the standard on inputs nobody had seen. It does not
  prove which code did it, so the report says `artifact: none`
  ([README](README.md#what-a-result-is-bound-to)). Through a Crucible-protocol
  harness the harness speaks for the library, which cannot be proved across a
  process boundary ([AUDITS.md](AUDITS.md#any-language-through-crucible-protocol-harnesses)).
  pq-verify's Bouncy Castle harness names the jar it loaded, with its sha256,
  but that is the harness's word, not something pq-verify checked.
- **Only the functions a library exports.** liboqs builds HQC's code-layer
  functions and Classic McEliece's backends with hidden visibility: its HQC
  shared library cannot be audited at all, and its McEliece only through the
  KEM API. BoringSSL does not export its NTT (nor ML-DSA's), so pq-verify
  checks it against BoringSSL's own in-tree NIST vectors instead.

## The contained worker

`--audit-contained` keeps a library away from its verdict
([SECURITY.md](SECURITY.md#what-pq-verify-does-on-purpose)). What it does not
do:

- **It does not stop the library reading files.** The worker can read
  whatever your user can, and that includes NIST's expected answers, which
  this package ships. On NIST's vectors, on the edge cases and on the
  accumulated vectors (all published, or derived from published seeds), a
  pass says the answers were right, not that the library computed them. Only
  the fresh questions have answers that exist nowhere until pq-verify computes
  them, and there are few of them: 40 by default, eight in each of five
  groups (`--fresh-count`).
- **A replayed seed asks nothing new.** `--fresh-seed` reproduces an earlier
  run. The seed is on the command line and in the earlier report, where the
  worker can read it.
- **The fresh answers come from pq-verify's reference.** They need kyber-py
  (`pip install "pq-verify[full]"`). Without it the fresh questions are not
  applicable, the report says so, and the scope is partial.
- **It is not a sandbox.** The filter is a list of system calls pq-verify
  knows to be dangerous. A call that is not on it is allowed, and nothing
  shows the list is complete. There is no limit on memory or CPU, and no
  namespace: run a binary you do not trust in a container or a VM.
- **A filter kill is a finding about the library, not a proof of malice.** A
  library that opens a log file for writing, or a socket to the kernel's
  crypto API, is stopped and reported like any other. Whether that behaviour
  belongs in your product is yours to judge; pq-verify reports that it
  happened, and cannot say which call it was.
- **ML-KEM only, x86-64 Linux only.** The worker serves the derandomised
  ML-KEM entry points `--audit-kem` binds. There is no contained path yet for
  ML-DSA, SLH-DSA or the other schemes, and none for `--constant-time`. The
  worker's source has the AArch64 system calls, but nothing has run it there,
  so pq-verify does not start it there: `CANNOT VERIFY`.
- **The library must load on its own.** The worker starts with an environment
  of its own (no `LD_LIBRARY_PATH`, no `LD_PRELOAD`) and loads the library
  from memory, so a dependency found only through `LD_LIBRARY_PATH`, or
  relative to the library's own directory (`$ORIGIN`), is not found:
  `CANNOT VERIFY`, with the loader's message.
- **Processes are attributed by where they hang.** While a contained audit
  runs, pq-verify adopts orphaned descendants, and at the end it stops every
  child it did not have before and did not start itself. A program that
  embeds pq-verify and starts children of its own on another thread during an
  audit would see them stopped. The command line starts none.
- **The worker is compiled where it runs.** A C compiler is needed at audit
  time, and the report names it and hashes the worker it built
  (`containment.worker`).

## Schemes

Covered: ML-KEM, ML-DSA and SLH-DSA (FIPS 203/204/205), LMS/HSS and
XMSS/XMSS^MT (SP 800-208), and the composition of RFC 10024 hybrid groups. On
tracks of their own, never part of a FIPS verdict: FN-DSA (FIPS 206 draft),
Classic McEliece (not a FIPS standard) and HQC's code layer (standard not
final).

**Not covered:** FrodoKEM, NTRU and NTRU Prime, BIKE, isogeny-based schemes
such as SQIsign, NIST's additional signature candidates (MAYO, UOV, CROSS,
HAWK and the rest), and the classical half of a hybrid beyond the checks
[HYBRID.md](HYBRID.md) lists. A parameter set pq-verify does not know is
refused on the command line (`unknown parameter set`, exit status 2). That
is "not covered", not `CANNOT VERIFY`: no report is written, and nothing
about the library is claimed.

## Within a covered scheme

- **FN-DSA (draft).** Verification is checked against pinned vectors and
  malformed inputs. A library's signatures are checked for validity under
  pq-verify's verifier, with no nonce reused, not byte for byte: signing is
  randomised. Framing (headers, padding, context strings) follows Falcon
  round 3 and may change in the final standard.
  - **Emulated floating point (`fpr_*`).** Where a library exports Falcon's
    emulation of binary64 (PQClean's clean build and the reference built with
    `FALCON_FPEMU` do), `fpr_scaled`, `fpr_add`, `fpr_mul`, `fpr_div` and
    `fpr_sqrt` are held to exact rounding to nearest, ties to even, and
    `fpr_expm_p63` to the reference's ApproxExp bit for bit, on about 19,000
    inputs from a seed recorded in the report. That is a test, not a proof: a
    defect confined to inputs that are not drawn passes. Not checked:
    - the sign of a zero result (either is accepted: Falcon's emulation does
      not promise IEEE's rule);
    - the primitives Falcon inlines (`fpr_of`, `fpr_rint`, `fpr_floor`,
      `fpr_trunc`, `fpr_sub`, `fpr_inv`, `fpr_lt` and the rest): they cannot
      be called on their own;
    - a build on the CPU's floating point (PQClean's AVX2 and AArch64
      Falcon, liboqs on a CPU with AVX2), or one that hides the symbols: the
      stages are not applicable, and say so;
    - inputs outside Falcon's own domain: subnormals, infinities, NaNs.
  - **The sampler, through its signatures.** 1,000 signatures under one
    of the library's keys are tested for centring, variance σ² and
    symmetry, each to 6 standard deviations. It is a statistical test of
    the first moments, not of the distribution:
    - a defect that keeps them passes: a base sampler with one row of its
      table zeroed, so that every value above 6 comes out one less (about
      one draw in 4,000), does (measured);
    - so does a smaller bias than 1,000 signatures resolve: a sign bit
      within about one point of 1/2, a σ within about half a percent;
    - so does one that shows only under other keys, after more signatures,
      or for particular messages;
    - a correct library fails it about twice in 10^8 audits of FN-DSA-512
      and once in 10^8 of FN-DSA-1024, mostly on the centring test, whose
      chi-square has a heavier tail than a normal one.
  - **Not checked at all:** the FFT, `ffSampling` as such, and timing.
- **Classic McEliece.** Encapsulation's error vectors are checked for
  weight, validity and repetition, not for their distribution. A pass says
  the library computes the scheme exactly, not that the scheme or a
  parameter set is secure ([README](README.md#not-a-fips-standard-classic-mceliece)).
- **HQC.** The code layer only: the Reed–Solomon and Reed–Muller encoders and
  decoders. Not the KEM around it (key generation, encryption, sampling,
  hashing), and not constant time. Its rm-symmetry stage certifies that the
  inner decoder commutes with the code's symmetries, not that it is right: it
  skips ties and cannot see a defect that is itself symmetric, which the
  exact rm-decode stage catches. The KEM's formats are not settled: HQC-1's
  secret key is 2,305 bytes in the 2023 submission PQClean carries, 2,321 in
  v5.0.0 (August 2025) and 32, a seed, on the unreleased next-release branch.
- **Sampled and budgeted checks.** Where a check is sampled (xmss-reference's
  signing) or over a hash budget (larger LMS and XMSS trees), what did not
  run is reported as not run, never as passed, and `scope.complete` is
  false. A `VERIFIED` with an incomplete scope means every check that ran
  passed.

## Side channels

pq-verify compares values. It measures nothing physical: no timing, power,
electromagnetic or microarchitectural behaviour
([README](README.md#side-channels-are-not-measured)).

`--constant-time` is the exception, and it covers:

| Audit | Checked under Valgrind memcheck | Not checked |
|---|---|---|
| `--audit-kem` (ML-KEM) | Encaps and Decaps: secret-dependent branches and memory addresses | key generation (the public matrix seed is derived from the secret seed) |
| `--audit-dsa` (ML-DSA) | key generation and signing, in a build with the library's own declassifications compiled in and pq-verify's shim in front of them; every declassification is judged by the site table for that implementation ([CONSTANT-TIME.md](CONSTANT-TIME.md)) | any other build, which is CANNOT VERIFY: Sign branches on secret-derived values by design. Today only mldsa-native's portable C backend has a site table |
| `--audit-mceliece` (Classic McEliece) | Encaps and Decaps, the same way | key generation (its retries are declassified by design); inside the error-vector sampler, reports are listed, not judged |

Not covered by it at all: SLH-DSA, LMS/HSS, XMSS, FN-DSA, HQC and the hybrid
groups. Within its scope memcheck cannot see instruction timing (KyberSlash's
secret division; the library's integer divisions are listed for a reviewer
instead, on x86, ARM and RISC-V), the values a computation produces (Berzati et al.'s
template attack on ML-DSA's signing-time values,
[CONSTANT-TIME.md](CONSTANT-TIME.md#5-scope)) or anything below the
instruction level. It sees only the memory accesses Valgrind translates:
every run commits each instruction's result, so a secret-indexed load whose
value is discarded is still seen, but prefetch instructions are not
translated, so a secret-indexed prefetch is not. It checks the one binary
and code path described above
([AUDITS.md](AUDITS.md#constant-time---constant-time)).

`--leakage` is not a measurement: it computes, from the NTT's structure,
which layers would expose the secret if observed, as an input to masking
design.

## Parameter security

`pqverify_params` is not a cryptanalysis.

- **ML-KEM's three sets** report the lattice-estimator's primal-uSVP result
  (Albrecht et al.), pinned in `pq_verify/core.py`: β = 406, 630 and 864,
  118.6, 183.9 and 252.3 core-SVP bits classical. Only primal uSVP: not
  dual, dual-hybrid, Arora–Ge, BKW or any later attack. The values are a
  snapshot, with no lattice-estimator commit recorded, and change only by a
  deliberate edit; a newer estimator or a new attack does not reach them.
- **Custom parameters** go through a simplified primal-uSVP and primal-hybrid
  formula, calibrated on Kyber-512 (β = 406) and a sparse-secret set
  (hw = 40, β = 328). Elsewhere it is close, not exact: on ML-KEM-768's and
  ML-KEM-1024's parameters it gives β = 624 and 874, against the
  lattice-estimator's 630 and 864.
- **MEETS / BELOW** compares core-SVP bits with fixed thresholds (118, 183,
  252). NIST defines its levels by comparison with key search on AES and
  collision search on SHA; core-SVP is a convention for approximating that,
  not the definition.
- No estimate exists for ML-DSA, SLH-DSA, the hash-based schemes, FN-DSA,
  Classic McEliece or HQC.

More generally, no hardness assumption is verified: Module-LWE and
Module-SIS, the security of SHA-2, SHA-3 and SHAKE, and the decoding problems
under Classic McEliece and HQC are taken as given. A pass means the library
computes the standard; whether the standard is secure is outside pq-verify.

## Verdicts

A result is one of `VERIFIED`, `FINDINGS PRESENT`, `CANNOT VERIFY` or (on the
prompt/response path) `INCOMPLETE`. There is no approximate class: no
"verified within ε" and no confidence level. Every conformance check is
exact on the inputs it ran, and says nothing about inputs it did not run;
the one approximate figure, the parameter estimate above, is not a verdict. Random and
accumulated vectors widen the inputs; they do not turn a test into a bound.

## Proofs and tests

Two files carry proofs that hold for every input, checked by Coq with
`pq-verify --proofs` (each theorem must be closed under the global context,
with no axiom and nothing admitted):

| File | Proves |
|---|---|
| `pq_verify/coq/NTT.v` | the FIPS 203 and FIPS 204 forward NTTs equal the Chinese-remainder map they are defined to compute |
| `pq_verify/coq/Reduce.v` | `montgomery_reduce` (ML-KEM and ML-DSA), `barrett_reduce` and `reduce32` are congruent to their input and within bound for every input in range, with no intermediate overflowing its C type |

These are proofs about the algorithms as written in Coq, not about any
vendor's compiled code. CI checks them with Coq 8.18.0, the version Ubuntu
24.04 packages, and fails if that version changes; no other version is tested,
and a newer Coq or Rocq may need changes to the proof scripts.

`--audit-source` proves something about a library's own C source, by CBMC,
in C's semantics as CBMC models them. For ML-KEM: that four of its
functions have no undefined behaviour on any input FIPS 203 allows them, and
that its NTT and NTT-domain multiplication never overflow an int16
coefficient. For ML-DSA: that six of its functions have no undefined
behaviour on any input FIPS 204 gives them, and that its NTTs and NTT-domain
multiplication never overflow an int32 coefficient. It tests the reductions,
the zeta tables and ML-DSA's rounding on every input, as compiled. It does
not prove that an NTT computes the standard's transform, it covers no other
function, and it does not check strict aliasing
([SOURCE-AUDIT.md](SOURCE-AUDIT.md)).

Everything else is tested, not proved: every other vendor audit; the inverse NTTs; pq-verify's own SLH-DSA, LMS/HSS, XMSS, FN-DSA,
Classic McEliece and HQC references; and all hashing, sampling, encoding and
the FO transform. Each tested reference is held to at least one independent
source (NIST's ACVP vectors, the submitters' KATs, their decoders' answers).
A pass is two implementations agreeing on those inputs. A defect shared by
pq-verify's reference and the source it is pinned to would not show.

## Outside the code

- **Not a certificate.** Results are evidence toward FIPS 140-3 / CMVP and
  CNSA 2.0 readiness. A CMVP certificate is issued by NIST and the Canadian
  Centre for Cyber Security, after an accredited laboratory has tested the
  module.
- **Randomness.** pq-verify supplies or controls the randomness it audits
  with. Beyond refusing repeats (a reused FN-DSA nonce or McEliece error
  vector is a finding), it does not assess a library's own random number
  generator or entropy source.
- **Memory safety and the surrounding code.** The ML-KEM, ML-DSA, SLH-DSA
  and HQC audits give every buffer they pass the library 64 guard bytes on
  each side and check them after every call; a write into them fails the
  `bounds` stage. A write that skips past the guard bytes or lands elsewhere,
  a read out of bounds and a use of freed memory are not caught: run the
  library under AddressSanitizer or Valgrind for those. None of this is
  fuzzing or a review of the rest of the implementation: a passing NTT audit
  says the transform is correct, not that the library is free of defects
  elsewhere.
- **The self-suite.** Of its 160 checks, 54 verify post-quantum cryptography
  directly. The rest check the harness, or are classical and research
  engines, and are never counted as post-quantum evidence
  ([ARCHITECTURE.md](ARCHITECTURE.md#engines-and-where-they-are-heading)).
  The research track's DQBF stage decides XOR matrices, and matrices with
  clauses whose expansion has at most 2¹⁸ variables and clauses; a larger
  one is CANNOT VERIFY unless its XOR constraints alone refute it
  ([DQBF.md](docs/DQBF.md)). Its curve checks count points with certificates
  ([ECC.md](docs/ECC.md)): a general curve (j ≠ 0, 1728) from 2⁶⁴ to 2³²⁰ is
  counted by Schoof–Elkies–Atkin ([SEA.md](docs/SEA.md)), in minutes near the top
  of that range, and above 2³²⁰ it is CANNOT VERIFY unless its order is
  published.
