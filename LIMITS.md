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
- **Only the functions a library exports.** liboqs builds HQC's code-layer
  functions and Classic McEliece's backends with hidden visibility: its HQC
  shared library cannot be audited at all, and its McEliece only through the
  KEM API. BoringSSL does not export its NTT (nor ML-DSA's), so pq-verify
  checks it against BoringSSL's own in-tree NIST vectors instead.

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
  randomised. The Gaussian sampler's distribution and the floating-point
  FFT's precision are not checked. Framing (headers, padding, context
  strings) follows Falcon round 3 and may change in the final standard.
- **Classic McEliece.** Encapsulation's error vectors are checked for
  weight, validity and repetition, not for their distribution. A pass says
  the library computes the scheme exactly, not that the scheme or a
  parameter set is secure ([README](README.md#not-a-fips-standard-classic-mceliece)).
- **HQC.** The code layer only: the Reed–Solomon and Reed–Muller encoders and
  decoders. Not the KEM around it (key generation, encryption, sampling,
  hashing), and not constant time.
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
| `--audit-mceliece` (Classic McEliece) | Encaps and Decaps, the same way | key generation (its retries are declassified by design); inside the error-vector sampler, reports are listed, not judged |

Not covered by it at all: ML-DSA, SLH-DSA, LMS/HSS, XMSS, FN-DSA, HQC and the
hybrid groups. Within its scope memcheck cannot see instruction timing
(KyberSlash's secret division; the library's division instructions are listed
for a reviewer instead) or anything below the instruction level, and it
checks the one binary and code path described above
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
vendor's compiled code. Everything else is tested, not proved: every vendor
audit; the inverse NTTs; pq-verify's own SLH-DSA, LMS/HSS, XMSS, FN-DSA,
Classic McEliece and HQC references; and all hashing, sampling, encoding and
the FO transform. Each tested reference is held to at least one independent
source (NIST's ACVP vectors, the submitters' KATs, their decoders' answers).
A pass is two implementations agreeing on those inputs. A defect shared by
pq-verify's reference and the source it is pinned to would not show.

## Outside the code

- **Not a certificate.** Results are evidence toward FIPS 140-3 / CMVP and
  CNSA 2.0 readiness. Only an accredited laboratory issues a certificate.
- **Randomness.** pq-verify supplies or controls the randomness it audits
  with. Beyond refusing repeats (a reused FN-DSA nonce or McEliece error
  vector is a finding), it does not assess a library's own random number
  generator or entropy source.
- **Memory safety and the surrounding code.** Output-buffer bounds are
  checked where an audit says so (HQC's `bounds` stage, for one). That is not fuzzing
  or a review of the rest of the implementation: a passing NTT audit says the
  transform is correct, not that the library is free of defects elsewhere.
- **The self-suite.** Of its 160 checks, 54 verify post-quantum cryptography
  directly. The rest check the harness, or are classical and research
  engines, and are never counted as post-quantum evidence
  ([ARCHITECTURE.md](ARCHITECTURE.md#engines-and-where-they-are-heading)).
