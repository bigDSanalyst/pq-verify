# FN-DSA, Classic McEliece and HQC

Three schemes outside FIPS 203, 204 and 205, each checked as far as its
specification allows and no further: FN-DSA (`--audit-fndsa`, the FIPS 206
draft), Classic McEliece (`--audit-mceliece`, not a FIPS standard) and HQC's
error-correcting code (`--audit-hqc`, its standard not final). What every
check cannot see is in [LIMITS.md](../LIMITS.md); the pinned results, with
the commands that reproduce them, are in [AUDITS.md](../AUDITS.md). The rest
of pq-verify is described in the [README](../README.md).

---

## Draft track: FN-DSA (FIPS 206)

`pq-verify --fndsa` checks FN-DSA (Falcon) **verification** ahead of the final
FIPS 206. It is a separate task with its own report (`track: "draft"`,
`standard: "FIPS 206 (draft)"`): it is not one of the 160 self-suite checks,
not one of the 1566 ACVP vectors, and never part of a FIPS 203/204/205 verdict.

| Check | What |
|---|---|
| Vectors | Falcon-512 and Falcon-1024 outputs of PQClean's reference code (NIST KAT harness + PQClean's deterministic generator), each pinned to the sha256 PQClean publishes for it in the scheme's metadata; 30 signatures, NIST-API signed messages and detached |
| Rejections | for every detached signature, the inputs a verifier must refuse — altered message or nonce, a changed `s2` coefficient, the wrong header, `-0`, nonzero padding bits, trailing bytes, a public-key coefficient ≥ q — each required to fail **for the right reason** (an encoding error from the decoder, not a lucky norm check) |
| Arithmetic | the NTT mod q = 12289 for n = 512 and 1024 against the negacyclic definition, and every butterfly of every layer through the native Z_q engine, unchanged |

`pq-verify --audit-fndsa lib.so FN-DSA-512` audits a vendor's FN-DSA library
the same way, through its own entry points (the NIST API as PQClean exports
it, or liboqs's `OQS_SIG_falcon_*`): the pinned signatures verify, every
malformed input is refused, its keys are canonical and match their secret
keys, every secret key solves the NTRU equation `f·G − g·F = q` and meets
both Gram–Schmidt bounds (checked in exact integer and rational arithmetic),
and its signatures verify under pq-verify's verifier with no nonce reused.

Where the library exports Falcon's emulated floating point, as clean builds
do, each `fpr_*` function is also held to an exact reference. Rounding must be
to nearest, ties to even, and ApproxExp must match the reference bit for bit.
That arithmetic is what signing is built on, and a subtle mistake in it need
not show in Falcon's known-answer tests. A tie rounded away from zero,
truncation, or one ApproxExp coefficient off by one each leave PQClean's NIST
KAT output byte for byte the same.

Its sampler is checked by its output: 1,000 signatures under one of the
library's keys must be centred on 0, symmetric, of variance σ² over all
their coefficients, of the right covariance shape at every point of the
FFT, and distributed as the discrete Gaussian. A sampler whose sign bit
leans 53:47, whose σ is 2% low, or whose sampling tree conditions on a
coefficient 0.5% too large, still signs validly; on every key tried, each
failed this by more than 21 standard deviations. A signer that redraws
whenever a coefficient of s2 passes 3.6σ also signs validly, its variance
within the scale test's limit; the distribution test fails it by more than
7 standard deviations.

With `--constant-time`, signing also runs under Valgrind memcheck, with the
secret key and the signer's randomness marked secret. Falcon's signer
branches on secret-derived values by design, at a few known places: the
sampler's rejection, the norm bound, the encoder and the key's validity
checks. Each branch memcheck reports is matched by its function and source
line against those, read from the library's debug information, and any other
branch, or any secret memory address, fails. Allowing whole functions would
not do: GCC 13 inlines `fpr_floor` into the sampler and compiles its
branch-free select into a jump on the sampler's centre.

PQClean's Falcon passes every stage but that one, which it fails on that
jump at both sizes; liboqs's own Valgrind suppressions list the same line,
as not yet analysed. liboqs's AVX2 Falcon, which computes on the CPU's
floating point, passes it. Sixteen planted bugs in PQClean's source each fail
the audit in CI. The three arithmetic ones fail only the arithmetic stages,
the four sampler ones only the statistics, and a branch planted in the
emulated floating point's normalisation only constant time
([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md#fn-dsa-falcon-library-audit--draft-track-with-mutants)).

What is checked is Falcon round 3, the scheme FIPS 206 standardises.
Verification is integer arithmetic that the final standard is not expected to
change; framing (headers, padding, how a context string is bound) may change,
and lives in one section of `pq_verify/fndsa.py`. Of signing, the emulated
arithmetic is checked, and the sampler through the statistics of its
signatures. The FFT's results are not (its branches and addresses are,
with `--constant-time`), nor a sampler defect its signatures average away
([LIMITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/LIMITS.md#within-a-covered-scheme)).

---

## Not a FIPS standard: Classic McEliece

Classic McEliece was a NIST round-4 candidate that NIST did not select (it
chose HQC); it is on an ISO track (ISO/IEC 18033-2). pq-verify checks it on a
track of its own (`track: "classic-mceliece"`), never part of a FIPS verdict.

`pq-verify --mceliece` holds pq-verify's own implementation to the official
KATs for all ten parameter sets. The public keys (0.26–1.36 MB) are not
pinned: each is regenerated from the private key's seed, and the rebuilt KAT
must hash to the `nistkat-sha256` PQClean publishes for it.

`pq-verify --audit-mceliece lib.so mceliece348864` audits a library through
its own entry points (the NIST API, or liboqs's `OQS_KEM_classic_mceliece_*`):

| Stage | What |
|---|---|
| keyGen | each key regenerated from the seed its private key begins with: public key, pivots, Goppa polynomial and rejection string byte-exact, control bits encoding the regenerated permutation. No control over the library's randomness is needed |
| encaps | its ciphertexts decode under pq-verify's decoder to weight exactly t, the key is SHAKE256(1 ‖ e ‖ C), its own Decap agrees, no error vector repeats |
| decaps | ciphertexts built against its own key — weight t at random positions, in the identity part, in the T part and through the support's zero element; weight t−1 (decodable, must be rejected, also through the zero element), t+1, C = 0, random C, another key's ciphertext — each decapsulated to the exact key pq-verify computes |
| padding | mceliece6960119 only, where mt and k end mid-byte: a ciphertext or public key with a padding bit set is refused, as the submitters' reference does |
| ct:encaps, ct:decaps | with `--constant-time`: Decaps with the whole private key secret and Encaps with its randomness secret, under Valgrind memcheck; a secret-dependent branch or memory address fails, except inside the error-vector sampler, whose declassified rejection checks are listed instead ([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md#constant-time---constant-time)) |

PQClean's reference passes all ten sets; eight planted bugs each fail the
audit in CI ([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md)). Encapsulation's error-vector sampling
is checked for validity and repetition, not distribution.

A pass means the library computes Classic McEliece exactly. It says nothing
about the scheme's security: its cryptanalysis is active (key-recovery cost
estimates were published in 2025–2026 and disputed by the submitters), so
whether to deploy it, and with which parameter set, follows current agency
guidance such as BSI's TR-02102-1.

## Standard not final: HQC's error-correcting code

HQC was selected by NIST in March 2025; its standard is not final. pq-verify
checks its code layer on a track of its own (`track: "hqc"`), never part of a
FIPS verdict: the Reed–Solomon code over GF(2⁸) concatenated with a duplicated
Reed–Muller RM(1,7) that decryption decodes. Not the KEM around it.

The decoder is audited on its own because nothing else reaches it. Honest
decryptions rarely put more than two errors in front of the outer decoder, and
decapsulation re-encrypts, so no ciphertext, honest or built, can drive the
decoder into a corner and show its answer. A decoder bug that only bites on
rare error patterns passes every KAT and every round trip.

`pq-verify --hqc` holds pq-verify's reference to the submitters' published
generator polynomials and to their own decoders' answers on its built vectors,
for HQC v5.0.0 (whose code layer is the 2023 submission's) and the unreleased
next-release branch (a different field polynomial and bit order).

`pq-verify --audit-hqc lib.so HQC-1` calls a library's encoder and decoder
functions directly (`reed_solomon_*`, `reed_muller_*`, `code_*`; `--hqc-profile
next` for the next-release code):

| Stage | What |
|---|---|
| encode | Reed–Solomon, Reed–Muller and concatenated encoders, byte for byte |
| rm-decode | every codeword; noise up to the radius; blocks between two codewords at every distance up to the radius; ties broken to the lowest index, as the submitters' code does (equidistant blocks, and the GF(2⁷) inversion word, tied 14 ways); one exact copy outvoting noisy ones; random blocks. Each answer exact |
| rm-symmetry | the same blocks, each moved by eight random symmetries of the code (an affine map of the position bits, a codeword added, the copies permuted): each image must decode to the image of the block's own answer. No reference decoder; ties skipped |
| rs-decode | random errors up to the radius δ, all in the parity or all in the message part, and patterns whose leading Hankel minors vanish: the Berlekamp–Massey branch random patterns rarely reach |
| code-decode | whole received words within both radii → the message |
| bounds | no call writes outside its output buffer |

Built vectors, not random ones: four planted Berlekamp–Massey bugs fail on
5–9% of random full-weight error patterns and essentially never on honest
decryptions; the Hankel-built patterns trigger three of them every time.
The blocks between two codewords found a defect in the submitters' AVX2
decoder that 40 800 random and noisy blocks did not trigger once
([AUDITS.md](https://github.com/bigDSanalyst/pq-verify/blob/main/AUDITS.md)). rm-symmetry finds it again with no reference
decoder at all: a maximum-likelihood decoder commutes with every symmetry of
its code, and that one's answer follows how the codewords are numbered. It
certifies symmetry, not correctness: a defect that is itself symmetric (every
answer the complementary codeword) passes it, and rm-decode catches that. liboqs builds these functions with hidden
visibility, so its shared library cannot be audited this way: build its HQC
sources with default visibility. Not a side-channel review.
