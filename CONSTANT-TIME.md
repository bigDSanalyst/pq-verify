# Constant-time audit for ML-DSA: the specification

**2.13.0 extends the constant-time audit to ML-DSA.** It does not measure
timing, power or electromagnetic behaviour. It checks that the compiled code
does not branch, or index memory, on secret data except at points the
implementation has declared public. It requires those declarations to be
compiled in. A build that has none is reported as CANNOT VERIFY for key
generation and Sign, never as a pass. What it cannot see, instruction timing and intermediate
values, is what a laboratory measures; the boundary is the point.

This document is the specification the check implements. The proof of
concept runs against mldsa-native and is tested against this text. Where the
two disagree, this text changes and the revision is recorded at the end.

Status: specified, and implemented for mldsa-native (`pq_verify/ct_dsa.py`).
The proof of concept agreed with this text after the five revisions recorded
below. PQClean's ML-DSA declares nothing public at its pinned commit, so it
is CANNOT VERIFY, like every other pinned ML-DSA build; judging it would need
annotations added to its source first. The Classic McEliece port is
specified in section 6 and not yet built.

- [1. The architectural constraint](#1-the-architectural-constraint)
- [2. The hook protocol](#2-the-hook-protocol)
- [3. The policy](#3-the-policy)
- [4. The negative controls](#4-the-negative-controls)
- [5. Scope](#5-scope)
- [6. The Classic McEliece extension](#6-the-classic-mceliece-extension)
- [7. What pq-verify cannot do here](#7-what-pq-verify-cannot-do-here)
- [Proof of concept](#proof-of-concept)
- [Revisions](#revisions)

---

## 1. The architectural constraint

`pq_verify/ct_audit.py` checks constant time the way mlkem-native and
BoringSSL check themselves (ctgrind): secret inputs are marked *undefined*
with Valgrind memcheck's client requests, the library runs, and memcheck
reports every conditional branch (`UninitCondition`) and every memory
address (`UninitValue`) that depends on them. pq-verify does this from
outside: a small driver loads the vendor's compiled library with `dlopen`,
marks the secrets, calls the exported entry points, and marks the outputs
public only after the call returns.

For ML-KEM's Encaps and Decaps that is enough: nothing inside them may
depend on a secret, so any report is a leak. ML-DSA's Sign is different.
Its rejection loop decides, by design, from secret-derived values whether
to discard an attempt, and each attempt makes a challenge hash, `c̃`, that
is public before the attempt is accepted or rejected. A correct
implementation therefore branches on secret-derived data, at points where
the specification says the value may be public. An outside driver cannot
mark a value public at a point inside the library: memcheck reports the
first rejection branch long before Sign returns, and nothing the driver
does after the return changes that. Key generation has the same shape: the
public seed `ρ` is derived from the secret seed, and the secret vectors are
rejection-sampled.

So the check needs the implementation's own declarations of what is public,
compiled in at the points where those values are computed:

- **Hooked builds**: the library is compiled with its declassification
  annotations enabled and pq-verify's shim in front of them (section 2).
  memcheck then sees every secret-dependent branch and address inside the
  library, and the shim records every declassification, which the policy
  (section 3) judges.
- **Unhooked builds**: a library without annotations, or one compiled without
  the shim, gets **CANNOT VERIFY** for Sign and for key generation, with the
  reason. Never a pass. So does a library that carries the shim but declares
  nothing public, which means its annotations were not compiled in.

## 2. The hook protocol

Implementations annotate secrets in one of two ways, and pq-verify supplies
a shim for each. Both are header files placed first on the include path, so
neither needs a patch to the implementation's source.

| Annotation | Used by | pq-verify's shim |
|---|---|---|
| Valgrind client requests, `VALGRIND_MAKE_MEM_UNDEFINED` / `VALGRIND_MAKE_MEM_DEFINED` | mldsa-native (`MLD_CT_TESTING_SECRET` / `MLD_CT_TESTING_DECLASSIFY`, enabled by `MLD_CONFIG_CT_TESTING_ENABLED`), mlkem-native | `pq_verify/harness/ct/valgrind/memcheck.h`: includes the real header with `#include_next`, then redefines the two requests |
| `crypto_declassify(x, len)`, an empty macro in PQClean's `common/crypto_declassify.h` | PQClean's Classic McEliece | `pq_verify/harness/ct/crypto_declassify.h`, found before PQClean's own |

Both redefinitions call `pqv_ct_mark()` in `pq_verify/harness/ct/pqv_ct_shim.c`,
which is compiled into the library. Because the macros expand where the
annotation is written, the call carries the annotation's site: the function
(`__func__`), file and line, and the exact expression annotated. Expression
and function together name a site; file and line are kept for the reader.
`pqv_ct_mark()` first makes the real client request, so memcheck behaves
exactly as in the implementation's own constant-time tests. It then appends
one line to the log named by `PQV_CT_LOG`:

```
S <function> <file>:<line> <expression> <length>             a secret mark
D <function> <file>:<line> <expression> <length> <hex bytes>  a declassification
N <text>                                                     a note from the driver
```

A declassification's bytes are logged after they are marked defined, so the
logging cannot itself trip memcheck. A secret mark logs no bytes. Outside
Valgrind the client requests are no-ops and the log is still written, so the
policy can judge runs that memcheck does not slow down. A library that
exports `pqv_ct_mark` is a hooked build; any other gets CANNOT VERIFY.

mldsa-native is built for the check with its usual flags plus three, and the
shim's C file:

```
cc -O2 -g -fPIC -shared -DMLD_CONFIG_PARAMETER_SET=44 \
   -DMLD_CONFIG_CT_TESTING_ENABLED -I pq_verify/harness/ct -I mldsa \
   mldsa/mldsa_native.c pq_verify/harness/ct/pqv_ct_shim.c \
   pq_verify/harness/pqv_randombytes.c
```

`-g` changes no generated code; it lets memcheck name the inlined function a
report comes from (`mld_poly_chknorm_c`, not the exported function it was
inlined into).

**The driver** calls the internal API, `<prefix>_keypair_internal(pk, sk, seed)`
and `<prefix>_signature_internal(sig, m, mlen, pre, prelen, rnd, sk, 0)`,
whose explicit `rnd` makes every run reproducible. For key generation it
marks the 32-byte seed secret. For signing it marks `K` (`sk[32:64]`), the
packed `s1 ‖ s2 ‖ t0` (`sk[128:]`) and `rnd` secret, and leaves `ρ`
(`sk[0:32]`) and `tr` (`sk[64:128]`) public, as FIPS 204 defines them.
Outputs are marked public only after the call returns, and are written out
for the policy to compare.

**memcheck** runs with `--track-origins=yes
--vex-iropt-register-updates=allregs-at-each-insn`. The second matters: by
default Valgrind's translator deletes a load whose value is never used
before memcheck instruments it, so a secret-indexed read that the processor
still performs, and that still leaks through the cache, goes unreported
(section 5). With every instruction's result committed to the guest state,
no load can be deleted. ML-KEM's and Classic McEliece's constant-time runs
take the same options. Before anything is trusted, a self-test in the driver
must be reported twice: a branch on a marked secret, and a read indexed by
one whose register the next instruction overwrites, the pattern only this
setting keeps. If either is missed the result is CANNOT VERIFY.

Three runs keep every report attributable to one operation:

1. **Key generation, under memcheck**, from a secret seed.
2. **A search, outside Valgrind.** Messages are signed in batches of 128,
   with the key from an unmarked seed, until the run has a message accepted
   at its first attempt, two with rejections and one with a hint-weight
   rejection, or 2,048 messages. The policy judges every one of these calls.
3. **Signing, under memcheck**: the key marked secret, replaying the chosen
   messages (the first accepted at its first attempt, the two with the most
   attempts, the first with a hint-weight rejection).

## 3. The policy

**Values, not functions.** A declassification is allowed only at a known
site, with its expected length, at its expected point in the attempt, and
with its value checked against the public outputs wherever they determine
it. Any secret-dependent branch or address that memcheck reports is a
finding, wherever it is. There is no function-level exemption: exempting,
say, the norm check wholesale would hide the bug class it exists to catch
(a coefficient's sign taken with a branch, section 4).

The site table belongs to one implementation at one pinned commit; for the
proof of concept that is mldsa-native at `159509d`, portable C backend. Each
entry is the source's own declaration, with the source's justification.

**Key generation**

| Site (function, expression) | Length | Rule |
|---|---|---|
| `*_keypair_internal`, `(rho)` | 32 | once, first. Equals the returned public key's first 32 bytes |
| `mld_rej_eta_c`, `(&t_valid)` | 4 | 0 or 1, after `ρ`: a rejection-sampling outcome for `s1`, `s2`. At least 256·(k+ℓ) acceptances, one per coefficient. The four-way sampler draws polynomials in fours, so for ML-DSA-65 and -87 it also samples one polynomial it discards, with its outcomes declassified the same way; a polynomial's last byte can add one unused acceptance. So at most 257 per polynomial drawn |
| `*_keypair_internal`, `(pk)` | public key | once, last. Equals the returned public key |

**Signing**, where an attempt is everything from one `c̃` to the next:

| Site (function, expression) | Length | Rule |
|---|---|---|
| `*_signature_internal`, `(rho)` | 32 | once, before the first attempt. Equals `sk[0:32]`, the public part of the key |
| `mld_attempt_signature_generation`, `(challenge_bytes)` | λ/4 | opens an attempt. Public on every attempt: `H` is modelled as a random oracle (the source cites the Dilithium Round 3 specification, §5.5). On the accepting attempt it equals the signature's first λ/4 bytes |
| `mld_compute_pack_z`, `(&z_invalid)` | 4 | 0 or `0xFFFFFFFF`; one per polynomial of `z`, at most ℓ; a nonzero value ends the attempt |
| `mld_attempt_signature_generation`, `(&w0_invalid)`, `(&h_invalid)` | 4 | the same, at most `k` each, alternating per polynomial (`w0` first), and only after all ℓ `z` checks passed |
| `mld_attempt_signature_generation`, `(w0)` | `k`·1024 (`k` polynomials of 256 32-bit coefficients) | only after all ℓ + 2`k` checks of the attempt passed. On the accepting attempt it equals `Az − c·t1·2^d − 2γ2·w1 (mod q)`, its public value, which the policy recomputes from the public key and the signature (FIPS 204 arithmetic in `ct_dsa.py`) |
| `mld_attempt_signature_generation`, `(w1_packed)` | `k`·192 bytes (ML-DSA-44) or `k`·128 | the same position. `H(μ ‖ w1_packed)` equals the attempt's `c̃`, with `μ = H(tr ‖ M′)`. The source's argument for both: they are computable from the signature and public key, given that `t0` "need not be regarded as secret" (FIPS 204 §6.1, as the source cites it) |
| `mld_attempt_signature_generation`, `(sig)` | signature | once per call, in the last attempt, after its `w0` and `w1_packed`. Equals the returned signature |

**Order.** Each attempt runs `c̃`, then the `z` checks, then the `w0` and `h`
checks, then `w0` and `w1_packed`, then `sig`. After a nonzero flag the
attempt has no further declassifications, and no flag follows `w0`,
`w1_packed` or `sig`. Every attempt but the last must end at a nonzero flag
or after `w0` and `w1_packed`. The second case is a rejection by the
hint-weight check, the one place the source publishes values of a discarded
candidate. The table allows it on the source's stated argument. Nothing
public determines that candidate's `w0`, so only its length and position are
checked there; its `w1_packed` is still checked against `c̃`. A
declassification at any other site, out of order, of the wrong length or
with the wrong value is a finding.

**Coverage.** The memcheck run includes at least one call that rejects at
least once, and one that is accepted on its first attempt, or the stage
fails. Inputs are chosen by the search run (section 2), where the
annotations are no-ops and behaviour is identical, and are then replayed
under memcheck. The report states whether a hint-weight rejection was
exercised; with the pinned seeds every parameter set exercises one.

**Change.** The table is applied to any build of the implementation, not only
the pinned commit. A later commit that adds a declassification, changes one's
expression or length, moves one to another function, or changes its place in
the attempt fails until the table is reviewed. Moving one to another line in
the same place does not: a site is its function and expression. If FIPS 204 or FIPS 206 changes what may be
treated as public, for example `t0`'s status under §6.1, this table is what
changes.

**Not covered by this table**: mldsa-native's native backends (x86-64 and
AArch64) declassify at further sites, the rejection samplers' buffers in
`native/*/meta.h` and the norm check's fallback flag in `poly.c`, and a
build with them fails as undocumented until the table covers them. The
`mld_sign_verify_internal` and `mld_sign_pk_from_sk` sites are not
exercised: Verify has no secret inputs, and the driver does not call
`pk_from_sk`.

## 4. The negative controls

Each control is a planted change to mldsa-native. The check must give the
result in the third column, for the reason in the fourth.

| # | Planted change | Expected | Why |
|---|---|---|---|
| 0 | none (the pinned build) | clean | no report, every declassification allowed |
| 1 | `mld_poly_chknorm_c` takes `abs` with a branch on the coefficient's sign | **fail**: branch on a secret | the specification lets an implementation leak *that* a bound was exceeded, never a coefficient's sign; nothing was declassified at that branch |
| 2 | `z` declassified in `mld_compute_pack_z` before its norm check | **fail**: undocumented site | the site is not in the table. memcheck is silent: the premature declassification is what blinds it, so only the log can catch this |
| 3 | the signature declassified with `w0` and `w1_packed`, before `c̃` and `h` are packed and before the hint-weight check (a known site, at the wrong point), on a message accepted at its first attempt | **fail**: value, and only value | the position is the one the table allows, so only the comparison sees it: the bytes declassified are not the returned signature |
| 4 | the same build, on a message whose signing includes a hint-weight rejection | **fail**: position | the signature is declassified in an attempt that was rejected. Any other rejection ends its attempt before this point, so it takes a hint-weight rejection to expose it |
| 5 | a table read indexed by a secret coefficient inside `mld_poly_chknorm_c`, its value discarded | **fail**: secret used as an address | memcheck `UninitValue`, with every instruction's result committed (section 2) |
| 6 | `mld_decompose` divides with a hardware division instruction (same results) | **memcheck silent**, division listed | memcheck does not see instruction timing; the division list is the separate reviewer's artefact, as for KyberSlash in ML-KEM |
| — | the driver's self-test: a branch on a marked secret, and a read indexed by one whose register is overwritten at once | both must be reported | otherwise the run is CANNOT VERIFY |

Verify is not a control: its inputs are public, so memcheck has nothing to
track there.

## 5. Scope

memcheck sees secret-dependent branches and memory addresses. It does not
see instruction timing: a hardware division on a secret, the KyberSlash
class, is invisible to it, which is why the report lists division
instructions separately. It sees addresses only of the memory accesses
Valgrind translates. By default the translator deletes a load whose value is
never used, which control 5 showed: a secret-indexed read that the processor
still performs, and that still moves cache lines, went unreported. Every
constant-time run in pq-verify now commits each instruction's result, which
keeps such loads, and the self-test refuses any run that does not.
Prefetch instructions are not translated as memory accesses at all, so a
secret-indexed prefetch stays invisible under any setting. memcheck does not
see the values a computation produces either. Berzati, Calle Viera, Chartouny, Madec, Vergnaud and Vigilant
(*Exploiting Intermediate Value Leakage in Dilithium: A Template-Based
Approach*, TCHES 2023(4), 188–210,
[doi:10.46586/tches.v2023.i4.188-210](https://doi.org/10.46586/tches.v2023.i4.188-210))
profiled the reference implementation on an ARM Cortex-M4, predicted from
its power traces whether coefficients of a vector computed during signing
were zero, and recovered enough of the key for universal forgeries. The
leak is in the values the code computes, which no branch-and-address check
sees. That is measured on the deployment hardware, under ISO/IEC 17825 and
leakage-assessment methods such as TVLA (Goodwill, Jun, Jaffe and Rohatgi,
*A Testing Methodology for Side-Channel Resistance Validation*, NIST
Non-Invasive Attack Testing Workshop, 2011). It is where pq-verify's verdict
ends and a laboratory's begins. [LIMITS.md](LIMITS.md#side-channels) says
the same.

The check covers one binary, one compiler and one code path: the portable C
backend, built as above, on the messages the run chose.

## 6. The Classic McEliece extension

The current Classic McEliece check excuses every report inside the function
that drew the error vector's random bytes, because the sampler's
rejection checks branch by design. Its docstring admits the cost: a real
leak in the sampler's construction of the error vector lands in the same
excused list. That is the function-level exemption section 3 rules out.

PQClean's Classic McEliece already declares the sampler's public values.
`encrypt.c` passes each comparison mask through `crypto_declassify`
(`uint16_is_smaller_declassify`, `uint32_is_equal_declassify`), and
`pk_gen.c`, `sk_gen.c` and `controlbits.c` do the same in key generation.
In PQClean the macro is empty. pq-verify's `crypto_declassify.h`, found first
on the include path, routes it to the same shim. The McEliece policy then
has the same shape as ML-DSA's: known sites; masks of 2 or 4 bytes that are
all zeros or all ones; and every memcheck report is a finding, the sampler's
included. liboqs's copies (`src/kem/classic_mceliece/pqclean_*`) take the
same header. Until this is built, the current exemption stays, and the
report keeps saying what it excuses.

## 7. What pq-verify cannot do here

It does not measure physical leakage, does not see instruction timing, and
does not see intermediate values. Those are the subjects of ISO/IEC 17825
and of leakage-assessment methods such as TVLA, and they need the deployment
hardware, not the source. A clean constant-time report says the compiled
code does not branch or index memory on secret data except where the
implementation declared a value public, and that each declaration matched
the policy. It says nothing more.

---

## Proof of concept

mldsa-native at `159509d`, built as in section 2 for ML-DSA-44, -65 and -87
(GCC 13.3.0, x86-64, Valgrind 3.22.0), checked by `pq_verify/ct_dsa.py`.

**The pinned builds.** All three are clean: no memcheck report, no policy
finding, about 4–6 seconds each.

| Set | Search (outside Valgrind) | Under memcheck | Messages replayed |
|---|---|---|---|
| ML-DSA-44 | 128 calls, 515 attempts | 4 calls, 44 attempts | accepted at its first attempt; 8 attempts with a hint-weight rejection; 18; 17 |
| ML-DSA-65 | 896 calls, 4,440 attempts | 4 calls, 65 attempts | accepted at its first attempt; 33; 29; 2 attempts with a hint-weight rejection |
| ML-DSA-87 | 128 calls, 448 attempts | 3 calls, 32 attempts | accepted at its first attempt; 16 attempts with a hint-weight rejection; 15 |

Over 1,024 messages per set the mean number of attempts was 4.44, 5.02 and
3.87, against FIPS 204's expected 4.25, 5.1 and 3.85, and hint-weight
rejections occurred in 15, 1 and 9 calls. ML-DSA-65's is rare enough that
the search runs to message 862 to find one, which is why the search
continues until it has. On every accepting attempt, every declassified value
was compared with the public key and signature and matched, `w0` included.
The library has no division instructions.

**The controls** (section 4), on ML-DSA-65:

| # | Result |
|---|---|
| 0 | clean |
| 1 | fails: branch on a secret in `mld_poly_chknorm_c` (3 reports) |
| 2 | fails: `mld_compute_pack_z (z)` at `sign.c:601`, an undocumented site, in all 896 searched calls and all 4 replayed; memcheck silent |
| 3 | fails on the message accepted at its first attempt with exactly one finding: the signature declassified is not the one returned |
| 4 | fails on the message with the hint-weight rejection: the signature declassified in an attempt that was rejected. Among the 896 searched calls, only that one shows it |
| 5 | fails: secret used as a memory address in `mld_poly_chknorm_c` (3 reports). With Valgrind's default translation it passed (revision 2) |
| 6 | memcheck silent; division instructions listed in `poly_decompose` and `poly_use_hint`. Its key and its signatures of 1,024 messages are byte-identical to the pinned build's |
| — | self-test: both reported. With the default translation, or with precise state only at memory accesses, only the branch is, and the run is refused |

`tools/vendor_audits.json` records the pinned builds' results and the
controls as mutants, and CI re-runs them.

## Revisions

The proof of concept disagreed with the first version of this text in five
places. Each was settled by changing the text and the check together:

1. **Controls 3 and 4.** The first version declassified the signature early
   and expected the value rule to catch it on an accepted message and the
   position rule on a rejecting one. Placed anywhere before `w0`, both rules
   fire on every message, so neither control showed what the other could
   not. Control 3 now moves the signature's declassification to just before
   the hint-weight check: the value rule alone catches it on a message
   accepted at its first attempt. The position rule catches it only after a
   hint-weight rejection, so control 4 now names that message, and the
   search makes sure the run has one.
2. **memcheck missed control 5.** With Valgrind's default translation a
   secret-indexed load whose value is unused is deleted before memcheck
   instruments it: the planted table read, which the processor still
   performs, passed. Three settings were tried. `--vex-iropt-level=0` keeps
   the load but costs memcheck precision: it reported 7,527 false branches
   in liboqs's mlkem-native C backend, in a key generation with no secret
   input. `--vex-iropt-register-updates=allregs-at-mem-access` keeps a load
   only while its register survives to the next memory access, which the
   self-test's read did and control 5's did not. `allregs-at-each-insn`
   keeps every load, catches control 5, and reports nothing on the pinned
   clean builds, for about a tenth more time. All memcheck runs, ML-KEM's
   and Classic McEliece's included, now use it: every recorded ML-KEM and
   Classic McEliece row and leak mutant reproduced unchanged. The self-test
   plants the pattern only it keeps, so a run without it is refused.
3. **Key generation's sampling count.** The first rule allowed at most one
   unused acceptance per secret polynomial. mldsa-native's four-way sampler
   draws one more polynomial than ML-DSA-65 and -87 need, and discards it.
   The rule now counts the polynomials drawn.
4. **`w0` is compared.** The first version left `w0`'s bytes unchecked. On
   the accepting attempt the policy now recomputes them from the public key
   and signature, and they matched on every set.
5. **The search is judged too.** The shim logs outside Valgrind, so the
   policy now judges every searched call, 128 to 896 per set, as well as the
   handful memcheck replays. It also continues until it finds a hint-weight
   rejection, which ML-DSA-65 needed for control 4.
