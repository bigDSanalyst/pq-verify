# Source audit: CBMC and exhaustive checks of ML-KEM and ML-DSA C source

```sh
pq-verify --audit-source DIR [--json report.json] [--sarif report.sarif]
```

`--audit-source` checks an ML-KEM or ML-DSA library's C source with
[CBMC](https://github.com/diffblue/cbmc) and with exhaustive tests. It needs
the source, not the binary, and it changes nothing in it: there are no
annotations, contracts or loop invariants in the library. Each harness states
only what FIPS 203 or FIPS 204 fixes, such as a polynomial being 256
coefficients and the representatives an element of Z_q may have. pq-verify
reads the scheme off the library's `params.h` and the prefix its names carry
off its own headers. The harnesses are in
[`pq_verify/harness/source`](pq_verify/harness/source), ML-DSA's in its
[`mldsa`](pq_verify/harness/source/mldsa) directory.

`DIR` holds the arithmetic in the reference code's layout:
- **ML-KEM:** `params.h`, `poly.c`, `ntt.c`, `reduce.c`, `verify.c` and their
  headers. That is PQClean's `crypto_kem/ml-kem-{512,768,1024}/clean`.
- **ML-DSA:** `params.h`, `poly.c`, `ntt.c`, `reduce.c`, `rounding.c` and
  their headers. That is PQClean's `crypto_sign/ml-dsa-{44,65,87}/clean`.

PQClean's `common/` headers are found three levels up; give another include
directory with `--source-include DIR`. It needs `cbmc` (`apt install cbmc`)
and a C compiler, and for ML-DSA also `z3` (`apt install z3`) and Kissat,
which solves the NTT proofs. Ubuntu does not package Kissat, so build it at
its release commit, as CI does:

```bash
git clone --depth 1 --branch rel-4.0.4 https://github.com/arminbiere/kissat.git
cd kissat && ./configure && make && sudo install -m 0755 build/kissat /usr/local/bin/kissat
```

Without Kissat or Z3, an ML-DSA audit is CANNOT VERIFY before it runs
anything. An ML-KEM audit without Kissat runs its NTT with CBMC's built-in
MiniSat instead, to the same verdict more slowly. Each check in the report
names the solver that ran.

## Names and layout

The harnesses call the library's functions by role:
- **ML-KEM**, seven: `montgomery_reduce`, `barrett_reduce`, `zetas`, `ntt`,
  `poly_reduce`, `poly_basemul_montgomery` and `poly_frommsg`.
- **ML-DSA**, thirteen: `montgomery_reduce`, `reduce32`, `caddq`, `freeze`,
  `zetas`, `ntt`, `invntt_tomont`, `poly_pointwise_montgomery`,
  `poly_reduce`, `poly_chknorm`, `power2round`, `decompose` and `use_hint`.

Each is the library's prefix followed by the role, the prefix read off the
first of them its headers declare. ML-DSA's reference keeps its zeta table
`static` and unprefixed in `ntt.c`, so that role is `zetas` by default, and
the exhaustive test includes `ntt.c` to read it. A library that names a role
otherwise is given the name, with nothing edited:

```sh
pq-verify --audit-source DIR --source-symbol ntt=my_kyber_ntt \
    --source-symbol zetas=my_zeta_table
```

The data must still be the reference code's, and `params.h` must give the
standard's values, which each harness checks as it compiles:
- **ML-KEM:** a `poly` holding `int16_t coeffs[256]`, and `KYBER_N`,
  `KYBER_Q` and `KYBER_INDCPA_MSGBYTES` of 256, 3329 and 32.
- **ML-DSA:** a `poly` holding `int32_t coeffs[256]`, `N`, `Q` and `D` of 256,
  8380417 and 13, and `K`, `L`, `ETA`, `GAMMA1` and `GAMMA2` of one of FIPS
  204's three parameter sets.

The source must be C, not C++. A library that does not fit is CANNOT VERIFY,
with the role or file it lacks named, and never a pass.

Each function's body must be in those files. CBMC takes a call to a function
it has no body for to do nothing: an NTT defined in some other file would
keep every bound its input had, and pass. So pq-verify reads CBMC's warning
for such a call, and the run is CANNOT VERIFY, naming the function. Only the
harnesses' own inputs, the `nondet_` functions, have no body.

Nor may anything in the source change what a harness means. pq-verify reads
every file the checks compile, and every header those include outside the
system's, comments aside. It refuses each of these, naming the file and line:
- CBMC's own directives, `__CPROVER_…` and `#pragma CPROVER`. An assumption
  could drop inputs, a pragma turn a check off, a macro redefine an
  assertion.
- The harnesses' names, `nondet_…` and `PQV_…`.
- Inline assembly with an instruction in it, which CBMC skips without a
  warning. An empty template, such as PQClean's `__asm__("" : "+r"(b))`, is a
  compiler barrier with no instruction, so skipping it is exact, and it is
  allowed.

## ML-KEM: what is checked

Measured on PQClean's ML-KEM-768 at the commit `tools/vendor_audits.json`
pins (`0586a824`), with CBMC 5.95.1 and GCC 13.3, the NTT solved with
Kissat 4.0.4 and the others with CBMC's built-in MiniSat:

| Function | Checked for | Inputs | Result | Time |
|---|---|---|---|---|
| `poly_reduce` | UB-free; every output in {−(q−1)/2, …, (q−1)/2} | every polynomial: 256 coefficients, each any int16 | verified, 27 properties | 56 s |
| `ntt` | UB-free; no int16 overflow; every output in (−8q, 8q) | every polynomial with coefficients in (−q, q) | verified, 70 and 72 properties | 132 s and 252 s |
| `poly_basemul_montgomery` | UB-free; no int16 overflow; every output in (−2q, 2q) | every pair of polynomials with coefficients in (−q, q) | verified, 194 and 201 properties | 350 s and 345 s |
| `poly_frommsg` | UB-free; coefficient 8i+j is (q+1)/2 when bit j of byte i is set, else 0: FIPS 203's bit order | every 32-byte message | verified, 50 properties | 1 s |
| `barrett_reduce` | r ≡ a (mod q), r in {−(q−1)/2, …, (q−1)/2} | all 65,536 int16 values | 0 wrong | exhaustive |
| `montgomery_reduce` | r·2¹⁶ ≡ a (mod q), r in (−q, q) | all 218,169,344 values in {−q·2¹⁵, …, q·2¹⁵ − 1} | 0 wrong | exhaustive |
| `zetas` | entry i is 17^BitRev7(i)·2¹⁶ mod q, centred | all 128 entries | 0 wrong | exhaustive |

Where a row gives two numbers, the first is the undefined-behaviour run and
the second the overflow run. A run takes 8 minutes on three cores. The three
exhaustive checks take under two seconds together, built with `-O2` under
UBSan where the compiler has it.

**UB-free** means CBMC found no undefined behaviour on any input the harness
allows: no out-of-bounds access, invalid pointer, signed overflow, undefined
shift or division by zero. Every loop here has a fixed bound, so CBMC unrolls
each one completely, and an unwinding assertion confirms that it did. The
result is a proof for every allowed input, not a sample, in C's semantics as
CBMC models them.

**No int16 overflow** means no value is stored in a type it does not fit.
In C that is implementation-defined, not undefined. Coefficients that grow
past 32,767 are one way NTT code goes wrong.

## ML-DSA: what is checked

Measured on PQClean's ML-DSA-65 at the same commit, with the same tools and
Z3 4.8.12; the NTTs and the multiplication solved with Kissat, the
`montgomery_reduce` proof with Z3, the others with MiniSat:

| Function | Checked for | Inputs | Result | Time |
|---|---|---|---|---|
| `montgomery_reduce` | UB-free; r in (−q, q); f(a + 2³²) = f(a) + 1 | every int64 in {−2³¹q, …, 2³¹q − 1} | verified, 6 properties | 0.4 s |
| `ntt` | UB-free; no int32 overflow; every output in (−9q, 9q) | every polynomial with coefficients in (−q, q) | verified, 70 and 65 properties | 388 s and 252 s |
| `invntt_tomont` | UB-free; no int32 overflow in its unreduced sums, which reach 256(q − 1); every output in (−q, q) | every polynomial with coefficients in (−q, q) | verified, 111 and 103 properties | 374 s and 185 s |
| `poly_pointwise_montgomery` | UB-free; every output in (−q, q) | every pair of polynomials with coefficients in (−9q, 9q) | verified, 42 and 41 properties | 102 s and 24 s |
| `poly_reduce` | UB-free; every output in {−6,283,009, …, 6,283,008} | every polynomial with coefficients at most 2³¹ − 2²² − 1 | verified, 26 and 26 properties | 96 s and 95 s |
| `poly_chknorm` | UB-free, its doubling and `>> 31` mask included; the result is 0 or 1, and 1 whenever B > (q−1)/8 | every polynomial `reduce32` can return, and every int32 bound B | verified, 18 and 18 properties | 8 s and 8 s |
| `montgomery_reduce` | r·2³² ≡ a (mod q), r in (−q, q) | all 4,294,967,296 values in [0, 2³²) | 0 wrong | exhaustive |
| `reduce32` | r ≡ a (mod q), r in {−6,283,009, …, 6,283,008} | all 4,290,772,992 values at most 2³¹ − 2²² − 1 | 0 wrong | exhaustive |
| `caddq` | a + q if a < 0, else a | all 4,294,967,296 int32 values | 0 wrong | exhaustive |
| `freeze` | a mod⁺ q, in [0, q) | all 4,290,772,992 values at most 2³¹ − 2²² − 1 | 0 wrong | exhaustive |
| `zetas` | entry i is 1753^BitRev8(i)·2³² mod q, centred | entries 1 to 255 (entry 0 is never read) | 0 wrong | exhaustive |
| `power2round` | FIPS 204's Power2Round (Algorithm 35) | every r in [0, q) | 0 wrong | exhaustive |
| `decompose` | FIPS 204's Decompose (Algorithm 36), with its r⁺ − r₀ = q − 1 case | every r in [0, q) | 0 wrong | exhaustive |
| `use_hint` | FIPS 204's UseHint (Algorithm 40) | every r in [0, q), both hints | 0 wrong | exhaustive |

A run takes 23 minutes on three cores, the eight exhaustive checks 38
seconds of it, built with `-O2` under UBSan. For the three split jobs, the
overflow run checks only the group conversion checks fall in; the other two
groups are the undefined-behaviour run's, verdict for verdict. Their counts
include the one or two products decided by their operands' types (below).
`montgomery_reduce`'s overflow run reports the two conversions it is built
on, which are notes (below), not failures.

The input ranges are FIPS 204's:
- **The NTT's inputs** are s₁ and s₂ (|c| ≤ η), t₀ (in (−2¹², 2¹²]), y and z
  (|c| ≤ γ₁), the challenge c (in {−1, 0, 1}) and t₁·2ᵈ (in [0, q)): all
  inside (−q, q).
- **The inverse NTT's inputs** are pointwise products, or sums reduced first:
  also inside (−q, q).
- **The pointwise multiplication's inputs** are NTT outputs and the matrix
  A's entries: all inside (−9q, 9q).
- **The rounding functions' inputs** are standard representatives, in [0, q).

The rounding is checked against FIPS 204's algorithms as written, for γ₂ =
(q−1)/88 and (q−1)/32 alike, and `decompose` includes its corner case, where
r⁺ − r₀ = q − 1 and r₁ is 0.

`reduce32` and `freeze` are tested on every a ≤ 2³¹ − 2²² − 1, the inputs
`reduce32`'s comment allows, and on no others. For each of the 2²² values
above that, `reduce32`'s first step, `a + (1 << 22)`, overflows an int32,
which C leaves undefined. The exhaustive test runs under UBSan and stops at
the first undefined behaviour, so it would abort at a = 2³¹ − 2²².

## How the pieces fit

**ML-KEM.** `ntt` and `poly_basemul_montgomery` are checked with the two
reductions replaced by contracts (`stubs.c`):
- `montgomery_reduce` requires its input in {−q·2¹⁵, …, q·2¹⁵ − 1}, and every
  call is checked against that. It returns any value in (−q, q).
- `barrett_reduce` returns any value in {−(q−1)/2, …, (q−1)/2}.

The exhaustive test proves the library's own compiled reductions meet those
contracts on every input they admit. A caller proven safe against the
contracts is therefore safe with the real functions: a contract's output is
any value the real function could give, so it can only add behaviours. It
also keeps the proofs small: CBMC reasons about the contracts, not the
reductions' own multiplications.

**ML-DSA.** `ntt`, `invntt_tomont` and `poly_pointwise_montgomery` are checked
with `montgomery_reduce` replaced by its contract (`mldsa/stubs.c`): input
in {−2³¹q, …, 2³¹q − 1}, checked at every call, and any output in (−q, q).
Its int64 domain, about 2⁵⁵ values, is too large to enumerate, so the
contract is proved in two parts:
- CBMC proves, of the library's own C, that every input in the contract
  gives an output in (−q, q), and that f(a + 2³²) = f(a) + 1 whenever a and
  a + 2³² are both in it. It does this with Z3, which decides the second
  property in seconds. Kissat takes about 12 s; MiniSat and CaDiCaL had not
  finished after ten minutes.
- The exhaustive test checks r·2³² ≡ a (mod q) on every a in [0, 2³²), as
  compiled.

Together these give the congruence on every input. Write a = l + h·2³² with
l in [0, 2³²): the steps from l to a stay inside the interval, so
f(a) = f(l) + h, and f(a)·2³² = f(l)·2³² + h·2³² ≡ l + h·2³² = a (mod q).

**Large proofs in parts.** The ML-DSA NTT makes 1,024 int64 products, and as
one formula it is 42 million clauses. So its properties, and those of the
inverse NTT and the pointwise multiplication, are checked in three groups
instead, each its own CBMC run with the formula sliced to it; the NTT's
largest part is 21 million clauses:
- `montgomery_reduce`'s precondition;
- each multiplication's overflow;
- everything else, built without the precondition, so no product is left in
  its formula. In CBMC an assertion does not restrict the paths after it, so
  leaving the precondition out changes no other property.

pq-verify checks that every property CBMC lists is in exactly one group,
with the same description, file and line in both builds, or the run is
CANNOT VERIFY. A multiplication whose operands' types alone bound
it, such as an int32 by an int32 in int64 (under 2⁶²), cannot overflow. That
is read off CBMC's own typed program and decided there, not by the solver; a
product it cannot read that way stays a check.

**Solvers.** The NTT and pointwise proofs run with Kissat, the others with
CBMC's built-in MiniSat, and `montgomery_reduce`'s with Z3. Kissat replaced
CaDiCaL, which was slower. Each formula below was written once by CBMC and
given to Kissat 4.0.4 and CaDiCaL 1.7.3 at the same time, on the same
four-core machine; both answered UNSAT, no property can fail, on every one:

| Formula | Variables | Clauses | Kissat | CaDiCaL |
|---|---|---|---|---|
| ML-DSA `ntt`, contract group | 3.6 M | 21.0 M | 138 s, 1.9 GB | 355 s, 4.6 GB |
| ML-DSA `ntt`, rest | 2.2 M | 12.8 M | 256 s, 1.2 GB | 247 s, 2.8 GB |
| ML-DSA `invntt_tomont`, contract group | 4.4 M | 25.8 M | 180 s, 2.4 GB | 744 s, 5.6 GB |
| ML-DSA `invntt_tomont`, rest | 2.6 M | 15.1 M | 178 s, 1.4 GB | 310 s, 3.5 GB |
| ML-KEM `ntt`, undefined behaviour | 2.2 M | 11.8 M | 127 s, 1.2 GB | 161 s, 2.5 GB |
| ML-KEM `ntt`, overflow | 2.5 M | 13.0 M | 256 s, 1.4 GB | 441 s, 2.8 GB |

In all, Kissat took 19 minutes where CaDiCaL took 38, and it used less than
half the memory on every formula. On one, the ML-DSA NTT's rest group, it was
4% slower.

## Every check can fail

A check that cannot fail says nothing, so each one is shown failing first:
- **CBMC's self-test** (`selftest.c`): an out-of-bounds write, a signed
  overflow and a narrowing that does not fit, each of which CBMC must report.
  Also a call to a function with no body, which CBMC verifies and pq-verify
  must refuse: if a later CBMC stopped warning about such calls, this is
  what would notice.
- **Each solver**: Kissat and Z3, where a job runs with them, must report the
  same out-of-bounds write through CBMC and pass `selftest_model`. A solver
  that answered UNSAT wrongly would pass every proof it ran.
- **Reachability**: a false assertion at the end of each harness must fail,
  with the job's own solver. If it holds, no input reaches the end, the
  harness's assumptions contradict each other, and its passes are vacuous.
- **The exhaustive controls**: each comparison is run first on a copy of the
  function or table with one value wrong, and must count it. ML-DSA's run
  over a window around the planted value, its full domains being up to 2³²
  values.

Any of these not catching its defect makes the run CANNOT VERIFY.

## What C leaves to the compiler

Two things the reductions rely on are implementation-defined in C, not
undefined: a right shift of a negative value, and a conversion to a signed
type that does not fit. CBMC models the shift as filling with the sign and
the conversion as wrapping, as GCC and Clang do. Its `--undefined-shift-check`
reports only shifts that are undefined, by the type's width or more, or by a
negative amount. It does not report a shift of a negative value, and no CBMC
option does.

So the model is pinned twice. CBMC's self-test has `selftest_model`, which
must verify: a negative int32 or int64 shifted right fills with its sign, and
a narrowed value wraps, from int32 to int16 and from uint64 to int32. Each
exhaustive test then checks that the compiler in use does the same. If
either fails, the run is CANNOT VERIFY, because the proofs hold only for a
compiler that does what the model says.

In the ML-KEM functions this audit checks, PQClean shifts a negative value
only inside the two reductions: `>> 16` in `montgomery_reduce` and `>> 26` in
`barrett_reduce`. The exhaustive test runs those as compiled. The NTT's shifts
are of unsigned values, and `poly_frommsg` shifts a byte. Elsewhere,
`poly_compress`, `poly_tobytes` and `polyvec_compress` shift a coefficient
right by 15 to add q when it is negative. Those functions are not checked
here.

In ML-DSA, `montgomery_reduce` shifts an int64 right by 32, `reduce32` an
int32 by 23, and `caddq`, `decompose` and `poly_chknorm` build masks from a
`>> 31`.

## Verdicts

- **VERIFIED**: every check above passed.
- **FINDINGS PRESENT**: undefined behaviour, an overflow in an NTT or the
  NTT-domain multiplication, a broken output bound, a wrong reduction or
  rounding, or a zeta that is not the standard's. SARIF gives each one's file
  and line.
- **CANNOT VERIFY**: `cbmc`, a compiler or, for ML-DSA, `z3` is missing, the
  layout is not one pq-verify knows, a function a check calls has no body in
  the files given, the source holds something that could change what a
  harness means, a self-test or control was not caught, the compiler does
  not do what CBMC's model assumes, a harness's end was not reached, a split
  check's groups did not cover its properties, or a check did not finish.
  Each CBMC run is limited to `--audit-timeout` seconds (default 3600) and 8
  GB of address space, its solver capped the same, so a run that would hang
  or exhaust the machine stops instead. One that runs out of either has decided
  nothing, and the reason is reported. Runs go side by side only as far as
  the machine's memory holds them: each job's budget, from its measured
  peak, is in its scheme's table.

A value narrowed in a way C leaves implementation-defined, inside a function
whose results the run checked, is a note, not a finding.

## Notes on PQClean

ML-KEM:
- **`barrett_reduce` relies on two's-complement wrapping.** For 2,285 inputs,
  those with |a| ≥ 31,626, it stores two values that do not fit int16:
  `t *= KYBER_Q` (line 39) and `return a - t` (line 40). C leaves the result
  implementation-defined. GCC and Clang wrap, and the result is then still
  right, as the exhaustive test shows. On the path this audit proves, the NTT
  followed by `poly_reduce`, the NTT's outputs stay below 8q = 26,632, so it
  never sees such a value. Its other callers were not checked. This is not a
  bug, but a reviewer should know the code depends on the compiler for it.
- `cmov_int16` converts a negative `int` to `uint16_t` (`b = -b`, line 65).
  C defines that: it wraps. CBMC's conversion check reports it anyway, and the
  audit classes it as defined.

ML-DSA:
- **Two comments are off by one at one end.** pq-verify's Coq proofs already
  show both of the reference algorithms (`Reduce.v`:
  `mldsa_montgomery_top_input`, `mldsa_reduce32_lower_witness`); the source
  audit finds the same in PQClean's C. Neither changes any caller: every
  value PQClean passes is far from both.
  - `montgomery_reduce`'s comment gives its domain as −2³¹q ≤ a ≤ 2³¹q. At
    a = 2³¹q it returns q itself, outside the (−q, q) the comment promises;
    the congruence still holds. The contract proved here is
    {−2³¹q, …, 2³¹q − 1}.
  - `reduce32`'s comment, and those in `poly.c` and `polyvec.c`, give its
    output as −6,283,008 ≤ r ≤ 6,283,008. One input, a = −2,143,289,344,
    gives −6,283,009. The range proved here, and the one `poly_chknorm` is
    checked on, is {−6,283,009, …, 6,283,008}.
- `montgomery_reduce` converts a uint64 product to int32
  (`(int32_t)((uint64_t)a * QINV)`), which C leaves implementation-defined
  for values that do not fit, and an int64 to uint64, which C defines. Its
  results are checked with the values wrapped, as GCC and Clang do.

## Negative controls

CI runs `tools/source_audit.py` (in `vendor-audits.yml`), one job per
scheme and ML-DSA parameter set. It fetches PQClean at the pinned commit,
requires ML-KEM-512, 768 and 1024 and ML-DSA-44, 65 and 87 to be VERIFIED,
and applies each mutant below to a copy of ML-KEM-768 or ML-DSA-65. Each is
an exact edit of the source. Every one but each scheme's last is one
deliberate bug, and must fail the check named for it. The last hides a
function's body, and the run must refuse it rather than pass.

ML-KEM:

| # | Bug | Caught by | Evidence |
|---|---|---|---|
| 1 | `poly_frommsg`'s loop runs one step too far | CBMC, UB | out-of-bounds write to `r->coeffs[8 * i + j]` (line 123) |
| 2 | the NTT butterfly without its Montgomery reduction | CBMC, int16 overflow | `(int16_t)(zeta * r[j + len])` does not fit (line 89), and the output bound fails |
| 3 | `basemul` multiplies three factors before reducing | CBMC, UB | signed int32 overflow (line 141), and `montgomery_reduce`'s input contract fails |
| 4 | `montgomery_reduce` truncates t·q to 16 bits | exhaustive test | 218,106,093 of 218,169,344 inputs wrong |
| 5 | one zeta off by one | exhaustive test | entry 1 is −757; FIPS 203 gives −758 |
| 6 | `poly_frommsg` reads each byte's bits in the reverse order | CBMC, the harness's postcondition | coefficient 8i+j must come from bit j of byte i, FIPS 203's order; bounds and safety all still hold |
| 7 | `ntt`'s definition renamed, so the name the harness calls has no body | the no-body check: refused | CBMC itself verifies this run, since an NTT that does nothing keeps its input's bounds |

ML-DSA:

| # | Bug | Caught by | Evidence |
|---|---|---|---|
| 1 | the NTT butterfly without its Montgomery reduction | CBMC, UB | signed int32 overflow in `a[j] - t` and `a[j] + t` (lines 59 and 60), and the output bound fails |
| 2 | `invntt_tomont` without its final scaling | CBMC, the output bound | the outputs, the unscaled sums, leave (−q, q) (`h_invntt.c` line 19) |
| 3 | `poly_pointwise_montgomery` without its reduction | CBMC, the output bound | the unreduced products leave (−q, q) (`h_pointwise.c` line 20) |
| 4 | `montgomery_reduce` shifts by 31, not 32 | CBMC, its bound | r leaves (−q, q), and f(a + 2³²) = f(a) + 1 fails |
| 5 | `montgomery_reduce` truncates t·q to 32 bits | exhaustive test | 4,294,966,783 of the 4,294,967,296 low words wrong. Its bound and shift property still hold, so CBMC's half of the proof passes it |
| 6 | `reduce32` subtracts multiples of q − 1 | exhaustive test | 4,282,384,384 of 4,290,772,992 inputs wrong |
| 7 | `caddq` adds q − 1 | exhaustive test | 2,147,483,648 of 4,294,967,296 inputs wrong: every negative one |
| 8 | one zeta off by one | exhaustive test | entry 1 is 25,848; FIPS 204 gives 25,847 |
| 9 | `decompose` without its q − 1 corner case | exhaustive test | 261,888 of 8,380,417 inputs wrong: every r from 8,118,529 up |
| 10 | `use_hint` rounds up at r₀ = 0 | exhaustive test | 16 of 16,760,834 (r, hint) pairs wrong, the first at r = 0 |
| 11 | `poly_chknorm` reads one coefficient past the end | CBMC, UB | out-of-bounds read of `a->coeffs[i]` (line 284) |
| 12 | `ntt`'s definition renamed, so the name the harness calls has no body | the no-body check: refused | CBMC itself verifies this run, since an NTT that does nothing keeps its input's bounds |

Mutant 5 is why `montgomery_reduce`'s proof has two halves. It keeps the
bound and f(a + 2³²) = f(a) + 1, which CBMC proves, and breaks only the
congruence, which the exhaustive test checks. Mutant 4 shows CBMC's half
failing on its own terms: it breaks the bound and the shift property.

There is no strict-aliasing mutant: CBMC cannot check aliasing rules, so such
a control could never be caught.

## What this does not show

- That an NTT or an NTT-domain multiplication computes the standard's
  transform. These checks are about safety and bounds. Functional
  correctness is the job of the ACVP vectors (`--audit-kem`, `--audit-dsa`)
  and of pq-verify's checks against the NTT's definition. The zeta tables,
  the reductions and the bounds proved here are the pieces a proof of the
  transform's output would rest on.
- Any function not listed above. For ML-KEM: key generation, encapsulation
  and decapsulation as a whole, SHA-3, sampling, compression and encoding.
  For ML-DSA: key generation, signing and verification as a whole, SHAKE,
  sampling (`poly_uniform`, `poly_uniform_eta`, `poly_uniform_gamma1`,
  `poly_challenge`), packing and unpacking, the polynomial-vector layer
  (`polyvec.c`), and `make_hint`, whose equality with FIPS 204's MakeHint
  holds only under the signer's rejection conditions.
- `poly_chknorm`'s decision: that it returns 1 exactly when some
  coefficient's absolute value is at least B. None of the solvers tried
  (MiniSat, CaDiCaL, Z3) decided that equivalence over 256 coefficients in
  reasonable time; the ACVP vectors exercise it.
- A layout other than the reference code's. mlkem-native and mldsa-native,
  for two, have their own names, and their own CBMC proofs.
- Strict aliasing. CBMC does not check it, and neither does UBSan.
- Constant time: that is `--constant-time`.
- The compiled binary, beyond what the exhaustive tests run. CBMC reasons
  about C's semantics; the exhaustive tests run the compiled code.
