# Source audit: CBMC and exhaustive checks of ML-KEM C source

```sh
pq-verify --audit-source DIR [--json report.json] [--sarif report.sarif]
```

`--audit-source` checks an ML-KEM library's C source with
[CBMC](https://github.com/diffblue/cbmc) and with exhaustive tests. It needs
the source, not the binary, and it changes nothing in it: there are no
annotations, contracts or loop invariants in the library. Each harness states
only what FIPS 203 fixes, such as a polynomial being 256 coefficients and the
representatives an element of Z_q may have. pq-verify reads the prefix the
library's names carry off its own `reduce.h`. The harnesses are in
[`pq_verify/harness/source`](pq_verify/harness/source).

`DIR` holds the arithmetic in the reference code's layout: `params.h`,
`poly.c`, `ntt.c`, `reduce.c`, `verify.c` and their headers. That is
PQClean's `crypto_kem/ml-kem-{512,768,1024}/clean`. Its `common/` headers
are found three levels up; give another include directory with
`--source-include DIR`. It needs `cbmc` (`apt install cbmc`) and a C
compiler. CaDiCaL (`apt install cadical`) is optional: with it the NTT's
proof takes about half as long.

## What is checked

Measured on PQClean's ML-KEM-768 at the commit `tools/vendor_audits.json`
pins (`0586a824`), with CBMC 5.95.1 and GCC 13.3, the NTT solved with
CaDiCaL 1.7.3 and the others with CBMC's built-in MiniSat:

| Function | Checked for | Inputs | Result | Time |
|---|---|---|---|---|
| `poly_reduce` | UB-free; every output in {−(q−1)/2, …, (q−1)/2} | every polynomial: 256 coefficients, each any int16 | verified, 27 properties | 67 s |
| `ntt` | UB-free; no int16 overflow; every output in (−8q, 8q) | every polynomial with coefficients in (−q, q) | verified, 70 and 72 properties | 190 s and 488 s |
| `poly_basemul_montgomery` | UB-free; no int16 overflow; every output in (−2q, 2q) | every pair of polynomials with coefficients in (−q, q) | verified, 194 and 201 properties | 382 s and 391 s |
| `poly_frommsg` | UB-free; coefficient i is (q+1)/2 when bit i of the message is set, else 0 | every 32-byte message | verified, 50 properties | 1 s |
| `barrett_reduce` | r ≡ a (mod q), r in {−(q−1)/2, …, (q−1)/2} | all 65,536 int16 values | 0 wrong | exhaustive |
| `montgomery_reduce` | r·2¹⁶ ≡ a (mod q), r in (−q, q) | all 218,169,344 values in {−q·2¹⁵, …, q·2¹⁵ − 1} | 0 wrong | exhaustive |
| `zetas` | entry i is 17^BitRev7(i)·2¹⁶ mod q, centred | all 128 entries | 0 wrong | exhaustive |

A run takes about 10 minutes on three cores. The three exhaustive checks take
under two seconds together, built with `-O2` under UBSan where the compiler
has it.

**UB-free** means CBMC found no undefined behaviour on any input the harness
allows: no out-of-bounds access, invalid pointer, signed overflow, undefined
shift or division by zero. Every loop here has a fixed bound, so CBMC unrolls
each one completely, and an unwinding assertion confirms that it did. The
result is a proof for every allowed input, not a sample, in C's semantics as
CBMC models them.

**No int16 overflow** means no value is stored in a type it does not fit.
In C that is implementation-defined, not undefined. Coefficients that grow
past 32,767 are one way NTT code goes wrong.

## How the pieces fit

`ntt` and `poly_basemul_montgomery` are checked with the two reductions
replaced by contracts (`stubs.c`):
- `montgomery_reduce` requires its input in {−q·2¹⁵, …, q·2¹⁵ − 1}, and every
  call is checked against that. It returns any value in (−q, q).
- `barrett_reduce` returns any value in {−(q−1)/2, …, (q−1)/2}.

The exhaustive test proves the library's own compiled reductions meet those
contracts on every input they admit. A caller proven safe against the
contracts is therefore safe with the real functions: a contract's output is
any value the real function could give, so it can only add behaviours. It
also keeps the proofs small: CBMC reasons about the contracts, not the
reductions' own multiplications.

## Every check can fail

A check that cannot fail says nothing, so each one is shown failing first:
- **CBMC's self-test** (`selftest.c`): an out-of-bounds write, a signed
  overflow and a narrowing that does not fit, each of which CBMC must report.
- **Reachability**: a false assertion at the end of each harness must fail.
  If it holds, no input reaches the end, the harness's assumptions contradict
  each other, and its passes are vacuous.
- **The exhaustive controls**: each comparison is run first on a copy of the
  function or table with one value wrong, and must count it.

Any of these not catching its defect makes the run CANNOT VERIFY.

## Verdicts

- **VERIFIED**: every check above passed.
- **FINDINGS PRESENT**: undefined behaviour, an int16 overflow in `ntt` or
  the NTT-domain multiplication, a broken output bound, a wrong reduction or a
  zeta that is not FIPS 203's. SARIF gives each one's file and line.
- **CANNOT VERIFY**: `cbmc` or a compiler is missing, the layout is not one
  pq-verify knows, a self-test or control was not caught, a harness's end was
  not reached, or a check did not finish within `--audit-timeout` (default
  3600 s each).

A value narrowed in a way C leaves implementation-defined, inside a function
whose results the run checked, is a note, not a finding.

## Notes on PQClean

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

## Negative controls

CI runs `tools/source_audit.py` (in `vendor-audits.yml`). It fetches PQClean
at the pinned commit, requires ML-KEM-512, 768 and 1024 to be VERIFIED, and
then applies each mutant below to a copy of ML-KEM-768. Each mutant is one
deliberate bug, as an exact edit of the source, and must fail the check named
for it.

| # | Bug | Caught by | Evidence |
|---|---|---|---|
| 1 | `poly_frommsg`'s loop runs one step too far | CBMC, UB | out-of-bounds write to `r->coeffs[8 * i + j]` (line 123) |
| 2 | the NTT butterfly without its Montgomery reduction | CBMC, int16 overflow | `(int16_t)(zeta * r[j + len])` does not fit (line 89), and the output bound fails |
| 3 | `basemul` multiplies three factors before reducing | CBMC, UB | signed int32 overflow (line 141), and `montgomery_reduce`'s input contract fails |
| 4 | `montgomery_reduce` truncates t·q to 16 bits | exhaustive test | 218,106,093 of 218,169,344 inputs wrong |
| 5 | one zeta off by one | exhaustive test | entry 1 is −757; FIPS 203 gives −758 |

There is no strict-aliasing mutant: CBMC cannot check aliasing rules, so such
a control could never be caught.

## What this does not show

- That `ntt` or the NTT-domain multiplication compute FIPS 203's transform.
  These checks are about safety and bounds. Functional correctness is the job
  of the ACVP vectors (`--audit-kem`) and of pq-verify's checks against the
  NTT's definition. The zeta table, the reductions and the bounds proved here
  are the pieces a proof of the transform's output would rest on.
- Any function not listed above: key generation, encapsulation and
  decapsulation as a whole, SHA-3, sampling, compression and encoding.
- A layout other than the reference code's. mlkem-native, for one, has its
  own names, and its own CBMC proofs.
- Strict aliasing. CBMC does not check it, and neither does UBSan.
- Constant time: that is `--constant-time`.
- The compiled binary, beyond the two reductions and the zeta table. CBMC
  reasons about C's semantics; the exhaustive test runs the compiled code.
