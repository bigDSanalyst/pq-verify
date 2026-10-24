# Source audit, proof of concept: CBMC and exhaustive checks

This directory checks C source with [CBMC](https://github.com/diffblue/cbmc)
and with exhaustive tests. It needs the library's source, not its binary,
and it changes nothing in that source: there are no annotations, contracts or
loop invariants in the library. Each harness states only what FIPS 203 fixes,
such as a polynomial being 256 coefficients and the representatives an
element of Z_q may have. The library's function names live in one header,
`harness/pqv_ns.h`.

It is a proof of concept on one library: PQClean's ML-KEM-768 `clean` code,
at the commit `tools/vendor_audits.json` pins for the vendor audits
(`0586a824`). It is not wired into the `pq-verify` command yet.

## What is checked

Measured with CBMC 5.95.1 and GCC 13.3. The NTT was solved with CaDiCaL 1.7.3
and the others with CBMC's built-in MiniSat.

| Function | Checked for | Inputs | Result | Time |
|---|---|---|---|---|
| `poly_reduce` | UB-free; every output in {−(q−1)/2, …, (q−1)/2} | every polynomial: 256 coefficients, each any int16 | verified, 27 properties | 67 s |
| `ntt` | UB-free; no int16 overflow; every output in (−8q, 8q) | every polynomial with coefficients in (−q, q) | verified, 70 and 72 properties | 190 s and 488 s |
| `poly_basemul_montgomery` | UB-free; no int16 overflow; every output in (−2q, 2q) | every pair of polynomials with coefficients in (−q, q) | verified, 194 and 201 properties | 382 s and 391 s |
| `poly_frommsg` | UB-free; coefficient i is (q+1)/2 when bit i of the message is set, else 0 | every 32-byte message | verified, 50 properties | 1 s |
| `barrett_reduce` | r ≡ a (mod q), r in {−(q−1)/2, …, (q−1)/2} | all 65,536 int16 values | 0 wrong | exhaustive |
| `montgomery_reduce` | r·2¹⁶ ≡ a (mod q), r in (−q, q) | all 218,169,344 values in {−q·2¹⁵, …, q·2¹⁵ − 1} | 0 wrong | exhaustive |
| `zetas` | entry i is 17^BitRev7(i)·2¹⁶ mod q, centred | all 128 entries | 0 wrong | exhaustive |

The three exhaustive checks take 0.6 s together, built with `gcc -O2` under
UBSan, which reported nothing. The whole run, including the mutants, takes
about 20 minutes on three cores.

**UB-free** means CBMC found no undefined behaviour on any input the harness
allows: no out-of-bounds access, invalid pointer, signed overflow, undefined
shift or division by zero. Every loop here has a fixed bound, so CBMC unrolls
each one completely, and an unwinding assertion confirms that it did. The
result is a proof for every allowed input, not a sample. Each harness also
passes a reachability control: a false assertion at its end must fail. That
shows the harness's assumptions are consistent, so no result is vacuous.

**No int16 overflow** means no value is stored in a type it does not fit.
In C that is implementation-defined, not undefined. Coefficients that grow
past 32,767 are one way NTT code goes wrong.

## How the pieces fit

`ntt` and `basemul` are checked with the two reductions replaced by contracts
(`harness/stubs.c`):
- `montgomery_reduce` requires its input in {−q·2¹⁵, …, q·2¹⁵ − 1}, and every
  call is checked against that. It returns any value in (−q, q).
- `barrett_reduce` returns any value in {−(q−1)/2, …, (q−1)/2}.

The exhaustive test proves the library's own compiled reductions meet those
contracts on every input they admit. A caller proven safe against the
contracts is therefore safe with the real functions: a contract's output is
any value the real function could give, so it can only add behaviours. It
also keeps the proofs small: CBMC reasons about the contracts, not the
reductions' own multiplications.

## Findings on the unmodified library

- **`barrett_reduce` relies on two's-complement wrapping.** For 2,285 inputs,
  those with |a| ≥ 31,626, it stores two values that do not fit int16:
  `t *= KYBER_Q` (line 39) and `return a - t` (line 40). C leaves the result
  implementation-defined. GCC and Clang wrap, and the result is then still
  right, as the exhaustive test shows. ML-KEM's own callers never pass values
  that large: the NTT's outputs, proved above, stay below 8q = 26,632. This is
  not a bug, but a reviewer should know the code depends on the compiler for
  it.
- `cmov_int16` converts a negative `int` to `uint16_t` (`b = -b`, line 65).
  C defines that: it wraps. CBMC's conversion check reports it anyway, and the
  run classes it as defined, not as a finding.

## Negative controls

Each mutant is one deliberate bug, applied as an exact edit to a copy of the
library's source. Each must fail the check named for it.

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

- That `ntt` or `basemul` compute FIPS 203's transform. These checks are about
  safety and bounds. Functional correctness is covered elsewhere in pq-verify,
  by the ACVP vectors and the NTT's definition. The zeta table, the reductions
  and the bounds proved here are the pieces a proof of the transform's
  output would rest on.
- Any function not listed above, or any other library. Another library needs
  its names in `pqv_ns.h` and the same harnesses.
- Strict aliasing. CBMC does not check it, and neither does UBSan.
- Constant time. pq-verify's valgrind checks cover that.
- The compiled binary, beyond the two reductions. CBMC reasons about C's
  semantics; the exhaustive test runs the compiled code.

## Running it

```sh
sudo apt-get install cbmc cadical
git init pqclean
git -C pqclean fetch --depth 1 https://github.com/PQClean/PQClean \
    0586a824fc0d49df0b6b6e9179d8d15d06d0974f
git -C pqclean checkout FETCH_HEAD
python3 -I tools/cbmc/run_poc.py pqclean/crypto_kem/ml-kem-768/clean out/
```

It prints a line per check and writes `out/report.json`. It exits 0 only if
the library passes every check and every mutant is caught. CaDiCaL is
optional: without it CBMC's built-in MiniSat is used, and the NTT takes about
twice as long.
