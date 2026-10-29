# Elliptic curves in pq-verify

This is the specification for pq-verify's elliptic-curve arithmetic and
point counting (`pq_verify/ec.py`), for the cubic engine (`CUBIC_C` in
`pq_verify/core.py`), and for the self-suite's curve audit. The curve checks
are on the classical track: none of them is post-quantum evidence.

## What it did through 2.13.0

- **Point counts could be undecided, and some rows passed regardless.** The
  baby-step giant-step count did not use the quadratic twist, so on some
  curves (j = 0 ones, among them) it could not decide the group order. The
  curve audit's anomalous-trace rows passed whatever they found, and for
  p > 10¹⁴ a row passed that said only that SEA would be needed.
- **The cubic engine overflowed.** It computed Sol₃ = p² + (p − 1)·B(a, b)
  in 64 bits, wrong past p ≈ 3 × 10⁹. Its search for p = a² + 3b² took
  √(p/3) steps. Its integer square root overflowed: from (2³² − 1)² it
  returned wrong roots, and near 2⁶⁴ (at the largest prime below it, for
  one) it did not return at all.
- **`ecc_point_valid` accepted unreduced values.** A coordinate or
  coefficient outside [0, p) is not a field element, and an unreduced b
  made it compare the wrong right-hand side.
- **Several rows could not fail**: the j-invariant, the stability margin,
  and "Cubic analysis" for p ≢ 1 (mod 3).

## Point counts

For E: y² = x³ + ax + b over F_p (p > 3 prime, 0 ≤ a, b < p, nonsingular),
#E(F_p) is found by one of four methods, and each answer is a `Count` with
a certificate. `check_count` verifies a certificate from the curve alone,
without the method that produced it. Every certified count lies in the Hasse
interval p + 1 ± ⌊2√p⌋.

| Method | When | Certificate | What it rests on |
|---|---|---|---|
| direct | p < 2¹⁶ | none: the checker counts again, by another route | the definition |
| complex multiplication | j = 0 or 1728, any p | p = u² + 3v² (or u² + v²); a point the count annihilates; points that annihilate no other allowed order | Deuring: the trace is one of ±2u, ±(u ± 3v) (j = 0) or ±2u, ±2v (j = 1728), and 0 when E is supersingular |
| point orders | other curves, p < 2⁶⁴ | points of E and of its quadratic twist E′, each with its exact order and that order's factorization | Lagrange, Hasse, and #E + #E′ = 2p + 2 |
| Schoof–Elkies–Atkin | other curves, 2⁶⁴ ≤ p < 2³²⁰ | for each Elkies prime l, a kernel polynomial and Frobenius' eigenvalue on it; a point that separates the candidates left | φ² − tφ + p = 0 on the points of order l the kernel polynomial's roots give ([SEA.md](SEA.md)) |

**Complex multiplication.** Cornacchia's algorithm gives p = u² + 3v² for
j = 0 with p ≡ 1 (mod 3), or p = u² + v² for j = 1728 with p ≡ 1 (mod 4).
The trace is one of six (or four) values, and random points rule out every
candidate order they are not annihilated by. When p ≡ 2 (mod 3), or
3 (mod 4), the curve is supersingular and #E = p + 1. This counts secp256k1
in a tenth of a second, and its count equals the published group order.

**Point orders (Mestre).** For each point, baby-step giant-step finds a
multiple of its order in the Hasse interval, and factoring that multiple
gives the exact order. A point of E constrains #E ≡ 0 modulo its order, and
a point of the twist E′ constrains #E ≡ 2p + 2 modulo its order. Points are
added, alternately from E and E′, until the Chinese remainder theorem leaves
exactly one order in the interval. Mestre showed that for p > 229 one of the
two curves has a point that does this. The checker verifies each claimed
order (m·P = O, and (m/q)·P ≠ O for each prime q dividing m, each q checked
prime), then solves the congruences again.

**Published orders.** `verify_order(E, n)` certifies a curve's published
order without counting it, using the same kind of certificate. It checks
that n lies in the Hasse interval and annihilates random points, and that
their exact orders leave n as the only such multiple there. For a prime n
above 4√p, as for P-256, one point suffices.

**Integers.** Primality is proved by Miller–Rabin with the first thirteen
prime bases below 3.3 × 10²⁴ (Sorenson and Webster). Beyond that it is the
Baillie–PSW test, for which no composite is known. Factoring is
Pollard–Brent ρ, each factor checked for primality. Square roots are
Tonelli–Shanks.

**Schoof–Elkies–Atkin.** A general curve from 2⁶⁴ to 2³²⁰ is counted by SEA
([SEA.md](SEA.md)), in pure Python: P-256 in about a minute, with its
published order. The check needs none of the modular polynomials the count
used.

**Limits.** A general curve (j ≠ 0, 1728) above 2³²⁰ is CANNOT VERIFY unless
its order is published (`verify_order`).

## The cubic engine

- **Decomposition.** `find_decomp` finds p = a² + 3b² by Cornacchia's
  algorithm (Tonelli–Shanks for √−3 mod p), for any prime below 2⁶⁴.
- **Sol₃.** `cubic_solution_count` gives Sol₃ = #{x³ + y³ + z³ = 0 in F_p³}
  = p² + (p − 1)·B(a, b), computed in 128 bits. It returns −2 when Sol₃ does
  not fit in 64 bits, which is from p ≈ 3 × 10⁹.
- **B(a, b), checked two ways.** The Fermat cubic is isomorphic to
  y² = x³ − 432, whose count is p + 1 + B. So B is checked against complex
  multiplication at any size. For small p it is also checked against the
  Jacobi sum: J(χ, χ) for a cubic character χ, from its character sum, is
  primary, has norm p, and gives B = 2·Re J (Ireland and Rosen, ch. 8).
- **Point validation.** `ecc_point_valid` is false for any value outside
  [0, p).

## The self-suite's curve checks

The audit of each curve has eight rows, each able to fail (the tests break
them on purpose):

1. **Discriminant Δ ≠ 0.**
2. **j-invariant.** It satisfies j·(4a³ + 27b²) = 6912a³, checked without the
   inverse that computes it. It is unchanged under (a, b) → (u⁴a, u⁶b), and
   it is 0 or 1728 exactly when a or b is 0.
3. **Point count.** Certified, by its method, with its trace.
4. **Twist: #E + #E′ = 2p + 2.** The twist counted and certified on its own.
5. **Cubic B(a, b).** The engine's Sol₃ against 1 + (p − 1)·#E for
   y² = x³ − 432, counted by complex multiplication. Where Sol₃ does not fit
   in 64 bits, the row checks instead that the engine refuses it and that
   its B = #E − p − 1.
6. **ECC point validation.** The engine on a point of E, a point off it, an
   unreduced x and an unreduced b.
7. **Conformity D(t)** and 8. **Conservation law on family**, from the
   conformity engine (research framework). D must equal 2u′ + 4u² with
   u = Δ′/(12Δ) along the family Δ(t) = 4a³ + 27t², computed from Δ itself
   rather than from the ω derivatives the engine is given.

Its findings are a singular curve (CRITICAL), an anomalous one (#E = p:
CRITICAL), a supersingular one (HIGH), one of trace 2 (#E = p − 1, so its
embedding degree is 1: HIGH), and a small embedding degree (HIGH). The last
is SafeCurves'
transfer criterion: for ℓ the largest prime dividing #E, the least k with
ℓ | p^k − 1 must exceed (ℓ − 1)/100, or a pairing carries the discrete log
of the order-ℓ subgroup into F_(p^k). It is checked up to k = 100, and when
#E cannot be factored within a step limit an INFO finding says so. A rejected
certificate would be a CRITICAL defect in pq-verify. Through 2.13.0 there was
also a "near-singular fiber" finding, |4a³ + 27b²|/p < 0.01, which has no
meaning over F_p: a curve is singular or it is not, and the ratio depends on
which integers stand for a and b. And a "near-anomalous" finding fired for
every trace |t| ≤ 2, though traces −1 and −2 carry no transfer attack.

The cubic engine's audit checks Sol₃ for 21 small primes against a direct
count, and B against the Jacobi sum. At five primes of 41 to 63 bits it
checks B against complex multiplication, and checks that Sol₃, past 64 bits,
is refused. It also runs point validation with three unreduced values, and
compares kG for k = 0 to 40 with `pq_verify.ec`.

## What it does not do

- It counts points and validates them. It does not yet check a curve against
  the security criteria a standard sets: the embedding degree, the twist's
  security, or the FIPS 186-4 domain-parameter and public-key validation.
  That is the planned PKV audit.
- No curve check is evidence about a post-quantum implementation.
