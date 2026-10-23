# Schoof–Elkies–Atkin point counting in pq-verify

This is the specification for `pq_verify/sea.py`, which counts the points of
an elliptic curve over a large prime field. `pq_verify.ec.count` uses it for
general curves (j ≠ 0, 1728) from 2⁶⁴ to 2³²⁰. Below 2⁶⁴ the count is by
point orders, and j = 0 and 1728 are counted by complex multiplication at any
size ([ECC.md](ECC.md)). This is classical-track work: no point count is
evidence about a post-quantum implementation.

Every count carries a certificate, and `ec.check_count` verifies it from the
curve alone. The check does not use modular polynomials, Elkies' formulas or
anything else the search used, so a defect in the search can make a count
fail but cannot make a wrong count pass.

## The count

For E: y² = x³ + ax + b over F_p, #E(F_p) = p + 1 − t with |t| ≤ 2√p.

1. **t mod 2.** E has a point of order 2 exactly when x³ + ax + b has a root
   in F_p, that is, when gcd(x³ + ax + b, x^p − x) ≠ 1. Then #E is even and t
   is even.
2. **t mod l for Elkies primes l.** For an odd prime l, Ψ_l(F, j(E)) has a
   root in F_p exactly when E has an l-isogeny defined over F_p. Ψ_l is
   Müller's canonical modular polynomial, below. Such an l is an Elkies
   prime. For about half of all primes it has no root (an Atkin prime), and
   the prime is skipped.
   - **The isogenous curve.** From the root, Elkies' formulas give the
     normalized isogenous curve y² = x³ + Ãx + B̃ and p₁, the sum of the
     abscissas of the kernel's l − 1 nonzero points.
   - **The kernel polynomial.** Matching the two curves' Weierstrass
     functions gives the kernel polynomial K, of degree (l − 1)/2, whose
     roots are the abscissas of the kernel.
   - **Frobenius' eigenvalue.** Frobenius maps the kernel to itself, so it
     acts there as multiplication by some μ. The search over λ =
     1, …, (l − 1)/2 compares x^p with x([λ]P) modulo K, by division
     polynomials, and y^p with ±y([λ]P). Then t ≡ μ + p/μ (mod l).
3. **The Chinese remainder theorem** gives t modulo M, the product of 2 and
   the Elkies primes used. Primes are taken in order of estimated time per
   bit of t gained, until at most 2³² values of t ≡ t₀ (mod M) remain in the
   Hasse interval.
4. **Baby-step giant-step** on a random point P finds every remaining
   candidate n with nP = O. When exactly one remains, it is the count. If P
   leaves more than one, another point is tried, then points of the
   quadratic twist (whose order is 2p + 2 − n).

## Müller's canonical modular polynomial

For a prime l, let s = 12/gcd(12, l − 1), v = s(l − 1)/12 and

> f(τ) = l^s (η(lτ)/η(τ))^(2s),

a modular function for Γ₀(l). Ψ_l(F, J) is the polynomial whose roots, for
J = j(τ), are the l + 1 conjugates of f:

- f(τ) itself, a power series in q with a zero of order v;
- G(ζᵏw) for k = 0, …, l − 1, where w = q^(1/l), ζ = e^(2πi/l) and
  G(x) = x^(−v) E(x)^(2s)/E(x^l)^(2s), with E(x) = ∏(1 − xⁿ).

Ψ_l has degree l + 1 in F and degree v in J, against l + 1 in both for the
classical modular polynomial, and its coefficients are far smaller.

**The power sums.** P_m(j), the sum of the m-th powers of the l + 1
conjugates, is a polynomial in j of degree ⌊mv/l⌋. Because f vanishes at the
cusp, P_m is determined by the principal part and constant term of
l·U(G^m), the terms of G^m whose exponents are multiples of l. Those are the
coefficients of E(x)^(2sm) at x^(mv − lt), t = 0, …, ⌊mv/l⌋, multiplied by
E(q)^(−2sm). So E(x)^(2sm) is needed only to x^(mv), and only a few of its
coefficients are read.

With m = bc + a and b = ⌊√(l + 1)⌋, the powers E^(2sa) (a ≤ b) and E^(2sbc)
are computed by multiplication, each to x^((l + 1)v), and each needed
coefficient of E^(2sm) is one dot product. A principal part becomes a
polynomial in j by subtracting multiples of j^d, d from ⌊mv/l⌋ down to 0.

**At a point.** For J₀ ∈ F_p, Newton's identities over F_p[ε]/(ε^r) turn the
power sums at J₀ + ε into Ψ_l(F, J₀) and its first r − 1 derivatives in J.
The bivariate polynomial is never formed.

**Polynomial multiplication.** Polynomials over F_p are lists of integers.
They are multiplied by Kronecker substitution, packing each into one
integer. Past 2¹⁹ bits per operand, the packing is in base 10, and
decimal's number-theoretic transform does the multiplication, in a context
whose precision holds the whole product and in which any rounding raises.
Remainders modulo a fixed polynomial use its reversed inverse, computed once
by Newton's method.

## Elkies' formulas for the canonical polynomial

Write E₄ = −a/3, E₆ = −b/2, Δ = (E₄³ − E₆²)/1728 and j = E₄³/Δ, so that E is
y² = x³ − 3E₄x − 2E₆. The formulas follow from Ramanujan's equations, with
D = q d/dq:

> DE₂ = (E₂² − E₄)/12, DE₄ = (E₂E₄ − E₆)/3, DE₆ = (E₂E₆ − E₄²)/2,
> Dj = −jE₆/E₄, D log η(τ) = E₂(τ)/24.

Let f be a root of Ψ_l(F, j), and write partial derivatives of Ψ_l at (f, j)
as Ψ_F, Ψ_J, Ψ_FF, Ψ_FJ, Ψ_JJ. Write Ẽ_k for E_k(lτ).

1. Differentiating Ψ_l(f, j) = 0 gives Df = −Ψ_J Dj/Ψ_F. Let L = Df/f. From
   the definition of f, L = (s/12)(lẼ₂ − E₂).
2. **p₁.** Summing ℘ over the kernel ⟨1/l⟩ of C/(Z + τZ), by its q-expansion,
   gives p₁ = l(lẼ₂ − E₂) = 12lL/s.
3. **Ẽ₄.** Ramanujan's first equation at lτ gives
   l²Ẽ₄ = E₄ + K₁² + 2E₂K₁ − 12DK₁, with K₁ = 12L/s. Differentiating
   Ψ_l(f, j) = 0 twice gives D²f = N + (E₂/6)Df, with
   N = −(Ψ_FF Df² + 2Ψ_FJ Df Dj + Ψ_JJ Dj² + Ψ_J M)/Ψ_F and
   M = j((2/3)E₆²/E₄² + E₄/2). The quasimodular E₂ cancels:

   > l²Ẽ₄ = E₄ + (144/s)((1 + 1/s)L² − N/f).

4. **Δ̃ and j̃.** Since Δ = η²⁴, Δ̃ = Δ f^(12/s)/l¹², and j̃ = Ẽ₄³/Δ̃.
5. **Ẽ₆.** The Fricke involution gives Ψ_l(l^s/f, j̃) = 0, which has its own
   derivative: Dj̃ = Ψ_F L l^s/(f Ψ_J), with the partials now at
   (l^s/f, j̃). Then Ẽ₆ = −Ẽ₄ Dj̃/(l j̃).
6. **The isogenous curve.** The normalized isogeny is z ↦ z from C/(Z + τZ)
   to C/((1/l)Z + τZ), so Ã = −3l⁴Ẽ₄ and B̃ = −2l⁶Ẽ₆.

The step is refused as degenerate when Ψ_F = 0 (a repeated root), when
Ẽ₄, Δ̃ or Ψ_J at the dual point is 0, when j̃ is 0 or 1728, when
l^s/f is not a root of Ψ_l(F, j̃), or when Ẽ₆² ≠ Ẽ₄³ − 1728Δ̃.

**The kernel polynomial.** For y² = x³ + Ax + B,
℘(z) = z⁻² + Σ c_k z^(2k), with c₁ = −A/5, c₂ = −B/7 and
c_k = 3/((k − 2)(2k + 3))·Σ c_h c_(k−1−h). Over the kernel's nonzero
points, the sum of ℘^(2k) is (2k)!(c̃_k − c_k), and
℘^(2k) = T^k(x) with T(Q) = 4(x³ + Ax + B)Q″ + (6x² + 2A)Q′. These give the
power sums of K's roots, from p₁/2 upwards, and Newton's identities give K.

## The certificate and its check

A count's certificate holds, for each Elkies prime l, the kernel polynomial K
and the eigenvalue μ, and a point P on E or on its twist. `check` verifies:

1. **Each residue.** l is an odd prime below p and below 1000, K is monic
   of degree 1 to (l − 1)/2 with coefficients in [0, p), and 1 ≤ μ < l. (The
   bounds keep the check's work bounded.) Modulo K:
   - f_l ≡ 0, where f_k are the division polynomials (f_k = ψ_k for odd k,
     ψ_k/2y for even k). So each root of K is the abscissa of a point of
     order l;
   - with λ = μ or l − μ, whichever is at most (l − 1)/2,
     (x − x^p)·den = num, where x([λ]P) = x − num/den. The denominator is a
     unit modulo K, since no point of order l is also of order λ or 2;
   - (x³ + ax + b)^((p−1)/2)·g = ±f_(2λ), the sign + for μ = λ, where
     y([λ]P) = y·f_(2λ)/g.

   For each root of K there is then a point Q of order l with
   φ(Q) = [μ]Q. Frobenius satisfies φ² − tφ + p = 0, so (μ² − tμ + p)Q = O,
   and t ≡ μ + p/μ (mod l).
2. **t mod 2**, recomputed from gcd(x³ + ax + b, x^p − x).
3. **The candidates.** The Chinese remainder theorem gives t₀ mod M, and
   n = p + 1 − t must satisfy t ≡ t₀ (mod M) and |t| ≤ 2√p. At most 2³²
   candidates may remain, so that step 4's search is bounded.
4. **The point.** P is on its curve, and n·P = O (or (2p + 2 − n)·P = O on
   the twist). Another candidate differs from n by k·M with
   1 ≤ |k| ≤ k_max. A baby-step giant-step check shows that k·(M·P) ≠ O for
   every 1 ≤ k ≤ k_max, so no other candidate annihilates P. The true order
   annihilates P, so n is the true order.

Each step uses only the curve, polynomial arithmetic modulo K and point
arithmetic.

## Validation

Every claim below is reproduced by the test suite, at smaller sizes where it
would be slow.

- **Ψ_l.** For l = 2, 3, 5, 7 and 13, where X₀(l) has genus 0, Ψ_l equals
  the published Hauptmodul relation A(F) − FJ, with A(F) = (F + 16)³,
  (F + 27)(F + 3)³, (F² + 10F + 5)³, (F² + 13F + 49)(F² + 5F + 1)³ and
  (F² + 5F + 13)(F⁴ + 7F³ + 20F² + 19F + 1)³. It also equals an independent
  computation over Q with exact rationals, for l ≤ 17. The fast power sums
  equal a direct computation for l ≤ 47. On 54 curves, Ψ_l(F, j) has as
  many roots in F_p as the classical Φ_l(X, j), for l ≤ 23.
- **Elkies' formulas.** All 647 isogenies found for l = 3 to 43, at p of 20 to
  100 bits, were checked. The kernel polynomial divides ψ_l, and Vélu's
  formulas on it return the same Ã, B̃ and p₁. None was degenerate.
- **Residues.** 195 of 195 equal t mod l from exact counts, for l ≤ 31 at
  p of 24 to 62 bits.
- **Counts.** 20 SEA counts below 2⁶⁴, made to use Elkies primes, equal the
  point-order counts, with every certificate checked.
- **Published orders.** Counted by SEA, secp128r1, brainpoolP160r1, P-192,
  P-224 and P-256 have their published group orders, and `verify_order`
  certifies each order independently.

## Performance

`sea.py` is pure Python. The cost is in CPython's integer multiplication, at
40 to 100 kilobits for the polynomials modulo K and Ψ_l(F, j), and in the
power sums. P-256 took 58 s to count, with 20 Elkies primes up to 181 and 16
Atkin primes, and 14 s to check, on one core. secp128r1 takes 4 s and 1 s,
P-192 36 s and 7 s, and a random 320-bit curve 198 s and 50 s.

## Limits

- **Size.** `ec.count` uses SEA for 2⁶⁴ ≤ p < 2³²⁰ (`ec.SEA_BITS`). A general
  curve above that is CANNOT VERIFY unless its order is published
  (`verify_order`).
- **Atkin primes are not used.** Their partial information about t could
  replace some Elkies primes (Atkin's match-and-sort). They are skipped, so a
  curve with many of them needs larger Elkies primes.
- **Primes up to 1000** (`L_MAX`) are tried. If their Elkies primes do not
  leave at most 2³² candidates (`R_MAX`), the count is CANNOT VERIFY.
- **No point separates the candidates** only if the group's exponent divides
  M·k for some 1 ≤ k ≤ k_max on E and on its twist. The count is then CANNOT
  VERIFY. This has not been seen.
- The search raises `SEAError` if a kernel polynomial from the formulas has
  no Frobenius eigenvalue, or if no candidate annihilates a point. Either
  would be a defect in pq-verify, not a property of the curve.
