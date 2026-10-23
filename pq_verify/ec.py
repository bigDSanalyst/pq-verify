"""Elliptic curves over prime fields, with exact point counts that carry
certificates (ECC.md).

E: y^2 = x^3 + a x + b over F_p, p > 3 prime. #E(F_p) is found by

* direct counting, for p below 2^16;
* complex multiplication, for j = 0 and j = 1728, at any size: Cornacchia's
  algorithm gives the possible traces, and points rule out all but one;
* baby-step giant-step on E and on its quadratic twist (Mestre), for other
  curves up to 2^64: exact point orders, combined by the Chinese remainder
  theorem, leave one order in the Hasse interval;
* Schoof-Elkies-Atkin (pq_verify.sea, SEA.md), for other curves above 2^64
  and below 2^SEA_BITS: t modulo Elkies primes, each residue certified by
  a kernel polynomial and Frobenius' eigenvalue on it.

A count is a Count(n, method, certificate), and check_count verifies the
certificate from the curve without the method that found it. A published
order (a standard curve's) is verified by verify_order, by the same kind of
certificate, without counting. Anything else is CANNOT VERIFY (None).
"""

import math
import random

NAIVE_LIMIT = 1 << 16          # count directly below this p
BSGS_LIMIT = 1 << 64           # baby-step giant-step below this p
SEA_BITS = 320                 # Schoof-Elkies-Atkin for p of at most this many bits


class ECError(ValueError):
    """A curve or point that is not what it claims to be."""


# ---- integers: primality, factors, square roots ------------------------------

_SMALL_PRIMES = [q for q in range(2, 1000) if all(q % d for d in range(2, math.isqrt(q) + 1))]
# Miller-Rabin with these bases is a proof of primality below 3.3 x 10^24
# (Sorenson and Webster, 2015).
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
_MR_PROOF_LIMIT = 3317044064679887385961981


def _strong_probable_prime(n, base):
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(base, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


def jacobi(a, n):
    """The Jacobi symbol (a / n), n odd and positive."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be odd and positive")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def _strong_lucas_probable_prime(n):
    """The strong Lucas test with Selfridge's parameters (method A); n odd,
    not a square, with no small factor."""
    D = 5
    while True:
        j = jacobi(D, n)
        if j == -1:
            break
        if j == 0 and abs(D) != n:
            return False
        D = -D - 2 if D > 0 else -D + 2
    P, Q = 1, (1 - D) // 4
    d, s = n + 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    U, V, Qk = 1, P % n, Q % n                 # U_1, V_1, Q^1
    for bit in bin(d)[3:]:
        U, V, Qk = U * V % n, (V * V - 2 * Qk) % n, Qk * Qk % n        # k -> 2k
        if bit == "1":                                                 # 2k -> 2k + 1
            U, V = P * U + V, D * U + P * V
            U = (U + n if U % 2 else U) // 2 % n
            V = (V + n if V % 2 else V) // 2 % n
            Qk = Qk * Q % n
    if U == 0 or V == 0:
        return True
    for _ in range(s - 1):
        V, Qk = (V * V - 2 * Qk) % n, Qk * Qk % n
        if V == 0:
            return True
    return False


def is_prime(n):
    """n is prime: proved by Miller-Rabin below 3.3 x 10^24, and beyond by
    the Baillie-PSW test (Miller-Rabin base 2 and a strong Lucas test), which
    no known composite passes."""
    if n < 2:
        return False
    for q in _SMALL_PRIMES:
        if n % q == 0:
            return n == q
    if n < _MR_PROOF_LIMIT:
        return all(_strong_probable_prime(n, b) for b in _MR_BASES)
    r = math.isqrt(n)
    if r * r == n:
        return False
    return _strong_probable_prime(n, 2) and _strong_lucas_probable_prime(n)


def _rho(n, rng):
    """A nontrivial factor of the odd composite n (Pollard-Brent)."""
    while True:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g = r = q = 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g


def factor(n, rng=None):
    """The prime factorization of n >= 1, {prime: exponent}, each factor
    checked by is_prime."""
    rng = rng or random.Random(n)
    out = {}
    for q in _SMALL_PRIMES:
        while n % q == 0:
            out[q] = out.get(q, 0) + 1
            n //= q
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if is_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        r = math.isqrt(m)
        if r * r == m:
            stack += [r, r]
            continue
        d = _rho(m, rng)
        stack += [d, m // d]
    return dict(sorted(out.items()))


def largest_prime_factor(n, steps=1 << 18, rng=None):
    """The largest prime factor of n >= 2, or None if Pollard-Brent rho does
    not split a composite part within `steps` iterations. factor() has no
    bound, and a group order with two large prime factors would keep it
    searching: an audit asks this instead and says when it could not tell."""
    rng = rng or random.Random(n)
    best = 1
    for q in _SMALL_PRIMES:
        while n % q == 0:
            best, n = q, n // q
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if is_prime(m):
            best = max(best, m)
            continue
        r = math.isqrt(m)
        if r * r == m:
            stack.append(r)
            continue
        d = _rho_bounded(m, rng, steps)
        if d is None:
            return None
        stack += [d, m // d]
    return best if best > 1 else None


def _rho_bounded(n, rng, steps):
    """A nontrivial factor of the odd composite n by Pollard-Brent, or None
    after `steps` iterations of the map."""
    used = 0
    while used < steps:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g = r = q = 1
        x = ys = y
        while g == 1 and used < steps:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            used += r
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            used += r
            r *= 2
        if g == 1:
            return None
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g
    return None


def sqrt_mod(n, p):
    """A square root of n mod the odd prime p (Tonelli-Shanks), or None."""
    n %= p
    if n == 0:
        return 0
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def cornacchia(d, p):
    """(u, v) with u^2 + d v^2 = p and u, v > 0, for the prime p, or None if
    there is none (Cornacchia's algorithm)."""
    r0 = sqrt_mod(-d, p)
    if r0 is None:
        return None
    if 2 * r0 < p:
        r0 = p - r0
    a, b = p, r0
    limit = math.isqrt(p)
    while b > limit:
        a, b = b, a % b
    rest = p - b * b
    if rest % d:
        return None
    v = math.isqrt(rest // d)
    if v * v != rest // d or v == 0 or b == 0:
        return None
    return b, v


# ---- the curve --------------------------------------------------------------------

class Curve:
    """y^2 = x^3 + a x + b over F_p, p > 3 prime, nonsingular, 0 <= a, b < p.
    Points are (x, y) with 0 <= x, y < p, and None for the point at
    infinity."""

    def __init__(self, a, b, p):
        if not (isinstance(p, int) and p > 3 and is_prime(p)):
            raise ECError(f"p = {p} is not a prime above 3")
        if not (0 <= a < p and 0 <= b < p):
            raise ECError("a and b must lie in [0, p)")
        if (4 * a * a * a + 27 * b * b) % p == 0:
            raise ECError("the curve is singular: 4a^3 + 27b^2 = 0 mod p")
        self.a, self.b, self.p = a, b, p

    def __repr__(self):
        return f"Curve(a={self.a}, b={self.b}, p={self.p})"

    @property
    def j(self):
        a, b, p = self.a, self.b, self.p
        return 1728 * 4 * a ** 3 * pow(4 * a ** 3 + 27 * b * b, -1, p) % p

    def is_on(self, P):
        if P is None:
            return True
        if not (isinstance(P, tuple) and len(P) == 2):
            return False
        x, y = P
        p = self.p
        if not (isinstance(x, int) and isinstance(y, int) and 0 <= x < p and 0 <= y < p):
            return False
        return (y * y - (x * x * x + self.a * x + self.b)) % p == 0

    def neg(self, P):
        return None if P is None else (P[0], (-P[1]) % self.p)

    def add(self, P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        p = self.p
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2:
            if (y1 + y2) % p == 0:
                return None
            lam = (3 * x1 * x1 + self.a) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    def mul(self, k, P):
        if k < 0:
            k, P = -k, self.neg(P)
        R = None
        while k:
            if k & 1:
                R = self.add(R, P)
            P = self.add(P, P)
            k >>= 1
        return R

    def lift_x(self, x):
        y = sqrt_mod(x * x * x + self.a * x + self.b, self.p)
        return None if y is None else (x % self.p, y)

    def random_point(self, rng):
        while True:
            P = self.lift_x(rng.randrange(self.p))
            if P is not None:
                return P if rng.random() < 0.5 else self.neg(P)

    def twist(self):
        """The quadratic twist y^2 = x^3 + a d^2 x + b d^3, d the least
        quadratic non-residue mod p: #E + #E' = 2p + 2."""
        p = self.p
        d = 2
        while pow(d, (p - 1) // 2, p) != p - 1:
            d += 1
        return Curve(self.a * d * d % p, self.b * d * d * d % p, p)

    def hasse(self):
        """The Hasse interval [p + 1 - floor(2 sqrt p), p + 1 + floor(2 sqrt p)]."""
        w = math.isqrt(4 * self.p)
        return self.p + 1 - w, self.p + 1 + w


def point_order(E, P, multiple, factors=None):
    """The order of P on E, given a multiple of it (multiple * P = O) and
    optionally the multiple's factorization."""
    if E.mul(multiple, P) is not None:
        raise ECError("not a multiple of the point's order")
    factors = factors or factor(multiple)
    m = multiple
    for q in factors:
        while m % q == 0 and E.mul(m // q, P) is None:
            m //= q
    return m


# ---- counts and their certificates -----------------------------------------------

class Count:
    """n = #E(F_p), found by method ('naive', 'cm', 'orders' or 'sea'), with
    the certificate check_count verifies."""

    def __init__(self, n, method, certificate):
        self.n, self.method, self.certificate = n, method, certificate

    @property
    def trace(self):
        return None if self.n is None else self.certificate["p"] + 1 - self.n

    def __repr__(self):
        return f"Count({self.n}, {self.method!r})"


def _naive(E):
    p, n = E.p, 1
    for x in range(p):
        r = (x * x * x + E.a * x + E.b) % p
        n += 1 if r == 0 else (2 if pow(r, (p - 1) // 2, p) == 1 else 0)
    return n


def _cm_traces(E):
    """The traces complex multiplication allows for j = 0 (a = 0) and
    j = 1728 (b = 0), and the representation of p they come from; None for
    any other j. Supersingular cases (p = 2 mod 3 and p = 3 mod 4) have
    trace 0 alone."""
    p = E.p
    if E.a == 0:
        if p % 3 == 2:
            return {0}, None
        u, v = cornacchia(3, p)                  # p = u^2 + 3 v^2
        return {2 * u, -2 * u, u + 3 * v, -(u + 3 * v), u - 3 * v, -(u - 3 * v)}, (3, u, v)
    if E.b == 0:
        if p % 4 == 3:
            return {0}, None
        u, v = cornacchia(1, p)                  # p = u^2 + v^2
        return {2 * u, -2 * u, 2 * v, -2 * v}, (1, u, v)
    return None


def _crt_in(lo, hi, conditions):
    """The integers N in [lo, hi] with N = r mod m for each (r, m), or None
    when there are more than two (so not unique)."""
    r, m = 0, 1
    for ri, mi in conditions:
        g = math.gcd(m, mi)
        if (ri - r) % g:
            return []
        l = m // g * mi
        k = ((ri - r) // g) * pow(m // g, -1, mi // g) % (mi // g) if mi // g > 1 else 0
        r, m = (r + m * k) % l, l
    first = lo + (r - lo) % m
    out = []
    while first <= hi and len(out) < 3:
        out.append(first)
        first += m
    return out


def _bsgs_multiple(E, P, lo, hi):
    """Some N in [lo, hi] with N P = O, by baby-step giant-step; None if
    there is none."""
    width = hi - lo
    w = math.isqrt(width) + 1
    baby, cur = {}, None
    for j in range(w):                           # -(j P) -> j
        key = E.neg(cur)
        baby.setdefault(key, j)
        cur = E.add(cur, P)
    step = E.mul(w, P)
    g = E.mul(lo, P)
    for i in range(width // w + 2):
        if g in baby:
            n = lo + i * w + baby[g]
            if n <= hi and E.mul(n, P) is None:
                return n
        g = E.add(g, step)
    return None


def count(E, rng=None, max_points=40):
    """#E(F_p) with its certificate, or None (CANNOT VERIFY): direct counting
    below NAIVE_LIMIT, complex multiplication for j = 0 and 1728,
    baby-step giant-step on E and its twist below BSGS_LIMIT, and
    Schoof-Elkies-Atkin up to SEA_BITS bits."""
    rng = rng or random.Random(E.p * 1000003 + E.a * 7919 + E.b)
    p = E.p
    if p < NAIVE_LIMIT:
        n = _naive(E)
        return Count(n, "naive", {"p": p})
    cm = _cm_traces(E)
    if cm is not None:
        traces, rep = cm
        cands = sorted(p + 1 - t for t in traces)
        points = []
        alive = set(cands)
        for _ in range(max_points):
            if len(alive) == 1:
                break
            P = E.random_point(rng)
            killed = {N for N in alive if E.mul(N, P) is not None}
            if killed:
                points.append(P)
                alive -= killed
        if len(alive) != 1:
            return None
        n = alive.pop()
        # One point the answer annihilates, so the checker sees it work.
        P = E.random_point(rng)
        return Count(n, "cm", {"p": p, "representation": rep, "points": points, "witness": P})
    if p >= BSGS_LIMIT:
        if p.bit_length() > SEA_BITS:
            return None
        from . import sea
        return sea.count(E, rng)
    lo, hi = E.hasse()
    twist = E.twist()
    orders = {"E": [], "twist": []}
    l_e = l_t = 1
    for k in range(max_points):
        on, curve = ("E", E) if k % 2 == 0 else ("twist", twist)
        P = curve.random_point(rng)
        n0 = _bsgs_multiple(curve, P, lo, hi)
        if n0 is None:
            return None                      # impossible for a correct curve
        fac = factor(n0, rng)
        m = point_order(curve, P, n0, fac)
        orders[on].append((P, m, {q: e for q, e in factor(m, rng).items()}))
        if on == "E":
            l_e = l_e * m // math.gcd(l_e, m)
        else:
            l_t = l_t * m // math.gcd(l_t, m)
        sols = _crt_in(lo, hi, [(0, l_e), ((2 * p + 2) % l_t, l_t)])
        if len(sols) == 1:
            return Count(sols[0], "orders", {"p": p, "E": orders["E"], "twist": orders["twist"]})
    return None


def _check_order(E, P, m, fac):
    """m is the exact order of the point P (not O) on E, and fac its prime
    factorization."""
    if P is None or not E.is_on(P) or not isinstance(fac, dict) or not fac:
        return False
    prod = 1
    for q, e in fac.items():
        if not (isinstance(q, int) and isinstance(e, int) and e > 0 and is_prime(q)):
            return False
        prod *= q ** e
    if prod != m or E.mul(m, P) is not None:
        return False
    return all(E.mul(m // q, P) is not None for q in fac)


def check_count(E, c):
    """True iff c's certificate proves #E(F_p) = c.n, verified from E
    alone: a direct recount ('naive'); a representation of p, the traces
    complex multiplication allows from it, a point the count annihilates and
    points ruling out every other trace ('cm'); exact point orders on E
    and on its twist leaving c.n the only order in the Hasse interval
    ('orders'); or the trace modulo primes l, each from a kernel polynomial
    dividing the l-division polynomial and Frobenius' eigenvalue on it, and
    a point that separates the candidates left ('sea')."""
    if not isinstance(c, Count) or not isinstance(c.n, int):
        return False
    cert = c.certificate
    p = E.p
    if not isinstance(cert, dict) or cert.get("p") != p:
        return False
    lo, hi = E.hasse()
    if not lo <= c.n <= hi:
        return False
    if c.method == "naive":
        # A recount by another route: x^3 + a x + b's values, squared roots.
        squares = {}
        for y in range(p):
            s = y * y % p
            squares[s] = squares.get(s, 0) + 1
        return c.n == 1 + sum(squares.get((x * x * x + E.a * x + E.b) % p, 0) for x in range(p))
    if c.method == "cm":
        if (E.a == 0) == (E.b == 0):
            return False
        rep = cert.get("representation")
        if rep is None:
            traces = {0}
            if not ((E.a == 0 and p % 3 == 2) or (E.b == 0 and p % 4 == 3)):
                return False
        else:
            d, u, v = rep
            if d != (3 if E.a == 0 else 1) or u * u + d * v * v != p or u <= 0 or v <= 0:
                return False
            traces = ({2 * u, -2 * u, u + 3 * v, -(u + 3 * v), u - 3 * v, -(u - 3 * v)}
                      if d == 3 else {2 * u, -2 * u, 2 * v, -2 * v})
        if p + 1 - c.n not in traces:
            return False
        w = cert.get("witness")
        if w is None or not E.is_on(w) or E.mul(c.n, w) is not None:
            return False
        others = {p + 1 - t for t in traces} - {c.n}
        for P in cert.get("points", []):
            if not E.is_on(P):
                return False
            others = {N for N in others if E.mul(N, P) is None}
        return not others
    if c.method == "orders":
        twist = E.twist()
        conds = []
        for on, curve, target in (("E", E, 0), ("twist", twist, 2 * p + 2)):
            l = 1
            for item in cert.get(on, []):
                P, m, fac = item
                if not _check_order(curve, P, m, fac):
                    return False
                l = l * m // math.gcd(l, m)
            conds.append((target % l, l))
        return _crt_in(lo, hi, conds) == [c.n]
    if c.method == "sea":
        from . import sea
        return sea.check(E, c)
    return False


def verify_order(E, n, rng=None, points=4):
    """A certificate that #E(F_p) = n, for a published order n, or None:
    n is in the Hasse interval, it annihilates random points, and their
    exact orders leave n the only such multiple in the interval. For a prime
    n above 4 sqrt p one point suffices; a cofactor needs points whose
    orders together exceed the interval's width."""
    rng = rng or random.Random(n)
    lo, hi = E.hasse()
    if not lo <= n <= hi:
        return None
    fac = factor(n, rng)
    items, l = [], 1
    for _ in range(points):
        P = E.random_point(rng)
        if E.mul(n, P) is not None:
            return None                      # n is not the order
        m = point_order(E, P, n, fac)
        items.append((P, m, factor(m, rng)))
        l = l * m // math.gcd(l, m)
        if len(_crt_in(lo, hi, [(0, l)])) == 1:
            c = Count(n, "orders", {"p": E.p, "E": items, "twist": []})
            return c if check_count(E, c) else None
    return None
