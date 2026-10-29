"""Schoof-Elkies-Atkin point counting for large prime fields, with Elkies
primes, and a certificate checked from the curve alone (docs/SEA.md).

For E: y^2 = x^3 + a x + b over F_p with j(E) != 0, 1728, count(E) finds
#E(F_p) = p + 1 - t:

1. t mod 2, from whether x^3 + a x + b has a root in F_p.
2. For odd primes l: Mueller's canonical modular polynomial Psi_l(F, J) mod p,
   from q-expansions. If Psi_l(F, j(E)) has a root in F_p, l is an Elkies
   prime: E has an F_p-rational l-isogeny. Elkies' formulas give the
   isogenous curve and the kernel polynomial K, of degree (l - 1)/2, and
   Frobenius acts on the kernel as multiplication by some mu, so
   t = mu + p/mu (mod l).
3. The Chinese remainder theorem gives t mod M, and baby-step giant-step on
   a point finds the one candidate in the Hasse interval.

Step 2 is a search, and nothing in the certificate rests on it. check()
verifies, for each l, that K divides the l-division polynomial and that
Frobenius acts on the points of ker K as mu (both computed modulo K), and
that a point P has n P = O while (k M) P != O for every k that would give
another candidate."""

import decimal
import functools
import math
import random

from . import ec

try:                                   # the C implementation of decimal, whose
    import _decimal                    # multiplication is a number-theoretic transform
except ImportError:                    # pragma: no cover (PyPy, minimal builds)
    _decimal = None
_HAVE_NTT = _decimal is not None

_SCHOOL = 10                 # schoolbook multiplication below this many terms
_NTT_BITS = 1 << 19          # decimal multiplication from this many bits per operand
_NEWTON = 8                  # Newton reduction modulo polynomials of this degree and up
R_MAX = 1 << 32              # largest candidate set baby-step giant-step searches
L_MAX = 1000                 # largest prime l tried


class SEAError(ec.ECError):
    """An inconsistency in the search: a defect, never an answer."""


# ---- polynomials over F_p -------------------------------------------------------
# Lists of ints in [0, p), lowest degree first, no trailing zeros ([] is 0).

def _trim(a):
    while a and not a[-1]:
        a.pop()
    return a


def _mul(a, b, p):
    """a b over F_p."""
    la, lb = len(a), len(b)
    if not la or not lb:
        return []
    n = min(la, lb)
    if n < _SCHOOL:
        out = [0] * (la + lb - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] += x * y
        return _trim([x % p for x in out])
    if min(a) < 0 or min(b) < 0 or max(a) >= p or max(b) >= p:
        raise SEAError("coefficients must lie in [0, p)")   # a slot could overflow
    bits = 2 * p.bit_length() + n.bit_length() + 1      # a slot holds n (p - 1)^2
    if _HAVE_NTT and n * bits >= _NTT_BITS:
        return _mul_ntt(a, b, p, n)
    nb = (bits + 7) // 8
    A = int.from_bytes(b"".join([x.to_bytes(nb, "little") for x in a]), "little")
    B = A if b is a else int.from_bytes(b"".join([x.to_bytes(nb, "little") for x in b]), "little")
    m = la + lb - 1
    C = (A * B).to_bytes(nb * m, "little")
    return _trim([int.from_bytes(C[i * nb:(i + 1) * nb], "little") % p for i in range(m)])


def _mul_ntt(a, b, p, n):
    """a b by Kronecker substitution in base 10, multiplied by decimal's
    number-theoretic transform: exact, since the context's precision holds
    the whole product and any rounding raises."""
    k = len(str(n * (p - 1) * (p - 1)))
    fmt = "%0" + str(k) + "d"
    sa = "".join([fmt % x for x in reversed(a)])
    sb = sa if b is a else "".join([fmt % x for x in reversed(b)])
    ctx = decimal.Context(prec=len(sa) + len(sb), Emax=decimal.MAX_EMAX, Emin=decimal.MIN_EMIN,
                          traps=[decimal.Inexact, decimal.Rounded, decimal.Overflow,
                                 decimal.InvalidOperation])
    s = str(ctx.multiply(decimal.Decimal(sa), decimal.Decimal(sb)))
    m = len(a) + len(b) - 1
    s = s.zfill(k * m)
    top = len(s)
    return _trim([int(s[top - (i + 1) * k:top - i * k]) % p for i in range(m)])


def _low(a, b, n, p):
    """a b mod x^n."""
    return _trim(_mul(a[:n], b[:n], p)[:n])


def _add(a, b, p):
    if len(a) < len(b):
        a, b = b, a
    out = list(a)
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % p
    return _trim(out)


def _sub(a, b, p):
    out = list(a) + [0] * (len(b) - len(a))
    for i, x in enumerate(b):
        out[i] = (out[i] - x) % p
    return _trim(out)


def _neg(a, p):
    return [(-x) % p for x in a]


def _scale(a, c, p):
    c %= p
    return _trim([x * c % p for x in a]) if c else []


def _deriv(a, p):
    return _trim([i * a[i] % p for i in range(1, len(a))])


def _eval(a, x, p):
    r = 0
    for c in reversed(a):
        r = (r * x + c) % p
    return r


def _inv_series(a, n, p):
    """1/a mod x^n, a[0] != 0 (Newton)."""
    r = [pow(a[0], -1, p)]
    k = 1
    while k < n:
        k = min(2 * k, n)
        e = _low(a, r, k, p)
        e = [(-x) % p for x in e] + [0] * (k - len(e))
        e[0] = (e[0] + 2) % p
        r = _low(r, e, k, p)
    return r


def _divmod(a, b, p):
    """(q, r), a = q b + r, deg r < deg b (schoolbook)."""
    if not b:
        raise ZeroDivisionError("division by the zero polynomial")
    a = list(a)
    db = len(b) - 1
    if len(a) <= db:
        return [], _trim(a)
    inv = pow(b[-1], -1, p)
    q = [0] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] * inv % p
        if c:
            q[i - db] = c
            for j in range(db):
                a[i - db + j] = (a[i - db + j] - c * b[j]) % p
        a[i] = 0
    return _trim(q), _trim(a[:db])


def _monic(a, p):
    return _scale(a, pow(a[-1], -1, p), p) if a else a


def _gcd(a, b, p):
    a, b = _trim(list(a)), _trim(list(b))
    while b:
        a, b = b, _divmod(a, b, p)[1]
    return _monic(a, p)


class _Mod:
    """Arithmetic in F_p[x]/(m), m monic of degree d >= 1: Newton
    reduction (the quotient from the reversed polynomials) at degree
    _NEWTON and up."""

    def __init__(self, m, p):
        if not m or m[-1] != 1 or len(m) < 2:
            raise SEAError("modulus must be monic and nonconstant")
        self.m, self.p, self.d = m, p, len(m) - 1
        self.rinv = _inv_series(m[::-1], self.d, p) if self.d >= _NEWTON else None

    def reduce(self, c):
        d, p = self.d, self.p
        n = len(c)
        while n and not c[n - 1]:
            n -= 1
        if n < len(c):
            c = c[:n]
        if n <= d:
            return c
        if self.rinv is None or len(c) > 2 * d:
            return _divmod(c, self.m, p)[1]
        k = len(c) - d                                   # quotient length, <= d
        q = _low(c[::-1][:k], self.rinv, k, p)
        q = q + [0] * (k - len(q))
        q.reverse()
        qm = _mul(_trim(q), self.m, p)
        return _trim([(c[i] - (qm[i] if i < len(qm) else 0)) % p for i in range(d)])

    def mul(self, a, b):
        return self.reduce(_mul(a, b, self.p))

    def pow(self, a, e):
        r, a = [1], self.reduce(list(a))
        for bit in bin(e)[2:]:
            r = self.mul(r, r)
            if bit == "1":
                r = self.mul(r, a)
        return r

    def frobenius_x(self):
        """x^p mod m, by squaring and shifting."""
        p, r = self.p, [1]
        for bit in bin(p)[2:]:
            r = self.mul(r, r)
            if bit == "1":
                r = self.reduce([0] + r)
        return r


def _a_root(g, p, rng):
    """A root in F_p of g, a product of distinct linear factors (Cantor-Zassenhaus)."""
    g = _monic(g, p)
    while len(g) > 2:
        ring = _Mod(g, p)
        while True:
            h = _gcd(g, _sub(ring.pow([rng.randrange(p), 1], (p - 1) // 2), [1], p), p)
            if 1 < len(h) < len(g):
                break
        if 2 * (len(h) - 1) > len(g) - 1:
            h = _divmod(g, h, p)[0]
        g = _monic(h, p)
    return (-g[0]) % p


# ---- Mueller's canonical modular polynomial mod p ----------------------------------------
# f(tau) = l^s (eta(l tau)/eta(tau))^(2s), s = 12/gcd(12, l - 1), v = s(l - 1)/12.
# Psi_l(F, j(tau)) = prod (F - c) over f's l + 1 conjugates c: f itself, a
# power series in q with a zero of order v, and G(zeta^k w), w = q^(1/l),
# G(x) = x^-v E(x)^(2s) / E(x^l)^(2s), E(x) = prod (1 - x^n).

def _params(l):
    s = 12 // math.gcd(12, l - 1)
    return s, s * (l - 1) // 12


def _euler(n, p):
    """E(x) = prod (1 - x^k) to x^(n-1): Euler's pentagonal numbers."""
    c = [0] * n
    c[0] = 1
    k = 1
    while k * (3 * k - 1) // 2 < n:
        sgn = p - 1 if k % 2 else 1
        for g in (k * (3 * k - 1) // 2, k * (3 * k + 1) // 2):
            if g < n:
                c[g] = sgn
        k += 1
    return c


def _series_pow(a, e, n, p):
    r, base = [1], _trim(a[:n])
    while e:
        if e & 1:
            r = _low(r, base, n, p)
        e >>= 1
        if e:
            base = _low(base, base, n, p)
    return r


def _pad(a, n):
    return a + [0] * (n - len(a))


def _j_powers(T, p):
    """jp[d][t], the coefficient of q^-t in j(q)^d, for 0 <= t <= d <= T."""
    def sigma3(k):
        return sum(d ** 3 for d in range(1, k + 1) if k % d == 0)
    n = T + 1
    e4 = [1] + [240 * sigma3(k) % p for k in range(1, n)]
    e4 = _low(_low(e4, e4, n, p), e4, n, p)
    delta = _series_pow(_euler(n, p), 24, n, p)
    qj = _pad(_low(e4, _inv_series(delta, n, p), n, p), n)     # q j(q)
    jp, b = [[1]], [1]
    for d in range(1, T + 1):
        b = _pad(_low(b, qj, n, p), n)
        jp.append([b[d - t] for t in range(d + 1)])
    return jp


def _power_sums(l, p):
    """[P_1, ..., P_(l+1)]: P_m(J), the sum of the m-th powers of the roots
    of Psi_l(F, J), as a polynomial in J (lowest degree first).

    The conjugate f has a zero at the cusp, so P_m(j) has the principal part
    and constant term of the trace of G^m, l U(G^m): the coefficients of
    E(x)^(2sm) at x^(mv - lt), t = 0..floor(mv/l), times E(q)^(-2sm). With
    m = b c + a, E^(2sb c) and E^(2s a) are computed by multiplication and
    each needed coefficient is one dot product."""
    s, v = _params(l)
    N = (l + 1) * v + 1
    P1 = _pad(_series_pow(_euler(N, p), 2 * s, N, p), N)       # E(x)^(2s)
    b = max(1, math.isqrt(l + 1))
    baby = [_pad([1], N)]
    for _ in range(b):
        baby.append(_pad(_low(baby[-1], P1, N, p), N))
    T = v + 1
    qinv = _inv_series(P1[:T], T, p)                           # E(q)^(-2s)
    jp = _j_powers(T, p)
    sums = []
    giant, qm, c = baby[0], [1], 0
    while True:
        for a in range(b):
            m = b * c + a
            if m == 0:
                continue
            if m > l + 1:
                return sums
            Ba = baby[a]
            Tm = m * v // l
            coef = []
            for t in range(Tm + 1):
                k = m * v - l * t
                coef.append(sum(map(int.__mul__, giant[:k + 1], Ba[k::-1])) % p)
            qm = _pad(_low(qm, qinv, T, p), T)
            pp = [l * sum(coef[t + r] * qm[r] for r in range(Tm - t + 1)) % p for t in range(Tm + 1)]
            poly = [0] * (Tm + 1)
            for d in range(Tm, -1, -1):                       # principal part -> polynomial in j
                x = pp[d]
                poly[d] = x
                if x:
                    jd = jp[d]
                    for t in range(d + 1):
                        pp[t] = (pp[t] - x * jd[t]) % p
            sums.append(_trim(poly))
        c += 1
        giant = _pad(_low(giant, baby[b], N, p), N)


def _taylor(poly, x0, order, p):
    """The Taylor coefficients of poly at x0, to (x - x0)^(order - 1)."""
    out, cur, fact = [], list(poly), 1
    for k in range(order):
        if k:
            fact = fact * k % p
        out.append(_eval(cur, x0, p) * pow(fact, -1, p) % p)
        cur = _deriv(cur, p)
    return out


def _psi_at(sums, l, J0, order, p):
    """[Psi_l(F, J0), d/dJ, (1/2) d^2/dJ^2, ...] to the given order, each a
    polynomial in F: Newton's identities, over F_p[e]/(e^order), on the
    power sums at J = J0 + e."""
    pm = [_taylor(poly, J0, order, p) for poly in sums]
    E = [[1] + [0] * (order - 1)]
    for i in range(1, l + 2):
        acc = [0] * order
        for k in range(1, i + 1):
            x, y = E[i - k], pm[k - 1]
            sg = 1 if k % 2 else -1
            for r in range(order):
                if x[r]:
                    xr = sg * x[r]
                    for u in range(order - r):
                        acc[r + u] += xr * y[u]
        inv = pow(i, -1, p)
        E.append([z * inv % p for z in acc])
    out = []
    for r in range(order):
        poly = [0] * (l + 2)
        for i in range(l + 2):
            poly[l + 1 - i] = E[i][r] if i % 2 == 0 else (-E[i][r]) % p
        out.append(_trim(poly))
    return out


# ---- Elkies' step ------------------------------------------------------------------------

def _isogenous(a, b, p, l, sums, f, j):
    """(A~, B~, p1) for the root f of Psi_l(F, j): the normalized
    l-isogenous curve y^2 = x^3 + A~ x + B~ and p1, the sum of the
    abscissas of the kernel's l - 1 nonzero points; None when degenerate.
    Derived in docs/SEA.md from Ramanujan's equations."""
    s, _ = _params(l)
    inv = lambda x: pow(x % p, -1, p)
    E4, E6 = -a * inv(3) % p, -b * inv(2) % p
    delta = (E4 ** 3 - E6 * E6) * inv(1728) % p
    U0, U1, U2 = _psi_at(sums, l, j, 3, p)
    PF, PFF = _eval(_deriv(U0, p), f, p), _eval(_deriv(_deriv(U0, p), p), f, p)
    PJ, PFJ, PJJ = _eval(U1, f, p), _eval(_deriv(U1, p), f, p), 2 * _eval(U2, f, p) % p
    if PF == 0 or f == 0:
        return None
    Dj = -j * E6 * inv(E4) % p
    Df = -PJ * Dj * inv(PF) % p
    L = Df * inv(f) % p                                          # D log f
    Mj = j * (2 * E6 * E6 * inv(3 * E4 * E4) + E4 * inv(2)) % p
    N = -(PFF * Df * Df + 2 * PFJ * Df * Dj + PJJ * Dj * Dj + PJ * Mj) * inv(PF) % p
    Et4 = (E4 + 144 * inv(s) * ((inv(s) + 1) * L * L - N * inv(f))) * inv(l * l) % p
    Dt = delta * pow(f, 12 // s, p) * inv(pow(l, 12, p)) % p
    if Et4 == 0 or Dt == 0:
        return None
    jt = pow(Et4, 3, p) * inv(Dt) % p
    if jt == 0 or jt == 1728 % p:
        return None
    Fs = pow(l, s, p) * inv(f) % p                              # the root over the isogenous curve
    V0, V1 = _psi_at(sums, l, jt, 2, p)
    if _eval(V0, Fs, p):
        return None
    PFs, PJs = _eval(_deriv(V0, p), Fs, p), _eval(V1, Fs, p)
    if PJs == 0:
        return None
    Djt = PFs * Fs * L * inv(PJs) % p
    Et6 = -Et4 * Djt * inv(l * jt) % p
    if (Et6 * Et6 - pow(Et4, 3, p) + 1728 * Dt) % p:
        return None
    return -3 * pow(l, 4, p) * Et4 % p, -2 * pow(l, 6, p) * Et6 % p, 12 * l * L * inv(s) % p


def _weierstrass(A, B, n, p):
    """c_1..c_n: wp(z) = z^-2 + sum c_k z^(2k) for y^2 = x^3 + A x + B."""
    c = [0] * (n + 1)
    if n >= 1:
        c[1] = -A * pow(5, -1, p) % p
    if n >= 2:
        c[2] = -B * pow(7, -1, p) % p
    for k in range(3, n + 1):
        acc = sum(c[h] * c[k - 1 - h] for h in range(1, k - 1))
        c[k] = 3 * acc * pow((k - 2) * (2 * k + 3), -1, p) % p
    return c


def _kernel(A, B, At, Bt, p1, l, p):
    """The kernel polynomial of the normalized isogeny E -> E~ of degree
    l, monic of degree d = (l - 1)/2: the power sums of its roots from the
    two curves' Weierstrass expansions, sum over the kernel of
    wp^(2k) = (2k)! (c~_k - c_k), wp^(2k) = T^k(x),
    T(Q) = 4(x^3 + A x + B) Q'' + (6 x^2 + 2 A) Q'."""
    d = (l - 1) // 2
    c, ct = _weierstrass(A, B, d, p), _weierstrass(At, Bt, d, p)
    inv2 = pow(2, -1, p)
    s = [d % p, p1 * inv2 % p]
    Q = [0, 1]
    f = _trim([4 * B % p, 4 * A % p, 0, 4])
    g = _trim([2 * A % p, 0, 6])
    fact = 1
    for k in range(1, d):
        Q = _add(_mul(_deriv(_deriv(Q, p), p), f, p), _mul(_deriv(Q, p), g, p), p)
        fact = fact * (2 * k - 1) * (2 * k) % p
        rhs = fact * (ct[k] - c[k]) * inv2 % p
        known = sum(Q[m] * s[m] for m in range(k + 1)) % p
        s.append((rhs - known) * pow(Q[k + 1], -1, p) % p)
    e = [1]
    for i in range(1, d + 1):
        acc = sum((e[i - m] * s[m] if m % 2 else -e[i - m] * s[m]) for m in range(1, i + 1))
        e.append(acc * pow(i, -1, p) % p)
    return _trim([(e[d - i] if (d - i) % 2 == 0 else -e[d - i]) % p for i in range(d + 1)])


# ---- Frobenius on the kernel ----------------------------------------------------------------

class _Division:
    """The division polynomials modulo the ring's modulus K, computed as far
    as they are asked for: f_k = psi_k for odd k and psi_k / (2y) for even
    k, so every f_k is a polynomial in x, with F = 4(x^3 + a x + b) =
    (2y)^2."""

    def __init__(self, a, b, p, ring):
        md = ring.reduce
        self.ring, self.p = ring, p
        self.F = md(_trim([4 * b % p, 4 * a % p, 0, 4]))
        self.F2 = ring.mul(self.F, self.F)
        self.f = [[], [1], [1], md(_trim([(-a * a) % p, 12 * b % p, 6 * a % p, 0, 3])),
                  md(_trim([2 * (-8 * b * b - a ** 3) % p, 2 * (-4 * a * b) % p,
                            2 * (-5 * a * a) % p, 40 * b % p, 10 * a % p, 0, 2]))]

    def __getitem__(self, n):
        f, mm, p = self.f, self.ring.mul, self.p
        while len(f) <= n:
            k = len(f)
            m = k // 2
            if k % 2:                                    # psi_(2m+1)
                X = mm(f[m + 2], mm(f[m], mm(f[m], f[m])))
                Y = mm(f[m - 1], mm(f[m + 1], mm(f[m + 1], f[m + 1])))
                f.append(_sub(mm(self.F2, X), Y, p) if m % 2 == 0 else _sub(X, mm(self.F2, Y), p))
            else:                                        # psi_(2m)
                X = mm(f[m + 2], mm(f[m - 1], f[m - 1]))
                Y = mm(f[m - 2], mm(f[m + 1], f[m + 1]))
                f.append(mm(f[m], _sub(X, Y, p)))
        return f[n]


def _x_relation(div, xp, lam):
    """(x - x^p) den - num modulo K, zero iff x^p = x([lam] P) on ker K,
    where x([lam] P) = x - num/den (den is a unit modulo K when K's roots
    are abscissas of points of order l)."""
    mm, p, F = div.ring.mul, div.p, div.F
    if lam % 2:
        num, den = mm(F, mm(div[lam - 1], div[lam + 1])), mm(div[lam], div[lam])
    else:
        num, den = mm(div[lam - 1], div[lam + 1]), mm(F, mm(div[lam], div[lam]))
    return _sub(mm(_sub([0, 1], xp, p), den), num, p)


def _y_sign(div, r, lam):
    """+1 or -1 when y^p = +-y([lam] P) on ker K, else 0: y^p = y r, with
    r = (x^3 + a x + b)^((p - 1)/2), and y([lam] P) = y f_(2 lam) / g,
    g = f_lam^4 (lam odd) or F^2 f_lam^4 (lam even)."""
    mm, p = div.ring.mul, div.p
    sq = mm(div[lam], div[lam])
    g = mm(sq, sq) if lam % 2 else mm(div.F2, mm(sq, sq))
    lhs, two = mm(r, g), div[2 * lam]
    if lhs == two:
        return 1
    if lhs == _neg(two, p):
        return -1
    return 0


def _eigenvalue(a, b, p, l, K):
    """mu in [1, l - 1] with Frobenius = [mu] on ker K, or None."""
    ring = _Mod(K, p)
    div = _Division(a, b, p, ring)
    xp = ring.frobenius_x()
    for lam in range(1, (l - 1) // 2 + 1):
        if not _x_relation(div, xp, lam):
            sign = _y_sign(div, ring.pow(_trim([b, a, 0, 1]), (p - 1) // 2), lam)
            return lam if sign == 1 else l - lam if sign == -1 else None
    return None


def check_residue(a, b, p, l, K, mu):
    """t mod l, proved from K and mu alone, or None: K divides the
    l-division polynomial, so its roots are abscissas of points of order l,
    and Frobenius acts on those points as [mu]. Frobenius satisfies
    phi^2 - t phi + p = 0, so mu^2 - t mu + p = 0 (mod l)."""
    if not (isinstance(l, int) and 3 <= l < min(p, L_MAX) and ec.is_prime(l)):
        return None
    if not (isinstance(mu, int) and 1 <= mu < l):
        return None
    if not (isinstance(K, list) and 2 <= len(K) <= (l + 1) // 2 and K[-1] == 1
            and all(isinstance(c, int) and 0 <= c < p for c in K)):
        return None
    ring = _Mod(K, p)
    div = _Division(a, b, p, ring)
    if div[l]:
        return None
    lam, want = (mu, 1) if mu <= (l - 1) // 2 else (l - mu, -1)
    if _x_relation(div, ring.frobenius_x(), lam):
        return None
    if _y_sign(div, ring.pow(_trim([b, a, 0, 1]), (p - 1) // 2), lam) != want:
        return None
    return (mu + p * pow(mu, -1, l)) % l


def _parity(a, b, p):
    """t mod 2: 0 iff x^3 + a x + b has a root in F_p (a point of order 2)."""
    g = _trim([b, a, 0, 1])
    ring = _Mod(g, p)
    return 0 if len(_gcd(g, _sub(ring.frobenius_x(), [0, 1], p), p)) > 1 else 1


# ---- the count --------------------------------------------------------------------------------

def _cost(l, bits):
    """Estimated seconds for the prime l, at p of this many bits (CPython,
    measured at 256 bits): the power sums, x^p modulo Psi_l(x, j), and, for
    the half of the primes that are Elkies, the eigenvalue search."""
    _, v = _params(l)
    n = (l + 1) * v + 1
    k = bits / 256
    sums = 65e-6 * math.sqrt(l + 1) * n * k ** 1.2
    frob = 1.65e-3 * l ** 1.3 * k ** 2.3
    eigen = (l + 2.5 * bits) * 1.7e-3 * (l / 150) ** 1.3 * k ** 1.3
    return sums + frob + eigen / 2


def _primes(bits, limit=L_MAX):
    """The odd primes below limit, least estimated time per bit of t first."""
    ls = [q for q in range(3, limit) if all(q % d for d in range(2, math.isqrt(q) + 1))]
    return sorted(ls, key=lambda q: _cost(q, bits) / math.log2(q))


@functools.lru_cache(maxsize=48)
def _sums(l, p):
    """_power_sums, kept for the twist and for other curves over F_p."""
    return _power_sums(l, p)


@functools.lru_cache(maxsize=512)
def _elkies_root(l, p, j):
    """A root in F_p of Psi_l(F, j), or None when there is none (l is an
    Atkin prime for this j; the twist has the same j)."""
    U = _psi_at(_sums(l, p), l, j, 1, p)[0]
    g = _gcd(U, _sub(_Mod(U, p).frobenius_x(), [0, 1], p), p)
    if len(g) < 2:
        return None
    return _a_root(g, p, random.Random(l * 1000003 + j))


def _crt(res):
    r, m = 0, 1
    for ri, mi in res:
        r = r + m * ((ri - r) * pow(m, -1, mi) % mi)
        m *= mi
    return r % m, m


def _candidates(p, t0, M):
    """(t_min, R): the traces t = t_min + k M, 0 <= k < R, with |t| <= 2 sqrt p."""
    w = math.isqrt(4 * p)
    t_min = -w + (t0 + w) % M
    return t_min, (w - t_min) // M + 1 if t_min <= w else 0


def _solutions(C, P, base, M, R):
    """The k in [0, R) with (base - k M) P = O, the order of the curve C
    being base - k M for some k (for E, base = p + 1 - t_min); None when
    the baby steps collide (P is no use)."""
    S = C.mul(M, P)
    Q0 = C.mul(base, P)
    m = math.isqrt(R) + 1
    baby, cur = {}, None
    for j in range(m):
        if cur in baby:
            return None
        baby[cur] = j
        cur = C.add(cur, S)
    step = C.neg(C.mul(m, S))                    # Q0 - i m S = j S  <=>  k = i m + j
    g, out = Q0, []
    for i in range(R // m + 1):
        if g in baby:
            k = i * m + baby[g]
            if k < R:
                out.append(k)
        g = C.add(g, step)
    return out


def _distinct(C, S, kmax):
    """True iff k S != O for 1 <= k <= kmax (baby-step giant-step)."""
    if kmax <= 0:
        return True
    m = math.isqrt(kmax) + 1
    baby, cur = {}, None
    for j in range(m):                           # j S for 0 <= j < m
        if cur in baby:
            return False                         # (j - j') S = O, 0 < j - j' < m <= kmax
        baby[cur] = j
        cur = C.add(cur, S)
    G = C.mul(m, S)
    g = G
    for i in range(1, kmax // m + 2):            # k = i m - j: k S = O iff i m S = j S
        if g in baby and 1 <= i * m - baby[g] <= kmax:
            return False
        g = C.add(g, G)
    return True


def count(E, rng=None, log=None, limit=L_MAX, r_max=R_MAX):
    """#E(F_p) by SEA, as an ec.Count with method 'sea', or None when the
    Elkies primes below limit (at most L_MAX) do not narrow the trace to
    r_max candidates (at most R_MAX, the most check() will search), or no
    point separates them. E has j != 0, 1728."""
    a, b, p = E.a, E.b, E.p
    if a == 0 or b == 0:
        raise ec.ECError("j = 0 or 1728: use complex multiplication")
    rng = rng or random.Random(p ^ (a << 1) ^ (b << 2))
    limit, r_max = min(limit, L_MAX), min(r_max, R_MAX)
    w = math.isqrt(4 * p)
    need = (2 * w + 1 + r_max - 1) // r_max
    j = E.j
    res = [(_parity(a, b, p), 2)]
    M = 2
    residues = []
    for l in _primes(p.bit_length(), limit):
        if M >= need:
            break
        if l >= p:
            continue
        f = _elkies_root(l, p, j)
        if f is None:
            if log:
                log(f"l={l}: Atkin")
            continue
        iso = _isogenous(a, b, p, l, _sums(l, p), f, j)
        if iso is None:
            if log:
                log(f"l={l}: Elkies, degenerate")
            continue
        K = _kernel(a, b, iso[0], iso[1], iso[2], l, p)
        mu = _eigenvalue(a, b, p, l, K) if len(K) == (l + 1) // 2 else None
        if mu is None:
            raise SEAError(f"l = {l}: the kernel polynomial has no Frobenius eigenvalue")
        tl = (mu + p * pow(mu, -1, l)) % l
        res.append((tl, l))
        residues.append((l, K, mu))
        M *= l
        if log:
            log(f"l={l}: Elkies, t = {tl} (mod {l})")
    if M < need:
        return None
    t0, M = _crt(res)
    t_min, R = _candidates(p, t0, M)
    if R == 0:
        raise SEAError("no trace in the Hasse interval")
    for curve_name in ("E", "twist"):
        C = E if curve_name == "E" else E.twist()
        for _ in range(8):
            P = C.random_point(rng)
            base = p + 1 - t_min if curve_name == "E" else p + 1 + t_min
            step_sign = 1 if curve_name == "E" else -1
            sols = _solutions(C, P, base, step_sign * M, R)
            if sols == []:                         # the true order annihilates P
                raise SEAError("no candidate annihilates the point: a residue is wrong")
            if sols is not None and len(sols) == 1:
                t = t_min + sols[0] * M
                cert = {"p": p, "residues": residues, "parity": res[0][0],
                        "curve": curve_name, "point": P}
                return ec.Count(p + 1 - t, "sea", cert)
    return None


def check(E, c):
    """True iff c's 'sea' certificate proves #E(F_p) = c.n (docs/SEA.md)."""
    cert, p, a, b = c.certificate, E.p, E.a, E.b
    if not isinstance(cert, dict) or cert.get("p") != p or a == 0 or b == 0:
        return False
    residues = cert.get("residues")
    if not isinstance(residues, list):
        return False
    res, seen = [(_parity(a, b, p), 2)], set()
    for item in residues:
        if not (isinstance(item, tuple) and len(item) == 3 and isinstance(item[0], int)):
            return False
        l, K, mu = item
        if l in seen:
            return False
        seen.add(l)
        tl = check_residue(a, b, p, l, K, mu)
        if tl is None:
            return False
        res.append((tl, l))
    t0, M = _crt(res)
    lo, hi = E.hasse()
    n = c.n
    if not (isinstance(n, int) and lo <= n <= hi):
        return False
    t = p + 1 - n
    if (t - t0) % M:
        return False
    t_min, R = _candidates(p, t0, M)
    k = (t - t_min) // M
    if not 0 <= k < R or R > R_MAX:            # more candidates than a check should search
        return False
    name, P = cert.get("curve"), cert.get("point")
    if name == "E":
        C, order = E, n
    elif name == "twist":
        C, order = E.twist(), 2 * p + 2 - n
    else:
        return False
    if P is None or not C.is_on(P) or C.mul(order, P) is not None:
        return False
    # Any other candidate's order differs from this one by a nonzero
    # multiple k' M, |k'| <= max(k, R - 1 - k); P separates them iff no such
    # multiple annihilates it.
    return _distinct(C, C.mul(M, P), max(k, R - 1 - k))
