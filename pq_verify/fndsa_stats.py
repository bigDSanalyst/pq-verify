"""The statistics of an FN-DSA library's signatures -- DRAFT TRACK, ahead of
FIPS 206.

A Falcon signature is a short vector s = (s1, s2) that the signer's Gaussian
sampler draws from a spherical discrete Gaussian of parameter sigma (165.74
for FN-DSA-512, 168.39 for FN-DSA-1024), centred on 0, over the lattice coset
the message's hash point picks. The sign stage checks each signature for
validity: short enough, canonically encoded, its nonce new. A sampler that is
biased, or that draws with the wrong sigma, still produces valid signatures,
and its output leaks the secret key over enough of them. Falcon's
known-answer tests catch such a sampler only where they can be run, with the
NIST DRBG standing in for the library's randomness; a library whose signing
randomness pq-verify does not control cannot be held to them.

This stage asks the library for N signatures (1,000 by default) of distinct
messages under one key from its own keypair, recomputes s1 = c - s2 h mod q
for each, exactly, and tests the N * 2n coefficients against what an exact
sampler gives:
    valid       every signature decodes and lies within the norm bound
    centred     the 2n per-coefficient means: chi-square on 2n degrees of freedom
    scale       the variance of all the coefficients together, against sigma^2
    symmetric   as many positive coefficients as negative
    covariance  at each of the n/2 points of the FFT, the centred 2x2
                covariance of (s1, s2) must be the identity times the
                variance. Falcon's sampler works point by point in the FFT
                domain, along the Gram-Schmidt directions of the secret basis;
                a tree that stretches some directions and shrinks others keeps
                the variance and shows here. The sums are exact (s1 adj(s1),
                s2 adj(s2), s1 adj(s2), each a Kronecker product); see
                covariance().
    shape       the distribution. Each coefficient of an exact sampler's
                signature closely follows the discrete Gaussian D_{Z,sigma}
                (sigma is above the lattice's smoothing parameter; measured
                below), so the histograms of |s1| and of |s2| are each held
                to the D_{Z,sigma'} whose sigma' fits their own mean square.
                The fit leaves the scale to the scale test, and |x| the sign
                to the symmetry test: what is left is the shape. 16 bins of
                equal probability, the top one halved while each half
                expects about 50 draws, so that the far tail has bins of
                its own (25 bins for FN-DSA-512 at 1,000 signatures, 26 for
                FN-DSA-1024); Pearson's chi-square, summed over the two; see
                shape().
A test fails beyond 6 standard deviations (the chi-squares one-sided). A
correct library fails one about three times in 10^8 audits of FN-DSA-512 and
twice in 10^8 of FN-DSA-1024, mostly on the centring and covariance
chi-squares: the exact tail at 6 standard deviations is 1.4e-8 for each on
FN-DSA-512 (1,024 degrees of freedom; the covariance's, matched as a scaled
chi-square, about 1,017) and 7.1e-9 on FN-DSA-1024, against 2.0e-9 for each
of the scale and symmetry tests, which are near normal, and at most 7.1e-10
for the shape. The shape's chi-square, on 48 degrees of freedom (50 for
FN-DSA-1024), is too skewed for (chi2 - d) / sqrt(2d); its z is Wilson and
Hilferty's normal score, which reaches 6 where the chi-square's exact tail
is 7.1e-10, and fitting sigma only lowers that (Chernoff and Lehmann).

On PQClean's Falcon, 149 keys (116 of FN-DSA-512, 33 of FN-DSA-1024, 1,000
signatures each) stayed within 3.7 on the first three tests; the 95 of them
run with the covariance test (68 and 27) within 3.1 on it, and the 84 run
with the shape test (60 and 24) within 2.3 on it, its z averaging -0.34 and
-0.01 with standard deviations of 0.86 and 0.91. Simulated spherical
Gaussian signatures give the covariance's z a mean of +0.08 +- 0.10 and a
standard deviation of 0.94 (80 runs of FN-DSA-512). Simulated audits of
independent D_{Z,sigma} coefficients give the shape's z a mean of -0.21
and a standard deviation of 1.01, its upper tail lighter than a normal
one's: 46 of 4,000,000 runs of FN-DSA-512 passed 4, against 127, and 30
of 2,000,000 of FN-DSA-1024, against 63.

On PQClean's Falcon-512 with 1,000 signatures, four planted defects still
sign validly:
  - a sampler whose sign bit is 1 with probability 136/256 instead of 1/2
    drifts by 51 to 62 standard deviations (20 keys);
  - one that draws with a sigma 2% low sits 21 to 27 standard deviations
    below the expected variance (18 keys);
  - one whose top-level conditioning coefficient (the l10 that ffSampling
    adds to the first half's target) is 0.5% too large has a covariance 22
    to 40 standard deviations off, the centring, scale and symmetry tests
    within 3.0 (20 keys);
  - a signer that redraws whenever some |s2| exceeds 597 (3.6 sigma, where
    the encoding allows 2047), one signature in seven, fails the shape test
    alone, at 7.5 to 9.1 (20 keys): the tail of |s2| is gone, while its
    variance is only about half a percent low (the scale test's z -0.1 to
    -4.8).
The shape test, run on half the keys of the first three (29), saw none of
them, staying within 2.0.

Not seen here:
  - a defect inside the sampler that the signing basis averages away. Each
    coefficient of a signature sums the 2n values ffSampling drew for it,
    weighted by the secret basis, so it comes out near Gaussian whatever
    the draws' own shape. A base sampler with one row of its table zeroed,
    so that every value above 6 comes out one less (about one draw in
    4,000), leaves every statistic within noise, the shape's included
    (measured, PQClean, 16 keys; the shape test on 8 of them).
  - a covariance off only at particular coefficients, which the FFT
    averages across its points, and correlations between different points
    of the FFT;
  - one that shows only after more signatures, under other keys, or for
    particular messages;
  - a smaller bias than the test resolves. At 1,000 signatures, a sign bit
    within about one point of 1/2, or a sigma within about half a percent,
    passes; so does the conditioning coefficient 0.1% off (its covariance
    grows with the square of the error: 9 to 13 at 0.3%), and a signer that
    redraws on a bound beyond about 3.7 sigma (3.9 for FN-DSA-1024), where
    the shape's expected z falls to 6. The drift, covariance and shape
    statistics grow with the number of signatures, the variance one with
    its square root.
  - timing, and the key generator's own randomness.
"""
import bisect as _bisect
import cmath as _cmath
import math as _math
from collections import Counter as _Counter

from . import fndsa as F

SIGMA = {9: 165.7366171829776, 10: 168.38857144654395}   # Falcon round 3's sigma
SIGNATURES = 1000
THRESHOLD = 6.0
CHECKS = ("valid", "centred", "scale", "symmetric", "covariance", "shape")
SHAPE_BINS = 16         # bins of |x| of equal probability...
SHAPE_TAIL = 50         # ...the top one halved while each half expects this many


def _message(i):
    return b"pq-verify FN-DSA signature statistics " + i.to_bytes(4, "big")


def accumulator(logn):
    """What the tests need, summed as the signatures arrive."""
    n = 1 << logn
    return {"logn": logn, "count": 0, "invalid": 0, "first_invalid": None,
            "sums": [0] * (2 * n), "squares": 0, "positive": 0, "negative": 0,
            "largest_norm": 0, "r11": [0] * n, "r22": [0] * n, "r12": [0] * n,
            "abs1": _Counter(), "abs2": _Counter()}


def _adj(x):
    """x(1/X) in Z[X]/(X^n + 1): its value at each root of X^n + 1 is the
    conjugate of x's there."""
    n = len(x)
    return [x[0]] + [-x[n - k] for k in range(1, n)]


def add(acc, s):
    """Count one valid signature's coefficients s = s1 || s2."""
    norm = sum(x * x for x in s)
    acc["count"] += 1
    acc["largest_norm"] = max(acc["largest_norm"], norm)
    acc["squares"] += norm
    sums = acc["sums"]
    for j, x in enumerate(s):
        sums[j] += x
    acc["positive"] += sum(1 for x in s if x > 0)
    acc["negative"] += sum(1 for x in s if x < 0)
    n = len(s) // 2
    s1, s2 = list(s[:n]), list(s[n:])
    acc["abs1"].update(map(abs, s1))
    acc["abs2"].update(map(abs, s2))
    # s1 adj(s1), s2 adj(s2) and s1 adj(s2), exactly: at each root w of
    # X^n + 1 they are |s1(w)|^2, |s2(w)|^2 and s1(w) conj(s2(w)), the
    # covariance of (s1, s2) at that point of the FFT, summed
    from .fndsa_audit import _zmul
    a2 = _adj(s2)
    for key, prod in (("r11", _zmul(s1, _adj(s1))), ("r22", _zmul(s2, a2)),
                      ("r12", _zmul(s1, a2))):
        r = acc[key]
        for k, x in enumerate(prod):
            r[k] += x


def collect(v, pk, sk, count):
    """Ask the library for `count` signatures under (pk, sk); recompute s1
    for each, exactly; accumulate. The signatures are not kept."""
    from .fndsa_audit import _zmul
    logn, h = F.decode_public_key(pk)
    n, beta2 = 1 << logn, F.PARAMS[logn][2]
    acc = accumulator(logn)

    def invalid(i, why):
        acc["invalid"] += 1
        acc["first_invalid"] = acc["first_invalid"] or f"signature {i}: {why}"
    for i in range(count):
        msg = _message(i)
        try:
            sig = v.sign(sk, msg)
            if len(sig) < 2 + F.NONCE_LEN or sig[0] != 0x30 + logn:
                raise F.Reject("not a detached signature for this parameter set")
            nonce = sig[1:1 + F.NONCE_LEN]
            s2 = F._body(logn, sig[1 + F.NONCE_LEN:])
        except (RuntimeError, F.Reject) as exc:
            invalid(i, exc)
            continue
        c = F.hash_to_point(nonce, msg, n)
        s2h = _zmul(list(s2), h)
        s1 = [F._centre((ci - pi) % F.Q) for ci, pi in zip(c, s2h)]
        s = s1 + list(s2)
        norm = sum(x * x for x in s)
        if norm > beta2:
            invalid(i, f"norm^2 {norm} exceeds {beta2}")
            continue
        add(acc, s)
    return acc


def analyse(acc, asked):
    """[(check, ok, z, detail)] from collect()'s accumulators. `asked` is
    how many signatures were requested."""
    logn = acc["logn"]
    sigma = SIGMA[logn]
    beta2 = F.PARAMS[logn][2]
    N, d = acc["count"], 2 * (1 << logn)
    out = [("valid", acc["invalid"] == 0, None,
            f"{N} of {asked} decode and lie within the norm bound"
            + (f", the largest at {acc['largest_norm'] / beta2:.3f} of it" if N else "")
            + (f"; first failure: {acc['first_invalid']}" if acc["invalid"] else ""))]
    if N < 2:
        for name in CHECKS[1:]:
            out.append((name, False, None, "too few valid signatures to test"))
        return out
    total = N * d
    var = acc["squares"] / total
    chi2 = sum(t * t for t in acc["sums"]) / (N * var)
    z_mean = (chi2 - d) / _math.sqrt(2 * d)
    out.append(("centred", z_mean <= THRESHOLD, z_mean,
                f"the {d} coefficient means: chi-square {chi2:.1f} on {d} degrees of "
                f"freedom, z = {z_mean:+.2f} (a biased sampler shows as more)"))
    z_var = (var / sigma ** 2 - 1) / _math.sqrt(2 / total)
    out.append(("scale", abs(z_var) <= THRESHOLD, z_var,
                f"variance {var / sigma ** 2:.4f} sigma^2 for sigma = {sigma:.2f}, "
                f"z = {z_var:+.2f}"))
    pos, neg = acc["positive"], acc["negative"]
    z_sign = (pos - neg) / _math.sqrt(pos + neg) if pos + neg else 0.0
    out.append(("symmetric", abs(z_sign) <= THRESHOLD, z_sign,
                f"{pos:,} positive and {neg:,} negative coefficients, z = {z_sign:+.2f}"))
    q, mean, sd = covariance(acc)
    if q is None:
        out.append(("covariance", False, None,
                    "every signature is the same: nothing varies, so no covariance to test"))
    else:
        z_cov = (q - mean) / sd
        out.append(("covariance", z_cov <= THRESHOLD, z_cov,
                    f"the 2x2 covariance of (s1, s2) at the {d // 4} points of the FFT, "
                    f"against the variance times I: Q = {q:.1f}, {mean:.0f} +- {sd:.1f} for "
                    f"a spherical sampler, z = {z_cov:+.2f} (a covariance of the wrong "
                    f"shape shows as more)"))
    parts = shape(acc)
    if parts is None:
        out.append(("shape", False, None,
                    "every coefficient of s1 or of s2 is 0: no distribution to test"))
        return out
    chi2 = sum(p["chi2"] for p in parts)
    df = sum(p["df"] for p in parts)
    z_shape = wilson_hilferty(chi2, df)
    worst = max(parts, key=lambda p: p["worst"]["part"])
    w = worst["worst"]
    where = (f"|{worst['name']}| >= {w['lo']} ({w['lo'] / worst['sigma']:.2f} sigma)"
             if w["hi"] is None else
             f"{w['lo']} <= |{worst['name']}| < {w['hi']} ({w['lo'] / worst['sigma']:.2f} "
             f"to {w['hi'] / worst['sigma']:.2f} sigma)")
    out.append(("shape", z_shape <= THRESHOLD, z_shape,
                "|s1| and |s2| against the discrete Gaussian of each one's own mean square, "
                + ", ".join(f"{p['name']}: chi-square {p['chi2']:.1f} on {p['df']} degrees of "
                            f"freedom ({p['df'] + 1} bins)" for p in parts)
                + f"; z = {z_shape:+.2f} (a distribution of the wrong shape shows as more); "
                f"the bin furthest from it: {where}, {w['observed']:,} where {w['expected']:,.1f} "
                f"were expected"))
    return out


def wilson_hilferty(chi2, df):
    """The normal score of a chi-square on df degrees of freedom (Wilson and
    Hilferty's cube root). At the chi-square's exact 6-standard-deviation
    point it gives 5.94 to 5.96 for df from 40 to 64, the range the shape
    test meets (100 to 100,000 signatures): it errs towards passing."""
    a = 2 / (9 * df)
    return ((chi2 / df) ** (1 / 3) - (1 - a)) / _math.sqrt(a)


def _folded(sigma, amax):
    """P(|x| = k), k = 0..amax, x drawn from the discrete Gaussian D_{Z,sigma}
    (weight exp(-x^2 / (2 sigma^2)) at each integer). amax = 14 sigma leaves
    out less than e^-98 of the mass."""
    w = [_math.exp(-k * k / (2 * sigma * sigma)) for k in range(amax + 1)]
    w = [w[0]] + [2 * x for x in w[1:]]
    total = _math.fsum(w)
    return [x / total for x in w]


def shape_bins(sigma, total):
    """(edges, probabilities): the bins of |x| for `total` draws, bin i
    holding edges[i-1] <= |x| < edges[i] (from 0; the last bin has no top),
    and each one's probability under D_{Z,sigma}. SHAPE_BINS bins of equal
    probability as near as the integers allow; then the top one is halved,
    and its upper half halved again, as long as each half would expect
    SHAPE_TAIL draws (less a fraction of one draw where an edge rounds to
    an integer), so that the far tail, which a signer that redraws on some
    bound cuts away, has bins of its own."""
    amax = int(14 * sigma) + 2
    p = _folded(sigma, amax)
    halvings = 0
    while total / (SHAPE_BINS * 2 ** (halvings + 1)) >= SHAPE_TAIL:
        halvings += 1
    bounds = ([b / SHAPE_BINS for b in range(1, SHAPE_BINS)]
              + [1 - 1 / (SHAPE_BINS * 2 ** j) for j in range(1, halvings + 1)])
    edges, cum, k = [], 0.0, 0
    for u in bounds:                    # the least k with P(|x| < k) >= u
        while k <= amax and cum < u:
            cum += p[k]
            k += 1
        if k <= amax and (not edges or k > edges[-1]):
            edges.append(k)
    probs = [0.0] * (len(edges) + 1)
    for k, x in enumerate(p):
        probs[_bisect.bisect_right(edges, k)] += x
    return edges, probs


def shape(acc):
    """For s1 and s2 apart: Pearson's chi-square of the histogram of |x|
    against D_{Z,sigma_hat}, sigma_hat^2 that component's own mean square
    (the maximum-likelihood fit). The fit takes the scale out, so this
    tests the shape alone; |x| takes the sign out, which the symmetry test
    has. Each component's chi-square is counted on (bins - 1) degrees of
    freedom: with sigma fitted from the raw coefficients its law lies
    between the chi-squares on (bins - 2) and (bins - 1) (Chernoff and
    Lehmann, 1954), so the larger is the conservative choice. None when a
    component is all zero."""
    parts = []
    for name, hist in (("s1", acc["abs1"]), ("s2", acc["abs2"])):
        total = sum(hist.values())
        square = sum(k * k * c for k, c in hist.items())
        if not square:
            return None
        sigma = _math.sqrt(square / total)
        edges, probs = shape_bins(sigma, total)
        observed = [0] * len(probs)
        for k, c in hist.items():
            observed[_bisect.bisect_right(edges, k)] += c
        chi2, worst = 0.0, None
        for i, (o, p) in enumerate(zip(observed, probs)):
            e = total * p
            part = (o - e) ** 2 / e
            chi2 += part
            if worst is None or part > worst["part"]:
                worst = {"part": part, "observed": o, "expected": e,
                         "lo": edges[i - 1] if i else 0,
                         "hi": edges[i] if i < len(edges) else None}
        parts.append({"name": name, "chi2": chi2, "df": len(probs) - 1, "sigma": sigma,
                      "worst": worst})
    return parts


def covariance(acc):
    """(Q, its mean, its standard deviation for a spherical sampler).

    At each of the n/2 points w_j = exp(i pi (2j + 1) / n) of the FFT (the
    other n/2 are their conjugates), W_j is the centred 2x2 scatter matrix of
    (s1(w_j), s2(w_j)) over the N signatures, from exact integer sums:
    r11(w) - |S1(w)|^2 / N and so on, S the sum of the signatures. C_j =
    W_j / ((N - 1) n v), v the pooled centred variance, so that the C_j's
    traces average exactly 2: the scale is the scale test's to judge, and the
    centre the centring test's. A spherical sampler gives I at every point;
    Q = (N - 1) sum_j |C_j - I|_F^2. For spherical Gaussian vectors each W_j
    is a complex Wishart matrix on N - 1 degrees of freedom, so each point
    adds 4 on average with variance 8 + 36 / (N - 1), and the normalisation
    takes one from the total."""
    n, N = 1 << acc["logn"], acc["count"]
    sums = acc["sums"]
    centred = acc["squares"] - sum(t * t for t in sums) / N
    sd = _math.sqrt(n / 2 * (8 + 36 / (N - 1)))
    if centred <= 0:
        return None, 2 * n - 1, sd
    scale = centred / 2                 # (N - 1) n v, v = centred / ((N - 1) 2n)
    r11, r22, r12 = acc["r11"], acc["r22"], acc["r12"]
    m1s, m2s = sums[:n], sums[n:]
    q = 0.0
    for j in range(n // 2):
        w = _cmath.exp(1j * _math.pi * (2 * j + 1) / n)
        p, e11, e22, e12, m1, m2 = 1 + 0j, 0j, 0j, 0j, 0j, 0j
        for k in range(n):
            e11 += r11[k] * p
            e22 += r22[k] * p
            e12 += r12[k] * p
            m1 += m1s[k] * p
            m2 += m2s[k] * p
            p *= w
        d1 = (e11.real - abs(m1) ** 2 / N) / scale
        d2 = (e22.real - abs(m2) ** 2 / N) / scale
        o = (e12 - m1 * m2.conjugate() / N) / scale
        q += (N - 1) * ((d1 - 1) ** 2 + (d2 - 1) ** 2 + 2 * abs(o) ** 2)
    return q, 2 * n - 1, sd


def run(v, tally, signatures=SIGNATURES):
    """Record the stage 'sampler' in `tally`; returns what the report needs."""
    info = {"signatures_asked": signatures, "signatures": 0, "threshold": THRESHOLD,
            "checks": {}}
    if not signatures:
        tally.not_applicable("sampler", len(CHECKS), "not asked (--fndsa-signatures 0)")
        return info
    if not (v.has("keypair") and v.has("sign")):
        tally.not_applicable("sampler", len(CHECKS), "no keypair and signing entry points")
        return info
    try:
        pk, sk = v.keypair()
        F.decode_public_key(pk)
    except (RuntimeError, F.Reject) as exc:
        for name in CHECKS:
            tally.rec("sampler", False, f"{name}: no key to sign with", str(exc))
        return info
    acc = collect(v, pk, sk, signatures)
    info["signatures"] = acc["count"]
    for name, ok, z, detail in analyse(acc, signatures):
        info["checks"][name] = {"ok": ok, "z": z, "detail": detail}
        tally.rec("sampler", ok, f"{name}: {signatures} signatures under one key",
                  "" if ok else detail)
    return info
