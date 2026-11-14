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
    covariance  the shape: at each of the n/2 points of the FFT, the centred
                2x2 covariance of (s1, s2) must be the identity times the
                variance. Falcon's sampler works point by point in the FFT
                domain, along the Gram-Schmidt directions of the secret basis;
                a tree that stretches some directions and shrinks others keeps
                the variance and shows here. The sums are exact (s1 adj(s1),
                s2 adj(s2), s1 adj(s2), each a Kronecker product); see
                covariance().
A test fails beyond 6 standard deviations (the chi-squares one-sided). A
correct library fails one about three times in 10^8 audits of FN-DSA-512 and
twice in 10^8 of FN-DSA-1024, mostly on the two chi-squares: the exact tail
at 6 standard deviations is 1.4e-8 for each on FN-DSA-512 (1,024 degrees of
freedom; the covariance's, matched as a scaled chi-square, about 1,017) and
7.1e-9 on FN-DSA-1024, against 2.0e-9 for each of the other two, which are
near normal. On PQClean's Falcon, 65 keys (56 of FN-DSA-512, 9 of
FN-DSA-1024, 1,000 signatures each) stayed within 3.3 on the first three,
and 11 of them (8 and 3) within 1.7 on the covariance. Simulated spherical
Gaussian signatures give the covariance's z a mean of +0.08 +- 0.10 and a
standard deviation of 0.94 (80 runs of FN-DSA-512).

On PQClean's Falcon-512 with 1,000 signatures, three planted defects still
sign validly:
  - a sampler whose sign bit is 1 with probability 136/256 instead of 1/2
    drifts by 53 to 61 standard deviations (10 keys);
  - one that draws with a sigma 2% low sits 21 to 27 standard deviations
    below the expected variance (9 keys);
  - one whose top-level conditioning coefficient (the l10 that ffSampling
    adds to the first half's target) is 0.5% too large has a covariance 26
    to 37 standard deviations off, every other test within 3.0 (10 keys).

Not seen here:
  - a defect that keeps the first two moments. A base sampler with one row
    of its table zeroed, so that every value above 6 comes out one less
    (about one draw in 4,000), leaves every statistic within noise
    (measured, PQClean, 8 keys).
  - a covariance off only at particular coefficients, which the FFT
    averages across its points, and correlations between different points
    of the FFT;
  - one that shows only after more signatures, under other keys, or for
    particular messages;
  - a smaller bias than the test resolves. At 1,000 signatures, a sign bit
    within about one point of 1/2, or a sigma within about half a percent,
    passes; so does the conditioning coefficient 0.1% off (its covariance
    grows with the square of the error: 9 to 13 at 0.3%). The drift and
    covariance statistics grow with the number of signatures, the variance
    one with its square root.
  - timing, and the key generator's own randomness.
"""
import cmath as _cmath
import math as _math

from . import fndsa as F

SIGMA = {9: 165.7366171829776, 10: 168.38857144654395}   # Falcon round 3's sigma
SIGNATURES = 1000
THRESHOLD = 6.0
CHECKS = ("valid", "centred", "scale", "symmetric", "covariance")


def _message(i):
    return b"pq-verify FN-DSA signature statistics " + i.to_bytes(4, "big")


def accumulator(logn):
    """What the tests need, summed as the signatures arrive."""
    n = 1 << logn
    return {"logn": logn, "count": 0, "invalid": 0, "first_invalid": None,
            "sums": [0] * (2 * n), "squares": 0, "positive": 0, "negative": 0,
            "largest_norm": 0, "r11": [0] * n, "r22": [0] * n, "r12": [0] * n}


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
    # s1 adj(s1), s2 adj(s2) and s1 adj(s2), exactly: at each root w of
    # X^n + 1 they are |s1(w)|^2, |s2(w)|^2 and s1(w) conj(s2(w)), the
    # covariance of (s1, s2) at that point of the FFT, summed
    from .fndsa_audit import _zmul
    n = len(s) // 2
    s1, s2 = list(s[:n]), list(s[n:])
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
        return out
    z_cov = (q - mean) / sd
    out.append(("covariance", z_cov <= THRESHOLD, z_cov,
                f"the 2x2 covariance of (s1, s2) at the {d // 4} points of the FFT, against "
                f"the variance times I: Q = {q:.1f}, {mean:.0f} +- {sd:.1f} for a spherical "
                f"sampler, z = {z_cov:+.2f} (a covariance of the wrong shape shows as more)"))
    return out


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
