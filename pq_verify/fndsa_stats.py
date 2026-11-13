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
    valid      every signature decodes and lies within the norm bound
    centred    the 2n per-coefficient means: chi-square on 2n degrees of freedom
    scale      the variance, against sigma^2
    symmetric  as many positive coefficients as negative
A test fails beyond 6 standard deviations (the chi-square one-sided). A
correct library fails one about twice in 10^8 audits of FN-DSA-512 and
once in 10^8 of FN-DSA-1024, mostly on the chi-square: its exact tail at 6
standard deviations is 1.4e-8 on 1,024 degrees of freedom and 7.1e-9 on
2,048, against 2.0e-9 for each of the other two, which are near normal. On
PQClean's Falcon, 29 keys (23 of FN-DSA-512, 6 of FN-DSA-1024, 1,000
signatures each) stayed within 3.3.

On PQClean's Falcon-512 with 1,000 signatures, both planted defects still
sign validly:
  - a sampler whose sign bit is 1 with probability 136/256 instead of 1/2
    drifts by 53 to 60 standard deviations (6 keys);
  - one that draws with a sigma 2% low sits 25 to 27 standard deviations
    below the expected variance (5 keys).

Not seen here:
  - a defect that keeps these moments. A base sampler with one row of its
    table zeroed, so that every value above 6 comes out one less (about one
    draw in 4,000), leaves every statistic within noise (measured, PQClean,
    1,000 signatures).
  - one that shows only after more signatures, under other keys, or for
    particular messages;
  - a smaller bias than the test resolves. At 1,000 signatures, a sign bit
    within about one point of 1/2, or a sigma within about half a percent,
    passes. The drift statistic grows with the number of signatures, the
    variance one with its square root.
  - timing, and the key generator's own randomness.
"""
import math as _math

from . import fndsa as F

SIGMA = {9: 165.7366171829776, 10: 168.38857144654395}   # Falcon round 3's sigma
SIGNATURES = 1000
THRESHOLD = 6.0
CHECKS = ("valid", "centred", "scale", "symmetric")


def _message(i):
    return b"pq-verify FN-DSA signature statistics " + i.to_bytes(4, "big")


def accumulator(logn):
    """What the tests need, summed as the signatures arrive."""
    return {"logn": logn, "count": 0, "invalid": 0, "first_invalid": None,
            "sums": [0] * (2 << logn), "squares": 0, "positive": 0, "negative": 0,
            "largest_norm": 0}


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
    return out


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
