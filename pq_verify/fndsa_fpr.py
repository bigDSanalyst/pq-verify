"""Falcon's emulated floating point, checked exactly -- DRAFT TRACK, ahead of
FIPS 206.

Falcon's key generator and signer compute in IEEE-754 binary64. Builds that
do not use the CPU's floating point -- PQClean's "clean" Falcon and the
reference implementation built with FALCON_FPEMU -- emulate it with integer
arithmetic and export the emulation as functions on 64-bit words:

    fpr_scaled(i, sc)     i * 2^sc, for a 64-bit integer i
    fpr_add, fpr_mul, fpr_div, fpr_sqrt
    fpr_expm_p63(x, ccs)  ApproxExp: an integer near 2^63 * ccs * exp(-x),
                          which the Gaussian sampler's rejection step uses

The emulation must round as binary64 does: to nearest, ties to even. A rounding
defect need not change Falcon's known-answer tests (a different last bit
almost never changes a sampled integer), so they cannot be relied on to see
one. This stage asks each exported function between 1,200 and 10,000
inputs from Falcon's domain and compares every answer with

    fpr_scaled, add, mul, div   the exact result, in rational arithmetic,
                                rounded to nearest, ties to even
    fpr_sqrt                    the exact square root, rounded the same way
    fpr_expm_p63                the reference implementation's computation,
                                bit for bit: its 13 integer coefficients (from
                                FACCT, eprint 2018/1234) and its integer
                                arithmetic

Before the reference is trusted it is checked on what it is about to ask:
against this machine's own IEEE-754 arithmetic (scaled, add, mul, div, sqrt),
and, for ApproxExp, against 2^63 * ccs * exp(-x) to 60 digits, within the
2^-50 its authors report. If either check fails, the stage does not run.

Falcon's domain, from the code's own contract: values are zeros or normal
numbers -- never subnormals, infinities or NaNs -- and the caller keeps results
in range. Nothing outside it is asked. fpr_expm_p63 is asked for
0 <= x <= ln 2 and 0 <= ccs < 1, as the sampler calls it.

Not checked here:
  - the sign of a zero result: Falcon's emulation does not promise IEEE's
    rule (x + (-x) may come back as -0), and either sign is accepted;
  - the primitives Falcon inlines (fpr_of, fpr_rint, fpr_floor, fpr_trunc,
    fpr_neg, fpr_sub, fpr_half, fpr_sqr, fpr_inv, fpr_lt and the rest): they
    are compiled into their callers and cannot be called on their own;
  - builds that use the CPU's floating point (PQClean's AVX2 and AArch64
    Falcon, liboqs on a CPU with AVX2): they export no fpr_* function, and
    their arithmetic is the CPU's; and builds that hide the symbols;
  - the FFT, the sampler, the statistics of the signatures, timing.
The inputs are drawn from a seed, new for each run unless one is given; a
defect confined to inputs that are never drawn can pass.
"""
import ctypes as _ct
import math as _math
import os as _os
import random as _random
import re as _re
import struct as _struct
from decimal import Decimal as _Dec, localcontext as _localcontext
from fractions import Fraction as _Fr

M52 = (1 << 52) - 1
M64 = (1 << 64) - 1
SIGN = 1 << 63
OPS = ("scaled", "add", "mul", "div", "sqrt", "expm_p63")
STAGES = tuple("fpr_" + op for op in OPS)
# Without these three, a group of fpr_* symbols is not the emulation: a build
# on the CPU's floating point inlines them, and what it does export (such as
# fpr_expm_p63) takes doubles, not 64-bit words.
CORE = ("add", "mul", "div")

# ApproxExp's coefficients: FACCT's polynomial for exp(-x), scaled by 2^63,
# as in fpr_expm_p63 of Falcon's reference implementation and of PQClean.
EXPM_C = (
    0x00000004741183A3, 0x00000036548CFC06, 0x0000024FDCBF140A,
    0x0000171D939DE045, 0x0000D00CF58F6F84, 0x000680681CF796E3,
    0x002D82D8305B0FEA, 0x011111110E066FD0, 0x0555555555070F00,
    0x155555555581FF00, 0x400000000002B400, 0x7FFFFFFFFFFF4800,
    0x8000000000000000,
)
EXPM_TOLERANCE = 1 << 13          # 2^-50 of 2^63: the accuracy its authors report
ONE, TWO = 0x3FF0000000000000, 0x4000000000000000
LN2 = 0x3FE62E42FEFA39EF          # the double nearest ln 2
ONE_MINUS = 0x3FEFFFFFFFFFFFFF    # the largest double below 1


# ---------------------------------------------------------------------------
# binary64, exactly
# ---------------------------------------------------------------------------

def _pow2(k):
    return _Fr(1 << k) if k >= 0 else _Fr(1, 1 << -k)


def decode(u):
    """The exact value of a binary64 word: a Fraction for a zero or a normal
    number, None for a subnormal, an infinity or a NaN."""
    e, m = (u >> 52) & 0x7FF, u & M52
    if e == 0:
        return _Fr(0) if m == 0 else None
    if e == 0x7FF:
        return None
    v = (m | 1 << 52) * _pow2(e - 1075)
    return -v if u >> 63 else v


def encode(v):
    """v rounded to the nearest binary64, ties to even, as a word; None when
    the result is not a zero or a normal number (outside Falcon's domain)."""
    if v == 0:
        return 0
    neg = v < 0
    a = -v if neg else v
    n, d = a.numerator, a.denominator

    def split(e):                       # floor(a / 2^e), the remainder, the divisor
        num, den = (n, d << e) if e >= 0 else (n << -e, d)
        q, r = divmod(num, den)
        return q, r, den
    e = n.bit_length() - d.bit_length() - 52     # a / 2^e lies in [2^51, 2^53)
    q, r, den = split(e)
    if q < 1 << 52:
        e -= 1
        q, r, den = split(e)
    if 2 * r > den or (2 * r == den and q & 1):
        q += 1
        if q == 1 << 53:
            q, e = 1 << 52, e + 1
    b = e + 1075
    if not 1 <= b <= 2046:
        return None
    return (SIGN if neg else 0) | b << 52 | (q & M52)


def exact(op, a, b=None):
    """The correctly rounded answer to fpr_<op>, as a word; None outside
    Falcon's domain. scaled takes (i, sc) as integers."""
    if op == "scaled":
        return encode(a * _pow2(b))
    if op == "sqrt":
        return sqrt_rounded(a)
    x, y = decode(a), decode(b)
    if x is None or y is None:
        return None
    if op == "add":
        return encode(x + y)
    if op == "mul":
        return encode(x * y)
    if op == "div":
        return None if y == 0 else encode(x / y)
    raise ValueError(op)


def sqrt_rounded(u):
    """The square root of a non-negative word, correctly rounded. A square
    root is never exactly halfway between two doubles, so a root known to
    lie strictly between the integers r and r + 1, r of 56 bits or more,
    rounds as r + 1/2 does."""
    x = decode(u)
    if x is None or x < 0:
        return None
    if x == 0:
        return 0
    m, e = (u & M52) | 1 << 52, ((u >> 52) & 0x7FF) - 1075    # x = m * 2^e
    if e & 1:
        m, e = m << 1, e - 1
    t = 30                                     # m * 4^t: 113 bits or more, a 56-bit root
    n = m << (2 * t)
    r = _math.isqrt(n)
    root = _Fr(r) if r * r == n else _Fr(2 * r + 1, 2)
    return encode(root * _pow2(e // 2 - t))


def approx_exp(x, ccs):
    """fpr_expm_p63 as the reference computes it: z = floor(2^63 x) << 1,
    Horner's rule over EXPM_C keeping the high 64 bits of each 128-bit
    product, then the same with ccs."""
    z = (int(decode(x) * (1 << 63)) << 1) & M64
    y = EXPM_C[0]
    for c in EXPM_C[1:]:
        y = (c - ((z * y) >> 64)) & M64
    z = (int(decode(ccs) * (1 << 63)) << 1) & M64
    return (z * y) >> 64


def expm_true(x, ccs):
    """2^63 * ccs * exp(-x), to 60 significant digits (a Decimal)."""
    with _localcontext() as ctx:
        ctx.prec = 60
        xv, cv = decode(x), decode(ccs)
        xd = _Dec(xv.numerator) / _Dec(xv.denominator)
        cd = _Dec(cv.numerator) / _Dec(cv.denominator)
        return (-xd).exp() * cd * _Dec(1 << 63)


def bits(f):
    return _struct.unpack("<Q", _struct.pack("<d", f))[0]


def flt(u):
    return _struct.unpack("<d", _struct.pack("<Q", u))[0]


def hardware(op, a, b=None):
    """This machine's IEEE-754 answer, through Python's floats."""
    if op == "scaled":
        return bits(_math.ldexp(float(a), b))     # int to float rounds to nearest even
    if op == "sqrt":
        return bits(_math.sqrt(flt(a)))
    x, y = flt(a), flt(b)
    if op == "add":
        return bits(x + y)
    if op == "mul":
        return bits(x * y)
    return bits(x / y)


def same(got, want):
    """Equal words, a zero of either sign standing for an exact zero."""
    return got == want or (want & ~SIGN == 0 and got & ~SIGN == 0)


def ulps(got, want):
    """How many representable steps `got` lies from `want`, or None when
    their signs differ (the words of same-signed doubles are in order)."""
    if (got ^ want) & SIGN:
        return None
    d = (got & ~SIGN) - (want & ~SIGN)
    return -d if got & SIGN else d


# ---------------------------------------------------------------------------
# What to ask: Falcon's domain, its edges, and inputs built to round on a tie
# ---------------------------------------------------------------------------

def _normal(rng, emin, emax, sign=None):
    s = rng.getrandbits(1) if sign is None else sign
    return s << 63 | (1023 + rng.randint(emin, emax)) << 52 | rng.getrandbits(52)


def _word(m, e, sign=0):
    """The word for (-1)^sign * m * 2^e, m an integer of 53 bits at most and
    the value normal (asserted: these build questions, not answers)."""
    w = encode(_Fr(m) * _pow2(e))
    assert w is not None and decode(w) == _Fr(m) * _pow2(e)
    return w | (SIGN if sign else 0)


def _tie_pair(rng):
    """(x, y) whose exact sum lies halfway between two doubles: s = (2Q + 1)
    2^(f-1) sits between Q 2^f and (Q + 1) 2^f; with x = Q' 2^f, the other
    operand y = (2(Q - Q') + 1) 2^(f-1) is a double too, and opposite in sign
    when Q' > Q (a subtraction)."""
    f = rng.randint(-100, 40)
    q = rng.getrandbits(52) | 1 << 52
    q2 = rng.getrandbits(52) | 1 << 52 if rng.getrandbits(1) else q
    k = 2 * (q - q2) + 1
    s = rng.getrandbits(1)
    x, y = _word(q2, f, s), _word(abs(k), f - 1, s ^ (k < 0))
    return (x, y) if rng.getrandbits(1) else (y, x)


def _mul_tie(rng):
    """(x, y) whose exact product has 54 significant bits, the last one set:
    halfway between two doubles."""
    while True:
        a = rng.getrandbits(26) | 1 << 26 | 1          # 27 bits, odd
        b = rng.getrandbits(27) | 1 << 27 | 1          # 28 bits, odd
        if (a * b).bit_length() == 54:
            break
    ea, eb = rng.randint(-60, 30), rng.randint(-60, 30)
    return _word(a, ea, rng.getrandbits(1)), _word(b, eb, rng.getrandbits(1))


def _int_tie(rng):
    """An integer of 55 to 63 bits halfway between two doubles: the bits
    below its top 53 are 10...0."""
    length = rng.randint(55, 63)
    drop = length - 53
    i = ((rng.getrandbits(52) | 1 << 52) << drop) | 1 << (drop - 1)
    return -i if rng.getrandbits(1) else i


def _between(rng, lo, hi):
    """A double drawn uniformly from the words lo..hi (one binade)."""
    return lo + rng.randrange(hi - lo + 1)


def cases(seed, scale=1):
    """{op: [(a, b)]} for the six primitives, drawn from `seed`. Each op has
    a fixed number of cases (times `scale`), so a run's totals do not depend
    on its seed: scaled 1,214, add 3,009, mul 2,005, div 1,805, sqrt 1,306,
    expm_p63 10,006 at scale 1."""
    rng = _random.Random(seed)
    out = {op: [] for op in OPS}

    def fixed(op, *pairs):
        for a, b in pairs:
            want = approx_exp(a, b) if op == "expm_p63" else exact(op, a, b)
            assert want is not None, (op, a, b)
            out[op].append((a, b))

    def draw(op, count, make):
        """`count` cases with an answer in Falcon's domain."""
        got = 0
        while got < count * scale:
            a, b = make()
            want = approx_exp(a, b) if op == "expm_p63" else exact(op, a, b)
            if want is not None:
                out[op].append((a, b))
                got += 1

    # fpr_scaled: 64-bit integers of every length, times a power of two
    fixed("scaled", (0, 0), (1, 0), (-1, 0), (1 << 53, 0), ((1 << 53) + 1, 0),
          ((1 << 54) - 1, 0), ((1 << 63) - 1, 0), (-((1 << 63) - 1), 0), (3, -1),
          (12289, 0), (-12289, 7), (1, 300), (1, -300), (5, -1000))

    def scaled():
        length = rng.randint(1, 63)
        i = rng.getrandbits(length - 1) | 1 << (length - 1)
        return (-i if rng.getrandbits(1) else i), rng.randint(-300, 300)
    draw("scaled", 1000, scaled)
    draw("scaled", 200, lambda: (_int_tie(rng), rng.randint(-60, 60)))

    # fpr_add: Falcon's range, a wide one, operands within 3 binades of each
    # other (cancellation, and ties half the time), ties built in, edges
    p53 = 0x4340000000000000                               # 2^53
    fixed("add", (ONE, ONE), (ONE, SIGN | ONE), (ONE, 0), (0, ONE), (0, 0),
          (p53, ONE),                                      # 2^53 + 1: a tie, kept even
          (p53 | 1, ONE),                                  # (2^53 + 2) + 1: rounds up
          (TWO, SIGN | 0x3CB0000000000000),                # 2 - 2^-52: exact, a binade down
          (TWO, SIGN | 0x3CA0000000000000),                # 2 - 2^-53: a tie, rounds to 2
          (ONE, 0x3CA0000000000000))                       # 1 + 2^-53: a tie, kept even
    draw("add", 800, lambda: (_normal(rng, -60, 60), _normal(rng, -60, 60)))
    draw("add", 500, lambda: (_normal(rng, -480, 480), _normal(rng, -480, 480)))

    def close():
        x = _normal(rng, -60, 60)
        ex = (x >> 52) & 0x7FF
        y = rng.getrandbits(1) << 63 | (ex - rng.randint(0, 3)) << 52 | rng.getrandbits(52)
        return (x, y) if rng.getrandbits(1) else (y, x)
    draw("add", 1200, close)
    draw("add", 500, lambda: _tie_pair(rng))

    # fpr_mul
    fixed("mul", (ONE, ONE), (TWO, SIGN | ONE), (0, ONE), (SIGN | ONE, 0),
          (0x3FF8000000000000, 0x3FE0000000000000))
    draw("mul", 1000, lambda: (_normal(rng, -60, 60), _normal(rng, -60, 60)))
    draw("mul", 500, lambda: (_normal(rng, -480, 480), _normal(rng, -480, 480)))
    draw("mul", 500, lambda: _mul_tie(rng))

    # fpr_div: a quotient is never exactly halfway, so exact quotients instead
    fixed("div", (ONE, ONE), (0x4008000000000000, TWO), (0, ONE), (ONE, SIGN | ONE),
          (ONE, 0x4008000000000000))
    draw("div", 1000, lambda: (_normal(rng, -60, 60), _normal(rng, -60, 60)))
    draw("div", 500, lambda: (_normal(rng, -480, 480), _normal(rng, -480, 480)))

    def exact_quotient():
        y = rng.getrandbits(29) | 1 << 29 | 1
        k = rng.getrandbits(22) | 1
        e1, e2 = rng.randint(-40, 40), rng.randint(-40, 40)
        return _word(y * k, e1, rng.getrandbits(1)), _word(y, e2, rng.getrandbits(1))
    draw("div", 300, exact_quotient)

    # fpr_sqrt: non-negative; a root is never exactly halfway either
    fixed("sqrt", (0, None), (ONE, None), (TWO, None), (0x4010000000000000, None),
          (0x3FE0000000000000, None), (p53, None))
    draw("sqrt", 1000, lambda: (_normal(rng, -480, 480, sign=0), None))

    def square():
        r = rng.getrandbits(25) | 1 << 25                  # r^2 fits in 52 bits
        return _word(r * r, 2 * rng.randint(-100, 100)), None
    draw("sqrt", 300, square)

    # fpr_expm_p63: x in [0, ln 2], ccs in [0, 1); most cases near x = ln 2
    # and ccs = 1, where a change in a coefficient shows most often
    fixed("expm_p63", (0, 0), (0, 0x3FE0000000000000), (0, ONE_MINUS), (LN2, ONE_MINUS),
          (LN2, 0x3FE0000000000000), (0x3C30000000000000, ONE_MINUS))
    ln2 = flt(LN2)
    draw("expm_p63", 4000, lambda: (bits(rng.random() * ln2), bits(rng.random())))
    x_lo, c_lo = bits(0.67), bits(0.95)
    draw("expm_p63", 6000, lambda: (_between(rng, x_lo, LN2), _between(rng, c_lo, ONE_MINUS)))
    return out


def check_reference(asked):
    """The reference, on what is about to be asked: against this machine's
    IEEE-754 arithmetic, and ApproxExp against exp itself (every eighth case).
    (True, the worst deviation of ApproxExp in units of 2^-63) or (False, why)."""
    for op in ("scaled", "add", "mul", "div", "sqrt"):
        for a, b in asked[op]:
            want, hw = exact(op, a, b), hardware(op, a, b)
            if want is None or not same(hw, want):
                return False, (f"pq-verify's reference and this machine's floating point "
                               f"disagree on fpr_{op}({a:#x}, {b!r})")
    worst = _Dec(0)
    for x, c in asked["expm_p63"][::8]:
        dev = abs(_Dec(approx_exp(x, c)) - expm_true(x, c))
        if dev > EXPM_TOLERANCE:
            return False, (f"pq-verify's ApproxExp is {dev:.1f} from 2^63 ccs exp(-x) at "
                           f"x={flt(x)!r}, ccs={flt(c)!r}: beyond 2^-50")
        worst = max(worst, dev)
    return True, worst


# ---------------------------------------------------------------------------
# Binding: which exported functions are Falcon's emulated arithmetic
# ---------------------------------------------------------------------------

_FPR = _re.compile(r"^(?P<impl>.*?)fpr_(?P<op>scaled|add|mul|div|sqrt|expm_p63)$")


def find(exported, param_set, prefix=None):
    """([(implementation, {op: symbol})], [(implementation, why)]): the
    groups of fpr_* functions that are Falcon's emulation, and those that are
    not. A name with a parameter set in it ("512") serves that set only."""
    from .symbols import with_prefix
    groups = {}
    for name in with_prefix(exported, prefix):
        m = _FPR.match(name)
        if not m:
            continue
        impl = m["impl"]
        if not prefix and not any(k in impl.lower() for k in ("falcon", "fndsa", "fn_dsa")):
            continue
        groups.setdefault(impl, {})[m["op"]] = name
    n = "512" if param_set.endswith("512") else "1024"
    other = "1024" if n == "512" else "512"
    found, skipped = [], []
    for impl, syms in sorted(groups.items()):
        if other in impl and n not in impl:
            continue
        missing = [op for op in CORE if op not in syms]
        if missing:
            skipped.append((impl, f"{impl}fpr_* exports {', '.join(sorted(syms))} but "
                                  f"not {', '.join('fpr_' + m for m in missing)}: not "
                                  "Falcon's emulated arithmetic (a build on the CPU's "
                                  "floating point passes doubles)"))
            continue
        found.append((impl, syms))
    return found, skipped


def _bind(lib, syms):
    U64 = _ct.c_uint64
    types = {"scaled": [_ct.c_int64, _ct.c_int], "sqrt": [U64]}
    fns = {}
    for op, name in syms.items():
        f = getattr(lib, name)
        f.restype = U64
        f.argtypes = types.get(op, [U64, U64])
        fns[op] = f
    return fns


def _case(name, op, a, b):
    if op == "scaled":
        return f"{name}({a}, {b})"
    if op == "sqrt":
        return f"{name}({a:#018x})"
    if op == "expm_p63":
        return f"{name}(x={flt(a)!r}, ccs={flt(b)!r})"
    return f"{name}({a:#018x}, {b:#018x})"


def run(lib_path, exported, param_set, tally, prefix=None, seed=None, scale=1):
    """Ask every bound primitive its cases and record each answer in
    `tally`, stage fpr_<op>. Returns what the report needs: the seed, the
    implementations asked, the reference's own check."""
    seed_given = seed is not None
    seed = seed if seed_given else _os.urandom(32)
    info = {"seed": seed.hex(), "seed_supplied": seed_given, "implementations": [],
            "not_emulated": [], "reference": None, "reference_approx_exp_error": None}
    found, skipped = find(exported, param_set, prefix)
    info["not_emulated"] = [why for _impl, why in skipped]
    if not found:
        where = f" among the symbols starting with {prefix}" if prefix else ""
        why = ("no Falcon emulated-arithmetic functions (fpr_add, fpr_mul, ...) are "
               f"exported{where}: a build on the CPU's floating point, or hidden symbols"
               + (f"; {skipped[0][1]}" if skipped else ""))
        for st in STAGES:
            tally.not_applicable(st, 1, why)
        return info
    asked = cases(seed, scale)
    ok, worst = check_reference(asked)
    if not ok:
        info["reference"] = worst
        for st in STAGES:
            tally.not_applicable(st, 1, f"the reference could not be confirmed: {worst}")
        return info
    info["reference"] = "confirmed"
    # pq-verify's ApproxExp against 2^63 ccs exp(-x), largest |difference| over
    # the cases it was checked on, in units of 2^-63: the reference's, not the
    # library's
    info["reference_approx_exp_error"] = float(worst)
    lib = _ct.CDLL(lib_path)
    for impl, syms in found:
        info["implementations"].append({"prefix": impl, "symbols": dict(syms)})
        fns = _bind(lib, syms)
        for op in OPS:
            if op not in fns:
                tally.not_applicable("fpr_" + op, 1, f"{impl}fpr_{op} is not exported")
                continue
            f, name = fns[op], syms[op]
            for a, b in asked[op]:
                if op == "expm_p63":
                    want, got = approx_exp(a, b), f(a, b)
                    ok = got == want
                    detail = ""
                    if not ok:
                        dev = abs(_Dec(got) - expm_true(a, b))
                        detail = (f"returned {got:#018x}, the reference {want:#018x} "
                                  f"({got - want:+d}); {dev:.1f} from 2^63 ccs exp(-x)"
                                  + (" -- beyond 2^-50" if dev > EXPM_TOLERANCE else ""))
                else:
                    want = exact(op, a, b)
                    got = f(a) if op == "sqrt" else f(a, b)
                    ok = same(got, want)
                    detail = ""
                    if not ok:
                        d = ulps(got, want)
                        detail = (f"returned {got:#018x}, correctly rounded {want:#018x} ("
                                  + ("the opposite sign" if d is None else
                                     f"{d:+d} unit{'s' if abs(d) != 1 else ''} in the last place")
                                  + ")")
                tally.rec("fpr_" + op, ok, _case(name, op, a, b), detail)
    return info
