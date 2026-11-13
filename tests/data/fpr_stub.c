/*
 * Test stand-in: Falcon's emulated arithmetic (fpr_*) as PQClean's clean
 * Falcon exports it -- 64-bit words in, 64-bit words out -- computed here on
 * the CPU's IEEE-754 binary64, which rounds to nearest, ties to even, as the
 * emulation must. Built with one of
 *   -DMUT_TIES_AWAY   a result exactly halfway goes away from zero
 *   -DMUT_TRUNC       every inexact result goes toward zero
 *   -DMUT_EXPM_COEFF  one ApproxExp coefficient one unit off
 * it carries the defect planted in PQClean's own source by the vendor audits
 * (tools/vendor_audits.json). -DFPR_NS=prefix names the symbols (default
 * PQCLEAN_FALCON512_CLEAN_); -DNATIVE_EXPM_ONLY exports only fpr_expm_p63,
 * taking doubles, as a build on the CPU's floating point may.
 *
 * The planted rules need to know where the exact result lies: each operation
 * gets its rounding error exactly (TwoSum for a sum, fma for a product, a
 * quotient's or a root's remainder) and moves to the neighbour the rule asks.
 */
#include <math.h>
#include <stdint.h>
#include <string.h>

#ifndef FPR_NS
#define FPR_NS PQCLEAN_FALCON512_CLEAN_
#endif
#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)
#define NS(name) CAT(FPR_NS, name)

static const uint64_t C[] = {
    0x00000004741183A3u, 0x00000036548CFC06u, 0x0000024FDCBF140Au,
    0x0000171D939DE045u, 0x0000D00CF58F6F84u, 0x000680681CF796E3u,
#ifdef MUT_EXPM_COEFF
    0x002D82D8305B0FEBu,
#else
    0x002D82D8305B0FEAu,
#endif
    0x011111110E066FD0u, 0x0555555555070F00u, 0x155555555581FF00u,
    0x400000000002B400u, 0x7FFFFFFFFFFF4800u, 0x8000000000000000u
};

static uint64_t hi64(uint64_t a, uint64_t b) {
    return (uint64_t)(((unsigned __int128)a * b) >> 64);
}

#ifdef NATIVE_EXPM_ONLY

uint64_t NS(fpr_expm_p63)(double x, double ccs) {
    uint64_t z = (uint64_t)(x * 9223372036854775808.0) << 1, y = C[0];
    for (unsigned u = 1; u < sizeof C / sizeof C[0]; u++) y = C[u] - hi64(z, y);
    z = (uint64_t)(ccs * 9223372036854775808.0) << 1;
    return hi64(z, y);
}

#else

static double D(uint64_t u) { double d; memcpy(&d, &u, sizeof d); return d; }
static uint64_t U(double d) { uint64_t u; memcpy(&u, &d, sizeof u); return u; }

/* s: the correctly rounded result; dir: the sign of (exact - s), 0 when
 * exact; tie: the exact value lies halfway between s and its neighbour on
 * that side. */
static double planted(double s, int dir, int tie) {
#if defined(MUT_TIES_AWAY)
    if (tie) {
        double n = nextafter(s, dir > 0 ? INFINITY : -INFINITY);
        return fabs(n) > fabs(s) ? n : s;
    }
#elif defined(MUT_TRUNC)
    if (dir) {
        double n = nextafter(s, dir > 0 ? INFINITY : -INFINITY);
        return fabs(n) < fabs(s) ? n : s;
    }
#endif
    (void)dir; (void)tie;
    return s;
}

/* e = exact - s, itself a double. */
static double settle(double s, double e) {
    if (e == 0) return planted(s, 0, 0);
    double n = nextafter(s, e > 0 ? INFINITY : -INFINITY);
    return planted(s, e > 0 ? 1 : -1, n - s == 2 * e);
}

uint64_t NS(fpr_add)(uint64_t x, uint64_t y) {
    double a = D(x), b = D(y), s = a + b;
    double bp = s - a, ap = s - bp, e = (a - ap) + (b - bp);      /* TwoSum */
    return U(settle(s, e));
}

uint64_t NS(fpr_mul)(uint64_t x, uint64_t y) {
    double a = D(x), b = D(y), s = a * b;
    return U(settle(s, fma(a, b, -s)));
}

uint64_t NS(fpr_div)(uint64_t x, uint64_t y) {
    double a = D(x), b = D(y), q = a / b;
    double r = fma(-q, b, a);                  /* a - q b exactly; never halfway */
    return U(planted(q, r == 0 ? 0 : ((r > 0) == (b > 0) ? 1 : -1), 0));
}

uint64_t NS(fpr_sqrt)(uint64_t x) {
    double a = D(x), r = sqrt(a);
    double rem = fma(-r, r, a);                /* a - r^2 exactly; never halfway */
    return U(planted(r, rem == 0 ? 0 : (rem > 0 ? 1 : -1), 0));
}

uint64_t NS(fpr_scaled)(int64_t i, int sc) {
    double d = (double)i;                      /* to nearest, ties to even */
    __int128 e = (__int128)i - (__int128)d;
    int dir = e == 0 ? 0 : (e > 0 ? 1 : -1), tie = 0;
    if (dir) {
        double n = nextafter(d, dir > 0 ? INFINITY : -INFINITY);
        tie = (__int128)n - (__int128)d == 2 * e;
    }
    return U(ldexp(planted(d, dir, tie), sc));
}

uint64_t NS(fpr_expm_p63)(uint64_t x, uint64_t ccs) {
    uint64_t z = (uint64_t)(D(x) * 9223372036854775808.0) << 1, y = C[0];
    for (unsigned u = 1; u < sizeof C / sizeof C[0]; u++) y = C[u] - hi64(z, y);
    z = (uint64_t)(D(ccs) * 9223372036854775808.0) << 1;
    return hi64(z, y);
}

#endif
