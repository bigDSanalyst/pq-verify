/* Every input of the library's reduce32, caddq and freeze; its zeta table
 * against FIPS 204's definition; and its rounding against FIPS 204's own
 * algorithms on every r in [0, q). Built from the library's reduce.c and
 * rounding.c, and its ntt.c included here for the zeta table, which the
 * reference keeps static: the code that ships, as the compiler built it.
 *
 *   montgomery_reduce(a), every a in [0, 2^32): r * 2^32 = a mod q, r in (-q, q)
 *   reduce32(a), every a <= 2^31 - 2^22 - 1:   r = a mod q, r in {-6283009..6283008}
 *   caddq(a), every int32 a:                    a + q if a < 0, else a
 *   freeze(a), every a <= 2^31 - 2^22 - 1:      r = a mod+ q, in [0, q)
 *   zetas[i], i = 1..255:                       1753^BitRev8(i) * 2^32 mod q, centred
 *   power2round(r), every r in [0, q):          FIPS 204 Algorithm 35
 *   decompose(r), every r in [0, q):            Algorithm 36
 *   use_hint(r, h), every r in [0, q), h 0, 1:  Algorithm 40
 *
 * montgomery_reduce's int64 domain, about 2^55 values, is too large to
 * enumerate. Here it is checked on every low word, a in [0, 2^32); CBMC
 * proves f(a + 2^32) = f(a) + 1 (h_montgomery.c), which carries the
 * congruence to every input of its contract.
 *
 * Each comparison is first run on a copy of the function or table with one
 * value wrong, over a window around it, and must count that one: a check
 * that cannot fail would say nothing about the library. It also checks that
 * this compiler does what CBMC's model assumes for what C leaves to it: a
 * right shift of a negative int32 or int64 fills with its sign, and a
 * conversion to int32 that does not fit wraps.
 *
 * Output, one line each: "model NAME ok|DIFFERENT", "control NAME ok|FAILED",
 * then "NAME CASES inputs|entries WRONG wrong [first X]". Exit status: 0 all
 * correct, 1 something wrong, 2 a control failed or the compiler is not the
 * model's (the run decided nothing).
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "reduce.h"
#include "rounding.h"
#include "ntt.c"

#define QQ ((int64_t)Q)
#define REDUCE32_MAX (2147483647 - (1 << 22))

typedef struct {
    int64_t cases, wrong, first;
} tally;

static int64_t mod(int64_t x) {
    int64_t r = x % QQ;
    return r < 0 ? r + QQ : r;
}

/* x mod+- m for an even m: the representative in (-m/2, m/2] */
static int64_t cmod(int64_t x, int64_t m) {
    int64_t r = x % m;
    if (r < 0)
        r += m;
    return r > m / 2 ? r - m : r;
}

static void count(tally *t, int64_t at) {
    if (!t->wrong++)
        t->first = at;
}

/* FIPS 204, Algorithms 35, 36 and 40, as written there */
static void fips_power2round(int64_t r, int64_t *r1, int64_t *r0) {
    int64_t rp = mod(r);
    *r0 = cmod(rp, (int64_t)1 << D);
    *r1 = (rp - *r0) >> D;
}

static void fips_decompose(int64_t r, int64_t *r1, int64_t *r0) {
    int64_t rp = mod(r);
    *r0 = cmod(rp, 2 * (int64_t)GAMMA2);
    if (rp - *r0 == QQ - 1) {
        *r1 = 0;
        *r0 = *r0 - 1;
    } else {
        *r1 = (rp - *r0) / (2 * (int64_t)GAMMA2);
    }
}

static int64_t fips_use_hint(int64_t h, int64_t r) {
    int64_t m = (QQ - 1) / (2 * GAMMA2), r1, r0;
    fips_decompose(r, &r1, &r0);
    if (h == 1 && r0 > 0)
        return (r1 + 1) % m;
    if (h == 1 && r0 <= 0)
        return ((r1 - 1) % m + m) % m;
    return r1;
}

/* The library's functions, and the controls: one output moved off by one. */
static int32_t mont_lib(int64_t a) { return PQV_SYM_montgomery_reduce(a); }
static int32_t mont_ctl(int64_t a) {
    int32_t r = PQV_SYM_montgomery_reduce(a);
    return a == 3000000000LL ? r + 1 : r;
}
static int32_t reduce32_lib(int32_t a) { return PQV_SYM_reduce32(a); }
static int32_t reduce32_ctl(int32_t a) {
    int32_t r = PQV_SYM_reduce32(a);
    return a == 123456789 ? r + 1 : r;
}
static int32_t caddq_lib(int32_t a) { return PQV_SYM_caddq(a); }
static int32_t caddq_ctl(int32_t a) {
    int32_t r = PQV_SYM_caddq(a);
    return a == -987654 ? r + 1 : r;
}
static int32_t freeze_lib(int32_t a) { return PQV_SYM_freeze(a); }
static int32_t freeze_ctl(int32_t a) {
    int32_t r = PQV_SYM_freeze(a);
    return a == 7654321 ? r + 1 : r;
}
static int32_t p2r_lib(int32_t *a0, int32_t a) { return PQV_SYM_power2round(a0, a); }
static int32_t p2r_ctl(int32_t *a0, int32_t a) {
    int32_t r = PQV_SYM_power2round(a0, a);
    return a == 4000000 ? r + 1 : r;
}
static int32_t dec_lib(int32_t *a0, int32_t a) { return PQV_SYM_decompose(a0, a); }
static int32_t dec_ctl(int32_t *a0, int32_t a) {
    int32_t r = PQV_SYM_decompose(a0, a);
    if (a == 5000000)
        *a0 += 1;
    return r;
}
static int32_t hint_lib(int32_t a, unsigned h) { return PQV_SYM_use_hint(a, h); }
static int32_t hint_ctl(int32_t a, unsigned h) {
    int32_t r = PQV_SYM_use_hint(a, h);
    return a == 6000000 && h == 1 ? r + 1 : r;
}

static tally check_montgomery(int32_t (*f)(int64_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++) {
        int32_t r = f(a);
        if (r <= -Q || r >= Q || ((int64_t)r * 4294967296LL - a) % QQ != 0)
            count(&t, a);
    }
    return t;
}

static tally check_reduce32(int32_t (*f)(int32_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++) {
        int32_t r = f((int32_t)a);
        if (r < -6283009 || r > 6283008 || (a - r) % QQ != 0)
            count(&t, a);
    }
    return t;
}

static tally check_caddq(int32_t (*f)(int32_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++)
        if (f((int32_t)a) != (a < 0 ? a + QQ : a))
            count(&t, a);
    return t;
}

static tally check_freeze(int32_t (*f)(int32_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++)
        if (f((int32_t)a) != mod(a))
            count(&t, a);
    return t;
}

static tally check_power2round(int32_t (*f)(int32_t *, int32_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++) {
        int32_t a0, a1 = f(&a0, (int32_t)a);
        int64_t r1, r0;
        fips_power2round(a, &r1, &r0);
        if (a1 != r1 || a0 != r0)
            count(&t, a);
    }
    return t;
}

static tally check_decompose(int32_t (*f)(int32_t *, int32_t), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++, t.cases++) {
        int32_t a0, a1 = f(&a0, (int32_t)a);
        int64_t r1, r0;
        fips_decompose(a, &r1, &r0);
        if (a1 != r1 || a0 != r0)
            count(&t, a);
    }
    return t;
}

static tally check_use_hint(int32_t (*f)(int32_t, unsigned), int64_t lo, int64_t hi) {
    tally t = {0, 0, 0};
    for (int64_t a = lo; a <= hi; a++)
        for (unsigned h = 0; h <= 1; h++, t.cases++)
            if (f((int32_t)a, h) != fips_use_hint(h, a))
                count(&t, a);
    return t;
}

static unsigned bitrev8(unsigned i) {
    unsigned r = 0;
    for (int b = 0; b < 8; b++)
        r |= ((i >> b) & 1u) << (7 - b);
    return r;
}

static tally check_zetas(const int32_t *z) {
    tally t = {0, 0, 0};
    for (unsigned i = 1; i < 256; i++, t.cases++) {
        int64_t w = 1;
        for (unsigned k = 0; k < bitrev8(i); k++)
            w = w * 1753 % QQ;
        int64_t want = w * 4294967296LL % QQ;
        if (want > QQ / 2)
            want -= QQ;
        if (z[i] != want)
            count(&t, i);
    }
    return t;
}

/* volatile: the compiler must do these at run time, as it does in the library */
static volatile int32_t negative32 = -12345;
static volatile int64_t negative64 = -((int64_t)12345 << 33);
static volatile int64_t wide64 = ((int64_t)1 << 40) + 3000000000LL;
static volatile uint64_t wideu64 = 0xF0000000DEADBEEFULL;

static int model(void) {
    int shift = (negative32 >> 31) == -1 && (negative32 >> 1) == (negative32 - (negative32 & 1)) / 2
             && (negative64 >> 32) == -24690 && (negative64 >> 63) == -1;
    int wraps = (int32_t)wide64 == (int64_t)3000000000LL - 4294967296LL
             && (int32_t)wideu64 == -559038737;   /* 0xDEADBEEF - 2^32 */
    printf("model arithmetic_shift %s\n", shift ? "ok" : "DIFFERENT");
    printf("model narrowing_wraps %s\n", wraps ? "ok" : "DIFFERENT");
    return shift && wraps;
}

static int control(const char *name, tally ctl, tally real) {
    /* One more wrong than the library has over the same window; a library
     * already wrong there is a finding either way. */
    int ok = ctl.wrong == real.wrong + 1 || real.wrong > 0;
    printf("control %s %s\n", name, ok ? "ok" : "FAILED");
    return ok;
}

static int show(const char *name, const char *unit, tally t) {
    printf("%s %" PRId64 " %s %" PRId64 " wrong", name, t.cases, unit, t.wrong);
    if (t.wrong)
        printf(" first %" PRId64, t.first);
    printf("\n");
    return t.wrong != 0;
}

int main(void) {
    int32_t zc[256];
    for (int i = 0; i < 256; i++)
        zc[i] = PQV_SYM_zetas[i];
    zc[77] += 1;

    int model_ok = model();
    int controls_ok =
        control("montgomery_reduce",
                check_montgomery(mont_ctl, 3000000000LL - 1000, 3000000000LL + 1000),
                check_montgomery(mont_lib, 3000000000LL - 1000, 3000000000LL + 1000))
      & control("reduce32", check_reduce32(reduce32_ctl, 123456789 - 1000, 123456789 + 1000),
                check_reduce32(reduce32_lib, 123456789 - 1000, 123456789 + 1000))
      & control("caddq", check_caddq(caddq_ctl, -987654 - 1000, -987654 + 1000),
                check_caddq(caddq_lib, -987654 - 1000, -987654 + 1000))
      & control("freeze", check_freeze(freeze_ctl, 7654321 - 1000, 7654321 + 1000),
                check_freeze(freeze_lib, 7654321 - 1000, 7654321 + 1000))
      & control("power2round", check_power2round(p2r_ctl, 4000000 - 1000, 4000000 + 1000),
                check_power2round(p2r_lib, 4000000 - 1000, 4000000 + 1000))
      & control("decompose", check_decompose(dec_ctl, 5000000 - 1000, 5000000 + 1000),
                check_decompose(dec_lib, 5000000 - 1000, 5000000 + 1000))
      & control("use_hint", check_use_hint(hint_ctl, 6000000 - 1000, 6000000 + 1000),
                check_use_hint(hint_lib, 6000000 - 1000, 6000000 + 1000))
      & control("zetas", check_zetas(zc), check_zetas(PQV_SYM_zetas));

    int wrong = show("montgomery_reduce", "inputs", check_montgomery(mont_lib, 0, 4294967295LL))
              | show("reduce32", "inputs", check_reduce32(reduce32_lib, INT32_MIN, REDUCE32_MAX))
              | show("caddq", "inputs", check_caddq(caddq_lib, INT32_MIN, INT32_MAX))
              | show("freeze", "inputs", check_freeze(freeze_lib, INT32_MIN, REDUCE32_MAX))
              | show("zetas", "entries", check_zetas(PQV_SYM_zetas))
              | show("power2round", "inputs", check_power2round(p2r_lib, 0, QQ - 1))
              | show("decompose", "inputs", check_decompose(dec_lib, 0, QQ - 1))
              | show("use_hint", "inputs", check_use_hint(hint_lib, 0, QQ - 1));
    return !(controls_ok && model_ok) ? 2 : wrong ? 1 : 0;
}
