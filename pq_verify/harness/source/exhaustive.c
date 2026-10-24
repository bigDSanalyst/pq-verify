/* Every input of the library's two reductions, and its zeta table against
 * FIPS 203's definition. Compiled against the library's own reduce.c and
 * ntt.c, so it checks the code that ships, as the compiler built it.
 *
 *   barrett_reduce(a), every int16 a:            r = a mod q, r in {-(q-1)/2..(q-1)/2}
 *   montgomery_reduce(a), every a the library
 *     documents, {-q*2^15 .. q*2^15 - 1}:        r = a * 2^-16 mod q, r in {-q+1..q-1}
 *   zetas[i], i = 0..127:                        17^BitRev7(i) * 2^16 mod q, centred
 *
 * Each comparison is first run on a copy of the function or table with one
 * value wrong, and must count that one: a check that cannot fail would say
 * nothing about the library.
 *
 * Output, one line each: "control NAME ok|FAILED", then
 * "NAME CASES inputs|entries WRONG wrong [first X]". Exit status: 0 all
 * correct, 1 something wrong, 2 a control failed (the run decided nothing).
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "pqv_ns.h"
#include "params.h"
#include "reduce.h"
#include "ntt.h"

#define Q KYBER_Q

typedef struct {
    long cases, wrong;
    int64_t first;
} tally;

static int64_t mod(int64_t x) {
    int64_t r = x % Q;
    return r < 0 ? r + Q : r;
}

static unsigned bitrev7(unsigned i) {
    unsigned r = 0;
    for (int b = 0; b < 7; b++)
        r |= ((i >> b) & 1u) << (6 - b);
    return r;
}

static void count(tally *t, int64_t at) {
    if (!t->wrong++)
        t->first = at;
}

/* The controls: the library's function with one output moved off by one. */
static int16_t barrett(int16_t a) { return NS(barrett_reduce)(a); }
static int16_t barrett_control(int16_t a) {
    int16_t r = NS(barrett_reduce)(a);
    return a == 1234 ? (int16_t)(r + 1) : r;
}
static int16_t montgomery(int32_t a) { return NS(montgomery_reduce)(a); }
static int16_t montgomery_control(int32_t a) {
    int16_t r = NS(montgomery_reduce)(a);
    return a == 123456 ? (int16_t)(r + 1) : r;
}

static tally check_barrett(int16_t (*f)(int16_t)) {
    tally t = {0, 0, 0};
    for (int32_t a = INT16_MIN; a <= INT16_MAX; a++, t.cases++) {
        int16_t r = f((int16_t)a);
        if (r < -(Q - 1) / 2 || r > (Q - 1) / 2 || mod((int64_t)a - r) != 0)
            count(&t, a);
    }
    return t;
}

static tally check_montgomery(int16_t (*f)(int32_t), int64_t inv16) {
    tally t = {0, 0, 0};
    for (int64_t a = -(int64_t)Q * 32768; a <= (int64_t)Q * 32768 - 1; a++, t.cases++) {
        int16_t r = f((int32_t)a);
        if (r <= -Q || r >= Q || mod(r - mod(a) * inv16) != 0)
            count(&t, a);
    }
    return t;
}

static tally check_zetas(const int16_t *z) {
    tally t = {0, 0, 0};
    for (unsigned i = 0; i < 128; i++, t.cases++) {
        int64_t w = 1;
        for (unsigned k = 0; k < bitrev7(i); k++)
            w = w * 17 % Q;
        int64_t want = w * 65536 % Q;
        if (want > Q / 2)
            want -= Q;
        if (z[i] != want)
            count(&t, i);
    }
    return t;
}

static int control(const char *name, tally ctl, tally real) {
    /* One more wrong than the library has; a library already wrong is a
     * finding either way, so its control decides nothing extra. */
    int ok = ctl.wrong == real.wrong + 1 || real.wrong > 0;
    printf("control %s %s\n", name, ok ? "ok" : "FAILED");
    return ok;
}

static int show(const char *name, const char *unit, tally t) {
    printf("%s %ld %s %ld wrong", name, t.cases, unit, t.wrong);
    if (t.wrong)
        printf(" first %" PRId64, t.first);
    printf("\n");
    return t.wrong != 0;
}

int main(void) {
    int64_t inv16 = 1; /* 2^16 * inv16 = 1 mod q: (2^16)^(q-2) */
    for (int k = 0; k < Q - 2; k++)
        inv16 = inv16 * 65536 % Q;

    int16_t zc[128];
    for (int i = 0; i < 128; i++)
        zc[i] = NS(zetas)[i];
    zc[77] = (int16_t)(zc[77] + 1);

    tally b = check_barrett(barrett), m = check_montgomery(montgomery, inv16),
          z = check_zetas(NS(zetas));
    int controls_ok = control("barrett_reduce", check_barrett(barrett_control), b)
                    & control("montgomery_reduce", check_montgomery(montgomery_control, inv16), m)
                    & control("zetas", check_zetas(zc), z);
    int wrong = show("barrett_reduce", "inputs", b) | show("montgomery_reduce", "inputs", m)
              | show("zetas", "entries", z);
    return !controls_ok ? 2 : wrong ? 1 : 0;
}
