/* CBMC's own negative controls. Each function has exactly one defect of a
 * class --audit-source relies on CBMC to find, and each must be reported.
 * A CBMC that misses any of them makes the run CANNOT VERIFY: its silence
 * on the library would mean nothing. */
#include <stdint.h>

int nondet_int(void);

void selftest_bounds(void) {          /* writes a[4] of int a[4] */
    int a[4];
    int i = nondet_int();
    __CPROVER_assume(i >= 0 && i <= 4);
    a[i] = 1;
    (void)a;
}

void selftest_signed_overflow(void) { /* x * 65536 overflows int32 */
    int32_t x = nondet_int();
    __CPROVER_assume(x > 40000 && x < 50000);
    int32_t y = x * 65536;
    (void)y;
}

void selftest_narrowing(void) {       /* stores more than int16 holds */
    int x = nondet_int();
    __CPROVER_assume(x > 40000 && x < 50000);
    int16_t t = (int16_t)x;
    (void)t;
}
