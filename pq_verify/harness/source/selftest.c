/* CBMC's own negative controls. Each function has exactly one defect of a
 * class --audit-source relies on CBMC to find, and each must be reported.
 * A CBMC that misses any of them makes the run CANNOT VERIFY: its silence
 * on the library would mean nothing. */
#include <stdint.h>

int nondet_int(void);
int64_t nondet_int64(void);
uint64_t nondet_uint64(void);

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

/* Not a defect: CBMC's model of the two things C leaves to the compiler
 * that ML-KEM and ML-DSA code relies on. A right shift of a negative value
 * fills with the sign, and a narrowing conversion wraps, as GCC and Clang do:
 * in int32 and int16 for ML-KEM, and in int64 and from uint64 to int32 for
 * ML-DSA's montgomery_reduce. Every CBMC proof in this audit is in that
 * model, so it must hold here, and the exhaustive tests check the compiler
 * does the same. */
void selftest_model(void) {
    int32_t x = nondet_int();
    __CPROVER_assume(x < 0);
    __CPROVER_assert((x >> 31) == -1 && (x >> 1) == (x - (x & 1)) / 2,
                     "model: a right shift of a negative value fills with its sign");
    int y = nondet_int();
    __CPROVER_assume(y > 32767 && y < 65536);
    __CPROVER_assert((int16_t)y == y - 65536, "model: a narrowing conversion wraps");
    int64_t w = nondet_int64();
    __CPROVER_assume(w < 0);
    __CPROVER_assert((w >> 63) == -1 && (w >> 32) == (w - (w & 0xFFFFFFFFLL)) / 4294967296LL,
                     "model: a right shift of a negative int64 fills with its sign");
    uint64_t u = nondet_uint64();
    __CPROVER_assume((u & 0xFFFFFFFFULL) >= 0x80000000ULL);
    __CPROVER_assert((int32_t)u == (int64_t)(u & 0xFFFFFFFFULL) - 4294967296LL,
                     "model: a narrowing from uint64 to int32 keeps the low 32 bits");
}

/* Not a defect CBMC reports, but one pq-verify must see: a call to a
 * function whose body is in none of the files compiled. CBMC takes the call
 * to do nothing and verifies the assertion, so a proof through such a call
 * is vacuous. pq-verify reads CBMC's warning and refuses the run; if CBMC
 * stopped printing it, this control is what would notice. */
void pqv_selftest_undefined(int16_t r[4]);

void selftest_no_body(void) {
    int16_t r[4] = {0, 0, 0, 0};
    pqv_selftest_undefined(r);
    __CPROVER_assert(r[0] == 0, "no body: the call changed nothing");
}
