/* Multiplication in the NTT domain (FIPS 203 MultiplyNTTs) on every pair of
 * NTT-domain polynomials with representatives in (-q, q). */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips203.h"
#include "poly.h"

void harness(void) {
    poly r, a, b;
    for (int i = 0; i < KYBER_N; i++) {
        a.coeffs[i] = nondet_int16();
        b.coeffs[i] = nondet_int16();
        __CPROVER_assume(a.coeffs[i] > -KYBER_Q && a.coeffs[i] < KYBER_Q);
        __CPROVER_assume(b.coeffs[i] > -KYBER_Q && b.coeffs[i] < KYBER_Q);
    }
    PQV_SYM_poly_basemul_montgomery(&r, &a, &b);
    for (int i = 0; i < KYBER_N; i++)
        __CPROVER_assert(r.coeffs[i] > -2 * KYBER_Q && r.coeffs[i] < 2 * KYBER_Q,
                         "basemul: every output coefficient in (-2q, 2q)");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
