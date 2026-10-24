/* poly_pointwise_montgomery on every pair of polynomials with coefficients in
 * (-9q, 9q): the NTT's outputs, and the matrix A's entries in [0, q). Each
 * product is under 81 q^2, inside montgomery_reduce's contract: no undefined
 * behaviour, and every output in (-q, q). */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "poly.h"

void harness(void) {
    poly a, b, c;
    for (int i = 0; i < N; i++) {
        a.coeffs[i] = nondet_int32();
        b.coeffs[i] = nondet_int32();
        __CPROVER_assume(a.coeffs[i] > -9 * Q && a.coeffs[i] < 9 * Q);
        __CPROVER_assume(b.coeffs[i] > -9 * Q && b.coeffs[i] < 9 * Q);
    }
    PQV_SYM_poly_pointwise_montgomery(&c, &a, &b);
    for (int i = 0; i < N; i++)
        __CPROVER_assert(c.coeffs[i] > -Q && c.coeffs[i] < Q,
                         "poly_pointwise_montgomery: every output in (-q, q)");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
