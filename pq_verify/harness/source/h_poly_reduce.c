/* poly_reduce on every possible polynomial: all 256 coefficients any int16.
 * Uses the library's real barrett_reduce, not the contract. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips203.h"
#include "poly.h"

void harness(void) {
    poly r;
    for (int i = 0; i < KYBER_N; i++)
        r.coeffs[i] = nondet_int16();
    PQV_SYM_poly_reduce(&r);
    for (int i = 0; i < KYBER_N; i++)
        __CPROVER_assert(r.coeffs[i] >= -(KYBER_Q - 1) / 2 && r.coeffs[i] <= (KYBER_Q - 1) / 2,
                         "poly_reduce: every output coefficient in {-(q-1)/2, ..., (q-1)/2}");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
