/* poly_reduce on every polynomial reduce32 accepts: each coefficient at most
 * 2^31 - 2^22 - 1. No undefined behaviour, and every output in
 * {-6283009, ..., 6283008}: the reference's comment says -6283008, but
 * reduce32(-2143289344) is -6283009. The exhaustive test checks reduce32's
 * congruence. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "poly.h"

void harness(void) {
    poly a;
    for (int i = 0; i < N; i++) {
        a.coeffs[i] = nondet_int32();
        __CPROVER_assume(a.coeffs[i] <= 2147483647 - (1 << 22));
    }
    PQV_SYM_poly_reduce(&a);
    for (int i = 0; i < N; i++)
        __CPROVER_assert(a.coeffs[i] >= -6283009 && a.coeffs[i] <= 6283008,
                         "poly_reduce: every output in {-6283009, ..., 6283008}");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
