/* poly_chknorm on every polynomial reduce32 can return (-6283009 <= c <=
 * 6283008) and every int32 bound B, FIPS 204's gamma1 - beta, gamma2 - beta
 * and gamma2 among them: no undefined behaviour, a result of 0 or 1, and 1
 * whenever B > (q-1)/8. Its absolute value is a mask, c - ((c >> 31) & 2 * c):
 * the doubling must not overflow, and the shift is of a negative value, which
 * C leaves to the compiler (CBMC's model of it is pinned by the self-test, the
 * compiler's by the exhaustive test).
 *
 * That it returns 1 exactly when some |coefficient| >= B is not checked:
 * none of the solvers tried (MiniSat, CaDiCaL, Z3) decided that equivalence
 * over 256 coefficients in reasonable time. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "poly.h"

void harness(void) {
    poly a;
    int32_t B = nondet_int32();
    for (int i = 0; i < N; i++) {
        a.coeffs[i] = nondet_int32();
        __CPROVER_assume(a.coeffs[i] >= -6283009 && a.coeffs[i] <= 6283008);
    }
    int r = PQV_SYM_poly_chknorm(&a, B);
    __CPROVER_assert(r == 0 || r == 1, "poly_chknorm: the result is 0 or 1");
    __CPROVER_assert(B <= (Q - 1) / 8 || r == 1, "poly_chknorm: 1 whenever B > (q-1)/8");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
