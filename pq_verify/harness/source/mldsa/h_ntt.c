/* ntt on every polynomial with coefficients in (-q, q). FIPS 204 applies the
 * NTT to s1 and s2 (|c| <= eta), t0 (in (-2^12, 2^12]), y and z (|c| <= gamma1),
 * the challenge c (in {-1, 0, 1}) and t1 * 2^d (in [0, q)): all in (-q, q).
 * No undefined behaviour, no int32 overflow, and every output in (-9q, 9q):
 * each of the 8 layers adds less than q. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "ntt.h"

void harness(void) {
    int32_t a[N];
    for (int i = 0; i < N; i++) {
        a[i] = nondet_int32();
        __CPROVER_assume(a[i] > -Q && a[i] < Q);
    }
    PQV_SYM_ntt(a);
    for (int i = 0; i < N; i++)
        __CPROVER_assert(a[i] > -9 * Q && a[i] < 9 * Q, "ntt: every output in (-9q, 9q)");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
