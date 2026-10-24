/* invntt_tomont on every polynomial with coefficients in (-q, q), which FIPS
 * 204's algorithms give it: pointwise products, and sums reduced first. Its
 * sums go unreduced through 8 layers, up to 256 (q - 1) = 2,145,386,496, just
 * under 2^31: no undefined behaviour, no int32 overflow, every output in
 * (-q, q). */
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
    PQV_SYM_invntt_tomont(a);
    for (int i = 0; i < N; i++)
        __CPROVER_assert(a[i] > -Q && a[i] < Q, "invntt_tomont: every output in (-q, q)");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
