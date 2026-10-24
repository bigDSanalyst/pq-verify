/* The forward NTT on every element of R_q written with representatives in
 * (-q, q): any 256 coefficients there, which covers FIPS 203's Z_q = {0..q-1}
 * and the small signed coefficients the library feeds it. */
#include "pqv_ns.h"
#include "params.h"
#include "ntt.h"

void harness(void) {
    int16_t r[KYBER_N];
    for (int i = 0; i < KYBER_N; i++) {
        r[i] = nondet_int16();
        __CPROVER_assume(r[i] > -KYBER_Q && r[i] < KYBER_Q);
    }
    NS(ntt)(r);
    for (int i = 0; i < KYBER_N; i++)
        __CPROVER_assert(r[i] > -8 * KYBER_Q && r[i] < 8 * KYBER_Q,
                         "ntt: every output coefficient in (-8q, 8q)");
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
