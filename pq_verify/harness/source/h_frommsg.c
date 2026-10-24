/* FIPS 203 Decompress_1(ByteDecode_1(m)) on every 32-byte message. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips203.h"
#include "poly.h"

void harness(void) {
    poly r;
    uint8_t msg[KYBER_INDCPA_MSGBYTES];
    for (int i = 0; i < KYBER_INDCPA_MSGBYTES; i++)
        msg[i] = nondet_uint8();
    PQV_SYM_poly_frommsg(&r, msg);
    /* FIPS 203's BytesToBits: coefficient 8i+j comes from bit j of byte i */
    for (int i = 0; i < KYBER_N; i++) {
        int bit = (msg[i / 8] >> (i % 8)) & 1;
        __CPROVER_assert(r.coeffs[i] == (bit ? (KYBER_Q + 1) / 2 : 0),
                         "frommsg: coefficient 8i+j is (q+1)/2 if bit j of byte i is set, else 0");
    }
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
