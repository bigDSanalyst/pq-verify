/* FIPS 203's constants. Every harness states its inputs and bounds in the
 * library's KYBER_N, KYBER_Q and KYBER_INDCPA_MSGBYTES, so a params.h that
 * gives other values is not ML-KEM: the build stops here rather than prove
 * bounds for another n or q. Included after the library's params.h. */
#ifndef PQV_FIPS203_H
#define PQV_FIPS203_H
#if !defined(KYBER_N) || !defined(KYBER_Q) || !defined(KYBER_INDCPA_MSGBYTES)
#error "params.h does not define KYBER_N, KYBER_Q and KYBER_INDCPA_MSGBYTES"
#elif KYBER_N != 256 || KYBER_Q != 3329 || KYBER_INDCPA_MSGBYTES != 32
#error "params.h is not FIPS 203's: KYBER_N must be 256, KYBER_Q 3329, KYBER_INDCPA_MSGBYTES 32"
#endif
#endif
