/* FIPS 204's constants. Every ML-DSA harness states its inputs and bounds in
 * the library's N, Q, D and GAMMA2, so a params.h that gives other values, or
 * a K, L, ETA, GAMMA1, GAMMA2 that is none of FIPS 204's three parameter sets,
 * is not ML-DSA: the build stops here rather than prove bounds for another n
 * or q. Included after the library's params.h. */
#ifndef PQV_FIPS204_H
#define PQV_FIPS204_H
#if !defined(N) || !defined(Q) || !defined(D) || !defined(K) || !defined(L) || \
    !defined(ETA) || !defined(GAMMA1) || !defined(GAMMA2)
#error "params.h does not define N, Q, D, K, L, ETA, GAMMA1 and GAMMA2"
#elif N != 256 || Q != 8380417 || D != 13
#error "params.h is not FIPS 204's: N must be 256, Q 8380417, D 13"
#elif !((K == 4 && L == 4 && ETA == 2 && GAMMA1 == (1 << 17) && GAMMA2 == (Q - 1) / 88) || \
        (K == 6 && L == 5 && ETA == 4 && GAMMA1 == (1 << 19) && GAMMA2 == (Q - 1) / 32) || \
        (K == 8 && L == 7 && ETA == 2 && GAMMA1 == (1 << 19) && GAMMA2 == (Q - 1) / 32))
#error "params.h is none of FIPS 204's parameter sets (K, L, ETA, GAMMA1, GAMMA2)"
#endif
/* montgomery_reduce's contract: {-2^31 q, ..., 2^31 q - 1}. The reference's
 * comment says -2^31 q <= a <= 2^31 q, but at a = 2^31 q it returns q. */
#define PQV_MONT_MIN (-((int64_t)Q << 31))
#define PQV_MONT_MAX (((int64_t)Q << 31) - 1)
#endif
