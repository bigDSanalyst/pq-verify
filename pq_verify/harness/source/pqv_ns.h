/* The library's names. pq-verify reads the prefix they carry off the
 * library's reduce.h and passes it as -DPQV_PREFIX=... (empty when the
 * headers rename the functions themselves, as pq-crystals' reference does).
 * A library that names a function some other way is given that name with
 * --source-symbol ROLE=NAME, which defines PQV_SYM_<role>. Every harness is
 * written against FIPS 203's objects, a polynomial of 256 coefficients mod q,
 * and reaches the library only through these names. */
#ifndef PQV_NS_H
#define PQV_NS_H
#include <stdint.h>

#ifndef PQV_PREFIX
#define PQV_PREFIX
#endif
#define PQV_CAT2(a, b) a##b
#define PQV_CAT(a, b) PQV_CAT2(a, b)
#define NS(x) PQV_CAT(PQV_PREFIX, x)

#ifndef PQV_SYM_montgomery_reduce
#define PQV_SYM_montgomery_reduce NS(montgomery_reduce)
#endif
#ifndef PQV_SYM_barrett_reduce
#define PQV_SYM_barrett_reduce NS(barrett_reduce)
#endif
#ifndef PQV_SYM_zetas
#define PQV_SYM_zetas NS(zetas)
#endif
#ifndef PQV_SYM_ntt
#define PQV_SYM_ntt NS(ntt)
#endif
#ifndef PQV_SYM_poly_reduce
#define PQV_SYM_poly_reduce NS(poly_reduce)
#endif
#ifndef PQV_SYM_poly_basemul_montgomery
#define PQV_SYM_poly_basemul_montgomery NS(poly_basemul_montgomery)
#endif
#ifndef PQV_SYM_poly_frommsg
#define PQV_SYM_poly_frommsg NS(poly_frommsg)
#endif

#ifndef PQV_SYM_reduce32
#define PQV_SYM_reduce32 NS(reduce32)
#endif
#ifndef PQV_SYM_caddq
#define PQV_SYM_caddq NS(caddq)
#endif
#ifndef PQV_SYM_freeze
#define PQV_SYM_freeze NS(freeze)
#endif
#ifndef PQV_SYM_invntt_tomont
#define PQV_SYM_invntt_tomont NS(invntt_tomont)
#endif
#ifndef PQV_SYM_poly_pointwise_montgomery
#define PQV_SYM_poly_pointwise_montgomery NS(poly_pointwise_montgomery)
#endif
#ifndef PQV_SYM_poly_chknorm
#define PQV_SYM_poly_chknorm NS(poly_chknorm)
#endif
#ifndef PQV_SYM_power2round
#define PQV_SYM_power2round NS(power2round)
#endif
#ifndef PQV_SYM_decompose
#define PQV_SYM_decompose NS(decompose)
#endif
#ifndef PQV_SYM_use_hint
#define PQV_SYM_use_hint NS(use_hint)
#endif
int16_t nondet_int16(void);
uint8_t nondet_uint8(void);
int32_t nondet_int32(void);
int64_t nondet_int64(void);
#endif
