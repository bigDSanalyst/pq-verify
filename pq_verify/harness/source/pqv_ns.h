/* The library's names, from the prefix pq-verify reads off its source and
 * passes as -DPQV_PREFIX=... (empty when the headers rename the functions
 * themselves, as pq-crystals' reference does). Every harness is written
 * against FIPS 203's objects, a polynomial of 256 coefficients mod q, and
 * reaches the library only through NS(). */
#ifndef PQV_NS_H
#define PQV_NS_H
#include <stdint.h>

#ifndef PQV_PREFIX
#define PQV_PREFIX
#endif
#define PQV_CAT2(a, b) a##b
#define PQV_CAT(a, b) PQV_CAT2(a, b)
#define NS(x) PQV_CAT(PQV_PREFIX, x)

int16_t nondet_int16(void);
uint8_t nondet_uint8(void);
#endif
