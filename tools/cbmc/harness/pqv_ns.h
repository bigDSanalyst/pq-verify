/* The library's names. Only this file knows them; every harness is written
 * against FIPS 203's objects (a polynomial of 256 coefficients mod q). */
#ifndef PQV_NS_H
#define PQV_NS_H
#define NS(x) PQCLEAN_MLKEM768_CLEAN_##x
#include <stdint.h>
int16_t nondet_int16(void);
uint8_t nondet_uint8(void);
#endif
