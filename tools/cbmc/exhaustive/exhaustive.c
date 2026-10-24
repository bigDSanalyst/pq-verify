/* Every input of the library's two reductions, and its zeta table against
 * FIPS 203's definition. Compiled against the library's own reduce.c and
 * ntt.c, so it checks the code that ships, as the compiler built it.
 *
 *   barrett_reduce(a), every int16 a:            r = a mod q, r in {-(q-1)/2..(q-1)/2}
 *   montgomery_reduce(a), every a the library
 *     documents, {-q*2^15 .. q*2^15 - 1}:        r = a * 2^-16 mod q, r in {-q+1..q-1}
 *   zetas[i], i = 0..127:                        17^BitRev7(i) * 2^16 mod q, centred
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "params.h"
#include "reduce.h"
#include "ntt.h"

#define NS(x) PQCLEAN_MLKEM768_CLEAN_##x
#define Q KYBER_Q

static int64_t mod(int64_t x) { int64_t r = x % Q; return r < 0 ? r + Q : r; }

static unsigned bitrev7(unsigned i) {
    unsigned r = 0;
    for (int b = 0; b < 7; b++) r |= ((i >> b) & 1u) << (6 - b);
    return r;
}

int main(void) {
    int failed = 0;

    long bad = 0, n = 0; int32_t first = 0;
    for (int32_t a = INT16_MIN; a <= INT16_MAX; a++, n++) {
        int16_t r = NS(barrett_reduce)((int16_t)a);
        if (r < -(Q - 1) / 2 || r > (Q - 1) / 2 || mod((int64_t)a - r) != 0) {
            if (!bad++) first = a;
        }
    }
    printf("barrett_reduce %ld inputs %ld wrong", n, bad);
    if (bad) printf(" first a=%" PRId32 " r=%d", first, NS(barrett_reduce)((int16_t)first));
    printf("\n");
    failed |= bad != 0;

    /* 2^16 * inv16 = 1 mod q */
    int64_t inv16 = 1;
    for (int k = 0; k < Q - 2; k++) inv16 = inv16 * 65536 % Q;   /* (2^16)^(q-2) */
    bad = 0; n = 0;
    for (int64_t a = -(int64_t)Q * 32768; a <= (int64_t)Q * 32768 - 1; a++, n++) {
        int16_t r = NS(montgomery_reduce)((int32_t)a);
        if (r <= -Q || r >= Q || mod(r - mod(a) * inv16) != 0) {
            if (!bad++) first = (int32_t)a;
        }
    }
    printf("montgomery_reduce %ld inputs %ld wrong", n, bad);
    if (bad) printf(" first a=%" PRId32 " r=%d", first, NS(montgomery_reduce)(first));
    printf("\n");
    failed |= bad != 0;

    bad = 0;
    int first_i = -1;
    for (unsigned i = 0; i < 128; i++) {
        int64_t z = 1;
        for (unsigned k = 0; k < bitrev7(i); k++) z = z * 17 % Q;
        int64_t want = z * 65536 % Q;
        if (want > Q / 2) want -= Q;
        if (NS(zetas)[i] != want) { if (!bad++) first_i = (int)i; }
    }
    printf("zetas 128 entries %ld wrong", bad);
    if (bad) printf(" first i=%d has %d", first_i, NS(zetas)[first_i]);
    printf("\n");
    failed |= bad != 0;

    return failed;
}
