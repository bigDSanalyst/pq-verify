/*
 * Test shim for --audit-mceliece --constant-time: a fake KEM with
 * mceliece348864's sizes. Encapsulation draws its randomness through
 * randombytes() in a sampler function of its own, with a rejection branch
 * on the fresh bytes (listed, not judged, as the submitters' sampler is).
 * Planted leaks, by -D: LEAK_ENC_BRANCH (a branch on the error vector
 * outside the sampler), LEAK_DEC_BRANCH (a branch on the private key),
 * LEAK_DEC_INDEX (a table indexed by the private key), NO_RNG
 * (encapsulation draws nothing through randombytes()).
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/random.h>

#define PK 261120
#define SK 6492
#define CT 96

/* Under memcheck the driver's randombytes() interposes on this one. */
int randombytes(uint8_t *out, size_t n) {
    while (n) {
        ssize_t r = getrandom(out, n, 0);
        if (r <= 0) return -1;
        out += r;
        n -= (size_t)r;
    }
    return 0;
}

static volatile uint8_t sink;

__attribute__((noinline)) static void sample(uint8_t *e) {
    uint8_t r[CT];
    do {
        randombytes(r, CT);
    } while (r[0] == 0xFF);            /* rejection on its own randomness */
    memcpy(e, r, CT);
}

int shim_mce_keypair(uint8_t *pk, uint8_t *sk) {
    randombytes(sk, SK);
    memset(pk, 0, PK);
    memcpy(pk, sk, 32);
    return 0;
}

int shim_mce_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk) {
    uint8_t e[CT];
#ifdef NO_RNG
    memset(e, 7, CT);
#else
    sample(e);
#endif
    for (int i = 0; i < CT; i++) ct[i] = e[i] ^ pk[i];
#ifdef LEAK_ENC_BRANCH
    if (e[1] & 1) sink = 1;            /* a branch on the error vector */
#endif
    for (int i = 0; i < 32; i++) ss[i] = e[i];
    return 0;
}

int shim_mce_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk) {
    for (int i = 0; i < 32; i++) ss[i] = ct[i] ^ sk[i];
#ifdef LEAK_DEC_BRANCH
    if (sk[5] & 1) sink = 1;           /* a branch on the private key */
#endif
#ifdef LEAK_DEC_INDEX
    static uint8_t table[256];
    for (int i = 0; i < 256; i++) table[i] = (uint8_t)(i * 7);
    ss[1] ^= table[sk[7]];             /* a table indexed by the private key */
#endif
    return 0;
}
