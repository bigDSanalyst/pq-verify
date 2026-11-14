/* A stand-in FN-DSA signer for pq_verify.ct_fndsa's tests. The NIST API's
   keypair and signature; signing draws a 40-byte nonce and a 48-byte seed
   from randombytes(), as PQClean's Falcon does, and takes one branch on
   secret data at a site the policy lists: the sampler's rejection, on the
   very source line PQClean's has (sampler and BerExp are named as PQClean
   names them). By -D, a planted leak:
     LEAK_BRANCH  a branch on a secret-key byte, outside the listed sites
     LEAK_INDEX   a table read indexed by a secret-key byte
     NO_SEED      no secret randomness: only the nonce is drawn */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* The driver's, which takes this one's place when it is loaded. */
__attribute__((weak)) int randombytes(uint8_t *out, size_t n) {
    memset(out, 0x42, n);
    return 0;
}

typedef struct { uint8_t p; } sampler_context;
static volatile int sink;
static const volatile uint8_t table[256];

static int BerExp(uint8_t *p, uint8_t x, uint8_t ccs) {
    uint32_t w = (uint32_t)(*p ^ x ^ ccs) << 31;
    return (int)(w >> 31);
}

__attribute__((noinline)) static int sampler(sampler_context *spc, uint8_t x, uint8_t ccs) {
    if (BerExp(&spc->p, x, ccs)) {
        sink = 1;
        return 1;
    }
    return 0;
}

int crypto_sign_keypair(uint8_t *pk, uint8_t *sk) {
    memset(pk, 0, 897);
    pk[0] = 0x09;
    sk[0] = 0x59;
    for (int i = 1; i < 1281; i++)
        sk[i] = (uint8_t)(i * 7);
    return 0;
}

int crypto_sign_signature(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,
                          const uint8_t *sk) {
    uint8_t nonce[40], seed[48];
    sampler_context spc;
    randombytes(nonce, sizeof nonce);
#ifdef NO_SEED
    memset(seed, 0, sizeof seed);
#else
    randombytes(seed, sizeof seed);
#endif
    spc.p = seed[0];
    int z = sampler(&spc, sk[5], (uint8_t)(mlen ? m[0] : 0));
#ifdef LEAK_BRANCH
    if (sk[7] & 1) {
        sink = 2;
    }
#endif
#ifdef LEAK_INDEX
    sink = table[sk[9]];
#endif
    sig[0] = 0x39;
    memcpy(sig + 1, nonce, sizeof nonce);
    sig[41] = (uint8_t)z;
    *siglen = 42;
    return 0;
}

int crypto_sign_verify(const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
                       const uint8_t *pk) {
    (void)sig; (void)siglen; (void)m; (void)mlen; (void)pk;
    return -1;
}
