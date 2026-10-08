/*
 * Test shim: liboqs's public ML-DSA-44 API (OQS_SIG_ml_dsa_44_*) and its RNG
 * hook (OQS_randombytes_custom_algorithm), each call forwarded to Python
 * (dilithium-py), so pq-verify's "oqs" calling convention -- the message-first
 * argument order, the *_with_ctx_str variants, randomness drawn through the
 * hook -- is tested without building liboqs.
 *
 * Faults, by compile flag:
 *   -DPQVTEST_DROP_CTX       sign_with_ctx_str signs as if the context were empty
 *   -DPQVTEST_OVERDRAW       keypair draws 48 random bytes, not FIPS 204's 32
 *   -DPQVTEST_SECOND_IMPL    also exports an mldsa-native-style backend, so
 *                            two implementations are ambiguous
 */
#include <stddef.h>
#include <stdint.h>

typedef void (*rng_fn)(uint8_t *, size_t);
typedef int (*kp_cb)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*sign_cb)(uint8_t *, size_t *, const uint8_t *, size_t, const uint8_t *, size_t,
                       const uint8_t *, const uint8_t *);
typedef int (*ver_cb)(const uint8_t *, size_t, const uint8_t *, size_t, const uint8_t *, size_t,
                      const uint8_t *);

static rng_fn RNG;
static kp_cb KP;
static sign_cb SG;
static ver_cb VF;
static const uint8_t EMPTY[1];

static int CUSTOM;

void OQS_randombytes_custom_algorithm(rng_fn f) { RNG = f; CUSTOM = 1; }
int OQS_randombytes_switch_algorithm(const char *alg) { (void)alg; CUSTOM = 0; return 0; }
/* 1 while pq-verify's deterministic hook is installed: it must not outlive the audit */
int pqvtest_rng_is_custom(void) { return CUSTOM; }
void pqvtest_oqs_register(kp_cb k, sign_cb s, ver_cb v) { KP = k; SG = s; VF = v; }

int OQS_SIG_ml_dsa_44_keypair(uint8_t *pk, uint8_t *sk) {
#ifdef PQVTEST_OVERDRAW
    uint8_t seed[48];
    RNG(seed, 48);
#else
    uint8_t seed[32];
    RNG(seed, 32);
#endif
    return KP(pk, sk, seed);
}

int OQS_SIG_ml_dsa_44_sign_with_ctx_str(uint8_t *sig, size_t *siglen, const uint8_t *m,
                                        size_t mlen, const uint8_t *ctx, size_t ctxlen,
                                        const uint8_t *sk) {
    uint8_t rnd[32];
    RNG(rnd, 32);
#ifdef PQVTEST_DROP_CTX
    (void)ctx; (void)ctxlen;
    return SG(sig, siglen, m, mlen, EMPTY, 0, rnd, sk);
#else
    return SG(sig, siglen, m, mlen, ctx, ctxlen, rnd, sk);
#endif
}

int OQS_SIG_ml_dsa_44_sign(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,
                           const uint8_t *sk) {
    return OQS_SIG_ml_dsa_44_sign_with_ctx_str(sig, siglen, m, mlen, EMPTY, 0, sk);
}

int OQS_SIG_ml_dsa_44_verify_with_ctx_str(const uint8_t *m, size_t mlen, const uint8_t *sig,
                                          size_t siglen, const uint8_t *ctx, size_t ctxlen,
                                          const uint8_t *pk) {
    return VF(m, mlen, sig, siglen, ctx, ctxlen, pk);
}

int OQS_SIG_ml_dsa_44_verify(const uint8_t *m, size_t mlen, const uint8_t *sig, size_t siglen,
                             const uint8_t *pk) {
    return VF(m, mlen, sig, siglen, EMPTY, 0, pk);
}

#ifdef PQVTEST_SECOND_IMPL
int PQCP_MLDSA_NATIVE_MLDSA44_C_keypair(uint8_t *pk, uint8_t *sk) {
    return OQS_SIG_ml_dsa_44_keypair(pk, sk);
}
int PQCP_MLDSA_NATIVE_MLDSA44_C_verify(const uint8_t *sig, size_t siglen, const uint8_t *m,
                                       size_t mlen, const uint8_t *ctx, size_t ctxlen,
                                       const uint8_t *pk) {
    return VF(m, mlen, sig, siglen, ctx, ctxlen, pk);
}
#endif
