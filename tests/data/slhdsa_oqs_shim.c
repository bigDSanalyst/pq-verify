/*
 * Test shim: liboqs's SLH-DSA API for SLH-DSA-SHA2-128f, as liboqs 0.16.0
 * shapes it (src/sig/slh_dsa/wrappers): a pure algorithm and one HashSLH-DSA
 * algorithm per approved hash, each with keypair, sign, sign_with_ctx_str,
 * verify and verify_with_ctx_str; the RNG hook OQS_randombytes_custom_algorithm;
 * OQS_SIG_new for the sizes; and slh_sign_internal / slh_verify_internal with
 * the parameter object, which liboqs exports through its internal_api.patch.
 * The wrappers draw their randomness as liboqs's do (3n bytes for a key, n for
 * addrnd) and call back into Python (tests/test_pqverify.py), which answers
 * NIST's inputs from NIST's results and any other with a stand-in signature.
 *
 * Faults in the wrappers, by compile flag:
 *   -DPQVTEST_DROP_CTX          pure sign_with_ctx_str signs with no context
 *   -DPQVTEST_PLAIN_CTX         pure sign (no context) signs with the context "x"
 *   -DPQVTEST_SHORT_ADDRND      pure sign_with_ctx_str draws n - 1 bytes of addrnd
 *   -DPQVTEST_WRONG_HASH        the SHA2-384 algorithm signs and verifies as SHA2-256
 *   -DPQVTEST_VERIFY_WRONG_HASH the SHA2-384 algorithm verifies as SHA2-256; NIST
 *                               has no valid SHA2-384 sigVer case for this set
 *   -DPQVTEST_NO_KEYPAIR_RNG    keypair draws no randomness
 *   -DPQVTEST_BAD_SIGLEN        OQS_SIG_new gives the pure algorithm a signature
 *                               one byte short
 *   -DPQVTEST_VERIFY_DROP_CTX   pure verify_with_ctx_str verifies with no context
 */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define N 16
#define SIGLEN 17088

typedef struct { int set; } slh_param_t;
const slh_param_t slh_dsa_sha2_128f = {1};

typedef int (*pqv_rbg)(uint8_t *, size_t);
typedef int (*kg_cb)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *, const uint8_t *);
typedef int (*kgr_cb)(uint8_t *, uint8_t *, pqv_rbg);
/* iface: 0 internal, 1 pure, 2 pre-hash */
typedef size_t (*sign_cb)(int, uint8_t *, const uint8_t *, size_t, const uint8_t *, size_t,
                          const char *, const uint8_t *, const uint8_t *);
typedef int (*ver_cb)(int, const uint8_t *, size_t, const uint8_t *, size_t,
                      const uint8_t *, size_t, const char *, const uint8_t *);
static kg_cb KG; static sign_cb SIGN; static ver_cb VER;

/* the same registration as slhdsa_shim.c; the key callback with its own RBG
 * is not used: liboqs's keypair draws through OQS_randombytes */
void pqvtest_slhdsa_register(kg_cb a, kgr_cb b, sign_cb c, ver_cb d)
{
    (void)b; KG = a; SIGN = c; VER = d;
}

typedef void (*rng_fn)(uint8_t *, size_t);
static rng_fn RNG;
static int CUSTOM;

void OQS_randombytes_custom_algorithm(rng_fn f) { RNG = f; CUSTOM = 1; }
int OQS_randombytes_switch_algorithm(const char *alg) { (void)alg; RNG = 0; CUSTOM = 0; return 0; }
/* 1 while pq-verify's deterministic hook is installed: it must not outlive the audit */
int pqvtest_rng_is_custom(void) { return CUSTOM; }

static void randombytes(uint8_t *x, size_t n)
{
    if (RNG) RNG(x, n); else memset(x, 0x5a, n);
}

static int keypair(uint8_t *pk, uint8_t *sk)
{
    uint8_t seed[3 * N] = {0};
#ifndef PQVTEST_NO_KEYPAIR_RNG
    randombytes(seed, sizeof seed);          /* SK.seed || SK.prf || PK.seed */
#endif
    return KG(sk, pk, seed, seed + N, seed + 2 * N) == 0 ? 0 : -1;
}

static const char *hash_of(const char *ph, int verifying)
{
#ifdef PQVTEST_WRONG_HASH
    if (ph && strcmp(ph, "SHA2-384") == 0) return "SHA2-256";
#endif
#ifdef PQVTEST_VERIFY_WRONG_HASH
    if (verifying && ph && strcmp(ph, "SHA2-384") == 0) return "SHA2-256";
#endif
    (void)verifying;
    return ph;
}

static int sign(int iface, const char *ph, uint8_t *sig, size_t *siglen, const uint8_t *m,
                size_t mlen, const uint8_t *ctx, size_t ctxlen, const uint8_t *sk, int with_ctx)
{
    uint8_t addrnd[N] = {0};
    size_t draw = N;
#ifdef PQVTEST_DROP_CTX
    if (iface == 1 && with_ctx) { ctx = NULL; ctxlen = 0; }
#endif
#ifdef PQVTEST_PLAIN_CTX
    if (iface == 1 && !with_ctx) { ctx = (const uint8_t *)"x"; ctxlen = 1; }
#endif
#ifdef PQVTEST_SHORT_ADDRND
    if (iface == 1 && with_ctx) draw = N - 1;
#endif
    randombytes(addrnd, draw);
    *siglen = SIGN(iface, sig, m, mlen, ctx, ctxlen, hash_of(ph, 0), sk, addrnd);
    return *siglen ? 0 : -1;
}

static int verify(int iface, const char *ph, const uint8_t *m, size_t mlen, const uint8_t *sig,
                  size_t siglen, const uint8_t *ctx, size_t ctxlen, const uint8_t *pk,
                  int with_ctx)
{
#ifdef PQVTEST_VERIFY_DROP_CTX
    if (iface == 1 && with_ctx) { ctx = NULL; ctxlen = 0; }
#endif
    (void)with_ctx;
    return VER(iface, m, mlen, sig, siglen, ctx, ctxlen, hash_of(ph, 1), pk) ? 0 : -1;
}

#define WRAP(PFX, IFACE, PH)                                                                 \
    int PFX##keypair(uint8_t *pk, uint8_t *sk) { return keypair(pk, sk); }                  \
    int PFX##sign(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,              \
                  const uint8_t *sk)                                                         \
    { return sign(IFACE, PH, sig, siglen, m, mlen, NULL, 0, sk, 0); }                        \
    int PFX##sign_with_ctx_str(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen, \
                               const uint8_t *ctx, size_t ctxlen, const uint8_t *sk)         \
    { return sign(IFACE, PH, sig, siglen, m, mlen, ctx, ctxlen, sk, 1); }                    \
    int PFX##verify(const uint8_t *m, size_t mlen, const uint8_t *sig, size_t siglen,       \
                    const uint8_t *pk)                                                       \
    { return verify(IFACE, PH, m, mlen, sig, siglen, NULL, 0, pk, 0); }                      \
    int PFX##verify_with_ctx_str(const uint8_t *m, size_t mlen, const uint8_t *sig,         \
                                 size_t siglen, const uint8_t *ctx, size_t ctxlen,           \
                                 const uint8_t *pk)                                          \
    { return verify(IFACE, PH, m, mlen, sig, siglen, ctx, ctxlen, pk, 1); }

WRAP(OQS_SIG_slh_dsa_pure_sha2_128f_, 1, NULL)
WRAP(OQS_SIG_slh_dsa_sha2_224_prehash_sha2_128f_, 2, "SHA2-224")
WRAP(OQS_SIG_slh_dsa_sha2_256_prehash_sha2_128f_, 2, "SHA2-256")
WRAP(OQS_SIG_slh_dsa_sha2_384_prehash_sha2_128f_, 2, "SHA2-384")
WRAP(OQS_SIG_slh_dsa_sha2_512_prehash_sha2_128f_, 2, "SHA2-512")
WRAP(OQS_SIG_slh_dsa_sha2_512_224_prehash_sha2_128f_, 2, "SHA2-512/224")
WRAP(OQS_SIG_slh_dsa_sha2_512_256_prehash_sha2_128f_, 2, "SHA2-512/256")
WRAP(OQS_SIG_slh_dsa_sha3_224_prehash_sha2_128f_, 2, "SHA3-224")
WRAP(OQS_SIG_slh_dsa_sha3_256_prehash_sha2_128f_, 2, "SHA3-256")
WRAP(OQS_SIG_slh_dsa_sha3_384_prehash_sha2_128f_, 2, "SHA3-384")
WRAP(OQS_SIG_slh_dsa_sha3_512_prehash_sha2_128f_, 2, "SHA3-512")
WRAP(OQS_SIG_slh_dsa_shake_128_prehash_sha2_128f_, 2, "SHAKE-128")
WRAP(OQS_SIG_slh_dsa_shake_256_prehash_sha2_128f_, 2, "SHAKE-256")

/* slhdsa-c's internal interface, as liboqs's internal_api.patch exports it */
size_t slh_sign_internal(uint8_t *sig, const uint8_t *m, size_t m_sz, const uint8_t *sk,
                         const uint8_t *addrnd, const slh_param_t *prm)
{
    (void)prm; return SIGN(0, sig, m, m_sz, NULL, 0, NULL, sk, addrnd);
}
int slh_verify_internal(const uint8_t *m, size_t m_sz, const uint8_t *sig, size_t sig_sz,
                        const uint8_t *pk, const slh_param_t *prm)
{
    (void)prm; return VER(0, m, m_sz, sig, sig_sz, NULL, 0, NULL, pk);
}

/* the head of liboqs's OQS_SIG (src/sig/sig.h) */
typedef struct {
    const char *method_name;
    const char *alg_version;
    uint8_t claimed_nist_level;
    bool euf_cma;
    bool suf_cma;
    bool sig_with_ctx_support;
    size_t length_public_key;
    size_t length_secret_key;
    size_t length_signature;
} oqs_sig_head;

void *OQS_SIG_new(const char *name)
{
    size_t len = strlen(name);
    if (strncmp(name, "SLH_DSA_", 8) != 0 || len < 10 ||
        strcmp(name + len - 10, "_SHA2_128F") != 0)
        return NULL;                         /* only this parameter set is built */
    oqs_sig_head *s = calloc(1, sizeof *s);
    if (!s) return NULL;
    s->method_name = "SLH-DSA";
    s->alg_version = "FIPS205";
    s->claimed_nist_level = 1;
    s->euf_cma = true;
    s->sig_with_ctx_support = true;
    s->length_public_key = 2 * N;
    s->length_secret_key = 4 * N;
    s->length_signature = SIGLEN;
#ifdef PQVTEST_BAD_SIGLEN
    if (strcmp(name, "SLH_DSA_PURE_SHA2_128F") == 0) s->length_signature = SIGLEN - 1;
#endif
    return s;
}
void OQS_SIG_free(void *s) { free(s); }
