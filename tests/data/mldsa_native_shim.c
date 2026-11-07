/*
 * Test shim: mldsa-native's v2 API for ML-DSA-65, forwarded to the callbacks
 * the test registers (backed by dilithium-py; the same three as mldsa_shim.c).
 * It exports keypair_internal, the pure signature and verify (signature draws
 * rnd through randombytes(): link pq-verify's randomness harness), and the
 * native HashML-DSA pair, signature_pre_hash_internal and
 * verify_pre_hash_internal. Those take the digest PH and an MLD_PREHASH_*
 * number, and format M' = 1 || |ctx| || ctx || OID || PH themselves, checking
 * PH's length, as mldsa-native does.
 *
 * Fault, by compile flag:
 *   -DPQVTEST_VERIFY_SHA3_512_AS_SHA2_512
 *       verify_pre_hash_internal encodes SHA3-512's OID as SHA2-512's (both
 *       64-byte digests, so the length check passes); signing is right
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

int randombytes(uint8_t *out, size_t n);

#define SIGBYTES 3309

typedef int (*kp_cb)(uint8_t *pk, uint8_t *sk, const uint8_t *seed);
typedef int (*sig_cb)(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,
                      const uint8_t *pre, size_t prelen, const uint8_t *rnd,
                      const uint8_t *sk);
typedef int (*ver_cb)(const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
                      const uint8_t *pre, size_t prelen, const uint8_t *pk);

static kp_cb KP;
static sig_cb SG;
static ver_cb VF;

void pqvtest_register(kp_cb kp, sig_cb sg, ver_cb vf, int extra_rng) {
  (void)extra_rng;
  KP = kp; SG = sg; VF = vf;
}

int PQVTEST_MLDSA_NATIVE_MLDSA65_keypair_internal(uint8_t *pk, uint8_t *sk,
                                                  const uint8_t *seed) {
  return KP(pk, sk, seed);
}

static size_t pure_prefix(uint8_t *pre, const uint8_t *ctx, size_t ctxlen) {
  if (ctxlen > 255) return 0;
  pre[0] = 0;
  pre[1] = (uint8_t)ctxlen;
  if (ctxlen) memcpy(pre + 2, ctx, ctxlen);
  return 2 + ctxlen;
}

int PQVTEST_MLDSA_NATIVE_MLDSA65_signature(uint8_t *sig, const uint8_t *m, size_t mlen,
                                           const uint8_t *ctx, size_t ctxlen,
                                           const uint8_t *sk) {
  uint8_t pre[2 + 255], rnd[32];
  size_t siglen, n = pure_prefix(pre, ctx, ctxlen);
  if (!n) return -1;
  randombytes(rnd, sizeof rnd);
  return SG(sig, &siglen, m, mlen, pre, n, rnd, sk);
}

int PQVTEST_MLDSA_NATIVE_MLDSA65_verify(const uint8_t *sig, const uint8_t *m, size_t mlen,
                                        const uint8_t *ctx, size_t ctxlen,
                                        const uint8_t *pk) {
  uint8_t pre[2 + 255];
  size_t n = pure_prefix(pre, ctx, ctxlen);
  if (!n) return -1;
  return VF(sig, SIGBYTES, m, mlen, pre, n, pk);
}

/* MLD_PREHASH_* (mldsa_native.h) -> the hash's OID arc under
 * 2.16.840.1.101.3.4.2 and its digest length */
static const struct { uint8_t arc; size_t len; } PH[13] = {
  {0, 0},
  {4, 28}, {1, 32}, {2, 48}, {3, 64}, {5, 28}, {6, 32},   /* SHA2-224 .. SHA2-512/256 */
  {7, 28}, {8, 32}, {9, 48}, {10, 64},                    /* SHA3-224 .. SHA3-512 */
  {11, 32}, {12, 64},                                     /* SHAKE-128, SHAKE-256 */
};

static size_t pre_hash_prefix(uint8_t *pre, const uint8_t *ph, size_t phlen,
                              const uint8_t *ctx, size_t ctxlen, int hashalg) {
  static const uint8_t arc[10] = {0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                                  0x04, 0x02};
  if (hashalg < 1 || hashalg > 12 || ctxlen > 255 || phlen != PH[hashalg].len)
    return 0;
  pre[0] = 1;
  pre[1] = (uint8_t)ctxlen;
  if (ctxlen) memcpy(pre + 2, ctx, ctxlen);
  memcpy(pre + 2 + ctxlen, arc, sizeof arc);
  pre[2 + ctxlen + sizeof arc] = PH[hashalg].arc;
  memcpy(pre + 2 + ctxlen + sizeof arc + 1, ph, phlen);
  return 2 + ctxlen + sizeof arc + 1 + phlen;
}

int PQVTEST_MLDSA_NATIVE_MLDSA65_signature_pre_hash_internal(
    uint8_t *sig, const uint8_t *ph, size_t phlen, const uint8_t *ctx, size_t ctxlen,
    const uint8_t *rnd, const uint8_t *sk, int hashalg) {
  uint8_t pre[2 + 255 + 11 + 64];
  size_t siglen, n = pre_hash_prefix(pre, ph, phlen, ctx, ctxlen, hashalg);
  if (!n) return -1;
  return SG(sig, &siglen, NULL, 0, pre, n, rnd, sk);
}

int PQVTEST_MLDSA_NATIVE_MLDSA65_verify_pre_hash_internal(
    const uint8_t *sig, const uint8_t *ph, size_t phlen, const uint8_t *ctx,
    size_t ctxlen, const uint8_t *pk, int hashalg) {
  uint8_t pre[2 + 255 + 11 + 64];
  size_t n;
#ifdef PQVTEST_VERIFY_SHA3_512_AS_SHA2_512
  if (hashalg == 10) hashalg = 4;      /* MLD_PREHASH_SHA3_512 -> MLD_PREHASH_SHA2_512 */
#endif
  n = pre_hash_prefix(pre, ph, phlen, ctx, ctxlen, hashalg);
  if (!n) return -1;
  return VF(sig, SIGBYTES, NULL, 0, pre, n, pk);
}
