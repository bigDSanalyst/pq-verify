/*
 * Test shim: the pq-crystals ML-DSA-65 ABI, forwarded to callbacks the test
 * registers (backed by dilithium-py). Linked with pq-verify's randomness
 * harness, so keypair() and signature() draw NIST's seed and rnd through
 * randombytes() exactly as pq-crystals ref and PQClean do. This lets the
 * --audit-dsa ctypes path, the harness and the negative controls be tested
 * offline, without fetching a vendor library.
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

int randombytes(uint8_t *out, size_t n);

typedef int (*kp_cb)(uint8_t *pk, uint8_t *sk, const uint8_t *seed);
typedef int (*sig_cb)(uint8_t *sig, size_t *siglen, const uint8_t *m, size_t mlen,
                      const uint8_t *pre, size_t prelen, const uint8_t *rnd,
                      const uint8_t *sk);
typedef int (*ver_cb)(const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
                      const uint8_t *pre, size_t prelen, const uint8_t *pk);

static kp_cb KP;
static sig_cb SG;
static ver_cb VF;
static int EXTRA_RNG;

void pqvtest_register(kp_cb kp, sig_cb sg, ver_cb vf, int extra_rng) {
  KP = kp; SG = sg; VF = vf; EXTRA_RNG = extra_rng;
}

int pqvtest_dilithium3_ref_keypair(uint8_t *pk, uint8_t *sk) {
  uint8_t seed[32];
  randombytes(seed, 32);
  if (EXTRA_RNG) {
    uint8_t spare[8];
    randombytes(spare, sizeof spare);
  }
  return KP(pk, sk, seed);
}

int pqvtest_dilithium3_ref_signature_internal(uint8_t *sig, size_t *siglen,
                                              const uint8_t *m, size_t mlen,
                                              const uint8_t *pre, size_t prelen,
                                              const uint8_t *rnd, const uint8_t *sk) {
  return SG(sig, siglen, m, mlen, pre, prelen, rnd, sk);
}

int pqvtest_dilithium3_ref_signature(uint8_t *sig, size_t *siglen,
                                     const uint8_t *m, size_t mlen,
                                     const uint8_t *ctx, size_t ctxlen,
                                     const uint8_t *sk) {
  uint8_t pre[257], rnd[32];
  if (ctxlen > 255) return -1;
  pre[0] = 0;
  pre[1] = (uint8_t)ctxlen;
  if (ctxlen) memcpy(pre + 2, ctx, ctxlen);
  randombytes(rnd, 32);
  return SG(sig, siglen, m, mlen, pre, 2 + ctxlen, rnd, sk);
}

int pqvtest_dilithium3_ref_verify_internal(const uint8_t *sig, size_t siglen,
                                           const uint8_t *m, size_t mlen,
                                           const uint8_t *pre, size_t prelen,
                                           const uint8_t *pk) {
  return VF(sig, siglen, m, mlen, pre, prelen, pk);
}

int pqvtest_dilithium3_ref_verify(const uint8_t *sig, size_t siglen,
                                  const uint8_t *m, size_t mlen,
                                  const uint8_t *ctx, size_t ctxlen,
                                  const uint8_t *pk) {
  uint8_t pre[257];
  if (ctxlen > 255) return -1;
  pre[0] = 0;
  pre[1] = (uint8_t)ctxlen;
  if (ctxlen) memcpy(pre + 2, ctx, ctxlen);
  return VF(sig, siglen, m, mlen, pre, 2 + ctxlen, pk);
}
