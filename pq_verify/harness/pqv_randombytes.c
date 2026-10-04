/*
 * pq-verify's randomness harness for vendor audits.
 *
 * Link this file in place of a library's randombytes() to audit APIs that
 * draw their randomness internally (crypto_sign_keypair, a randomised
 * crypto_sign_signature): pq-verify loads NIST's seed with pqv_rng_set()
 * before each call, so the output is comparable byte-for-byte with NIST's.
 *
 * A call that asks for more bytes than were queued is recorded in
 * pqv_rng_overrun() and served zeros: a library that draws randomness the
 * standard does not call for is a finding, not a crash.
 *
 * Never link this into a production build: it is deterministic by design.
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define PQV_RNG_MAX 4096

static uint8_t pqv_buf[PQV_RNG_MAX];
static size_t pqv_len, pqv_pos, pqv_over;

int pqv_rng_set(const uint8_t *in, size_t n) {
  if (n > PQV_RNG_MAX) return -1;
  memcpy(pqv_buf, in, n);
  pqv_len = n;
  pqv_pos = 0;
  pqv_over = 0;
  return 0;
}

/* Bytes asked for beyond what was queued since the last pqv_rng_set. */
size_t pqv_rng_overrun(void) { return pqv_over; }

/* Bytes queued but never drawn since the last pqv_rng_set. */
size_t pqv_rng_unused(void) { return pqv_len - pqv_pos; }

/* int, not void: PQClean and mldsa-native declare int, pq-crystals void; a
 * caller that ignores the result is unaffected. */
int randombytes(uint8_t *out, size_t n) {
  size_t i;
  for (i = 0; i < n; i++) {
    if (pqv_pos < pqv_len) {
      out[i] = pqv_buf[pqv_pos++];
    } else {
      out[i] = 0;
      pqv_over++;
    }
  }
  return 0;
}

/* PQClean namespaces its RNG. */
int PQCLEAN_randombytes(uint8_t *out, size_t n) { return randombytes(out, n); }
