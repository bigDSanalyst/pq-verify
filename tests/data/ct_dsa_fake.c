/*
 * Test shim for --audit-dsa --constant-time: mldsa-native's internal API
 * names, linked with pq-verify's constant-time shim (so it is a hooked build)
 * but declaring nothing public, as a library built without its annotations
 * would. pq-verify must report CANNOT VERIFY, never a pass. It computes
 * nothing real.
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

int PQCP_MLDSA_NATIVE_MLDSA44_keypair_internal(uint8_t *pk, uint8_t *sk,
                                               const uint8_t *seed) {
    memset(pk, 0, 1312);
    memset(sk, 0, 2560);
    (void)seed;
    return 0;
}

int PQCP_MLDSA_NATIVE_MLDSA44_signature_internal(uint8_t *sig, const uint8_t *m,
                                                 size_t mlen, const uint8_t *pre,
                                                 size_t prelen, const uint8_t *rnd,
                                                 const uint8_t *sk, int externalmu) {
    memset(sig, 0, 2420);
    (void)m; (void)mlen; (void)pre; (void)prelen; (void)rnd; (void)sk; (void)externalmu;
    return 0;
}
