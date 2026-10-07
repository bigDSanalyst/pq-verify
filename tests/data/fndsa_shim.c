/*
 * Test shim: an FN-DSA-512 library in PQClean's NIST API whose verify and
 * open call back into Python (backed by pq_verify.fndsa), so the
 * --audit-fndsa ctypes path can be tested offline and faults planted in the
 * callbacks. No keypair or signing: those stages report not applicable.
 * Built with -DPQVTEST_PADDED_TOO it also exports a padded variant, which
 * makes every role ambiguous.
 */
#include <stddef.h>
#include <stdint.h>

typedef int (*ver_cb)(const uint8_t *, size_t, const uint8_t *, size_t, const uint8_t *);
typedef int (*open_cb)(uint8_t *, size_t *, const uint8_t *, size_t, const uint8_t *);
static ver_cb VER; static open_cb OPEN;

void pqvtest_fndsa_register(ver_cb v, open_cb o) { VER = v; OPEN = o; }

int PQCLEAN_FALCON512_CLEAN_crypto_sign_verify(const uint8_t *sig, size_t siglen,
        const uint8_t *m, size_t mlen, const uint8_t *pk) {
    return VER(sig, siglen, m, mlen, pk);
}
int PQCLEAN_FALCON512_CLEAN_crypto_sign_open(uint8_t *m, size_t *mlen,
        const uint8_t *sm, size_t smlen, const uint8_t *pk) {
    return OPEN(m, mlen, sm, smlen, pk);
}
#ifdef PQVTEST_PADDED_TOO
int PQCLEAN_FALCONPADDED512_CLEAN_crypto_sign_verify(const uint8_t *sig, size_t siglen,
        const uint8_t *m, size_t mlen, const uint8_t *pk) {
    return VER(sig, siglen, m, mlen, pk);
}
#endif
