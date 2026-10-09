/*
 * Test shim: a Classic McEliece library in the NIST API, PQClean's naming
 * (PQV_NS, e.g. -DPQV_NS=PQCLEAN_MCELIECE348864_CLEAN), whose three entry
 * points call back into Python, so the --audit-mceliece ctypes path can be
 * tested offline and faults planted in the callbacks.
 */
#include <stddef.h>
#include <stdint.h>

#define PASTE(a, b) a##_##b
#define NAME(a, b) PASTE(a, b)

typedef int (*kp_cb)(uint8_t *, uint8_t *);
typedef int (*enc_cb)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*dec_cb)(uint8_t *, const uint8_t *, const uint8_t *);
static kp_cb KP;
static enc_cb ENC;
static dec_cb DEC;

void pqvtest_mceliece_register(kp_cb k, enc_cb e, dec_cb d) { KP = k; ENC = e; DEC = d; }

int NAME(PQV_NS, crypto_kem_keypair)(uint8_t *pk, uint8_t *sk) { return KP(pk, sk); }
int NAME(PQV_NS, crypto_kem_enc)(uint8_t *ct, uint8_t *ss, const uint8_t *pk) {
    return ENC(ct, ss, pk);
}
int NAME(PQV_NS, crypto_kem_dec)(uint8_t *ss, const uint8_t *ct, const uint8_t *sk) {
    return DEC(ss, ct, sk);
}
