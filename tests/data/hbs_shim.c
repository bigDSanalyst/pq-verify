/*
 * Test shim: a pqv_hbs adapter whose five functions call back into Python
 * (backed by pq_verify.hbs), so the --audit-hbs ctypes path can be tested
 * offline and faults planted in the callbacks.
 */
#include <stddef.h>
#include <stdint.h>
#include "pqv_hbs.h"

typedef int (*sup_cb)(uint32_t, uint32_t, uint32_t);
typedef int (*ver_cb)(uint32_t, const uint8_t *, size_t, const uint8_t *, size_t,
                      const uint8_t *, size_t);
typedef int (*kg_cb)(uint32_t, uint32_t, uint32_t, const uint8_t *, size_t,
                     uint8_t *, size_t *);
typedef int (*sg_cb)(uint32_t, uint32_t, uint32_t, const uint8_t *, size_t, uint64_t,
                     const uint8_t *, size_t, uint8_t *, size_t *);
static sup_cb SUP; static ver_cb VER; static kg_cb KG; static sg_cb SG;

void pqvtest_hbs_register(sup_cb a, ver_cb b, kg_cb c, sg_cb d) {
    SUP = a; VER = b; KG = c; SG = d;
}
int pqv_hbs_abi(void) { return PQV_HBS_ABI; }
const char *pqv_hbs_name(void) { return "pqv-test-shim"; }
int pqv_hbs_supports(uint32_t s, uint32_t t, uint32_t o) { return SUP(s, t, o); }
int pqv_hbs_verify(uint32_t s, const uint8_t *pk, size_t pkl, const uint8_t *m,
                   size_t ml, const uint8_t *sig, size_t sl) {
    return VER(s, pk, pkl, m, ml, sig, sl);
}
int pqv_hbs_keygen(uint32_t s, uint32_t t, uint32_t o, const uint8_t *seed,
                   size_t sl, uint8_t *pk, size_t *pkl) {
    return KG(s, t, o, seed, sl, pk, pkl);
}
int pqv_hbs_sign(uint32_t s, uint32_t t, uint32_t o, const uint8_t *seed, size_t sl,
                 uint64_t idx, const uint8_t *m, size_t ml, uint8_t *sig, size_t *sigl) {
    return SG(s, t, o, seed, sl, idx, m, ml, sig, sigl);
}
