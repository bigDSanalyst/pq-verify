/*
 * Test shim: an HQC code layer exporting the six encoder/decoder entry points
 * under PQClean's naming (PQV_NS, e.g. -DPQV_NS=PQCLEAN_HQC128_CLEAN), each
 * calling back into Python with its role, so the --audit-hqc ctypes path can
 * be tested offline and faults planted in the callbacks.
 */
#include <stdint.h>

#define PASTE(a, b) a##_##b
#define NAME(a, b) PASTE(a, b)

typedef void (*hqc_cb)(int, uint8_t *, const uint8_t *);
static hqc_cb CB;

void pqvtest_hqc_register(hqc_cb c) { CB = c; }

void NAME(PQV_NS, reed_solomon_encode)(uint8_t *o, const uint8_t *i) { CB(0, o, i); }
void NAME(PQV_NS, reed_solomon_decode)(uint8_t *o, const uint8_t *i) { CB(1, o, i); }
void NAME(PQV_NS, reed_muller_encode)(uint8_t *o, const uint8_t *i) { CB(2, o, i); }
void NAME(PQV_NS, reed_muller_decode)(uint8_t *o, const uint8_t *i) { CB(3, o, i); }
void NAME(PQV_NS, code_encode)(uint8_t *o, const uint8_t *i) { CB(4, o, i); }
void NAME(PQV_NS, code_decode)(uint8_t *o, const uint8_t *i) { CB(5, o, i); }
