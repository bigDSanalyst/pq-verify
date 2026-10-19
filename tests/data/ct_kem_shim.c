/*
 * Test shim for --constant-time: a fake ML-KEM-512-sized KEM with the
 * derandomised NIST API. It computes nothing real (outputs are XOR mixes),
 * only enough data flow for the secret inputs to reach its code. Built with
 * -DLEAK_BRANCH (encaps branches on m), -DLEAK_INDEX (decaps indexes a table
 * with a byte of the secret key) or -DLEAK_DISCARDED (decaps reads such a
 * table and overwrites the register at once, the load Valgrind's default
 * translation deletes), it plants one leak each.
 */
#include <stddef.h>
#include <stdint.h>

#define EK 800
#define DK 1632
#define CT 768

int shim_kem_keypair_derand(uint8_t *ek, uint8_t *dk, const uint8_t *coins) {
    for (size_t i = 0; i < EK; i++) ek[i] = (uint8_t)(coins[i % 32] * 3 + i);
    for (size_t i = 0; i < DK; i++) dk[i] = (uint8_t)(coins[32 + i % 32] ^ i);
    return 0;
}

int shim_kem_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *ek, const uint8_t *m) {
    for (size_t i = 0; i < CT; i++) ct[i] = (uint8_t)(ek[i % EK] ^ m[i % 32]);
    for (size_t i = 0; i < 32; i++) ss[i] = (uint8_t)(m[i] + ek[i]);
#ifdef LEAK_BRANCH
    if (m[0] & 1) { ss[0] ^= 0x5a; __asm__ volatile(""); }
#endif
    return 0;
}

int shim_kem_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *dk) {
    uint8_t acc = 0;
    for (size_t i = 0; i < CT; i++) acc ^= (uint8_t)(ct[i] & dk[i % 768]);
    for (size_t i = 0; i < 32; i++) ss[i] = (uint8_t)(acc ^ dk[DK - 32 + i]);
#ifdef LEAK_INDEX
    static uint8_t table[256];
    for (int i = 0; i < 256; i++) table[i] = (uint8_t)(i * 7);
    ss[1] ^= table[dk[3]];
#endif
#ifdef LEAK_DISCARDED
    static const volatile uint8_t lut[256];
    uint32_t t;
#if defined(__x86_64__)
    __asm__ volatile("movzbl (%1,%2), %0\n\txorl %0, %0"
                     : "=&r"(t) : "r"(lut), "r"((uintptr_t)dk[3]) : "cc");
#elif defined(__aarch64__)
    __asm__ volatile("ldrb %w0, [%1, %2]\n\tmov %w0, #0"
                     : "=&r"(t) : "r"(lut), "r"((uintptr_t)dk[3]));
#else
    t = lut[dk[3]];
#endif
    ss[2] ^= (uint8_t)t;
#endif
    return 0;
}
