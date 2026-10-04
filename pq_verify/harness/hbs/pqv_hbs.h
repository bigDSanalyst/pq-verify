/*
 * pq-verify's adapter interface for stateful hash-based signature libraries
 * (LMS/HSS, XMSS, XMSS^MT): "pqv_hbs" version 1.
 *
 * LMS and XMSS libraries have no common C API: each has its own key
 * formats, state handling and callbacks. An adapter is a small C file that
 * maps one library onto the five functions below; `pq-verify --audit-hbs`
 * loads the library built with it and drives it with every pinned vector.
 * Adapters for cisco/hash-sigs and xmss-reference ship in this directory.
 *
 * Encodings, so that every adapter means the same bytes:
 *   PQV_HBS_LMS     public key and signature in HSS form (RFC 8554 §6):
 *                   pk = u32(L) || LMS public key; a one-level signature is
 *                   u32(0) || LMS signature. type = LMS typecode, ots =
 *                   LM-OTS typecode. seed = SEED || I of the top tree; child
 *                   trees, the C randomizer and x_q[i] are derived as
 *                   SP 800-208 / RFC 8554 Appendix A with the ACVP
 *                   convention (C from i = 0xFFFD).
 *   PQV_HBS_XMSS    pk = OID || root || SEED; signature without the message.
 *   PQV_HBS_XMSSMT  the same for XMSS^MT. type = OID, ots = 0. seed =
 *                   S_XMSS || SK_PRF || SEED (n bytes each), SP 800-208's
 *                   PRF_keygen derivation.
 * Every function returns 0 for success (verify: a valid signature) and
 * nonzero otherwise. Lengths are in/out: capacity in, length written out.
 */
#ifndef PQV_HBS_H
#define PQV_HBS_H

#include <stddef.h>
#include <stdint.h>

#define PQV_HBS_ABI 1

#define PQV_HBS_LMS    1
#define PQV_HBS_XMSS   2
#define PQV_HBS_XMSSMT 3

#define PQV_HBS_CAN_VERIFY 1
#define PQV_HBS_CAN_KEYGEN 2
#define PQV_HBS_CAN_SIGN   4

int pqv_hbs_abi(void);
const char *pqv_hbs_name(void);
int pqv_hbs_supports(uint32_t scheme, uint32_t type, uint32_t ots);
int pqv_hbs_verify(uint32_t scheme, const uint8_t *pk, size_t pklen,
                   const uint8_t *m, size_t mlen,
                   const uint8_t *sig, size_t siglen);
int pqv_hbs_keygen(uint32_t scheme, uint32_t type, uint32_t ots,
                   const uint8_t *seed, size_t seedlen,
                   uint8_t *pk, size_t *pklen);
int pqv_hbs_sign(uint32_t scheme, uint32_t type, uint32_t ots,
                 const uint8_t *seed, size_t seedlen, uint64_t index,
                 const uint8_t *m, size_t mlen, uint8_t *sig, size_t *siglen);

#endif
