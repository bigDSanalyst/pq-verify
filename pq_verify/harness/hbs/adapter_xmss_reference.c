/*
 * pqv_hbs adapter for XMSS/xmss-reference (XMSS and XMSS^MT, every RFC 8391
 * and SP 800-208 set). Link against xmss_core.c (not xmss_core_fast.c) and
 * NOT the library's randombytes.c: this file provides randombytes() and
 * serves the seed pq-verify passes in.
 */
#include <string.h>
#include <stdlib.h>
#include "pqv_hbs.h"
#include "params.h"
#include "xmss.h"

static const uint8_t *seed_in;
static size_t seed_left, seed_over;

void randombytes(unsigned char *out, unsigned long long len) {
    unsigned long long i;
    for (i = 0; i < len; i++) {
        if (seed_left) { out[i] = *seed_in++; seed_left--; }
        else { out[i] = 0; seed_over++; }
    }
}

int pqv_hbs_abi(void) { return PQV_HBS_ABI; }
const char *pqv_hbs_name(void) { return "xmss-reference"; }

static int params_for(uint32_t scheme, uint32_t oid, xmss_params *p) {
    if (scheme == PQV_HBS_XMSS) return xmss_parse_oid(p, oid);
    if (scheme == PQV_HBS_XMSSMT) return xmssmt_parse_oid(p, oid);
    return -1;
}

int pqv_hbs_supports(uint32_t scheme, uint32_t type, uint32_t ots) {
    xmss_params p;
    (void)ots;
    if (params_for(scheme, type, &p)) return 0;
    return PQV_HBS_CAN_VERIFY | PQV_HBS_CAN_KEYGEN | PQV_HBS_CAN_SIGN;
}

int pqv_hbs_verify(uint32_t scheme, const uint8_t *pk, size_t pklen,
                   const uint8_t *m, size_t mlen,
                   const uint8_t *sig, size_t siglen) {
    xmss_params p;
    if (pklen < 4) return -1;
    uint32_t oid = ((uint32_t)pk[0] << 24) | (pk[1] << 16) | (pk[2] << 8) | pk[3];
    if (params_for(scheme, oid, &p) || pklen != p.pk_bytes + 4) return -1;
    unsigned long long smlen = siglen + mlen, outlen = 0;
    unsigned char *sm = malloc(smlen ? smlen : 1), *out = malloc(smlen ? smlen : 1);
    if (!sm || !out) { free(sm); free(out); return -1; }
    memcpy(sm, sig, siglen);
    memcpy(sm + siglen, m, mlen);
    int rc = scheme == PQV_HBS_XMSS ? xmss_sign_open(out, &outlen, sm, smlen, pk)
                                    : xmssmt_sign_open(out, &outlen, sm, smlen, pk);
    if (rc == 0 && (outlen != mlen || memcmp(out, m, mlen))) rc = 1;
    free(sm); free(out);
    return rc ? 1 : 0;
}

static int keypair(uint32_t scheme, uint32_t oid, const uint8_t *seed,
                   size_t seedlen, uint8_t *pk, uint8_t *sk, xmss_params *p) {
    if (params_for(scheme, oid, p) || seedlen != 3 * p->n) return -1;
    seed_in = seed; seed_left = seedlen; seed_over = 0;
    int rc = scheme == PQV_HBS_XMSS ? xmss_keypair(pk, sk, oid)
                                    : xmssmt_keypair(pk, sk, oid);
    return (rc || seed_left || seed_over) ? -1 : 0;
}

int pqv_hbs_keygen(uint32_t scheme, uint32_t type, uint32_t ots,
                   const uint8_t *seed, size_t seedlen,
                   uint8_t *pk, size_t *pklen) {
    xmss_params p;
    (void)ots;
    if (params_for(scheme, type, &p) || *pklen < p.pk_bytes + 4) return -1;
    uint8_t *sk = malloc(p.sk_bytes + 4);
    if (!sk) return -1;
    int rc = keypair(scheme, type, seed, seedlen, pk, sk, &p);
    free(sk);
    if (rc) return -1;
    *pklen = p.pk_bytes + 4;
    return 0;
}

int pqv_hbs_sign(uint32_t scheme, uint32_t type, uint32_t ots,
                 const uint8_t *seed, size_t seedlen, uint64_t index,
                 const uint8_t *m, size_t mlen, uint8_t *sig, size_t *siglen) {
    xmss_params p;
    (void)ots;
    if (params_for(scheme, type, &p) || *siglen < p.sig_bytes) return -1;
    uint8_t *pk = malloc(p.pk_bytes + 4), *sk = malloc(p.sk_bytes + 4);
    unsigned long long smlen = 0;
    uint8_t *sm = malloc(p.sig_bytes + mlen);
    int rc = -1;
    if (pk && sk && sm && keypair(scheme, type, seed, seedlen, pk, sk, &p) == 0) {
        /* sk = OID || idx (index_bytes, big-endian) || ...: sign leaf `index` */
        for (unsigned i = 0; i < p.index_bytes; i++)
            sk[4 + p.index_bytes - 1 - i] = (uint8_t)(index >> (8 * i));
        int s = scheme == PQV_HBS_XMSS ? xmss_sign(sk, sm, &smlen, m, mlen)
                                       : xmssmt_sign(sk, sm, &smlen, m, mlen);
        if (s == 0 && smlen == p.sig_bytes + mlen) {
            memcpy(sig, sm, p.sig_bytes);
            *siglen = p.sig_bytes;
            rc = 0;
        }
    }
    free(pk); free(sk); free(sm);
    return rc;
}
