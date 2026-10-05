/*
 * pqv_hbs adapter for XMSS/xmss-reference (XMSS and XMSS^MT, every RFC 8391
 * and SP 800-208 set). Link against xmss_core.c (not xmss_core_fast.c) and
 * NOT the library's randombytes.c: this file provides randombytes() and
 * serves the seed pq-verify passes in.
 */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
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
    return PQV_HBS_CAN_VERIFY | PQV_HBS_CAN_KEYGEN | PQV_HBS_CAN_SIGN | PQV_HBS_CAN_STATE;
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

/* ---- stateful: xmss-reference advances the index inside sk; the key file
 * is sk itself (OID || idx || ...), rewritten before a signature leaves. ---- */

static long read_file(const char *path, unsigned char *buf, size_t cap) {
    FILE *f = fopen(path, "rb");
    if (!f) return -1;
    size_t n = fread(buf, 1, cap, f);
    int more = fgetc(f) != EOF;
    fclose(f);
    return more ? -1 : (long)n;
}

static int write_file(const char *path, const unsigned char *buf, size_t len) {
    char tmp[4096];
    if (snprintf(tmp, sizeof tmp, "%s.pqv-tmp", path) >= (int)sizeof tmp) return -1;
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return -1;
    if (write(fd, buf, len) != (ssize_t)len || fsync(fd)) { close(fd); unlink(tmp); return -1; }
    close(fd);
    return rename(tmp, path);
}

static int load_sk(uint32_t scheme, const char *state, uint8_t **sk, xmss_params *p) {
    uint8_t head[4];
    FILE *f = fopen(state, "rb");
    if (!f) return -1;
    size_t got = fread(head, 1, 4, f);
    fclose(f);
    if (got != 4) return -1;
    uint32_t oid = ((uint32_t)head[0] << 24) | (head[1] << 16) | (head[2] << 8) | head[3];
    if (params_for(scheme, oid, p)) return -1;
    *sk = malloc(p->sk_bytes + 4);
    if (!*sk) return -1;
    if (read_file(state, *sk, p->sk_bytes + 4) != (long)(p->sk_bytes + 4)) {
        free(*sk); *sk = NULL; return -1;
    }
    return 0;
}

int pqv_hbs_state_keygen(uint32_t scheme, uint32_t type, uint32_t ots,
                         const uint8_t *seed, size_t seedlen, const char *state,
                         uint8_t *pk, size_t *pklen) {
    xmss_params p;
    (void)ots;
    if (access(state, F_OK) == 0) return -1;
    if (params_for(scheme, type, &p) || *pklen < p.pk_bytes + 4) return -1;
    uint8_t *sk = malloc(p.sk_bytes + 4);
    if (!sk) return -1;
    int rc = keypair(scheme, type, seed, seedlen, pk, sk, &p);
    if (rc == 0) rc = write_file(state, sk, p.sk_bytes + 4);
    free(sk);
    if (rc) return -1;
    *pklen = p.pk_bytes + 4;
    return 0;
}

int pqv_hbs_state_sign(uint32_t scheme, const char *state,
                       const uint8_t *m, size_t mlen, uint8_t *sig, size_t *siglen) {
    xmss_params p;
    uint8_t *sk = NULL;
    if (load_sk(scheme, state, &sk, &p)) return -1;
    if (*siglen < p.sig_bytes) { free(sk); return -1; }
    unsigned long long smlen = 0;
    uint8_t *sm = malloc(p.sig_bytes + mlen);
    int rc = -1;
    if (sm) {
        int s = scheme == PQV_HBS_XMSS ? xmss_sign(sk, sm, &smlen, m, mlen)
                                       : xmssmt_sign(sk, sm, &smlen, m, mlen);
        /* the advanced (or, after the last leaf, wiped) key is stored first */
        if (write_file(state, sk, p.sk_bytes + 4) == 0 && s == 0
            && smlen == p.sig_bytes + mlen) {
            memcpy(sig, sm, p.sig_bytes);
            *siglen = p.sig_bytes;
            rc = 0;
        }
    }
    free(sk); free(sm);
    return rc;
}

int pqv_hbs_state_skip(uint32_t scheme, const char *state, uint64_t next) {
    xmss_params p;
    uint8_t *sk = NULL;
    if (load_sk(scheme, state, &sk, &p)) return -1;
    uint64_t now = 0;
    for (unsigned i = 0; i < p.index_bytes; i++) now = (now << 8) | sk[4 + i];
    int rc = -1;
    if (next >= now) {                      /* forward only */
        for (unsigned i = 0; i < p.index_bytes; i++)
            sk[4 + p.index_bytes - 1 - i] = (uint8_t)(next >> (8 * i));
        rc = write_file(state, sk, p.sk_bytes + 4);
    }
    free(sk);
    return rc;
}
