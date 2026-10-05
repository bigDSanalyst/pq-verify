/*
 * pqv_hbs adapter for cisco/hash-sigs (LMS/HSS, SHA-256 n = 32 only).
 * Build hash-sigs with SECRET_METHOD 2 (its default, the ACVP-compatible
 * derivation): the master seed is then SEED || I of the top tree.
 */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include "pqv_hbs.h"
#include "hss.h"

static const uint8_t *seed_in;
static size_t seed_left;
static unsigned char priv[64];
static size_t priv_len;

static bool give_seed(void *out, size_t len) {
    if (len > seed_left) return false;
    memcpy(out, seed_in, len);
    seed_in += len; seed_left -= len;
    return true;
}

static bool keep_priv(unsigned char *key, size_t len, void *ctx) {
    (void)ctx;
    if (len > sizeof priv) return false;
    memcpy(priv, key, len);
    if (len > priv_len) priv_len = len;
    return true;
}

int pqv_hbs_abi(void) { return PQV_HBS_ABI; }
const char *pqv_hbs_name(void) { return "cisco/hash-sigs"; }

int pqv_hbs_supports(uint32_t scheme, uint32_t type, uint32_t ots) {
    /* RFC 8554's SHA-256 n = 32 sets only; no SP 800-208 192-bit or SHAKE */
    if (scheme != PQV_HBS_LMS || type < 5 || type > 9 || ots < 1 || ots > 4) return 0;
    return PQV_HBS_CAN_VERIFY | PQV_HBS_CAN_KEYGEN | PQV_HBS_CAN_SIGN | PQV_HBS_CAN_STATE;
}

int pqv_hbs_verify(uint32_t scheme, const uint8_t *pk, size_t pklen,
                   const uint8_t *m, size_t mlen,
                   const uint8_t *sig, size_t siglen) {
    (void)pklen;
    if (scheme != PQV_HBS_LMS) return -1;
    return hss_validate_signature(pk, m, mlen, sig, siglen, NULL) ? 0 : 1;
}

static int make_key(uint32_t type, uint32_t ots, const uint8_t *seed,
                    size_t seedlen, uint8_t *pk, size_t pkcap) {
    param_set_t lm = type, lmots = ots;
    seed_in = seed; seed_left = seedlen; priv_len = 0;
    if (!hss_generate_private_key(give_seed, 1, &lm, &lmots, keep_priv, NULL,
                                  pk, pkcap, NULL, 0, NULL))
        return -1;
    return seed_left == 0 ? 0 : -2;      /* the whole SEED || I was consumed */
}

int pqv_hbs_keygen(uint32_t scheme, uint32_t type, uint32_t ots,
                   const uint8_t *seed, size_t seedlen,
                   uint8_t *pk, size_t *pklen) {
    if (scheme != PQV_HBS_LMS) return -1;
    size_t need = hss_get_public_key_len(1, (param_set_t[]){type},
                                         (param_set_t[]){ots});
    if (!need || *pklen < need) return -1;
    if (make_key(type, ots, seed, seedlen, pk, *pklen)) return -1;
    *pklen = need;
    return 0;
}

int pqv_hbs_sign(uint32_t scheme, uint32_t type, uint32_t ots,
                 const uint8_t *seed, size_t seedlen, uint64_t index,
                 const uint8_t *m, size_t mlen, uint8_t *sig, size_t *siglen) {
    if (scheme != PQV_HBS_LMS) return -1;
    unsigned char pk[64];
    if (make_key(type, ots, seed, seedlen, pk, sizeof pk)) return -1;
    /* The private key starts with the 8-byte big-endian count of signatures
     * already issued: set it to the leaf NIST's vector signs with. */
    for (int i = 7; i >= 0; i--) { priv[i] = (unsigned char)(index & 0xff); index >>= 8; }
    struct hss_working_key *w = hss_load_private_key(NULL, priv, 0, NULL, 0, NULL);
    if (!w) return -1;
    size_t need = hss_get_signature_len_from_working_key(w);
    int rc = -1;
    if (need && *siglen >= need &&
        hss_generate_signature(w, NULL, priv, m, mlen, sig, need, NULL)) {
        *siglen = need;
        rc = 0;
    }
    hss_free_working_key(w);
    return rc;
}

/* ---- stateful: hash-sigs' own private-key updates, kept in a file ---- */

#define KEYMAX 64

static long read_file(const char *path, unsigned char *buf, size_t cap) {
    FILE *f = fopen(path, "rb");
    if (!f) return -1;
    size_t n = fread(buf, 1, cap, f);
    int more = fgetc(f) != EOF;
    fclose(f);
    return more ? -1 : (long)n;
}

/* Atomic and durable: write a sibling, fsync it, rename it over. */
static int write_file(const char *path, const unsigned char *buf, size_t len) {
    char tmp[4096];
    if (snprintf(tmp, sizeof tmp, "%s.pqv-tmp", path) >= (int)sizeof tmp) return -1;
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return -1;
    if (write(fd, buf, len) != (ssize_t)len || fsync(fd)) { close(fd); unlink(tmp); return -1; }
    close(fd);
    return rename(tmp, path);
}

/* hash-sigs hands over either the whole key or just its first 8 bytes (the
 * count); either way the stored key must reflect it before signing goes on. */
static bool store_priv(unsigned char *key, size_t len, void *ctx) {
    const char *path = ctx;
    unsigned char cur[KEYMAX];
    long have = read_file(path, cur, sizeof cur);
    if (have < 0) {                         /* first write: the whole key */
        if (len > sizeof cur) return false;
        return write_file(path, key, len) == 0;
    }
    if (len > (size_t)have) {
        if (len > sizeof cur) return false;
        have = (long)len;
    }
    memcpy(cur, key, len);
    return write_file(path, cur, (size_t)have) == 0;
}

static bool load_priv(unsigned char *key, size_t len, void *ctx) {
    unsigned char cur[KEYMAX];
    long have = read_file(ctx, cur, sizeof cur);
    if (have < 0 || (size_t)have < len) return false;
    memcpy(key, cur, len);
    return true;
}

int pqv_hbs_state_keygen(uint32_t scheme, uint32_t type, uint32_t ots,
                         const uint8_t *seed, size_t seedlen, const char *state,
                         uint8_t *pk, size_t *pklen) {
    if (scheme != PQV_HBS_LMS || access(state, F_OK) == 0) return -1;
    param_set_t lm = type, lmots = ots;
    size_t need = hss_get_public_key_len(1, &lm, &lmots);
    if (!need || *pklen < need) return -1;
    seed_in = seed; seed_left = seedlen;
    if (!hss_generate_private_key(give_seed, 1, &lm, &lmots, store_priv, (void *)state,
                                  pk, *pklen, NULL, 0, NULL) || seed_left)
        return -1;
    *pklen = need;
    return 0;
}

int pqv_hbs_state_sign(uint32_t scheme, const char *state,
                       const uint8_t *m, size_t mlen, uint8_t *sig, size_t *siglen) {
    if (scheme != PQV_HBS_LMS) return -1;
    struct hss_working_key *w = hss_load_private_key(load_priv, (void *)state, 0,
                                                     NULL, 0, NULL);
    if (!w) return -1;
    size_t need = hss_get_signature_len_from_working_key(w);
    int rc = -1;
    if (need && *siglen >= need &&
        hss_generate_signature(w, store_priv, (void *)state, m, mlen, sig, need, NULL)) {
        *siglen = need;
        rc = 0;
    }
    hss_free_working_key(w);
    return rc;
}

int pqv_hbs_state_skip(uint32_t scheme, const char *state, uint64_t next) {
    unsigned char cur[KEYMAX];
    long have = read_file(state, cur, sizeof cur);
    if (scheme != PQV_HBS_LMS || have < 8) return -1;
    uint64_t now = 0;
    for (int i = 0; i < 8; i++) now = (now << 8) | cur[i];
    if (next < now) return -1;              /* forward only */
    for (int i = 7; i >= 0; i--) { cur[i] = (unsigned char)(next & 0xff); next >>= 8; }
    return write_file(state, cur, (size_t)have);
}
