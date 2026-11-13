/*
 * A small ML-KEM (FIPS 203) for pq-verify's tests: the derandomised NIST API
 * for one parameter set, chosen with -DK=2, 3 or 4. It is a known-good library
 * for the contained worker to audit, and the base its planted defects are cut
 * from. Written for reading, not for use: it is not constant time.
 *
 *   -DMUT_NO_EK_CHECK  encaps skips the modulus check (FIPS 203 section 7.2)
 *   -DMUT_NO_DK_CHECK  decaps skips the hash check (section 7.3)
 *   -DMUT_NO_REJECT    decaps returns K' for a ciphertext that does not
 *                      re-encrypt (no implicit rejection)
 *   -DMUT_COMPRESS     Compress rounds down
 *   -DMUT_OVERRUN      encaps writes one byte past the shared secret
 *   -DPQV_HOOK=fn      key generation first calls fn(coins), which the test
 *                      defines in another file: a planted behaviour
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#ifndef K
#define K 3
#endif
#if K == 2
#define ETA1 3
#define DU 10
#define DV 4
#define NAME(f) pqvref_mlkem512_##f
#elif K == 3
#define ETA1 2
#define DU 10
#define DV 4
#define NAME(f) pqvref_mlkem768_##f
#elif K == 4
#define ETA1 2
#define DU 11
#define DV 5
#define NAME(f) pqvref_mlkem1024_##f
#else
#error "K must be 2, 3 or 4"
#endif
#define ETA2 2
#define N 256
#define Q 3329
#define EK_BYTES (384 * K + 32)
#define DK_BYTES (768 * K + 96)
#define CT_BYTES (32 * (DU * K + DV))

#ifdef PQV_HOOK
void PQV_HOOK(const uint8_t *coins);
#endif

/* ---------------------------- Keccak ---------------------------- */

static uint64_t rol(uint64_t x, int s) { return (x << s) | (x >> (64 - s)); }

static void keccakf(uint64_t st[25])
{
    static const uint64_t rc[24] = {
        0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
        0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
        0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
        0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
        0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
        0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
        0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL };
    static const int rotc[24] = { 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
                                  27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44 };
    static const int piln[24] = { 10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
                                  15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1 };
    uint64_t t, bc[5];
    int r, i, j;

    for (r = 0; r < 24; r++) {
        for (i = 0; i < 5; i++)
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        for (i = 0; i < 5; i++) {
            t = bc[(i + 4) % 5] ^ rol(bc[(i + 1) % 5], 1);
            for (j = 0; j < 25; j += 5) st[j + i] ^= t;
        }
        t = st[1];
        for (i = 0; i < 24; i++) {
            j = piln[i];
            bc[0] = st[j];
            st[j] = rol(t, rotc[i]);
            t = bc[0];
        }
        for (j = 0; j < 25; j += 5) {
            for (i = 0; i < 5; i++) bc[i] = st[j + i];
            for (i = 0; i < 5; i++) st[j + i] ^= ~bc[(i + 1) % 5] & bc[(i + 2) % 5];
        }
        st[0] ^= rc[r];
    }
}

typedef struct { uint64_t s[25]; unsigned pos, rate; } sponge;

static void absorb(sponge *c, const uint8_t *in, size_t n)
{
    size_t i;
    for (i = 0; i < n; i++) {
        c->s[c->pos / 8] ^= (uint64_t)in[i] << (8 * (c->pos % 8));
        if (++c->pos == c->rate) { keccakf(c->s); c->pos = 0; }
    }
}

static void finish(sponge *c, uint8_t pad)
{
    c->s[c->pos / 8] ^= (uint64_t)pad << (8 * (c->pos % 8));
    c->s[(c->rate - 1) / 8] ^= (uint64_t)0x80 << (8 * ((c->rate - 1) % 8));
    keccakf(c->s);
    c->pos = 0;
}

static void squeeze(sponge *c, uint8_t *out, size_t n)
{
    size_t i;
    for (i = 0; i < n; i++) {
        if (c->pos == c->rate) { keccakf(c->s); c->pos = 0; }
        out[i] = (uint8_t)(c->s[c->pos / 8] >> (8 * (c->pos % 8)));
        c->pos++;
    }
}

/* One call: absorb a and b, squeeze n bytes. rate 136 pad 0x06 is SHA3-256,
   rate 72 pad 0x06 SHA3-512, rate 136 pad 0x1f SHAKE256. */
static void hash2(unsigned rate, uint8_t pad, const uint8_t *a, size_t an,
                  const uint8_t *b, size_t bn, uint8_t *out, size_t n)
{
    sponge c;
    memset(&c, 0, sizeof c);
    c.rate = rate;
    absorb(&c, a, an);
    if (bn) absorb(&c, b, bn);
    finish(&c, pad);
    squeeze(&c, out, n);
}

#define H(a, an, out)          hash2(136, 0x06, a, an, NULL, 0, out, 32)
#define G2(a, an, b, bn, out)  hash2(72, 0x06, a, an, b, bn, out, 64)
#define J(a, an, b, bn, out)   hash2(136, 0x1f, a, an, b, bn, out, 32)

/* ------------------------- the ring R_q ------------------------- */

typedef struct { int16_t c[N]; } poly;

static int16_t zetas[128];      /* 17^BitRev7(i) */
static int16_t gammas[128];     /* 17^(2 BitRev7(i) + 1) */
static int tables_ready;

static int32_t mod_q(int32_t x) { x %= Q; return x < 0 ? x + Q : x; }

static void tables(void)
{
    int i, j, e;
    int32_t p;
    if (tables_ready) return;
    for (i = 0; i < 128; i++) {
        int br = 0;
        for (j = 0; j < 7; j++) br |= ((i >> j) & 1) << (6 - j);
        for (p = 1, e = 0; e < br; e++) p = p * 17 % Q;
        zetas[i] = (int16_t)p;
        gammas[i] = (int16_t)(p * p % Q * 17 % Q);
    }
    tables_ready = 1;
}

static void ntt(poly *f)                                   /* Algorithm 9 */
{
    int i = 1, len, start, j;
    for (len = 128; len >= 2; len /= 2)
        for (start = 0; start < N; start += 2 * len) {
            int32_t z = zetas[i++];
            for (j = start; j < start + len; j++) {
                int32_t t = z * f->c[j + len] % Q;
                f->c[j + len] = (int16_t)mod_q(f->c[j] - t);
                f->c[j] = (int16_t)mod_q(f->c[j] + t);
            }
        }
}

static void intt(poly *f)                                  /* Algorithm 10 */
{
    int i = 127, len, start, j;
    for (len = 2; len <= 128; len *= 2)
        for (start = 0; start < N; start += 2 * len) {
            int32_t z = zetas[i--];
            for (j = start; j < start + len; j++) {
                int32_t t = f->c[j];
                f->c[j] = (int16_t)mod_q(t + f->c[j + len]);
                f->c[j + len] = (int16_t)mod_q(z * (f->c[j + len] - t));
            }
        }
    for (j = 0; j < N; j++) f->c[j] = (int16_t)(f->c[j] * 3303 % Q);
}

/* h += f * g in the NTT domain (Algorithms 11 and 12) */
static void mul_acc(poly *h, const poly *f, const poly *g)
{
    int i;
    for (i = 0; i < 128; i++) {
        int32_t a0 = f->c[2 * i], a1 = f->c[2 * i + 1];
        int32_t b0 = g->c[2 * i], b1 = g->c[2 * i + 1];
        int32_t c0 = (a0 * b0 + a1 * b1 % Q * gammas[i]) % Q;
        int32_t c1 = (a0 * b1 + a1 * b0) % Q;
        h->c[2 * i] = (int16_t)mod_q(h->c[2 * i] + c0);
        h->c[2 * i + 1] = (int16_t)mod_q(h->c[2 * i + 1] + c1);
    }
}

static void add(poly *r, const poly *a)
{
    int i;
    for (i = 0; i < N; i++) r->c[i] = (int16_t)mod_q(r->c[i] + a->c[i]);
}

static void sample_ntt(poly *a, const uint8_t rho[32], uint8_t j, uint8_t i)   /* Alg. 7 */
{
    uint8_t ji[2], b[3];
    sponge c;
    int n = 0;
    ji[0] = j; ji[1] = i;
    memset(&c, 0, sizeof c);
    c.rate = 168;                                           /* SHAKE128 */
    absorb(&c, rho, 32);
    absorb(&c, ji, 2);
    finish(&c, 0x1f);
    while (n < N) {
        int d1, d2;
        squeeze(&c, b, 3);
        d1 = b[0] | (b[1] & 15) << 8;
        d2 = b[1] >> 4 | b[2] << 4;
        if (d1 < Q) a->c[n++] = (int16_t)d1;
        if (d2 < Q && n < N) a->c[n++] = (int16_t)d2;
    }
}

static void sample_cbd(poly *f, int eta, const uint8_t seed[32], uint8_t nonce)  /* Alg. 8 */
{
    uint8_t buf[64 * 3];
    int i, j;
    hash2(136, 0x1f, seed, 32, &nonce, 1, buf, (size_t)64 * eta);    /* PRF */
#define BIT(k) ((buf[(k) / 8] >> ((k) % 8)) & 1)
    for (i = 0; i < N; i++) {
        int x = 0, y = 0;
        for (j = 0; j < eta; j++) {
            x += BIT(2 * i * eta + j);
            y += BIT(2 * i * eta + eta + j);
        }
        f->c[i] = (int16_t)mod_q(x - y);
    }
#undef BIT
}

static void encode(uint8_t *out, const poly *f, int d)     /* ByteEncode_d */
{
    int i, j;
    memset(out, 0, (size_t)32 * d);
    for (i = 0; i < N; i++)
        for (j = 0; j < d; j++)
            out[(i * d + j) / 8] |= (uint8_t)(((f->c[i] >> j) & 1) << ((i * d + j) % 8));
}

static void decode(poly *f, const uint8_t *in, int d)      /* ByteDecode_d */
{
    int i, j;
    for (i = 0; i < N; i++) {
        int v = 0;
        for (j = 0; j < d; j++)
            v |= ((in[(i * d + j) / 8] >> ((i * d + j) % 8)) & 1) << j;
        f->c[i] = (int16_t)(d == 12 ? v % Q : v);
    }
}

static void compress(poly *f, int d)
{
    int i;
    for (i = 0; i < N; i++)
#ifdef MUT_COMPRESS
        f->c[i] = (int16_t)((((uint32_t)f->c[i] << d) / Q) & ((1u << d) - 1));
#else
        f->c[i] = (int16_t)(((((uint32_t)f->c[i] << d) + Q / 2) / Q) & ((1u << d) - 1));
#endif
}

static void decompress(poly *f, int d)
{
    int i;
    for (i = 0; i < N; i++)
        f->c[i] = (int16_t)(((uint32_t)f->c[i] * Q + (1u << (d - 1))) >> d);
}

/* ---------------------------- K-PKE ---------------------------- */

static void matrix(poly a[K][K], const uint8_t rho[32])
{
    int i, j;
    for (i = 0; i < K; i++)
        for (j = 0; j < K; j++)
            sample_ntt(&a[i][j], rho, (uint8_t)j, (uint8_t)i);
}

static void pke_keygen(uint8_t *ek, uint8_t *dk_pke, const uint8_t d[32])     /* Alg. 13 */
{
    static poly a[K][K];
    poly s[K], e[K], t;
    uint8_t g[64], k = K, n = 0;
    int i, j;

    G2(d, 32, &k, 1, g);                                    /* rho || sigma */
    matrix(a, g);
    for (i = 0; i < K; i++) sample_cbd(&s[i], ETA1, g + 32, n++);
    for (i = 0; i < K; i++) sample_cbd(&e[i], ETA1, g + 32, n++);
    for (i = 0; i < K; i++) { ntt(&s[i]); ntt(&e[i]); }
    for (i = 0; i < K; i++) {
        memset(&t, 0, sizeof t);
        for (j = 0; j < K; j++) mul_acc(&t, &a[i][j], &s[j]);
        add(&t, &e[i]);
        encode(ek + 384 * i, &t, 12);
        encode(dk_pke + 384 * i, &s[i], 12);
    }
    memcpy(ek + 384 * K, g, 32);
}

static void pke_encrypt(uint8_t *c, const uint8_t *ek, const uint8_t m[32],
                        const uint8_t r[32])                                  /* Alg. 14 */
{
    static poly a[K][K];
    poly t[K], y[K], e1[K], e2, u, v, mu;
    uint8_t n = 0;
    int i, j;

    for (i = 0; i < K; i++) decode(&t[i], ek + 384 * i, 12);
    matrix(a, ek + 384 * K);
    for (i = 0; i < K; i++) sample_cbd(&y[i], ETA1, r, n++);
    for (i = 0; i < K; i++) sample_cbd(&e1[i], ETA2, r, n++);
    sample_cbd(&e2, ETA2, r, n);
    for (i = 0; i < K; i++) ntt(&y[i]);
    for (i = 0; i < K; i++) {
        memset(&u, 0, sizeof u);
        for (j = 0; j < K; j++) mul_acc(&u, &a[j][i], &y[j]);    /* A transposed */
        intt(&u);
        add(&u, &e1[i]);
        compress(&u, DU);
        encode(c + 32 * DU * i, &u, DU);
    }
    memset(&v, 0, sizeof v);
    for (j = 0; j < K; j++) mul_acc(&v, &t[j], &y[j]);
    intt(&v);
    add(&v, &e2);
    decode(&mu, m, 1);
    decompress(&mu, 1);
    add(&v, &mu);
    compress(&v, DV);
    encode(c + 32 * DU * K, &v, DV);
}

static void pke_decrypt(uint8_t m[32], const uint8_t *dk_pke, const uint8_t *c)   /* Alg. 15 */
{
    poly u, v, s, w;
    int i, j;

    memset(&w, 0, sizeof w);
    for (i = 0; i < K; i++) {
        decode(&u, c + 32 * DU * i, DU);
        decompress(&u, DU);
        ntt(&u);
        decode(&s, dk_pke + 384 * i, 12);
        mul_acc(&w, &s, &u);
    }
    intt(&w);
    decode(&v, c + 32 * DU * K, DV);
    decompress(&v, DV);
    for (j = 0; j < N; j++) w.c[j] = (int16_t)mod_q(v.c[j] - w.c[j]);
    compress(&w, 1);
    encode(m, &w, 1);
}

/* ---------------------------- ML-KEM ---------------------------- */

int NAME(keypair_derand)(uint8_t *ek, uint8_t *dk, const uint8_t *coins)        /* Alg. 16 */
{
#ifdef PQV_HOOK
    PQV_HOOK(coins);
#endif
    tables();
    pke_keygen(ek, dk, coins);
    memcpy(dk + 384 * K, ek, EK_BYTES);
    H(ek, EK_BYTES, dk + 768 * K + 32);
    memcpy(dk + 768 * K + 64, coins + 32, 32);
    return 0;
}

int NAME(enc_derand)(uint8_t *ct, uint8_t *ss, const uint8_t *ek, const uint8_t *m)   /* Alg. 17 */
{
    uint8_t h[32], kr[64];
    tables();
#ifndef MUT_NO_EK_CHECK
    {
        uint8_t again[384];
        poly t;
        int i;
        for (i = 0; i < K; i++) {                           /* the modulus check */
            decode(&t, ek + 384 * i, 12);
            encode(again, &t, 12);
            if (memcmp(again, ek + 384 * i, 384)) return -1;
        }
    }
#endif
    H(ek, EK_BYTES, h);
    G2(m, 32, h, 32, kr);
    pke_encrypt(ct, ek, m, kr + 32);
    memcpy(ss, kr, 32);
#ifdef MUT_OVERRUN
    ss[32] ^= 0xff;
#endif
    return 0;
}

int NAME(dec)(uint8_t *ss, const uint8_t *ct, const uint8_t *dk)                 /* Alg. 18 */
{
    static uint8_t again[CT_BYTES];
    const uint8_t *ek = dk + 384 * K, *h = dk + 768 * K + 32, *z = dk + 768 * K + 64;
    uint8_t m[32], kr[64], test[32];

    tables();
#ifndef MUT_NO_DK_CHECK
    H(ek, EK_BYTES, test);                                  /* the hash check */
    if (memcmp(test, h, 32)) return -1;
#endif
    pke_decrypt(m, dk, ct);
    G2(m, 32, h, 32, kr);
    pke_encrypt(again, ek, m, kr + 32);
    memcpy(ss, kr, 32);
#ifndef MUT_NO_REJECT
    if (memcmp(again, ct, CT_BYTES)) J(z, 32, ct, CT_BYTES, ss);
#endif
    (void)test; (void)z;
    return 0;
}
