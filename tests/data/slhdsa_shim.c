/*
 * Test shim: an SLH-DSA-SHA2-128f library with slhdsa-c's API
 * (pq-code-package/slhdsa-c) whose entry points call back into Python, so the
 * --audit-slhdsa ctypes path can be tested offline and faults planted in the
 * callbacks. The Python side (tests/test_pqverify.py) answers NIST's inputs
 * from NIST's own expected results, keyed by the inputs in slhdsa-c's argument
 * order, and any other input with a stand-in signature.
 * Built with -DPQVTEST_NO_PREHASH it has no pre-hash entry points; with
 * -DPQVTEST_TWO_SIGNERS it exports a second pure signer, which makes that role
 * ambiguous.
 */
#include <stddef.h>
#include <stdint.h>

typedef struct { int set; } slh_param_t;
const slh_param_t slh_dsa_sha2_128f = {1};

typedef int (*pqv_rbg)(uint8_t *, size_t);
typedef int (*kg_cb)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *, const uint8_t *);
typedef int (*kgr_cb)(uint8_t *, uint8_t *, pqv_rbg);
/* iface: 0 internal, 1 pure, 2 pre-hash */
typedef size_t (*sign_cb)(int, uint8_t *, const uint8_t *, size_t, const uint8_t *, size_t,
                          const char *, const uint8_t *, const uint8_t *);
typedef int (*ver_cb)(int, const uint8_t *, size_t, const uint8_t *, size_t,
                      const uint8_t *, size_t, const char *, const uint8_t *);
static kg_cb KG; static kgr_cb KGR; static sign_cb SIGN; static ver_cb VER;

void pqvtest_slhdsa_register(kg_cb a, kgr_cb b, sign_cb c, ver_cb d)
{
    KG = a; KGR = b; SIGN = c; VER = d;
}

int slh_keygen_internal(uint8_t *sk, uint8_t *pk, const uint8_t *sk_seed,
                        const uint8_t *sk_prf, const uint8_t *pk_seed, const slh_param_t *prm)
{
    (void)prm; return KG(sk, pk, sk_seed, sk_prf, pk_seed);
}
int slh_keygen(uint8_t *sk, uint8_t *pk, int (*rbg)(uint8_t *, size_t), const slh_param_t *prm)
{
    (void)prm; return KGR(sk, pk, rbg);
}
size_t slh_sign_internal(uint8_t *sig, const uint8_t *m, size_t m_sz, const uint8_t *sk,
                         const uint8_t *addrnd, const slh_param_t *prm)
{
    (void)prm; return SIGN(0, sig, m, m_sz, NULL, 0, NULL, sk, addrnd);
}
size_t slh_sign(uint8_t *sig, const uint8_t *m, size_t m_sz, const uint8_t *ctx, size_t ctx_sz,
                const uint8_t *sk, const uint8_t *addrnd, const slh_param_t *prm)
{
    (void)prm; return SIGN(1, sig, m, m_sz, ctx, ctx_sz, NULL, sk, addrnd);
}
int slh_verify_internal(const uint8_t *m, size_t m_sz, const uint8_t *sig, size_t sig_sz,
                        const uint8_t *pk, const slh_param_t *prm)
{
    (void)prm; return VER(0, m, m_sz, sig, sig_sz, NULL, 0, NULL, pk);
}
int slh_verify(const uint8_t *m, size_t m_sz, const uint8_t *sig, size_t sig_sz,
               const uint8_t *ctx, size_t ctx_sz, const uint8_t *pk, const slh_param_t *prm)
{
    (void)prm; return VER(1, m, m_sz, sig, sig_sz, ctx, ctx_sz, NULL, pk);
}
#ifndef PQVTEST_NO_PREHASH
size_t hash_slh_sign(uint8_t *sig, const uint8_t *m, size_t m_sz, const uint8_t *ctx,
                     size_t ctx_sz, const char *ph, const uint8_t *sk, const uint8_t *addrnd,
                     const slh_param_t *prm)
{
    (void)prm; return SIGN(2, sig, m, m_sz, ctx, ctx_sz, ph, sk, addrnd);
}
int hash_slh_verify(const uint8_t *m, size_t m_sz, const uint8_t *sig, size_t sig_sz,
                    const uint8_t *ctx, size_t ctx_sz, const char *ph, const uint8_t *pk,
                    const slh_param_t *prm)
{
    (void)prm; return VER(2, m, m_sz, sig, sig_sz, ctx, ctx_sz, ph, pk);
}
#endif
#ifdef PQVTEST_TWO_SIGNERS
size_t pqvtest_other_slh_sign(uint8_t *sig, const uint8_t *m, size_t m_sz, const uint8_t *ctx,
                              size_t ctx_sz, const uint8_t *sk, const uint8_t *addrnd,
                              const slh_param_t *prm)
{
    (void)prm; return SIGN(1, sig, m, m_sz, ctx, ctx_sz, NULL, sk, addrnd);
}
#endif
size_t slh_pk_sz(const slh_param_t *prm) { (void)prm; return 32; }
size_t slh_sk_sz(const slh_param_t *prm) { (void)prm; return 64; }
size_t slh_sig_sz(const slh_param_t *prm) { (void)prm; return 17088; }
