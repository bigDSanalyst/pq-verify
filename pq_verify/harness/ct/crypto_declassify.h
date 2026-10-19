/*
 * pq-verify's constant-time hook shim for PQClean's crypto_declassify().
 *
 * PQClean defines crypto_declassify(x, len) as an empty macro in
 * common/crypto_declassify.h. Put this directory before PQClean's common/
 * on the include path and the same calls mark the value public for
 * memcheck and record their call site through pqv_ct_mark(), in
 * pqv_ct_shim.c. CONSTANT-TIME.md, sections 2 and 6, is the specification.
 */
#ifndef PQCLEAN_CRYPTO_DECLASSIFY
#define PQCLEAN_CRYPTO_DECLASSIFY

#include <stddef.h>

int pqv_ct_mark(int secret, const char *fn, const char *file, int line,
                const char *expr, const volatile void *p, size_t n);

#define crypto_declassify(x, y) \
  ((void)pqv_ct_mark(0, __func__, __FILE__, __LINE__, #x, (x), (y)))

#endif /* PQCLEAN_CRYPTO_DECLASSIFY */
