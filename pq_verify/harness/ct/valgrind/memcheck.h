/*
 * pq-verify's constant-time hook shim for Valgrind client requests.
 *
 * Put this directory first on the include path (-I .../harness/ct) when
 * building a library whose constant-time annotations are Valgrind's own
 * client requests (mldsa-native with MLD_CONFIG_CT_TESTING_ENABLED, for one).
 * The real <valgrind/memcheck.h> is still included, and every request works
 * as before; VALGRIND_MAKE_MEM_UNDEFINED and VALGRIND_MAKE_MEM_DEFINED also
 * record their call site (function, file, line and the expression annotated)
 * through pqv_ct_mark(), in pqv_ct_shim.c, which is linked into the library.
 * CONSTANT-TIME.md, section 2, is the specification.
 */
#ifndef PQV_CT_SHIM_MEMCHECK_H
#define PQV_CT_SHIM_MEMCHECK_H

#include_next <valgrind/memcheck.h>

#ifndef PQV_CT_SHIM_IMPL
#include <stddef.h>

int pqv_ct_mark(int secret, const char *fn, const char *file, int line,
                const char *expr, const volatile void *p, size_t n);

#undef VALGRIND_MAKE_MEM_UNDEFINED
#undef VALGRIND_MAKE_MEM_DEFINED
#define VALGRIND_MAKE_MEM_UNDEFINED(p, n) \
  pqv_ct_mark(1, __func__, __FILE__, __LINE__, #p, (p), (n))
#define VALGRIND_MAKE_MEM_DEFINED(p, n) \
  pqv_ct_mark(0, __func__, __FILE__, __LINE__, #p, (p), (n))
#endif /* !PQV_CT_SHIM_IMPL */

#endif /* PQV_CT_SHIM_MEMCHECK_H */
