/*
 * pq-verify's constant-time hook shim: link this file into a library built
 * with pq_verify/harness/ct first on its include path.
 *
 * Each secret mark or declassification the library makes arrives here with
 * its call site. The real Valgrind client request is made first, so memcheck
 * behaves exactly as in the library's own constant-time tests; then one line
 * is appended to the log named by PQV_CT_LOG (no log when it is unset):
 *
 *   S <function> <file>:<line> <expression> <length>
 *   D <function> <file>:<line> <expression> <length> <hex bytes>
 *   N <text>                     (pqv_ct_note, from pq-verify's driver)
 *
 * A declassification's bytes are written after they are marked defined, so
 * the logging cannot itself trip memcheck; a secret mark logs no bytes.
 * Outside Valgrind the client requests are no-ops and only the log remains.
 * CONSTANT-TIME.md, section 2, is the specification.
 *
 * Never link this into a production build.
 */
#define PQV_CT_SHIM_IMPL
#include <valgrind/memcheck.h>

#include <fcntl.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define PQV_EXPORT __attribute__((visibility("default")))

PQV_EXPORT const char pqv_ct_shim_version[] = "pq-verify-ct-shim/1";

static int pqv_fd = -2;

static void pqv_open(void) {
  if (pqv_fd == -2) {
    const char *path = getenv("PQV_CT_LOG");
    pqv_fd = path ? open(path, O_WRONLY | O_APPEND | O_CREAT, 0600) : -1;
  }
}

static void pqv_put(const char *s, size_t n) {
  while (n) {
    ssize_t w = write(pqv_fd, s, n);
    if (w <= 0) return;
    s += w;
    n -= (size_t)w;
  }
}

static void pqv_str(const char *s) { pqv_put(s, strlen(s)); }

static void pqv_num(unsigned long v) {
  char t[24];
  size_t k = sizeof t;
  do {
    t[--k] = (char)('0' + v % 10);
    v /= 10;
  } while (v);
  pqv_put(t + k, sizeof t - k);
}

PQV_EXPORT void pqv_ct_note(const char *what) {
  pqv_open();
  if (pqv_fd < 0) return;
  pqv_str("N\t");
  pqv_str(what);
  pqv_str("\n");
}

PQV_EXPORT int pqv_ct_mark(int secret, const char *fn, const char *file, int line,
                           const char *expr, const volatile void *p, size_t n) {
  static const char hex[] = "0123456789abcdef";
  const char *base;
  char buf[512];
  size_t i, j = 0;

  if (secret)
    VALGRIND_MAKE_MEM_UNDEFINED(p, n);
  else
    VALGRIND_MAKE_MEM_DEFINED(p, n);

  pqv_open();
  if (pqv_fd < 0) return 0;
  base = strrchr(file, '/');
  base = base ? base + 1 : file;
  pqv_str(secret ? "S\t" : "D\t");
  pqv_str(fn);
  pqv_str("\t");
  pqv_str(base);
  pqv_str(":");
  pqv_num((unsigned long)line);
  pqv_str("\t");
  pqv_str(expr);
  pqv_str("\t");
  pqv_num((unsigned long)n);
  if (!secret) {
    pqv_str("\t");
    for (i = 0; i < n; i++) {
      unsigned char c = ((const volatile unsigned char *)p)[i];
      buf[j++] = hex[c >> 4];
      buf[j++] = hex[c & 15];
      if (j == sizeof buf) {
        pqv_put(buf, j);
        j = 0;
      }
    }
    pqv_put(buf, j);
  }
  pqv_str("\n");
  return 0;
}
