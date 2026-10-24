/* montgomery_reduce on every input of its contract, {-2^31 q, ..., 2^31 q - 1}:
 * no undefined behaviour, r in (-q, q), and f(a + 2^32) = f(a) + 1 whenever a
 * and a + 2^32 are both in it. Its int64 domain, about 2^55 values, is too
 * large to enumerate, so CBMC proves this of the library's own C, unstubbed.
 * It uses Z3, which decides the shift property in seconds; Kissat takes
 * about 12 s, and MiniSat and CaDiCaL had not after ten minutes.
 *
 * With the exhaustive test, which checks r * 2^32 = a mod q for every a in
 * [0, 2^32), this gives the congruence on every input. Write a = l + h * 2^32
 * with l in [0, 2^32). The steps from l to a stay inside the interval, so
 * f(a) = f(l) + h, and f(a) * 2^32 = f(l) * 2^32 + h * 2^32 = l + h * 2^32 = a
 * mod q. The NTT's harnesses use the bound as montgomery_reduce's contract
 * (stubs.c). */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "reduce.h"

void harness(void) {
    int64_t a = nondet_int64();
    __CPROVER_assume(a >= PQV_MONT_MIN && a <= PQV_MONT_MAX);
    int32_t r = PQV_SYM_montgomery_reduce(a);
    __CPROVER_assert(r > -Q && r < Q, "montgomery_reduce: r in (-q, q)");
    if (a <= PQV_MONT_MAX - 4294967296LL) {
        int32_t s = PQV_SYM_montgomery_reduce(a + 4294967296LL);
        __CPROVER_assert(s == r + 1, "montgomery_reduce: f(a + 2^32) = f(a) + 1");
    }
#ifdef PQV_REACH
    __CPROVER_assert(0, "reach: the end of the harness is reachable");
#endif
}
