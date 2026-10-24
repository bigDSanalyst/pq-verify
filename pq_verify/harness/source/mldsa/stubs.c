/* The contract standing in for the library's montgomery_reduce while CBMC
 * checks its callers: exactly what h_montgomery.c proves of the library's own
 * function on every input it admits. The output is any value the contract
 * allows, an over-approximation: it can only add behaviours, never hide one. */
#include "pqv_ns.h"
#include "params.h"
#include "pqv_fips204.h"
#include "reduce.h"

int32_t PQV_SYM_montgomery_reduce(int64_t a) {
#ifndef PQV_NO_PRECONDITION
    __CPROVER_assert(a >= PQV_MONT_MIN && a <= PQV_MONT_MAX,
                     "montgomery_reduce contract: input in {-2^31 q, ..., 2^31 q - 1}");
#else
    (void)a;
#endif
    int32_t r = nondet_int32();
    __CPROVER_assume(r > -Q && r < Q);
    return r;
}
