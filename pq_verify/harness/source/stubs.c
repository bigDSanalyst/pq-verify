/* Contracts standing in for the library's two reductions while CBMC checks
 * their callers. Each is exactly what the exhaustive test proves of the
 * library's own compiled function on every input it admits, so a caller
 * shown safe against the contract is safe with the real function.
 * The output is any value the contract allows (nondeterministic), which is
 * an over-approximation: it can only add behaviours, never hide one. */
#include "pqv_ns.h"
#include "params.h"
#include "reduce.h"

int16_t NS(montgomery_reduce)(int32_t a) {
#ifndef PQV_NO_PRECONDITION
    __CPROVER_assert(a >= -(int32_t)KYBER_Q * 32768 && a <= (int32_t)KYBER_Q * 32768 - 1,
                     "montgomery_reduce contract: input in {-q*2^15, ..., q*2^15 - 1}");
#endif
    int16_t r = nondet_int16();
    __CPROVER_assume(r > -KYBER_Q && r < KYBER_Q);
    return r;
}

int16_t NS(barrett_reduce)(int16_t a) {
    (void)a;
    int16_t r = nondet_int16();
    __CPROVER_assume(r >= -(KYBER_Q - 1) / 2 && r <= (KYBER_Q - 1) / 2);
    return r;
}
