/*
 * libperiod.c — Engine 6 for pq-verify
 *
 * Rank-2 matrix Schwarzian / Amari-Schwarzian verification, derived
 * from Paper 7 (Maino 2026, in preparation) and the Legendre family
 * y^2 = x(x-1)(x-z).
 *
 * The Legendre Picard-Fuchs equation is
 *     z(1-z) F'' + (1-2z) F' - F/4 = 0
 * which in companion form gives the Gauss-Manin connection
 *     U(z) = [[0, 1], [a(z), b(z)]]
 * with
 *     a(z) =  1 / (4 z (1-z))
 *     b(z) = -(1 - 2z) / (z (1-z))
 *
 * We verify, at any sample z in (0,1) or |z|>1:
 *   (I1) Matrix Riccati structure: Q = -(U' + U^2)  -- definitional
 *   (I2) [U, Q] is traceless
 *   (I3) [U, Q]^2 is a scalar matrix (rank-2 collapse)
 *   (I4) tr([U,Q]^2) = 2 * tr(U[U,Q]U')
 *   (I5) Closed form: tr(U[U,Q]U') = (-12z^2+12z-7)/(16 z^4 (z-1)^4)
 *
 * (I1)-(I4) follow from rank-2 algebra; they hold for ANY second-order
 * ODE in companion form, not just Legendre.  (I5) is Legendre-specific
 * and is the actual fingerprint that a period-theory implementation
 * must reproduce.
 *
 * Build:  gcc -O3 -Wall -shared -fPIC libperiod.c -lm -o libperiod.so
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <complex.h>

/* ---------- 2x2 matrix primitives (row-major, double) ---------- */
typedef struct { double m[4]; } M2;   /* m[0]=00, m[1]=01, m[2]=10, m[3]=11 */

static inline M2 m2_mul(M2 A, M2 B) {
    M2 C;
    C.m[0] = A.m[0]*B.m[0] + A.m[1]*B.m[2];
    C.m[1] = A.m[0]*B.m[1] + A.m[1]*B.m[3];
    C.m[2] = A.m[2]*B.m[0] + A.m[3]*B.m[2];
    C.m[3] = A.m[2]*B.m[1] + A.m[3]*B.m[3];
    return C;
}
static inline M2 m2_sub(M2 A, M2 B) {
    M2 C;
    for (int i=0;i<4;i++) C.m[i] = A.m[i] - B.m[i];
    return C;
}
static inline M2 m2_neg(M2 A) {
    M2 C;
    for (int i=0;i<4;i++) C.m[i] = -A.m[i];
    return C;
}
static inline double m2_trace(M2 A) { return A.m[0] + A.m[3]; }

/* ---------- Legendre Gauss-Manin connection U(z) and U'(z) ---------- */
/* a(z) = 1 / (4z(1-z));  b(z) = -(1-2z)/(z(1-z))                   */
static void legendre_U(double z, M2 *U) {
    double zm = 1.0 - z;
    double denom_a = 4.0 * z * zm;
    double denom_b = z * zm;
    U->m[0] = 0.0;
    U->m[1] = 1.0;
    U->m[2] = 1.0 / denom_a;
    U->m[3] = -(1.0 - 2.0*z) / denom_b;
}

/* Closed-form derivatives:
 *   a'(z) = (2z - 1) / (4 z^2 (1-z)^2)
 *   b'(z) = (1 - 2z + 2z^2) / (z^2 (1-z)^2)
 *           [equivalently (2z^2 - 2z + 1)/(z(1-z))^2]
 */
static void legendre_Uprime(double z, M2 *Up) {
    double zm = 1.0 - z;
    double zm2 = zm*zm;
    double z2  = z*z;
    Up->m[0] = 0.0;
    Up->m[1] = 0.0;
    Up->m[2] = (2.0*z - 1.0) / (4.0 * z2 * zm2);
    Up->m[3] = (2.0*z2 - 2.0*z + 1.0) / (z2 * zm2);
}

/* Closed-form second derivatives (verified symbolically):
 *   a''(z) = (-3z^3 + 6z^2 - 4z + 1) / (2 z^3 (z-1)^4)
 *   b''(z) = 2(-2z^3 + 3z^2 - 3z + 1) / (z^3 (z-1)^3)
 */
static void legendre_Upp(double z, M2 *Upp) {
    double zm1   = z - 1.0;
    double zm1_2 = zm1*zm1;
    double zm1_3 = zm1_2*zm1;
    double zm1_4 = zm1_3*zm1;
    double z2 = z*z, z3 = z2*z;
    Upp->m[0] = 0.0;
    Upp->m[1] = 0.0;
    Upp->m[2] = (-3.0*z3 + 6.0*z2 - 4.0*z + 1.0) / (2.0 * z3 * zm1_4);
    Upp->m[3] = 2.0 * (-2.0*z3 + 3.0*z2 - 3.0*z + 1.0) / (z3 * zm1_3);
}

/* Closed-form invariant (Legendre-specific): tr(U[U,Q]U') */
static double legendre_inv1_closed(double z) {
    double num   = -12.0*z*z + 12.0*z - 7.0;
    double zm    = z - 1.0;            /* (z-1) per derivation */
    double zm4   = zm*zm*zm*zm;
    double z4    = z*z*z*z;
    return num / (16.0 * z4 * zm4);
}

/* ---------- Core engine: compute invariants and identity checks ---------- */
typedef struct {
    double inv1;          /* tr(U[U,Q]U')   */
    double inv2;          /* tr([U,Q]^2)    */
    double inv1_closed;   /* Legendre closed form */
    double tr_comm;       /* tr([U,Q])      -- should be 0 */
    double comm2_off01;   /* [U,Q]^2 entry (0,1) -- should be 0 */
    double comm2_off10;   /* [U,Q]^2 entry (1,0) -- should be 0 */
    double comm2_diag_diff; /* [U,Q]^2 (0,0) - (1,1) -- should be 0 */

    /* Theorem 1: full residual R - 16 U[U,Q]U' entry-wise (must be ~ 0) */
    double thm1_resid[4];        /* R - 16U[U,Q]U' (0,0),(0,1),(1,0),(1,1)  */
    double thm1_resid_max;       /* max |entry| / max |R entry|              */
    double R_norm_inf;           /* max |R entry|                            */

    int    ok_riccati;
    int    ok_traceless;
    int    ok_scalar_comm2;
    int    ok_ratio;
    int    ok_closed_form;
    int    ok_theorem1;          /* R - 16U[U,Q]U' = 0 (full statement)      */
} period_result_t;

/* Compute everything at one sample z.  Tolerance is relative; scales chosen
 * to be tight at "ordinary" sample points (z in [0.2, 0.8] except near 0,1).
 */
void period_audit_legendre(double z, double tol, period_result_t *out) {
    M2 U, Up, Upp;
    legendre_U(z, &U);
    legendre_Uprime(z, &Up);
    legendre_Upp(z, &Upp);

    M2 U2  = m2_mul(U, U);
    M2 sum = { { Up.m[0]+U2.m[0], Up.m[1]+U2.m[1],
                 Up.m[2]+U2.m[2], Up.m[3]+U2.m[3] } };
    M2 Q   = m2_neg(sum);

    M2 UQ = m2_mul(U, Q);
    M2 QU = m2_mul(Q, U);
    M2 C  = m2_sub(UQ, QU);          /* [U, Q] */

    M2 C2     = m2_mul(C, C);        /* [U,Q]^2 */
    M2 CUp    = m2_mul(C, Up);
    M2 UCUp   = m2_mul(U, CUp);      /* U[U,Q]U' */

    out->inv1        = m2_trace(UCUp);
    out->inv2        = m2_trace(C2);
    out->inv1_closed = legendre_inv1_closed(z);
    out->tr_comm     = m2_trace(C);
    out->comm2_off01 = C2.m[1];
    out->comm2_off10 = C2.m[2];
    out->comm2_diag_diff = C2.m[0] - C2.m[3];

    /* ---- Theorem 1 (Paper 7): R = (A + S')^2 - 2(D+S)(D+2S)^2  =  16 U[U,Q]U' ---- */
    /* Q' = -(U'' + (U^2)') = -(U'' + U'U + UU')                                       */
    M2 UpU  = m2_mul(Up, U);
    M2 UUp  = m2_mul(U, Up);
    M2 sum2 = { { Upp.m[0]+UpU.m[0]+UUp.m[0],
                  Upp.m[1]+UpU.m[1]+UUp.m[1],
                  Upp.m[2]+UpU.m[2]+UUp.m[2],
                  Upp.m[3]+UpU.m[3]+UUp.m[3] } };
    M2 Qp = m2_neg(sum2);

    /* D = 2(U^2 - Q), A = -4 U U' - 2 Q', S = 2 Q                                     */
    M2 D, A, S, Sp;
    for (int i = 0; i < 4; i++) {
        D.m[i] = 2.0 * (U2.m[i] - Q.m[i]);
        A.m[i] = -4.0 * UUp.m[i] - 2.0 * Qp.m[i];
        S.m[i] = 2.0 * Q.m[i];
        Sp.m[i] = 2.0 * Qp.m[i];
    }

    /* inner1 = A + S',  inner2 = D + S,  inner3 = D + 2S                              */
    M2 inner1, inner2, inner3;
    for (int i = 0; i < 4; i++) {
        inner1.m[i] = A.m[i] + Sp.m[i];
        inner2.m[i] = D.m[i] + S.m[i];
        inner3.m[i] = D.m[i] + 2.0 * S.m[i];
    }

    /* R = inner1^2 - 2 inner2 inner3 inner3                                           */
    M2 inner1_sq    = m2_mul(inner1, inner1);
    M2 inner3_sq    = m2_mul(inner3, inner3);
    M2 prod         = m2_mul(inner2, inner3_sq);
    M2 R;
    for (int i = 0; i < 4; i++) {
        R.m[i] = inner1_sq.m[i] - 2.0 * prod.m[i];
    }

    /* RHS = 16 U[U,Q]U'                                                               */
    M2 RHS;
    for (int i = 0; i < 4; i++) {
        RHS.m[i] = 16.0 * UCUp.m[i];
    }

    /* Residual = R - RHS                                                              */
    double rnorm = 0.0, dnorm = 0.0;
    for (int i = 0; i < 4; i++) {
        out->thm1_resid[i] = R.m[i] - RHS.m[i];
        if (fabs(R.m[i])              > rnorm) rnorm = fabs(R.m[i]);
        if (fabs(out->thm1_resid[i])  > dnorm) dnorm = fabs(out->thm1_resid[i]);
    }
    out->R_norm_inf = rnorm;
    out->thm1_resid_max = (rnorm > 0.0) ? (dnorm / rnorm) : dnorm;

    /* Identity checks.  Use relative tolerance against |inv2| where it
     * makes sense; absolute for the things that should be exactly zero.   */
    double scale = fabs(out->inv2) + 1.0;
    out->ok_riccati       = 1;   /* definitional: Q is built from U and U'. That U
                                   * is the periods' connection and U', U'' its
                                   * derivatives is checked outside the engine,
                                   * through period_legendre_connection. */
    out->ok_traceless     = (fabs(out->tr_comm) < tol * scale);
    out->ok_scalar_comm2  = (fabs(out->comm2_off01) < tol*scale
                          && fabs(out->comm2_off10) < tol*scale
                          && fabs(out->comm2_diag_diff) < tol*scale);
    out->ok_ratio         = (fabs(out->inv2 - 2.0*out->inv1) < tol * scale);
    out->ok_closed_form   = (fabs(out->inv1 - out->inv1_closed)
                             < tol * (fabs(out->inv1_closed) + 1.0));
    out->ok_theorem1      = (out->thm1_resid_max < tol);
}

/* U(z), U'(z) and U''(z) exactly as this engine computes them, row-major,
 * for checks made outside it: that U is the connection of the Legendre
 * periods, (w, w')' = U (w, w'), and U', U'' its derivatives. */
void period_legendre_connection(double z, double *U, double *Up, double *Upp) {
    M2 a, b, c;
    legendre_U(z, &a);
    legendre_Uprime(z, &b);
    legendre_Upp(z, &c);
    for (int i = 0; i < 4; i++) {
        U[i] = a.m[i];
        Up[i] = b.m[i];
        Upp[i] = c.m[i];
    }
}

/* Residues at z=0, z=1: from the closed form,
 *      tr(U[U,Q]U') = (-12z^2 + 12z - 7) / (16 z^4 (z-1)^4)
 * has poles of order 4 at z=0 and z=1, with residues
 *      Res_{z=0}  = -17/4
 *      Res_{z=1}  = +17/4
 *
 * Numerical extraction: parametrise z = z0 + r e^{i theta}, dz = i r e^{i theta} d theta.
 *      Res = (1/(2 pi i)) * contour integral
 *          = (1/N) * sum_{k=0}^{N-1} f(z_k) * (z_k - z0)
 * (the i, r, and 2 pi factors all cancel against the trapezoid weight).
 */
double period_residue_numeric(double z0, double radius, int n_quad) {
    _Complex double sum = 0.0 + 0.0*I;
    for (int k = 0; k < n_quad; k++) {
        double theta = 2.0 * M_PI * k / n_quad;
        _Complex double offset = radius * (cos(theta) + I*sin(theta));
        _Complex double zc = z0 + offset;
        _Complex double num   = -12.0*zc*zc + 12.0*zc - 7.0;
        _Complex double zm    = zc - 1.0;
        _Complex double zm4   = zm*zm*zm*zm;
        _Complex double z4    = zc*zc*zc*zc;
        _Complex double f     = num / (16.0 * z4 * zm4);
        sum += f * offset;
    }
    sum /= n_quad;
    return creal(sum);
}

/* ---------- Standalone main: smoke test ---------- */
#ifdef PERIOD_STANDALONE
int main(void) {
    printf("libperiod standalone smoke test (Paper 7 rank-2 / Legendre)\n");
    printf("===========================================================\n");
    double samples[] = {0.25, 0.333333333333333, 0.5, 0.6, 0.75, 1.3, -0.5, 2.0};
    int n = sizeof(samples) / sizeof(samples[0]);
    period_result_t r;
    int total_ok = 0, total = 0;
    for (int i = 0; i < n; i++) {
        double z = samples[i];
        period_audit_legendre(z, 1e-10, &r);
        int ok = r.ok_traceless && r.ok_scalar_comm2 && r.ok_ratio
              && r.ok_closed_form && r.ok_theorem1;
        total_ok += ok ? 1 : 0;
        total += 1;
        printf(" z=%+8.4f | tr(U[U,Q]U')=%+.4e | ratio=%.3f | "
               "||R-16U[U,Q]U'||/||R|| = %.2e | %s\n",
               z, r.inv1, r.inv2 / r.inv1, r.thm1_resid_max,
               ok ? "PASS" : "FAIL");
    }
    printf("\n%d / %d sample points pass all identity checks "
           "(including Theorem 1).\n", total_ok, total);

    /* Residue smoke test */
    double res0 = period_residue_numeric(0.0, 1e-3, 4096);
    double res1 = period_residue_numeric(1.0, 1e-3, 4096);
    printf("\nRes_{z=0}  = %+.6f  (expected -4.25 = -17/4)\n", res0);
    printf("Res_{z=1}  = %+.6f  (expected +4.25 = +17/4)\n", res1);
    printf("Res_{z=inf} = %+.6f  (expected 0)\n", -(res0+res1));

    return (total_ok == total) ? 0 : 1;
}
#endif
