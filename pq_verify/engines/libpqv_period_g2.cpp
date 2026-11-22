
// libperiod_g2.cpp v2 -- rank-4 (genus-2 hyperelliptic) C++ engine for pq-verify
// Closed-form M(z), M'(z) derived from Paper 7 (Maino 2026) via Griffiths-Dwork.
// Templated entry functions so the same code path works for double AND
// std::complex<double> -- residues by complex matrix contour integration.

#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <complex>

using cd = std::complex<double>;

// ------------------- 4x4 matrix primitives, templated -------------------
template<typename T>
static inline void m4_mul(const T *A, const T *B, T *C) {
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            T s = T(0);
            for (int k = 0; k < 4; k++) s += A[i*4 + k] * B[k*4 + j];
            C[i*4 + j] = s;
        }
    }
}
template<typename T>
static inline void m4_neg(const T *A, T *C) { for (int i = 0; i < 16; i++) C[i] = -A[i]; }
template<typename T>
static inline void m4_sub(const T *A, const T *B, T *C) { for (int i = 0; i < 16; i++) C[i] = A[i] - B[i]; }
template<typename T>
static inline void m4_add(const T *A, const T *B, T *C) { for (int i = 0; i < 16; i++) C[i] = A[i] + B[i]; }
template<typename T>
static inline T m4_trace(const T *A) { return A[0] + A[5] + A[10] + A[15]; }

static inline double m4_max_abs(const double *A) {
    double m = 0.0;
    for (int i = 0; i < 16; i++) { double v = std::fabs(A[i]); if (v > m) m = v; }
    return m;
}

// ------------------- Closed-form M(z), M'(z), templated -------------------
template<typename T>
static void compute_M(T z, T *M) {
    M[0] = T((1.0/2.0)*(-(z*z) + 6.0*z - 11.0)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[1] = T((1.0/2.0)*(-(z*z) + 6.0*z + 11.0)/(z*(z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[2] = T((1.0/2.0)*(-z - 12.0)/(z*(z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[3] = T((3.0/2.0)/(z*(z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[4] = T(-3.0/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[5] = T((1.0/2.0)*(-(z*z) + 6.0*z + 11.0)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[6] = T((1.0/2.0)*(-z - 12.0)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[7] = T((3.0/2.0)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[8] = T(-3.0*z/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[9] = T((11.0*z - 3.0)/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[10] = T(-1.0/2.0*z*(z + 12.0)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[11] = T((3.0/2.0)*z/((z - 3.0)*(z - 2.0)*(z - 1.0)));
    M[12] = T(-3.0*(z*z)/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[13] = T(z*(11.0*z - 3.0)/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[14] = T((1.0/2.0)*(-18.0*(z*z) + 11.0*z - 6.0)/((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0));
    M[15] = T((3.0/2.0)*(z*z)/((z - 3.0)*(z - 2.0)*(z - 1.0)));
}
template<typename T>
static void compute_Mp(T z, T *Mp) {
    Mp[0] = T((1.0/2.0)*((z*z*z*z) - 12.0*(z*z*z) + 58.0*(z*z) - 120.0*z + 85.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[1] = T(((z*z*z*z*z) - 12.0*(z*z*z*z) + 14.0*(z*z*z) + 69.0*(z*z) - 121.0*z + 33.0)/((z*z)*((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0)));
    Mp[2] = T((1.0/2.0)*(3.0*(z*z*z*z) + 36.0*(z*z*z) - 205.0*(z*z) + 264.0*z - 72.0)/((z*z)*((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0)));
    Mp[3] = T(3.0*(-2.0*(z*z*z) + 9.0*(z*z) - 11.0*z + 3.0)/((z*z)*((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0)));
    Mp[4] = T(3.0*(3.0*(z*z) - 12.0*z + 11.0)/pow((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0, 2.0));
    Mp[5] = T((1.0/2.0)*((z*z*z*z) - 12.0*(z*z*z) - 8.0*(z*z) + 144.0*z - 157.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[6] = T(((z*z*z) + 15.0*(z*z) - 72.0*z + 69.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[7] = T((3.0/2.0)*(-3.0*(z*z) + 12.0*z - 11.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[8] = T(6.0*((z*z*z) - 3.0*(z*z) + 3.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[9] = T((-22.0*(z*z*z) + 75.0*(z*z) - 36.0*z - 33.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[10] = T((1.0/2.0)*((z*z*z*z) + 24.0*(z*z*z) - 83.0*(z*z) + 12.0*z + 72.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[11] = T(3.0*(-(z*z*z) + 3.0*(z*z) - 3.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[12] = T(3.0*z*((z*z*z) - 11.0*z + 12.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[13] = T((-11.0*(z*z*z*z) + 6.0*(z*z*z) + 103.0*(z*z) - 132.0*z + 18.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[14] = T(z*(9.0*(z*z*z) - 11.0*(z*z) - 57.0*z + 72.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
    Mp[15] = T((3.0/2.0)*z*(-(z*z*z) + 11.0*z - 12.0)/((z*z*z*z*z*z) - 12.0*(z*z*z*z*z) + 58.0*(z*z*z*z) - 144.0*(z*z*z) + 193.0*(z*z) - 132.0*z + 36.0));
}

// Mpp only needed for double Theorem 1 audit (not for residue integration).
static void compute_Mpp(double z, double *Mpp) {
    Mpp[0] = (-(z*z*z*z*z*z) + 18.0*(z*z*z*z*z) - 141.0*(z*z*z*z) + 570.0*(z*z*z) - 1227.0*(z*z) + 1332.0*z - 575.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[1] = (-3.0*(z*z*z*z*z*z*z*z) + 54.0*(z*z*z*z*z*z*z) - 203.0*(z*z*z*z*z*z) - 180.0*(z*z*z*z*z) + 2493.0*(z*z*z*z) - 5496.0*(z*z*z) + 5181.0*(z*z) - 2178.0*z + 396.0)/((z*z*z)*((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0));
    Mpp[2] = (-6.0*(z*z*z*z*z*z*z) - 72.0*(z*z*z*z*z*z) + 939.0*(z*z*z*z*z) - 3600.0*(z*z*z*z) + 6395.0*(z*z*z) - 5652.0*(z*z) + 2376.0*z - 432.0)/((z*z*z)*((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0));
    Mpp[3] = 3.0*(10.0*(z*z*z*z*z*z) - 90.0*(z*z*z*z*z) + 315.0*(z*z*z*z) - 540.0*(z*z*z) + 471.0*(z*z) - 198.0*z + 36.0)/((z*z*z)*((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0));
    Mpp[4] = 6.0*(-3.0*(2.0 - z)*((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0) - pow(3.0*(z*z) - 12.0*z + 11.0, 2.0))/pow((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0, 3.0);
    Mpp[5] = (-(z*z*z*z*z*z) + 18.0*(z*z*z*z*z) - 9.0*(z*z*z*z) - 486.0*(z*z*z) + 1875.0*(z*z) - 2628.0*z + 1295.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[6] = (-3.0*(z*z*z*z*z) - 54.0*(z*z*z*z) + 551.0*(z*z*z) - 1728.0*(z*z) + 2268.0*z - 1086.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[7] = 3.0*(6.0*(z*z*z*z) - 48.0*(z*z*z) + 141.0*(z*z) - 180.0*z + 85.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[8] = 6.0*(-z*pow(3.0*(z*z) - 12.0*z + 11.0, 2.0) + (3.0*(z*z) + 3.0*z*(z - 2.0) - 12.0*z + 11.0)*((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0))/pow((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0, 3.0);
    Mpp[9] = 2.0*((11.0*z - 3.0)*pow(3.0*(z*z) - 12.0*z + 11.0, 2.0) - (33.0*(z*z) - 132.0*z + 3.0*(z - 2.0)*(11.0*z - 3.0) + 121.0)*((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0))/pow((z*z*z) - 6.0*(z*z) + 11.0*z - 6.0, 3.0);
    Mpp[10] = (-(z*z*z*z*z*z) - 36.0*(z*z*z*z*z) + 249.0*(z*z*z*z) - 408.0*(z*z*z) - 324.0*(z*z) + 1296.0*z - 828.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[11] = 3.0*(3.0*(z*z*z*z*z) - 18.0*(z*z*z*z) + 25.0*(z*z*z) + 36.0*(z*z) - 108.0*z + 66.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[12] = 6.0*(-(z*z*z*z*z*z) + 33.0*(z*z*z*z) - 108.0*(z*z*z) + 108.0*(z*z) - 36.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[13] = 2.0*(11.0*(z*z*z*z*z*z) - 9.0*(z*z*z*z*z) - 309.0*(z*z*z*z) + 1113.0*(z*z*z) - 1296.0*(z*z) + 324.0*z + 198.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[14] = (-18.0*(z*z*z*z*z*z) + 33.0*(z*z*z*z*z) + 360.0*(z*z*z*z) - 1381.0*(z*z*z) + 1494.0*(z*z) - 108.0*z - 432.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
    Mpp[15] = 3.0*((z*z*z*z*z*z) - 33.0*(z*z*z*z) + 108.0*(z*z*z) - 108.0*(z*z) + 36.0)/((z*z*z*z*z*z*z*z*z) - 18.0*(z*z*z*z*z*z*z*z) + 141.0*(z*z*z*z*z*z*z) - 630.0*(z*z*z*z*z*z) + 1767.0*(z*z*z*z*z) - 3222.0*(z*z*z*z) + 3815.0*(z*z*z) - 2826.0*(z*z) + 1188.0*z - 216.0);
}

// ------------------- f2 and f4 via matrix expression (any numeric type T) -------------------
template<typename T>
static T evaluate_f2(T z) {
    T M[16], Mp[16];
    compute_M(z, M);
    compute_Mp(z, Mp);
    T MM[16], tmp[16], Q[16];
    m4_mul(M, M, MM);
    m4_add(Mp, MM, tmp); m4_neg(tmp, Q);
    T UQ[16], QU[16], cQ[16], cQ2[16];
    m4_mul(M, Q, UQ); m4_mul(Q, M, QU);
    m4_sub(UQ, QU, cQ);
    m4_mul(cQ, cQ, cQ2);
    return m4_trace(cQ2);
}
template<typename T>
static T evaluate_f4(T z) {
    T M[16], Mp[16];
    compute_M(z, M);
    compute_Mp(z, Mp);
    T MM[16], tmp[16], Q[16];
    m4_mul(M, M, MM);
    m4_add(Mp, MM, tmp); m4_neg(tmp, Q);
    T UQ[16], QU[16], cQ[16], cQ2[16], cQ4[16];
    m4_mul(M, Q, UQ); m4_mul(Q, M, QU);
    m4_sub(UQ, QU, cQ);
    m4_mul(cQ, cQ, cQ2);
    m4_mul(cQ2, cQ2, cQ4);
    return m4_trace(cQ4);
}

// ------------------- Result struct exposed to Python -------------------
struct period_g2_result_t {
    double tr_commQ, tr_commQ2, tr_commQ3, tr_commQ4;
    double thm1_resid[16];
    double thm1_resid_max, R_norm_inf;
    int ok_traceless, ok_tr3_zero, ok_theorem1;
};

extern "C" void period_g2_audit(double z, double tol, period_g2_result_t *out) {
    double M[16], Mp[16], Mpp[16];
    compute_M<double>(z, M); compute_Mp<double>(z, Mp); compute_Mpp(z, Mpp);
    double MM[16], tmp[16], Q[16];
    m4_mul(M, M, MM); m4_add(Mp, MM, tmp); m4_neg(tmp, Q);
    double UQ[16], QU[16], commQ[16];
    m4_mul(M, Q, UQ); m4_mul(Q, M, QU); m4_sub(UQ, QU, commQ);
    double cQ2[16], cQ3[16], cQ4[16];
    m4_mul(commQ, commQ, cQ2);
    m4_mul(cQ2, commQ, cQ3);
    m4_mul(cQ2, cQ2, cQ4);
    out->tr_commQ  = m4_trace(commQ);
    out->tr_commQ2 = m4_trace(cQ2);
    out->tr_commQ3 = m4_trace(cQ3);
    out->tr_commQ4 = m4_trace(cQ4);

    double MpU[16], UMp[16], tmp2[16], Qp[16];
    m4_mul(Mp, M, MpU); m4_mul(M, Mp, UMp);
    m4_add(Mpp, MpU, tmp); m4_add(tmp, UMp, tmp2); m4_neg(tmp2, Qp);
    double D[16], A[16], S[16], Sp[16];
    m4_sub(MM, Q, D); for (int i = 0; i < 16; i++) D[i] *= 2.0;
    for (int i = 0; i < 16; i++) A[i] = -4.0*UMp[i] - 2.0*Qp[i];
    for (int i = 0; i < 16; i++) S[i] = 2.0*Q[i];
    for (int i = 0; i < 16; i++) Sp[i] = 2.0*Qp[i];
    double in1[16], in2[16], in3[16];
    m4_add(A, Sp, in1); m4_add(D, S, in2);
    for (int i = 0; i < 16; i++) in3[i] = D[i] + 2.0*S[i];
    double in1sq[16], in3sq[16], prod[16], R[16];
    m4_mul(in1, in1, in1sq); m4_mul(in3, in3, in3sq);
    m4_mul(in2, in3sq, prod);
    for (int i = 0; i < 16; i++) R[i] = in1sq[i] - 2.0*prod[i];
    double cQ_Mp[16], U_cQ_Mp[16];
    m4_mul(commQ, Mp, cQ_Mp); m4_mul(M, cQ_Mp, U_cQ_Mp);
    double resid[16];
    for (int i = 0; i < 16; i++) { resid[i] = R[i] - 16.0*U_cQ_Mp[i]; out->thm1_resid[i] = resid[i]; }
    out->R_norm_inf = m4_max_abs(R);
    double r_inf = m4_max_abs(resid);
    out->thm1_resid_max = (out->R_norm_inf > 0.0) ? (r_inf / out->R_norm_inf) : r_inf;
    double scale = std::fabs(out->tr_commQ2) + 1.0;
    out->ok_traceless = (std::fabs(out->tr_commQ) < tol * scale);
    out->ok_tr3_zero  = (std::fabs(out->tr_commQ3) < tol * scale);
    out->ok_theorem1  = (out->thm1_resid_max < tol);
}

// ------------------- Residues via complex matrix contour integration -------------------
// At each z_k on the circle |z - z0| = r, evaluate f(z_k) via the matrix
// expression in std::complex<double> arithmetic, then sum (1/N) f(z_k) * offset_k.
extern "C" double period_g2_residue_f2(double z0, double radius, int n_quad) {
    cd sum(0.0, 0.0);
    for (int k = 0; k < n_quad; k++) {
        double theta = 2.0 * M_PI * k / n_quad;
        cd offset(radius * std::cos(theta), radius * std::sin(theta));
        cd zc(z0, 0.0); zc += offset;
        cd f = evaluate_f2<cd>(zc);
        sum += f * offset;
    }
    sum /= static_cast<double>(n_quad);
    return sum.real();
}
extern "C" double period_g2_residue_f4(double z0, double radius, int n_quad) {
    cd sum(0.0, 0.0);
    for (int k = 0; k < n_quad; k++) {
        double theta = 2.0 * M_PI * k / n_quad;
        cd offset(radius * std::cos(theta), radius * std::sin(theta));
        cd zc(z0, 0.0); zc += offset;
        cd f = evaluate_f4<cd>(zc);
        sum += f * offset;
    }
    sum /= static_cast<double>(n_quad);
    return sum.real();
}

extern "C" int period_g2_version(void) { return 65; }   // bumped: v2 with complex matrix residues
