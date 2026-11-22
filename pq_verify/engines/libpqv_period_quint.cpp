
// libperiod_quintic.cpp -- rank-4 CY3 (mirror quintic) C++ engine for pq-verify
// Picard-Fuchs operator: theta^4 omega = 5z (5theta+1)(5theta+2)(5theta+3)(5theta+4) omega
// Singularities at z = 0, z = 1/3125 (conifold), and z = infinity.
// Verifies Theorem 1 entry-wise + Paper 7 Section 6 trace structure.

#include <cstdio>
#include <cmath>
#include <complex>

using cd = std::complex<double>;

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

// Templated compute_M, compute_Mp -- work for both double and complex<double>
template<typename T>
static void compute_M(T z, T *M) {
    M[0] = T(0.0);
    M[1] = T(1.0);
    M[2] = T(0.0);
    M[3] = T(0.0);
    M[4] = T(0.0);
    M[5] = T(0.0);
    M[6] = T(1.0);
    M[7] = T(0.0);
    M[8] = T(0.0);
    M[9] = T(0.0);
    M[10] = T(0.0);
    M[11] = T(1.0);
    M[12] = T(-120.0/((z*z*z)*(3125.0*z - 1.0)));
    M[13] = T(-(15000.0*z - 1.0)/((z*z*z)*(3125.0*z - 1.0)));
    M[14] = T(-(45000.0*z - 7.0)/((z*z)*(3125.0*z - 1.0)));
    M[15] = T(-(25000.0*z - 6.0)/(z*(3125.0*z - 1.0)));
}
template<typename T>
static void compute_Mp(T z, T *Mp) {
    Mp[0] = T(0.0);
    Mp[1] = T(0.0);
    Mp[2] = T(0.0);
    Mp[3] = T(0.0);
    Mp[4] = T(0.0);
    Mp[5] = T(0.0);
    Mp[6] = T(0.0);
    Mp[7] = T(0.0);
    Mp[8] = T(0.0);
    Mp[9] = T(0.0);
    Mp[10] = T(0.0);
    Mp[11] = T(0.0);
    Mp[12] = T(375000.0/((z*z*z)*pow(3125.0*z - 1.0, 2.0)) + 360.0/((z*z*z*z)*(3125.0*z - 1.0)));
    Mp[13] = T(-15000.0/((z*z*z)*(3125.0*z - 1.0)) + 3125.0*(15000.0*z - 1.0)/((z*z*z)*pow(3125.0*z - 1.0, 2.0)) + 3.0*(15000.0*z - 1.0)/((z*z*z*z)*(3125.0*z - 1.0)));
    Mp[14] = T(-45000.0/((z*z)*(3125.0*z - 1.0)) + 3125.0*(45000.0*z - 7.0)/((z*z)*pow(3125.0*z - 1.0, 2.0)) + 2.0*(45000.0*z - 7.0)/((z*z*z)*(3125.0*z - 1.0)));
    Mp[15] = T(-25000.0/(z*(3125.0*z - 1.0)) + 3125.0*(25000.0*z - 6.0)/(z*pow(3125.0*z - 1.0, 2.0)) + (25000.0*z - 6.0)/((z*z)*(3125.0*z - 1.0)));
}
// Mpp only needed for Theorem 1's R; double-only version is enough
static void compute_Mpp(double z, double *Mpp) {
    Mpp[0] = 0.0;
    Mpp[1] = 0.0;
    Mpp[2] = 0.0;
    Mpp[3] = 0.0;
    Mpp[4] = 0.0;
    Mpp[5] = 0.0;
    Mpp[6] = 0.0;
    Mpp[7] = 0.0;
    Mpp[8] = 0.0;
    Mpp[9] = 0.0;
    Mpp[10] = 0.0;
    Mpp[11] = 0.0;
    Mpp[12] = -240.0*(9765625.0/pow(3125.0*z - 1.0, 2.0) + 9375.0/(z*(3125.0*z - 1.0)) + 6.0/(z*z))/((z*z*z)*(3125.0*z - 1.0));
    Mpp[13] = 2.0*(46875000.0/(3125.0*z - 1.0) - 9765625.0*(15000.0*z - 1.0)/pow(3125.0*z - 1.0, 2.0) + 45000.0/z - 9375.0*(15000.0*z - 1.0)/(z*(3125.0*z - 1.0)) - 6.0*(15000.0*z - 1.0)/(z*z))/((z*z*z)*(3125.0*z - 1.0));
    Mpp[14] = 2.0*(140625000.0/(3125.0*z - 1.0) - 9765625.0*(45000.0*z - 7.0)/pow(3125.0*z - 1.0, 2.0) + 90000.0/z - 6250.0*(45000.0*z - 7.0)/(z*(3125.0*z - 1.0)) - 3.0*(45000.0*z - 7.0)/(z*z))/((z*z)*(3125.0*z - 1.0));
    Mpp[15] = 4.0*(39062500.0/(3125.0*z - 1.0) - 9765625.0*(12500.0*z - 3.0)/pow(3125.0*z - 1.0, 2.0) + 12500.0/z - 3125.0*(12500.0*z - 3.0)/(z*(3125.0*z - 1.0)) - (12500.0*z - 3.0)/(z*z))/(z*(3125.0*z - 1.0));
}

struct period_quintic_result_t {
    double tr_commQ, tr_commQ2, tr_commQ3, tr_commQ4;
    double thm1_resid[16], thm1_resid_max, R_norm_inf;
    int ok_traceless, ok_tr3_zero, ok_theorem1;
};

extern "C" void period_quintic_audit(double z, double tol, period_quintic_result_t *out) {
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

// f2 and f4 via matrix expression in complex<double>
template<typename T>
static T evaluate_f2(T z) {
    T M[16], Mp[16];
    compute_M(z, M); compute_Mp(z, Mp);
    T MM[16], tmp[16], Q[16];
    m4_mul(M, M, MM); m4_add(Mp, MM, tmp); m4_neg(tmp, Q);
    T UQ[16], QU[16], cQ[16], cQ2[16];
    m4_mul(M, Q, UQ); m4_mul(Q, M, QU); m4_sub(UQ, QU, cQ);
    m4_mul(cQ, cQ, cQ2);
    return m4_trace(cQ2);
}
template<typename T>
static T evaluate_f4(T z) {
    T M[16], Mp[16];
    compute_M(z, M); compute_Mp(z, Mp);
    T MM[16], tmp[16], Q[16];
    m4_mul(M, M, MM); m4_add(Mp, MM, tmp); m4_neg(tmp, Q);
    T UQ[16], QU[16], cQ[16], cQ2[16], cQ4[16];
    m4_mul(M, Q, UQ); m4_mul(Q, M, QU); m4_sub(UQ, QU, cQ);
    m4_mul(cQ, cQ, cQ2); m4_mul(cQ2, cQ2, cQ4);
    return m4_trace(cQ4);
}

extern "C" double period_quintic_f2_at(double z) {
    return evaluate_f2<double>(z);
}
extern "C" double period_quintic_f4_at(double z) {
    return evaluate_f4<double>(z);
}
extern "C" int period_quintic_version(void) { return 51; }
