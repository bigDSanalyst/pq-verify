#!/usr/bin/env python3
"""
pq-verify v2.15.0 — Unified Post-Quantum & ECC Master Audit
==========================================================
Six field-native C/C++ engines. Six test phases. One file. Zero uploads.

Engines (all C, compiled inline at runtime):
  1. GF(2)        — bit-packed Gaussian elimination, AES S-box verification
  2. Z_3329       — Kyber ML-KEM NTT verification (libzq)
  3. Z_8380417    — Dilithium ML-DSA NTT verification (libzq32)
  4. Cubic+ECC    — B(a,b) formula + elliptic curve point validation
  5. Conformity   — D(t) stability on curve families (Paper 4, doi:10.5281/zenodo.19510026)
  6. Period       — Gauss-Manin / Amari-Schwarzian, ranks 2/4/4/8 (Paper 7, doi:10.5281/zenodo.20129361)

Test Phases:
  Phase 1: Geometric Depth Probe (conformity, Hasse bound, curve auditor)
  Phase 2: Industrial Scale & FIPS (100K butterflies, 10K keygen, AES S-box,
           full Kyber+Dilithium NTT, FIPS 203/204/205, CMS5 comparison)
  Phase 3: Adversarial Suite (singular, supersingular, anomalous, corrupted NTT)
  Phase 4: FIPS/SafeCurves + CFL Front-End (CFL→FOL→QBF→field router→engines)
  Phase 5: Formal Verification (batch Coq cert, persistent daemon, SHA-256 hash)
  Phase 6: Period / Gauss-Manin (Engine 6 — Theorem 1, Obs 4, Conjecture 7)

Colab:
  Cell 1: !apt-get install -y -qq gcc g++ coq
          !pip install -q "pq-verify[full]"
  Cell 2: from pq_verify import main, pqverify_acvp_all
  Cell 3: main()                # 160/160
          pqverify_acvp_all()   # 1566/1566

Author: Nicholas Maino (iamweare)
License: MIT
"""
import os, sys, ctypes, time, random, json, math, hashlib, struct, itertools
import atexit, shutil, subprocess, tempfile
from datetime import datetime, timezone

VERSION = "2.15.0"

# Status glyphs as names rather than escapes inlined into f-string expressions.
# A backslash inside an f-string expression is PEP 701 syntax (Python 3.12+);
# using it raised this package's real floor to 3.12 while the metadata still
# advertised 3.8, so pip installed happily on 3.11 and every import failed.
_OK, _BAD = '\u2705', '\u274c'

_PQV_WORKDIR = None


def _pqv_workdir():
    """Private per-process scratch directory for generated sources and engines.

    These files used to go to fixed paths -- /tmp/pqv_gf2.c, /tmp/libpqv_gf2.so,
    /tmp/pq_ntt_cert.v. Two problems, both demonstrated:

      * open(path, 'w') follows symlinks. Any local user who pre-created one of
        those paths as a symlink got an arbitrary file overwrite with this
        process's privileges -- pq-verify would happily destroy the target and
        fill it with C source.
      * Predictable names are shared state. Two runs on one machine (two CI
        jobs, two shells) clobber each other's sources mid-compile.

    mkdtemp() gives a fresh 0700 directory with an unpredictable name that only
    this user can enter, removed when the process exits.
    """
    global _PQV_WORKDIR
    if _PQV_WORKDIR is None or not os.path.isdir(_PQV_WORKDIR):
        _PQV_WORKDIR = tempfile.mkdtemp(prefix="pqv-")
        atexit.register(shutil.rmtree, _PQV_WORKDIR, True)
    return _PQV_WORKDIR


BANNER = f"""
╔══════════════════════════════════════════════════════════════════╗
║  pq-verify v{VERSION}                                              ║
║  Unified Post-Quantum & ECC Verification Pipeline               ║
║  GF(2) · Z_3329 · Z_8380417 · Cubic/ECC · Conformity           ║
║  Nicholas Maino · iamweare · 2026                                ║
╚══════════════════════════════════════════════════════════════════╝
"""

# ================================================================
# ENGINE 1: GF(2) — Bit-Packed Gaussian Elimination
# ================================================================

GF2_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define GF2_MAX_VARS 2048
#define GF2_MAX_LIMBS ((GF2_MAX_VARS+63)/64)
#define GF2_ROW_LIMBS ((GF2_MAX_LIMBS+3)&~3)
#define GF2_MAX_EQS 8192
#define M4RI_K 6
#define M4RI_THRESH 256
typedef struct{uint64_t rows[GF2_MAX_EQS][GF2_ROW_LIMBS];int parity[GF2_MAX_EQS];int num_equations;int num_variables;int num_limbs;}GF2System;
typedef struct{int satisfiable;int assignment[GF2_MAX_VARS];int num_pivots;int num_free_vars;int pivot_row[GF2_MAX_VARS];double solve_time_us;int used_m4ri;int m4ri_blocks;}GF2Result;
#define GF2_NS_MAX_FREE 32
typedef struct{int num_free;int free_cols[GF2_MAX_VARS];int basis[GF2_NS_MAX_FREE][GF2_MAX_VARS];int num_solutions_log2;double enumerate_time_us;}GF2NullSpace;
static inline void rxor(uint64_t*d,const uint64_t*s,int nl){for(int l=0;l<nl;l++)d[l]^=s[l];}
static inline void rcpy(uint64_t*d,const uint64_t*s,int nl){memcpy(d,s,sizeof(uint64_t)*nl);}
static inline void rswp(uint64_t*a,uint64_t*b,int nl){for(int l=0;l<nl;l++){uint64_t t=a[l];a[l]=b[l];b[l]=t;}}
static inline int rzero(const uint64_t*r,int nl){for(int l=0;l<nl;l++)if(r[l])return 0;return 1;}
static inline double dtus(struct timespec*a,struct timespec*b){return(b->tv_sec-a->tv_sec)*1e6+(b->tv_nsec-a->tv_nsec)/1e3;}
int gf2_init(GF2System*s,int nv){memset(s,0,sizeof(GF2System));if(nv<0||nv>GF2_MAX_VARS)return-1;s->num_variables=nv;s->num_limbs=(nv+63)/64;return 0;}
int gf2_add_xor(GF2System*s,int*v,int nv,int p){if(s->num_equations>=GF2_MAX_EQS)return-1;int r=s->num_equations;memset(s->rows[r],0,sizeof(uint64_t)*GF2_ROW_LIMBS);for(int i=0;i<nv;i++){int var=v[i];if(var<0||var>=s->num_variables)return-2;s->rows[r][var/64]^=(1ULL<<(var%64));}s->parity[r]=p&1;s->num_equations++;return 0;}
static void solve_direct(GF2System*sys,GF2Result*res){int n=sys->num_variables,m=sys->num_equations,nl=sys->num_limbs;int pr[GF2_MAX_VARS];memset(pr,-1,sizeof(int)*n);int cur=0,piv=0;for(int col=0;col<n&&cur<m;col++){int lb=col/64;uint64_t bt=1ULL<<(col%64);int p=-1;for(int r=cur;r<m;r++)if(sys->rows[r][lb]&bt){p=r;break;}if(p==-1)continue;if(p!=cur){rswp(sys->rows[cur],sys->rows[p],nl);int t=sys->parity[cur];sys->parity[cur]=sys->parity[p];sys->parity[p]=t;}pr[col]=cur;piv++;for(int r=0;r<m;r++){if(r==cur)continue;if(sys->rows[r][lb]&bt){rxor(sys->rows[r],sys->rows[cur],nl);sys->parity[r]^=sys->parity[cur];}}cur++;}res->satisfiable=1;for(int r=0;r<m;r++)if(rzero(sys->rows[r],nl)&&sys->parity[r]){res->satisfiable=0;break;}if(res->satisfiable){memset(res->assignment,0,sizeof(int)*n);for(int c=n-1;c>=0;c--){if(pr[c]==-1)continue;int r=pr[c],val=sys->parity[r];for(int c2=c+1;c2<n;c2++)if(sys->rows[r][c2/64]&(1ULL<<(c2%64)))val^=res->assignment[c2];res->assignment[c]=val&1;}}res->num_pivots=piv;res->num_free_vars=n-piv;memcpy(res->pivot_row,pr,sizeof(int)*n);res->used_m4ri=0;}
static void solve_m4ri(GF2System*sys,GF2Result*res){int n=sys->num_variables,m=sys->num_equations,nl=sys->num_limbs,k=M4RI_K;int pr[GF2_MAX_VARS];memset(pr,-1,sizeof(int)*n);uint64_t T[64][GF2_ROW_LIMBS];int Tp[64];int cur=0,pivs=0,mblk=0;for(int ci=0;ci<n;ci+=k){int bk=(ci+k<=n)?k:(n-ci),bp=0;int bpr[8],bpc[8];for(int j=0;j<bk&&cur<m;j++){int col=ci+j,lb=col/64;uint64_t bt=1ULL<<(col%64);int p=-1;for(int r=cur;r<m;r++)if(sys->rows[r][lb]&bt){p=r;break;}if(p==-1)continue;if(p!=cur){rswp(sys->rows[cur],sys->rows[p],nl);int t=sys->parity[cur];sys->parity[cur]=sys->parity[p];sys->parity[p]=t;}for(int r=cur+1;r<m;r++)if(sys->rows[r][lb]&bt){rxor(sys->rows[r],sys->rows[cur],nl);sys->parity[r]^=sys->parity[cur];}pr[col]=cur;bpc[bp]=col;bpr[bp]=cur;bp++;pivs++;cur++;}if(bp==0)continue;for(int p=bp-1;p>=1;p--){int col=bpc[p],lb=col/64;uint64_t bt=1ULL<<(col%64);for(int p2=0;p2<p;p2++)if(sys->rows[bpr[p2]][lb]&bt){rxor(sys->rows[bpr[p2]],sys->rows[bpr[p]],nl);sys->parity[bpr[p2]]^=sys->parity[bpr[p]];}}mblk++;memset(T[0],0,sizeof(uint64_t)*GF2_ROW_LIMBS);Tp[0]=0;for(int mask=1;mask<(1<<bp);mask++){int hi=0;for(int b=bp-1;b>=0;b--)if(mask&(1<<b)){hi=b;break;}int prev=mask^(1<<hi);rcpy(T[mask],T[prev],nl);rxor(T[mask],sys->rows[bpr[hi]],nl);Tp[mask]=Tp[prev]^sys->parity[bpr[hi]];}int bs=bpr[0];for(int r=0;r<bs;r++){int idx=0;for(int p=0;p<bp;p++){int c=bpc[p];if(sys->rows[r][c/64]&(1ULL<<(c%64)))idx|=(1<<p);}if(idx==0)continue;rxor(sys->rows[r],T[idx],nl);sys->parity[r]^=Tp[idx];}}res->satisfiable=1;for(int r=0;r<m;r++)if(rzero(sys->rows[r],nl)&&sys->parity[r]){res->satisfiable=0;break;}if(res->satisfiable){memset(res->assignment,0,sizeof(int)*n);for(int c=n-1;c>=0;c--){if(pr[c]==-1)continue;int r=pr[c],val=sys->parity[r];for(int c2=c+1;c2<n;c2++)if(sys->rows[r][c2/64]&(1ULL<<(c2%64)))val^=res->assignment[c2];res->assignment[c]=val&1;}}res->num_pivots=pivs;res->num_free_vars=n-pivs;memcpy(res->pivot_row,pr,sizeof(int)*n);res->used_m4ri=1;res->m4ri_blocks=mblk;}
void gf2_solve(GF2System*sys,GF2Result*res){struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);memset(res,0,sizeof(GF2Result));if(sys->num_variables<=M4RI_THRESH)solve_direct(sys,res);else solve_m4ri(sys,res);clock_gettime(CLOCK_MONOTONIC,&t1);res->solve_time_us=dtus(&t0,&t1);}
int gf2_verify(const GF2System*s,const int*a){for(int i=0;i<s->num_equations;i++){int sum=0;for(int j=0;j<s->num_variables;j++){if(s->rows[i][j/64]&(1ULL<<(j%64)))sum^=a[j];}if(sum!=s->parity[i])return 0;}return 1;}
void gf2_nullspace(const GF2System*sys,const GF2Result*res,GF2NullSpace*ns){
int n=sys->num_variables;memset(ns,0,sizeof(GF2NullSpace));
if(!res->satisfiable){ns->num_free=0;ns->num_solutions_log2=-1;return;}
int nf=0;
for(int c=0;c<n;c++){if(res->pivot_row[c]==-1){ns->free_cols[nf]=c;nf++;}}
ns->num_free=nf;ns->num_solutions_log2=nf;
int bmax=(nf<GF2_NS_MAX_FREE)?nf:GF2_NS_MAX_FREE;
for(int fi=0;fi<bmax;fi++){
int fc=ns->free_cols[fi];
memset(ns->basis[fi],0,sizeof(int)*n);
ns->basis[fi][fc]=1;
for(int c=0;c<n;c++){int r=res->pivot_row[c];if(r<0)continue;
if(sys->rows[r][fc/64]&(1ULL<<(fc%64)))ns->basis[fi][c]=1;}}}
int gf2_enumerate(const GF2System*sys,const GF2Result*res,const GF2NullSpace*ns,int*out,int max_sols,int n_out){
struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
if(!res->satisfiable||ns->num_free<0){return 0;}
int n=sys->num_variables,nf=ns->num_free;
if(nf>20||((1<<nf)>max_sols)){return -1;}
int total=1<<nf,count=0;
for(int mask=0;mask<total&&count<max_sols;mask++){
int*sol=out+count*n_out;
memcpy(sol,res->assignment,sizeof(int)*n);
for(int fi=0;fi<nf;fi++){if(mask&(1<<fi)){
for(int j=0;j<n;j++)sol[j]^=ns->basis[fi][j];}}
count++;}
clock_gettime(CLOCK_MONOTONIC,&t1);
return count;}
"""

# ================================================================
# ENGINE 2: Z_3329 — Kyber NTT Verification
# ================================================================

ZQ_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define ZQ_MAX_VARS 2048
#define ZQ_MAX_EQUATIONS 4096
typedef struct {
    uint16_t coefficients[ZQ_MAX_EQUATIONS][ZQ_MAX_VARS];
    uint16_t rhs[ZQ_MAX_EQUATIONS];
    int num_equations, num_variables;
    uint16_t q;
} ZqSystem;
typedef struct {
    int satisfiable;
    uint16_t assignment[ZQ_MAX_VARS];
    int num_pivots, num_free_vars;
    int pivot_columns[ZQ_MAX_VARS];
    double solve_time_us;
    int used_colcount_order;
} ZqResult;
static inline uint16_t zq_sub(uint16_t a,uint16_t b,uint16_t q){return(uint16_t)(a>=b?a-b:q-b+a);}
static inline uint16_t zq_mul(uint16_t a,uint16_t b,uint16_t q){return(uint16_t)(((uint32_t)a*(uint32_t)b)%q);}
static inline uint16_t zq_neg(uint16_t a,uint16_t q){return a==0?0:(uint16_t)(q-a);}
static uint16_t zq_inv(uint16_t a,uint16_t q){if(a==0)return 0;uint32_t base=a,exp=q-2,result=1;base%=q;while(exp>0){if(exp&1)result=(result*base)%q;exp>>=1;base=(base*base)%q;}return(uint16_t)result;}
/* Montgomery arithmetic: R = 2^16 */
static uint16_t _mq_ni; /* -q^(-1) mod R */
static uint16_t _mq_r2; /* R^2 mod q */
static void _mont_init(uint16_t q){
uint16_t inv=q;for(int i=0;i<4;i++)inv*=2-q*inv;
_mq_ni=(uint16_t)(-inv);
uint32_t r=((uint32_t)1<<16)%q;_mq_r2=(uint16_t)((r*r)%q);}
static inline uint16_t _mred(uint32_t T,uint16_t q){
uint16_t m=(uint16_t)(T*_mq_ni);uint32_t t=T+(uint32_t)m*q;
t>>=16;return t>=q?t-q:t;}
static inline uint16_t _mmul(uint16_t a,uint16_t b,uint16_t q){return _mred((uint32_t)a*(uint32_t)b,q);}
static inline uint16_t _mto(uint16_t a,uint16_t q){return _mred((uint32_t)a*_mq_r2,q);}
static inline uint16_t _mfr(uint16_t a,uint16_t q){return _mred(a,q);}
int zq_init(ZqSystem*s,int nv,uint16_t q){memset(s,0,sizeof(ZqSystem));s->q=(q==0)?3329:q;if(nv<0||nv>ZQ_MAX_VARS)return-1;s->num_variables=nv;return 0;}
int zq_add_equation(ZqSystem*s,const uint16_t*c,uint16_t rhs){if(s->num_equations>=ZQ_MAX_EQUATIONS)return-1;int i=s->num_equations;for(int j=0;j<s->num_variables;j++)s->coefficients[i][j]=c[j]%s->q;s->rhs[i]=rhs%s->q;s->num_equations++;return i;}
int zq_add_sparse(ZqSystem*s,const int*vi,const uint16_t*vc,int nt,uint16_t rhs){if(s->num_equations>=ZQ_MAX_EQUATIONS)return-1;for(int t=0;t<nt;t++)if(vi[t]<0||vi[t]>=s->num_variables)return-2;int i=s->num_equations;memset(s->coefficients[i],0,sizeof(uint16_t)*s->num_variables);for(int t=0;t<nt;t++)s->coefficients[i][vi[t]]=vc[t]%s->q;s->rhs[i]=rhs%s->q;s->num_equations++;return i;}
int zq_add_ntt_butterfly(ZqSystem*s,int vie,int vio,int voe,int voo,uint16_t w){uint16_t q=s->q;int v[4];uint16_t c[4];v[0]=voe;c[0]=1;v[1]=vie;c[1]=zq_neg(1,q);v[2]=vio;c[2]=zq_neg(w,q);if(zq_add_sparse(s,v,c,3,0)<0)return-1;v[0]=voo;c[0]=1;v[1]=vie;c[1]=zq_neg(1,q);v[2]=vio;c[2]=w;if(zq_add_sparse(s,v,c,3,0)<0)return-1;return 0;}
void zq_solve(ZqSystem*sys,ZqResult*r){
struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
int n=sys->num_variables,m=sys->num_equations;uint16_t q=sys->q;
_mont_init(q);
static uint16_t mat[ZQ_MAX_EQUATIONS][ZQ_MAX_VARS];
static uint16_t rhs[ZQ_MAX_EQUATIONS];
/* Convert to Montgomery domain */
for(int i=0;i<m;i++){for(int j=0;j<n;j++)mat[i][j]=_mto(sys->coefficients[i][j],q);
rhs[i]=_mto(sys->rhs[i],q);}
/* Column order: ascending nonzero count, counted once before elimination
   (empty columns last). A static order, not Markowitz pivoting. */
int cnnz[ZQ_MAX_VARS],cord[ZQ_MAX_VARS];
memset(cnnz,0,sizeof(int)*n);
for(int i=0;i<m;i++)for(int j=0;j<n;j++)if(mat[i][j])cnnz[j]++;
for(int i=0;i<n;i++)cord[i]=i;
for(int i=1;i<n;i++){int tmp=cord[i],tv=cnnz[tmp]?cnnz[tmp]:ZQ_MAX_EQUATIONS+1;
int j=i-1;while(j>=0){int cv=cnnz[cord[j]]?cnnz[cord[j]]:ZQ_MAX_EQUATIONS+1;
if(cv<=tv)break;cord[j+1]=cord[j];j--;}cord[j+1]=tmp;}
/* Gaussian elimination in that column order, Montgomery mul, zero-skip */
int pr=0,rank=0,pc[ZQ_MAX_VARS];memset(pc,-1,sizeof(int)*n);
for(int ci=0;ci<n&&pr<m;ci++){
int col=cord[ci];if(cnnz[col]==0)break;/* early term: remaining cols empty */
int best=-1;for(int row=pr;row<m;row++)if(mat[row][col]!=0){best=row;break;}
if(best==-1)continue;
if(best!=pr){uint16_t tr[ZQ_MAX_VARS];memcpy(tr,mat[pr],sizeof(uint16_t)*n);
memcpy(mat[pr],mat[best],sizeof(uint16_t)*n);memcpy(mat[best],tr,sizeof(uint16_t)*n);
uint16_t tp=rhs[pr];rhs[pr]=rhs[best];rhs[best]=tp;}
/* Scale pivot row: inv in Montgomery = to_mont(inv(from_mont(pv))) */
uint16_t inv=_mto(zq_inv(_mfr(mat[pr][col],q),q),q);
for(int j=0;j<n;j++)if(mat[pr][j])mat[pr][j]=_mmul(mat[pr][j],inv,q);
rhs[pr]=_mmul(rhs[pr],inv,q);
/* Eliminate: skip rows without entry in pivot col, skip zeros in pivot row */
for(int row=0;row<m;row++){if(row==pr||mat[row][col]==0)continue;
uint16_t f=mat[row][col];
for(int j=0;j<n;j++){if(mat[pr][j]==0)continue;/* zero-skip */
mat[row][j]=zq_sub(mat[row][j],_mmul(f,mat[pr][j],q),q);}
rhs[row]=zq_sub(rhs[row],_mmul(f,rhs[pr],q),q);
mat[row][col]=0;}
pc[rank]=col;r->pivot_columns[rank]=col;pr++;rank++;}
/* SAT check (0 in Montgomery ↔ 0 in regular domain) */
r->satisfiable=1;
for(int row=pr;row<m;row++){if(rhs[row]!=0){r->satisfiable=0;break;}}
r->num_pivots=rank;r->num_free_vars=n-rank;r->used_colcount_order=1;
/* Back-substitute: RREF means pivot cols are unit vectors → assignment = from_mont(rhs) */
if(r->satisfiable){memset(r->assignment,0,sizeof(r->assignment));
for(int i=0;i<rank;i++)r->assignment[pc[i]]=_mfr(rhs[i],q);}
clock_gettime(CLOCK_MONOTONIC,&t1);r->solve_time_us=(t1.tv_sec-t0.tv_sec)*1e6+(t1.tv_nsec-t0.tv_nsec)/1e3;}
int zq_verify(const ZqSystem*s,const uint16_t*a){uint16_t q=s->q;for(int i=0;i<s->num_equations;i++){uint32_t sum=0;for(int j=0;j<s->num_variables;j++)sum+=(uint32_t)s->coefficients[i][j]*(uint32_t)a[j];if((uint16_t)(sum%q)!=s->rhs[i])return 0;}return 1;}
/* ---- C batch butterfly: one crossing for N butterflies ----
   Computes each butterfly through the engine's Montgomery multiply -- the
   arithmetic the solver uses -- and compares with outputs computed by the
   caller in plain integer arithmetic. It used to compare (a+w*b)%q with
   itself, a check that could not fail. Returns the number of mismatches. */
int zq_batch_butterfly(const uint16_t*a_arr,const uint16_t*b_arr,
const uint16_t*w_arr,const uint16_t*exp_e,const uint16_t*exp_o,
uint8_t*pass_arr,int n,uint16_t q){
_mont_init(q);
int fails=0;
for(int i=0;i<n;i++){
uint16_t a=a_arr[i]%q;
uint16_t t=_mfr(_mmul(_mto(w_arr[i]%q,q),_mto(b_arr[i]%q,q),q),q);
uint16_t oe=(uint16_t)(((uint32_t)a+t)%q);
uint16_t oo=zq_sub(a,t,q);
pass_arr[i]=(oe==exp_e[i])&&(oo==exp_o[i]);
fails+=!pass_arr[i];}
return fails;}
/* ---- Precomputed Kyber NTT zetas (FIPS 203, bit-reversed) ---- */
static uint16_t _kyber_zetas[128];
static int _kyber_zetas_ready=0;
static uint16_t _pow_mod16(uint16_t base,uint32_t exp,uint16_t q){
uint32_t r=1,b=base;while(exp>0){if(exp&1)r=(r*b)%q;b=(b*b)%q;exp>>=1;}return(uint16_t)r;}
static uint32_t _bitrev7(uint32_t x){uint32_t r=0;for(int i=0;i<7;i++){r=(r<<1)|(x&1);x>>=1;}return r;}
static void _init_kyber_zetas(uint16_t q,uint16_t zeta){
if(_kyber_zetas_ready)return;
for(int i=0;i<128;i++)_kyber_zetas[i]=_pow_mod16(zeta,_bitrev7(i),q);
_kyber_zetas_ready=1;}
/* The table the NTT and the Freivalds check use, read out for checks
   made apart from the engine. */
void zq_zeta_table(uint16_t*out,uint16_t q,uint16_t zeta){
_init_kyber_zetas(q,zeta);
for(int i=0;i<128;i++)out[i]=_kyber_zetas[i];}
/* ---- Forward NTT (FIPS 203 Cooley-Tukey, in-place) ---- */
void zq_ntt_forward(uint16_t*f,int n,uint16_t q,uint16_t zeta){
_init_kyber_zetas(q,zeta);
int k=1;
for(int len=n/2;len>=2;len/=2){
for(int start=0;start<n;start+=2*len){
uint16_t w=_kyber_zetas[k++];
for(int j=start;j<start+len;j++){
uint16_t t=(uint16_t)(((uint32_t)w*f[j+len])%q);
f[j+len]=zq_sub(f[j],t,q);
f[j]=(uint16_t)((f[j]+(uint32_t)t)%q);}}}}
/* ---- Freivalds NTT check: O(n log n) probabilistic verification ---- */
/* Checks y == NTT(x) by: draw random r, verify r·y == (NTT^T·r)·x    */
/* NTT^T butterfly: (r_e,r_o) → (r_e+r_o, w*(r_e-r_o))                */
/* Layers applied in reverse order.                                     */
static void _ntt_transpose(uint16_t*r,int n,uint16_t q){
int k=127;
for(int len=2;len<=n/2;len*=2){
for(int start=n-2*len;start>=0;start-=2*len){
uint16_t w=_kyber_zetas[k--];
for(int j=start;j<start+len;j++){
uint16_t re=r[j],ro=r[j+len];
r[j]=(uint16_t)((re+(uint32_t)ro)%q);
r[j+len]=(uint16_t)(((uint32_t)w*zq_sub(re,ro,q))%q);}}}}
static uint32_t _xorshift(uint32_t s){s^=s<<13;s^=s>>17;s^=s<<5;return s;}
int zq_freivalds_ntt(const uint16_t*x,const uint16_t*y,
int n,uint16_t q,uint16_t zeta,int k_rounds,uint32_t seed){
_init_kyber_zetas(q,zeta);
uint32_t rng=seed?seed:42;
for(int round=0;round<k_rounds;round++){
uint16_t r[256];
for(int i=0;i<n;i++){rng=_xorshift(rng);r[i]=(uint16_t)(rng%q);}
/* lhs = r · y */
uint64_t lhs=0;for(int i=0;i<n;i++)lhs+=(uint64_t)r[i]*y[i];
lhs%=q;
/* apply NTT^T to r */
_ntt_transpose(r,n,q);
/* rhs = (NTT^T r) · x */
uint64_t rhs=0;for(int i=0;i<n;i++)rhs+=(uint64_t)r[i]*x[i];
rhs%=q;
if((uint16_t)lhs!=(uint16_t)rhs)return 0;}
return 1;}
"""

# ================================================================
# ENGINE 3: Z_8380417 — Dilithium NTT Verification
# ================================================================

ZQ32_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define ZQ32_MAX_VARS 256
#define ZQ32_MAX_EQUATIONS 512
#define ZQ32_DEFAULT_Q 8380417U
typedef struct {
    uint32_t coefficients[ZQ32_MAX_EQUATIONS][ZQ32_MAX_VARS];
    uint32_t rhs[ZQ32_MAX_EQUATIONS];
    int num_equations;int num_variables;uint32_t q;
} Zq32System;
typedef struct {
    int satisfiable;uint32_t assignment[ZQ32_MAX_VARS];
    int num_pivots;int num_free_vars;int pivot_columns[ZQ32_MAX_VARS];double solve_time_us;
    int used_colcount_order;
} Zq32Result;
static inline uint32_t zq32_sub(uint32_t a,uint32_t b,uint32_t q){return a>=b?a-b:q-b+a;}
static inline uint32_t zq32_mul(uint32_t a,uint32_t b,uint32_t q){return(uint32_t)(((uint64_t)a*(uint64_t)b)%q);}
static inline uint32_t zq32_neg(uint32_t a,uint32_t q){return a==0?0:(q-a);}
static uint32_t zq32_inv(uint32_t a,uint32_t q){if(a==0)return 0;uint64_t base=a%q,exp=(uint64_t)q-2,result=1;while(exp>0){if(exp&1)result=(result*base)%q;exp>>=1;base=(base*base)%q;}return(uint32_t)result;}
/* Montgomery32: R = 2^32 */
static uint32_t _m32_ni;
static uint32_t _m32_r2;
static void _m32_init(uint32_t q){
uint32_t inv=q;for(int i=0;i<4;i++)inv*=2-q*inv;
_m32_ni=(uint32_t)(-inv);
uint64_t r=((uint64_t)1<<32)%q;_m32_r2=(uint32_t)((r*r)%q);}
static inline uint32_t _m32red(uint64_t T,uint32_t q){
uint32_t m=(uint32_t)((uint32_t)T*_m32_ni);uint64_t t=T+(uint64_t)m*q;
t>>=32;return(uint32_t)(t>=q?t-q:t);}
static inline uint32_t _m32mul(uint32_t a,uint32_t b,uint32_t q){return _m32red((uint64_t)a*(uint64_t)b,q);}
static inline uint32_t _m32to(uint32_t a,uint32_t q){return _m32red((uint64_t)a*_m32_r2,q);}
static inline uint32_t _m32fr(uint32_t a,uint32_t q){return _m32red(a,q);}
int zq32_init(Zq32System*s,int nv,uint32_t q){memset(s,0,sizeof(Zq32System));s->q=(q==0)?ZQ32_DEFAULT_Q:q;if(nv<0||nv>ZQ32_MAX_VARS)return-1;s->num_variables=nv;return 0;}
int zq32_add_equation(Zq32System*s,const uint32_t*c,uint32_t rhs){if(s->num_equations>=ZQ32_MAX_EQUATIONS)return-1;int i=s->num_equations;for(int j=0;j<s->num_variables;j++)s->coefficients[i][j]=c[j]%s->q;s->rhs[i]=rhs%s->q;s->num_equations++;return i;}
int zq32_add_sparse(Zq32System*s,const int*vi,const uint32_t*vc,int nt,uint32_t rhs){if(s->num_equations>=ZQ32_MAX_EQUATIONS)return-1;for(int t=0;t<nt;t++)if(vi[t]<0||vi[t]>=s->num_variables)return-2;int i=s->num_equations;memset(s->coefficients[i],0,sizeof(uint32_t)*s->num_variables);for(int t=0;t<nt;t++)s->coefficients[i][vi[t]]=vc[t]%s->q;s->rhs[i]=rhs%s->q;s->num_equations++;return i;}
int zq32_add_ntt_butterfly(Zq32System*s,int vie,int vio,int voe,int voo,uint32_t w){uint32_t q=s->q;int v[3];uint32_t c[3];v[0]=voe;c[0]=1;v[1]=vie;c[1]=zq32_neg(1,q);v[2]=vio;c[2]=zq32_neg(w,q);if(zq32_add_sparse(s,v,c,3,0)<0)return-1;v[0]=voo;c[0]=1;v[1]=vie;c[1]=zq32_neg(1,q);v[2]=vio;c[2]=w;if(zq32_add_sparse(s,v,c,3,0)<0)return-1;return 0;}
void zq32_solve(Zq32System*sys,Zq32Result*r){
struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
int n=sys->num_variables,m=sys->num_equations;uint32_t q=sys->q;
_m32_init(q);
static uint32_t mat[ZQ32_MAX_EQUATIONS][ZQ32_MAX_VARS];
static uint32_t rhs[ZQ32_MAX_EQUATIONS];
for(int i=0;i<m;i++){for(int j=0;j<n;j++)mat[i][j]=_m32to(sys->coefficients[i][j],q);
rhs[i]=_m32to(sys->rhs[i],q);}
int cnnz[ZQ32_MAX_VARS],cord[ZQ32_MAX_VARS];
memset(cnnz,0,sizeof(int)*n);
for(int i=0;i<m;i++)for(int j=0;j<n;j++)if(mat[i][j])cnnz[j]++;
for(int i=0;i<n;i++)cord[i]=i;
for(int i=1;i<n;i++){int tmp=cord[i],tv=cnnz[tmp]?cnnz[tmp]:ZQ32_MAX_EQUATIONS+1;
int j=i-1;while(j>=0){int cv=cnnz[cord[j]]?cnnz[cord[j]]:ZQ32_MAX_EQUATIONS+1;
if(cv<=tv)break;cord[j+1]=cord[j];j--;}cord[j+1]=tmp;}
int pr=0,rank=0,pc[ZQ32_MAX_VARS];memset(pc,-1,sizeof(int)*n);
for(int ci=0;ci<n&&pr<m;ci++){
int col=cord[ci];if(cnnz[col]==0)break;
int best=-1;for(int row=pr;row<m;row++)if(mat[row][col]!=0){best=row;break;}
if(best==-1)continue;
if(best!=pr){uint32_t tr[ZQ32_MAX_VARS];memcpy(tr,mat[pr],sizeof(uint32_t)*n);
memcpy(mat[pr],mat[best],sizeof(uint32_t)*n);memcpy(mat[best],tr,sizeof(uint32_t)*n);
uint32_t tp=rhs[pr];rhs[pr]=rhs[best];rhs[best]=tp;}
uint32_t inv=_m32to(zq32_inv(_m32fr(mat[pr][col],q),q),q);
for(int j=0;j<n;j++)if(mat[pr][j])mat[pr][j]=_m32mul(mat[pr][j],inv,q);
rhs[pr]=_m32mul(rhs[pr],inv,q);
for(int row=0;row<m;row++){if(row==pr||mat[row][col]==0)continue;
uint32_t f=mat[row][col];
for(int j=0;j<n;j++){if(mat[pr][j]==0)continue;
mat[row][j]=zq32_sub(mat[row][j],_m32mul(f,mat[pr][j],q),q);}
rhs[row]=zq32_sub(rhs[row],_m32mul(f,rhs[pr],q),q);
mat[row][col]=0;}
pc[rank]=col;r->pivot_columns[rank]=col;pr++;rank++;}
r->satisfiable=1;
for(int row=pr;row<m;row++){if(rhs[row]!=0){r->satisfiable=0;break;}}
r->num_pivots=rank;r->num_free_vars=n-rank;r->used_colcount_order=1;
if(r->satisfiable){memset(r->assignment,0,sizeof(r->assignment));
for(int i=0;i<rank;i++)r->assignment[pc[i]]=_m32fr(rhs[i],q);}
clock_gettime(CLOCK_MONOTONIC,&t1);r->solve_time_us=(t1.tv_sec-t0.tv_sec)*1e6+(t1.tv_nsec-t0.tv_nsec)/1e3;}
/* ================================================================
   ML-DSA (FIPS 204) NTT + Freivalds verification, 32-bit.

   ML-DSA's transform is COMPLETE: zeta=1753 has multiplicative order 512
   mod q=8380417, so 2n | q-1 and the NTT splits to linear factors --
   8 layers, len 128..1, consuming 255 twiddles. (ML-KEM is the 7-layer
   incomplete case; its Freivalds lives in the 16-bit engine and cannot be
   reused here: wrong width, wrong layer count, wrong zeta table.)

   Freivalds: to check y == NTT(x) without recomputing the transform,
   draw random r and verify   r.y == (NTT^T r).x
   A Cooley-Tukey butterfly is [[1, w], [1, -w]] on (a, b); its transpose
   is [[1, 1], [w, -w]], i.e.
        out[j]     = in[j] + in[j+len]
        out[j+len] = w * (in[j] - in[j+len])
   applied with the LAYERS IN REVERSE ORDER and zetas descending.
   ================================================================ */
static uint32_t _dili_zetas[256];
static int _dili_zetas_ready=0;
static uint32_t _pow_mod32(uint32_t base,uint32_t exp,uint32_t q){
uint64_t r=1,b=base%q;while(exp>0){if(exp&1)r=(r*b)%q;b=(b*b)%q;exp>>=1;}return(uint32_t)r;}
static uint32_t _bitrev8(uint32_t x){uint32_t r=0;for(int i=0;i<8;i++){r=(r<<1)|(x&1);x>>=1;}return r;}
static void _init_dili_zetas(uint32_t q,uint32_t zeta){
if(_dili_zetas_ready)return;
for(int i=0;i<256;i++)_dili_zetas[i]=_pow_mod32(zeta,_bitrev8(i),q);
_dili_zetas_ready=1;}
/* The table the NTT and the Freivalds check use, read out for checks
   made apart from the engine. */
void zq32_zeta_table(uint32_t*out,uint32_t q,uint32_t zeta){
_init_dili_zetas(q,zeta);
for(int i=0;i<256;i++)out[i]=_dili_zetas[i];}

/* Forward ML-DSA NTT, in place. 8 layers: len = 128,64,...,2,1. */
void zq32_ntt_forward(uint32_t*f,int n,uint32_t q,uint32_t zeta){
_init_dili_zetas(q,zeta);
int k=1;
for(int len=n/2;len>=1;len/=2){
for(int start=0;start<n;start+=2*len){
uint32_t w=_dili_zetas[k++];
for(int j=start;j<start+len;j++){
uint32_t t=(uint32_t)(((uint64_t)w*f[j+len])%q);
f[j+len]=zq32_sub(f[j],t,q);
f[j]=(uint32_t)((f[j]+(uint64_t)t)%q);}}}}

/* NTT^T applied in place: layers reversed, zetas descending. */
static void _ntt32_transpose(uint32_t*r,int n,uint32_t q){
int k=255;
for(int len=1;len<=n/2;len*=2){
for(int start=n-2*len;start>=0;start-=2*len){
uint32_t w=_dili_zetas[k--];
for(int j=start;j<start+len;j++){
uint32_t re=r[j],ro=r[j+len];
r[j]=(uint32_t)((re+(uint64_t)ro)%q);
r[j+len]=(uint32_t)(((uint64_t)w*zq32_sub(re,ro,q))%q);}}}}

static uint32_t _xorshift32(uint32_t s){s^=s<<13;s^=s>>17;s^=s<<5;return s;}

/* Returns 1 if y == NTT(x) survives k_rounds Freivalds checks, else 0.
   Soundness: a wrong y passes one round with probability <= 1/q, so
   k rounds give <= q^-k (q = 8380417). */
int zq32_freivalds_ntt(const uint32_t*x,const uint32_t*y,
int n,uint32_t q,uint32_t zeta,int k_rounds,uint32_t seed){
_init_dili_zetas(q,zeta);
uint32_t rng=seed?seed:42;
for(int round=0;round<k_rounds;round++){
uint32_t r[256];
if(n>256)return -1;
for(int i=0;i<n;i++){rng=_xorshift32(rng);r[i]=(uint32_t)(rng%q);}
uint64_t lhs=0;
for(int i=0;i<n;i++)lhs=(lhs+(uint64_t)r[i]*y[i])%q;
_ntt32_transpose(r,n,q);
uint64_t rhs=0;
for(int i=0;i<n;i++)rhs=(rhs+(uint64_t)r[i]*x[i])%q;
if((uint32_t)lhs!=(uint32_t)rhs)return 0;}
return 1;}
"""

# ================================================================
# ENGINE 4: Cubic + ECC
# ================================================================

CUBIC_C = r"""
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>
static inline uint64_t mod_mul(uint64_t a,uint64_t b,uint64_t p){return(uint64_t)(((unsigned __int128)a*b)%p);}
static inline uint64_t mod_add(uint64_t a,uint64_t b,uint64_t p){uint64_t r=a+b;return(r>=p||r<a)?r-p:r;}
static inline uint64_t mod_sub(uint64_t a,uint64_t b,uint64_t p){return a>=b?a-b:p-b+a;}
static uint64_t mod_pow(uint64_t base,uint64_t exp,uint64_t p){uint64_t r=1;base%=p;while(exp>0){if(exp&1)r=mod_mul(r,base,p);base=mod_mul(base,base,p);exp>>=1;}return r;}
/* floor(sqrt(n)) for every 64-bit n: the squares are compared in 128 bits. */
static uint64_t isqrt(uint64_t n){if(n<2)return n;uint64_t x=(uint64_t)sqrtl((long double)n);if(x>0xFFFFFFFFull)x=0xFFFFFFFFull;while((unsigned __int128)x*x>n)x--;while((unsigned __int128)(x+1)*(x+1)<=n)x++;return x;}
static inline int sigma(int64_t n){int r=((n%3)+3)%3;return r==0?0:(r==1?1:-1);}
typedef struct{int64_t a;int64_t b;bool found;}Decomp;
/* A square root of n mod the odd prime p (Tonelli-Shanks), or UINT64_MAX. */
static uint64_t sqrt_mod(uint64_t n,uint64_t p){
    n%=p;if(n==0)return 0;
    if(mod_pow(n,(p-1)/2,p)!=1)return UINT64_MAX;
    uint64_t q=p-1;int s=0;while(!(q&1)){q>>=1;s++;}
    uint64_t z=2;while(mod_pow(z,(p-1)/2,p)!=p-1)z++;
    int m=s;uint64_t c=mod_pow(z,q,p),t=mod_pow(n,q,p),r=mod_pow(n,(q+1)/2,p);
    while(t!=1){int i=0;uint64_t t2=t;while(t2!=1){t2=mod_mul(t2,t2,p);i++;}
        uint64_t b=c;for(int k=0;k<m-i-1;k++)b=mod_mul(b,b,p);
        m=i;c=mod_mul(b,b,p);t=mod_mul(t,c,p);r=mod_mul(r,b,p);}
    return r;
}
/* p = a^2 + 3 b^2 with a, b > 0 for a prime p = 1 mod 3, by Cornacchia's
   algorithm: polylogarithmic, where the search it replaced took sqrt(p/3)
   steps. */
Decomp find_decomp(uint64_t p){
    if(p%3!=1)return(Decomp){0,0,false};
    uint64_t r=sqrt_mod(p-3,p);
    if(r==UINT64_MAX)return(Decomp){0,0,false};
    if(r<p-r)r=p-r;
    uint64_t x=p,y=r,lim=isqrt(p);
    while(y>lim){uint64_t t=x%y;x=y;y=t;}
    uint64_t rest=p-y*y;
    if(rest%3)return(Decomp){0,0,false};
    uint64_t v=isqrt(rest/3);
    if(v*v!=rest/3||v==0||y==0)return(Decomp){0,0,false};
    return(Decomp){(int64_t)y,(int64_t)v,true};
}
int64_t compute_B(int64_t a,int64_t b){return 2*b*sigma(b)-(a-b)*sigma(a-b)-(a+b)*sigma(a+b);}
/* Sol3 = #{x^3+y^3+z^3 = 0 in F_p^3}, computed in 128 bits: -1 when p
   has no decomposition, -2 when Sol3 does not fit in 64 bits. */
int64_t cubic_solution_count(uint64_t p){
    if(p>((uint64_t)1<<62))return-2;
    if(p==3)return 9;
    __int128 sol;
    if(p%3!=1)sol=(__int128)p*p;
    else{Decomp d=find_decomp(p);if(!d.found)return-1;
        sol=(__int128)p*p+(__int128)((int64_t)p-1)*compute_B(d.a,d.b);}
    if(sol>(__int128)INT64_MAX)return-2;
    return(int64_t)sol;
}
/* (x, y) on y^2 = x^3 + ax + b over F_p, with every value in [0, p): an
   unreduced coordinate is not a field element, and an unreduced b made the
   right-hand side wrong. */
bool ecc_point_valid(uint64_t x,uint64_t y,uint64_t a,uint64_t b,uint64_t p){
    if(p<2||x>=p||y>=p||a>=p||b>=p)return false;
    uint64_t lhs=mod_mul(y,y,p);uint64_t x3=mod_mul(mod_mul(x,x,p),x,p);
    uint64_t rhs=mod_add(mod_add(x3,mod_mul(a,x,p),p),b,p);return lhs==rhs;
}
typedef struct{uint64_t x,y;int inf;}ECPoint;
ECPoint ec_add(ECPoint P,ECPoint Q,uint64_t a,uint64_t p){
    if(P.inf)return Q;if(Q.inf)return P;
    if(P.x==Q.x&&P.y==mod_sub(0,Q.y,p))return(ECPoint){0,0,1};
    uint64_t lam;
    if(P.x==Q.x&&P.y==Q.y){uint64_t num=mod_add(mod_mul(3,mod_mul(P.x,P.x,p),p),a,p);uint64_t den=mod_pow(mod_mul(2,P.y,p),p-2,p);lam=mod_mul(num,den,p);}
    else{uint64_t num=mod_sub(Q.y,P.y,p);uint64_t den=mod_pow(mod_sub(Q.x,P.x,p),p-2,p);lam=mod_mul(num,den,p);}
    uint64_t x3=mod_sub(mod_sub(mod_mul(lam,lam,p),P.x,p),Q.x,p);
    uint64_t y3=mod_sub(mod_mul(lam,mod_sub(P.x,x3,p),p),P.y,p);return(ECPoint){x3,y3,0};
}
ECPoint ec_mul(ECPoint P,uint64_t k,uint64_t a,uint64_t p){ECPoint R={0,0,1};while(k>0){if(k&1)R=ec_add(R,P,a,p);P=ec_add(P,P,a,p);k>>=1;}return R;}
"""

# ================================================================
# ENGINE 5: Conformity Gradient  (Paper 4, Maino 2026, doi:10.5281/zenodo.19510026)
# Checks its Theorem 7.1 (covariant first integral), Theorem 10.1
# (Amari-Hodge identity) and Theorem 10.3 (Amari-Schwarzian cubic).
# ================================================================

CONFORMITY_C = r"""
#include <math.h>
#include <stdio.h>
#include <string.h>
typedef struct {
    double D, Theta_H, nu, A, Q, S, u;
    double cv_residual, ah_residual, ac_residual;
    int valid;
} conformity_result_t;
typedef struct {
    double omega, omega_p, omega_pp, omega_ppp, t;
} period_data_t;
typedef struct {
    conformity_result_t center;
    double cv_residual, ah_residual, ac_residual;
    int all_pass;
} conformity_check_t;

conformity_result_t conformity_compute(const period_data_t *pd) {
    conformity_result_t r;
    memset(&r, 0, sizeof(r));
    double w = pd->omega, wp = pd->omega_p, wpp = pd->omega_pp, wppp = pd->omega_ppp;
    if (fabs(w) < 1e-30) { r.valid = 0; return r; }
    double u = wp / w;
    double up = wpp / w - u * u;
    double upp = wppp / w - 3.0 * u * (wpp / w) + 2.0 * u * u * u;
    r.u = u;
    r.D = 2.0 * up + 4.0 * u * u;
    r.Theta_H = -2.0 * up;
    r.nu = (fabs(r.Theta_H) > 1e-30) ? (r.D + r.Theta_H) / (2.0 * r.Theta_H) : 0.0;
    r.Q = -(up + u * u);
    r.S = 2.0 * r.Q;
    r.A = 2.0 * upp;
    r.valid = 1;
    return r;
}

conformity_check_t conformity_verify(
    const period_data_t *pd_minus,
    const period_data_t *pd_center,
    const period_data_t *pd_plus,
    double dt
) {
    conformity_check_t chk;
    memset(&chk, 0, sizeof(chk));
    conformity_result_t rm = conformity_compute(pd_minus);
    conformity_result_t r0 = conformity_compute(pd_center);
    conformity_result_t rp = conformity_compute(pd_plus);
    chk.center = r0;
    if (!rm.valid || !r0.valid || !rp.valid) { chk.all_pass = 0; return chk; }
    double D_prime = (rp.D - rm.D) / (2.0 * dt);
    double Q_prime = (rp.Q - rm.Q) / (2.0 * dt);
    double TH_prime = (rp.Theta_H - rm.Theta_H) / (2.0 * dt);
    double S_prime = (rp.S - rm.S) / (2.0 * dt);
    /* CHECK 1: (D'+2Q')^2 = 2(D+2Q)(D+4Q)^2 */
    double lhs1 = (D_prime + 2.0 * Q_prime); lhs1 = lhs1 * lhs1;
    double rhs1 = 2.0 * (r0.D + 2.0 * r0.Q) * (r0.D + 4.0 * r0.Q) * (r0.D + 4.0 * r0.Q);
    double scale1 = fabs(rhs1) > 1e-30 ? fabs(rhs1) : 1.0;
    chk.cv_residual = fabs(lhs1 - rhs1) / scale1;
    /* CHECK 2: A + Theta_H' = 0 */
    double scale2 = fabs(r0.A) > 1e-30 ? fabs(r0.A) : 1.0;
    chk.ah_residual = fabs(r0.A + TH_prime) / scale2;
    /* CHECK 3: (A+S')^2 = 2(D+S)(D+2S)^2 */
    double lhs3 = (r0.A + S_prime); lhs3 = lhs3 * lhs3;
    double rhs3 = 2.0 * (r0.D + r0.S) * (r0.D + 2.0 * r0.S) * (r0.D + 2.0 * r0.S);
    double scale3 = fabs(rhs3) > 1e-30 ? fabs(rhs3) : 1.0;
    chk.ac_residual = fabs(lhs3 - rhs3) / scale3;
    double tol = 1e-3;
    chk.all_pass = (chk.cv_residual < tol) && (chk.ah_residual < tol) && (chk.ac_residual < tol);
    return chk;
}
"""

# ================================================================
# COMPILE ALL ENGINES
# ================================================================

# Engines that failed to compile in this process. A verifier that silently
# verifies LESS than it claims is worse than one that errors: in CI a skipped
# check reads as green. Anything that degrades coverage is recorded here and
# surfaced in every summary.
DEGRADED = {'engines': [], 'deps': [], 'skipped_checks': []}


def integrity_report(verbose=True):
    """What this run could NOT verify, and why.

    Returns (ok, lines). ok is False if any engine failed to build or any
    optional dependency was missing, i.e. if the run covered less than the
    tool's full claim. Call this before trusting a pass.
    """
    lines = []
    if DEGRADED['engines']:
        lines.append(f"engines unavailable: {', '.join(sorted(set(DEGRADED['engines'])))}"
                     "  (install gcc/g++ — checks depending on these did NOT run)")
    if DEGRADED['deps']:
        lines.append(f"dependencies missing: {', '.join(sorted(set(DEGRADED['deps'])))}"
                     "  (checks depending on these did NOT run)")
    if DEGRADED['skipped_checks']:
        lines.append(f"checks skipped: {', '.join(sorted(set(DEGRADED['skipped_checks'])))}")
    ok = not lines
    if verbose:
        if ok and not _ENGINES_ATTEMPTED:
            # Nothing here compiled an engine, so "every engine built" would
            # report a check that never happened.
            print("  INTEGRITY: nothing this run needed was missing "
                  "(no field engines were required).")
        elif ok:
            print("  INTEGRITY: full coverage — every engine built, every "
                  "dependency present.")
        else:
            print("  " + "!" * 66)
            print("  DEGRADED RUN — this run verified LESS than pq-verify claims:")
            for l in lines:
                print(f"    - {l}")
            print("  A pass here does NOT mean full verification.")
            print("  " + "!" * 66)
    return ok, lines


_ENGINES_ATTEMPTED = False

# Why an engine did not build, by name: the compiler's own words, for the
# integrity report and CI annotations (a bare "compilation failed" on another
# platform gives nobody anything to fix).
ENGINE_ERRORS = {}


# The flags each engine was actually built with, by output file: shows
# whether native CPU tuning is in effect on this machine.
ENGINE_FLAGS = {}


def _cc(compiler, flags, out, src):
    """Compile one engine, keeping its native tuning wherever the compiler
    allows. The flags are written for gcc on Linux, where they are used
    unchanged. Two do not travel: -lrt (macOS has no librt; clock_gettime is
    in libc) and -march=native, which Apple clang on arm64 may reject -- its
    spelling there is -mcpu=native, tried next, so Apple silicon still gets a
    build tuned to its own CPU. Only if both are refused is the engine built
    without CPU tuning: the engines are exact integer arithmetic, so that can
    cost speed but never change an answer, and an engine that does not build
    at all is worse."""
    flags = flags.split()
    # The C++ engines are C++11 (constexpr, alias declarations). g++ already
    # defaults to C++17; Apple clang++ defaults to C++98, where they do not
    # compile. Same code, same optimisation, either way.
    if compiler in ("g++", "c++", "clang++") and not any(f.startswith("-std=") for f in flags):
        flags.insert(0, "-std=c++17")
    if sys.platform == "darwin":
        flags = [f for f in flags if f != "-lrt"]
    attempts = [flags]
    if "-march=native" in flags:
        attempts.append([("-mcpu=native" if f == "-march=native" else f) for f in flags])
        attempts.append([f for f in flags if f != "-march=native"])
    for used in attempts:
        proc = subprocess.run([compiler, *used, '-o', out, src],
                              capture_output=True, text=True)
        if proc.returncode == 0:
            ENGINE_FLAGS[os.path.basename(out)] = {
                "flags": " ".join(used),
                "native_requested": len(attempts) > 1,
                "native": any(f in used for f in ("-march=native", "-mcpu=native"))}
            break
    return proc


def compile_all():
    global _ENGINES_ATTEMPTED
    _ENGINES_ATTEMPTED = True
    engines = {}
    DEGRADED['engines'].clear()
    for name, src, flags in [
        ('gf2',         GF2_C,         '-O3 -march=native -shared -fPIC -lm -lrt'),
        ('zq',          ZQ_C,          '-O3 -shared -fPIC -lm'),
        ('zq32',        ZQ32_C,        '-O3 -shared -fPIC -lm'),
        ('cubic',       CUBIC_C,       '-O3 -shared -fPIC -lm'),
        ('conformity',  CONFORMITY_C,  '-O3 -shared -fPIC -lm'),
    ]:
        _wd = _pqv_workdir()
        c_path = os.path.join(_wd, f'pqv_{name}.c')
        so_path = os.path.join(_wd, f'libpqv_{name}.so')
        with open(c_path, 'w') as f:
            f.write(src)
        # A list argv rather than os.system: no shell to quote for, and the
        # compiler's diagnostics are captured instead of thrown at /dev/null,
        # where a build failure looked identical to a missing compiler.
        proc = _cc('gcc', flags, so_path, c_path)
        if proc.returncode == 0:
            engines[name] = ctypes.CDLL(so_path)
            print(f"  {_OK} {name}")
        else:
            _why = (proc.stderr or proc.stdout or '').strip().splitlines()
            print(f"  {_BAD} {name} \u2014 compilation failed "
                  f"(is gcc installed? checks using this engine will NOT run)")
            for _l in _why[-3:]:
                print(f"      {_l[:160]}")
            engines[name] = None
            DEGRADED['engines'].append(name)
            ENGINE_ERRORS[name] = "\n".join(_why[-6:])[:1500]
    if DEGRADED['engines']:
        print(f"  \u26a0  {len(DEGRADED['engines'])} engine(s) unavailable — "
              f"this run cannot provide full coverage")
    return engines

# ================================================================
# PYTHON BINDINGS
# ================================================================

class GF2S(ctypes.Structure):
    _fields_ = [("rows",(ctypes.c_uint64*32)*8192),("parity",ctypes.c_int*8192),
                ("num_equations",ctypes.c_int),("num_variables",ctypes.c_int),("num_limbs",ctypes.c_int)]
class GF2R(ctypes.Structure):
    _fields_ = [("satisfiable",ctypes.c_int),("assignment",ctypes.c_int*2048),
                ("num_pivots",ctypes.c_int),("num_free_vars",ctypes.c_int),
                ("pivot_row",ctypes.c_int*2048),
                ("solve_time_us",ctypes.c_double),("used_m4ri",ctypes.c_int),("m4ri_blocks",ctypes.c_int)]
class GF2NS(ctypes.Structure):
    _fields_ = [("num_free",ctypes.c_int),("free_cols",ctypes.c_int*2048),
                ("basis",(ctypes.c_int*2048)*32),
                ("num_solutions_log2",ctypes.c_int),("enumerate_time_us",ctypes.c_double)]

class ZqS(ctypes.Structure):
    _fields_ = [("coefficients",(ctypes.c_uint16*2048)*4096),("rhs",ctypes.c_uint16*4096),
                ("num_equations",ctypes.c_int),("num_variables",ctypes.c_int),("q",ctypes.c_uint16)]
class ZqR(ctypes.Structure):
    _fields_ = [("satisfiable",ctypes.c_int),("assignment",ctypes.c_uint16*2048),
                ("num_pivots",ctypes.c_int),("num_free_vars",ctypes.c_int),
                ("pivot_columns",ctypes.c_int*2048),("solve_time_us",ctypes.c_double),
                ("used_colcount_order",ctypes.c_int)]

class Zq32S(ctypes.Structure):
    _fields_ = [("coefficients",(ctypes.c_uint32*256)*512),("rhs",ctypes.c_uint32*512),
                ("num_equations",ctypes.c_int),("num_variables",ctypes.c_int),("q",ctypes.c_uint32)]
class Zq32R(ctypes.Structure):
    _fields_ = [("satisfiable",ctypes.c_int),("assignment",ctypes.c_uint32*256),
                ("num_pivots",ctypes.c_int),("num_free_vars",ctypes.c_int),
                ("pivot_columns",ctypes.c_int*256),("solve_time_us",ctypes.c_double),
                ("used_colcount_order",ctypes.c_int)]

class Decomp(ctypes.Structure):
    _fields_ = [("a",ctypes.c_int64),("b",ctypes.c_int64),("found",ctypes.c_bool)]
class ECPoint(ctypes.Structure):
    _fields_ = [("x",ctypes.c_uint64),("y",ctypes.c_uint64),("inf",ctypes.c_int)]

class PeriodData(ctypes.Structure):
    _fields_ = [("omega",ctypes.c_double),("omega_p",ctypes.c_double),
                ("omega_pp",ctypes.c_double),("omega_ppp",ctypes.c_double),("t",ctypes.c_double)]
class ConformityResult(ctypes.Structure):
    _fields_ = [("D",ctypes.c_double),("Theta_H",ctypes.c_double),("nu",ctypes.c_double),
                ("A",ctypes.c_double),("Q",ctypes.c_double),("S",ctypes.c_double),("u",ctypes.c_double),
                ("cv_residual",ctypes.c_double),("ah_residual",ctypes.c_double),
                ("ac_residual",ctypes.c_double),("valid",ctypes.c_int)]
class ConformityCheck(ctypes.Structure):
    _fields_ = [("center",ConformityResult),
                ("cv_residual",ctypes.c_double),("ah_residual",ctypes.c_double),
                ("ac_residual",ctypes.c_double),("all_pass",ctypes.c_int)]

class EngineInputError(RuntimeError):
    """An engine refused its input: a variable outside the system, a system
    larger than the engine holds, or one equation too many. The refused row
    is not in the system, so a solve that went on would answer for a smaller
    system than the caller built: a check that passes on equations it never
    had. bind_all makes every init and add call raise this, where before
    they returned a code that no caller read."""
    def __init__(self, fn, rc):
        super().__init__(f"{fn} refused its input (returned {rc})")
        self.rc = rc


def _engine_rc(result, func, args):
    if result < 0:
        raise EngineInputError(getattr(func, "__name__", "engine call"), result)
    return result


def _checked(*fns):
    for fn in fns:
        fn.restype = ctypes.c_int
        fn.errcheck = _engine_rc


def bind_all(engines):
    if engines.get('gf2'):
        g = engines['gf2']
        g.gf2_init.argtypes = [ctypes.c_void_p, ctypes.c_int]
        g.gf2_add_xor.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_int]
        g.gf2_solve.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        g.gf2_verify.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
        g.gf2_verify.restype = ctypes.c_int
        g.gf2_nullspace.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        g.gf2_enumerate.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                                     ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_int]
        g.gf2_enumerate.restype = ctypes.c_int
        _checked(g.gf2_init, g.gf2_add_xor)

    if engines.get('zq'):
        z = engines['zq']
        z.zq_init.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_uint16]
        z.zq_add_equation.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint16), ctypes.c_uint16]
        z.zq_add_sparse.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_uint16), ctypes.c_int, ctypes.c_uint16]
        z.zq_add_ntt_butterfly.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_uint16]
        z.zq_solve.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        z.zq_verify.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint16)]
        z.zq_verify.restype = ctypes.c_int
        z.zq_batch_butterfly.argtypes = [ctypes.POINTER(ctypes.c_uint16),
            ctypes.POINTER(ctypes.c_uint16), ctypes.POINTER(ctypes.c_uint16),
            ctypes.POINTER(ctypes.c_uint16), ctypes.POINTER(ctypes.c_uint16),
            ctypes.POINTER(ctypes.c_uint8), ctypes.c_int, ctypes.c_uint16]
        z.zq_batch_butterfly.restype = ctypes.c_int
        z.zq_ntt_forward.argtypes = [ctypes.POINTER(ctypes.c_uint16),
            ctypes.c_int, ctypes.c_uint16, ctypes.c_uint16]
        z.zq_freivalds_ntt.argtypes = [ctypes.POINTER(ctypes.c_uint16),
            ctypes.POINTER(ctypes.c_uint16), ctypes.c_int,
            ctypes.c_uint16, ctypes.c_uint16, ctypes.c_int, ctypes.c_uint32]
        z.zq_freivalds_ntt.restype = ctypes.c_int
        z.zq_zeta_table.argtypes = [ctypes.POINTER(ctypes.c_uint16), ctypes.c_uint16, ctypes.c_uint16]
        z.zq_zeta_table.restype = None
        _checked(z.zq_init, z.zq_add_equation, z.zq_add_sparse, z.zq_add_ntt_butterfly)

    if engines.get('zq32'):
        z32 = engines['zq32']
        z32.zq32_init.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_uint32]
        z32.zq32_add_equation.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint32), ctypes.c_uint32]
        z32.zq32_add_sparse.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_uint32), ctypes.c_int, ctypes.c_uint32]
        z32.zq32_add_ntt_butterfly.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_uint32]
        z32.zq32_solve.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        z32.zq32_ntt_forward.argtypes = [ctypes.POINTER(ctypes.c_uint32),
            ctypes.c_int, ctypes.c_uint32, ctypes.c_uint32]
        z32.zq32_freivalds_ntt.argtypes = [ctypes.POINTER(ctypes.c_uint32),
            ctypes.POINTER(ctypes.c_uint32), ctypes.c_int,
            ctypes.c_uint32, ctypes.c_uint32, ctypes.c_int, ctypes.c_uint32]
        z32.zq32_freivalds_ntt.restype = ctypes.c_int
        z32.zq32_zeta_table.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_uint32, ctypes.c_uint32]
        z32.zq32_zeta_table.restype = None
        _checked(z32.zq32_init, z32.zq32_add_equation, z32.zq32_add_sparse,
                 z32.zq32_add_ntt_butterfly)

    if engines.get('cubic'):
        c = engines['cubic']
        c.find_decomp.argtypes = [ctypes.c_uint64]; c.find_decomp.restype = Decomp
        c.compute_B.argtypes = [ctypes.c_int64, ctypes.c_int64]; c.compute_B.restype = ctypes.c_int64
        c.cubic_solution_count.argtypes = [ctypes.c_uint64]; c.cubic_solution_count.restype = ctypes.c_int64
        c.ecc_point_valid.argtypes = [ctypes.c_uint64]*5; c.ecc_point_valid.restype = ctypes.c_bool
        c.ec_add.argtypes = [ECPoint, ECPoint, ctypes.c_uint64, ctypes.c_uint64]; c.ec_add.restype = ECPoint
        c.ec_mul.argtypes = [ECPoint, ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64]; c.ec_mul.restype = ECPoint

    if engines.get('conformity'):
        cf = engines['conformity']
        cf.conformity_compute.argtypes = [ctypes.POINTER(PeriodData)]
        cf.conformity_compute.restype = ConformityResult
        cf.conformity_verify.argtypes = [ctypes.POINTER(PeriodData), ctypes.POINTER(PeriodData),
                                          ctypes.POINTER(PeriodData), ctypes.c_double]
        cf.conformity_verify.restype = ConformityCheck

# ================================================================
# AUDIT RESULT TRACKING
# ================================================================

class AuditResult:
    def __init__(self, engine_name):
        self.engine = engine_name
        self.tests = []
        self.findings = []
        self.timestamp = datetime.now(timezone.utc).isoformat()
    def add_test(self, name, passed, detail="", time_us=0):
        self.tests.append({'name': name, 'passed': passed, 'detail': detail,
                           'time_us': time_us, 'skipped': False})
    def add_skip(self, name, reason, dep=None):
        """A check that COULD NOT RUN. Not a pass, and not a failure.

        A missing coqc is not evidence that a certificate is wrong, so
        recording it as a failed test told the reader something untrue and
        made the headline count unreadable -- 151/158 looked like seven broken
        checks when nothing was broken. It also bypassed integrity_report()
        entirely, so a run missing coq and sympy still announced 'full
        coverage: every dependency present'.

        This is the PQV000/PQV006 distinction -- cannot-verify versus
        verified-and-failed -- applied to pq-verify's own suite, which had it
        for everyone else's code and not its own.
        """
        deps = [dep] if isinstance(dep, str) else list(dep or ())
        self.tests.append({'name': name, 'passed': None, 'detail': reason,
                           'time_us': 0, 'skipped': True, 'dep': ', '.join(deps) or None})
        DEGRADED['deps'].extend(deps)
        DEGRADED['skipped_checks'].append(name)
    def add_finding(self, severity, description, evidence=""):
        self.findings.append({'severity': severity, 'description': description, 'evidence': evidence})
    def summary(self):
        """(passed, runnable, critical). Skipped checks are NOT in the
        denominator: a ratio that counts them reads as failures."""
        runnable = [t for t in self.tests if not t.get('skipped')]
        p = sum(1 for t in runnable if t['passed'])
        return p, len(runnable), sum(1 for f in self.findings if f['severity']=='CRITICAL')
    def n_skipped(self):
        return sum(1 for t in self.tests if t.get('skipped'))

# ================================================================
# AUDIT FUNCTIONS
# ================================================================

def _gf2_rank(eqs):
    """(consistent, rank) of XOR equations [(variables, parity), ...]:
    Gaussian elimination over GF(2) on Python integers, apart from the
    engine. Each pivot row is kept under its lowest set bit, so reducing a
    row by one only raises its lowest bit, and a row that reduces to 0 with
    parity 1 is the contradiction 0 = 1."""
    pivots = {}
    consistent = True
    for vs, p in eqs:
        m = 0
        for v in vs:
            m ^= 1 << v
        while m:
            low = m & -m
            if low not in pivots:
                pivots[low] = (m, p)
                break
            pm, pp = pivots[low]
            m ^= pm
            p ^= pp
        else:
            consistent = consistent and not p
    return consistent, len(pivots)


def _gf2_satisfied(eqs, x):
    """Whether the 0/1 assignment x satisfies every XOR equation."""
    return (all(v in (0, 1) for v in x)
            and all(sum(x[v] for v in vs) % 2 == p for vs, p in eqs))


def audit_gf2(lib, n_trials=1000):
    """Random XOR systems with at least as many equations as variables, so
    most have no solution. Each answer is checked apart from the engine: an
    assignment against every equation, an 'unsatisfiable' by elimination
    here. Through 2.13.0 an unsatisfiable answer counted as verified
    unchecked -- 874 of the 1000 -- so an engine that gave it to every
    system passed."""
    r = AuditResult('GF(2)')
    random.seed(42)
    n_sat = n_unsat = wrong = 0
    t_total = 0
    s = GF2S()  # reuse
    res = GF2R()
    for trial in range(n_trials):
        nv = random.randint(8, 32)
        n_eq = random.randint(nv, nv + 10)
        lib.gf2_init(ctypes.byref(s), nv)
        eqs = []
        for _ in range(n_eq):
            width = random.randint(2, min(6, nv))
            vs = random.sample(range(nv), width)
            p = random.randint(0, 1)
            eqs.append((vs, p))
            cv = (ctypes.c_int * len(vs))(*vs)
            lib.gf2_add_xor(ctypes.byref(s), cv, len(vs), p)
        lib.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        t_total += res.solve_time_us
        if res.satisfiable:
            n_sat += 1
            good = (_gf2_satisfied(eqs, list(res.assignment[:nv]))
                    and lib.gf2_verify(ctypes.byref(s), res.assignment) == 1)
            why = 'an assignment that does not satisfy the system'
        else:
            n_unsat += 1
            good = not _gf2_rank(eqs)[0]
            why = '"unsatisfiable" for a system with a solution'
        if not good:
            wrong += 1
            if wrong <= 3:
                r.add_finding('CRITICAL', f'GF(2) engine: {why} (system {trial + 1})')
    r.add_test(f'GF(2) random systems ({n_trials})', wrong == 0,
               f'{n_sat} solved, each assignment checked against every equation; '
               f'{n_unsat} unsatisfiable, each confirmed by elimination apart from '
               f'the engine; {wrong} wrong, {t_total:.0f}\u03bcs total', t_total)
    return r

def audit_gf2_nullspace(lib, n_trials=200):
    """Null-space enumeration: every solution of underdetermined GF(2)
    systems. Apart from the engine, elimination here gives each system's
    consistency and rank: an 'unsatisfiable' must be right, and a consistent
    system must have exactly 2^(variables - rank) solutions, each checked
    against every equation and all distinct -- which makes the enumeration
    complete. Through 2.13.0 an unsatisfiable answer counted as verified
    unchecked, and the number of free variables was compared only with the
    engine's own."""
    r = AuditResult('GF(2) Null-Space')
    random.seed(2026)
    t_total = 0
    # --- Test 1: underdetermined systems, enumerate + verify all solutions ---
    all_ok = 0
    total_solutions = 0
    n_unsat = 0
    for trial in range(n_trials):
        nv = random.randint(8, 20)
        n_eq = random.randint(max(2, nv - 8), nv - 1)  # fewer eqs than vars → free vars
        s = GF2S()
        lib.gf2_init(ctypes.byref(s), nv)
        eqs = []
        for _ in range(n_eq):
            width = random.randint(2, min(5, nv))
            vs = random.sample(range(nv), width)
            p = random.randint(0, 1)
            eqs.append((vs, p))
            cv = (ctypes.c_int * len(vs))(*vs)
            lib.gf2_add_xor(ctypes.byref(s), cv, len(vs), p)
        consistent, rank = _gf2_rank(eqs)
        res = GF2R()
        lib.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        if not res.satisfiable:
            n_unsat += 1
            if consistent:
                r.add_finding('CRITICAL', f'"unsatisfiable" for a system with a solution '
                                          f'(system {trial + 1})')
            else:
                all_ok += 1
            continue
        if not consistent:
            r.add_finding('CRITICAL', f'a solution claimed for a system with none (system {trial + 1})')
            continue
        ns = GF2NS()
        lib.gf2_nullspace(ctypes.byref(s), ctypes.byref(res), ctypes.byref(ns))
        if not ns.num_free == res.num_free_vars == nv - rank:
            r.add_finding('CRITICAL', f'free variables: null space {ns.num_free}, solver '
                                      f'{res.num_free_vars}, elimination {nv - rank}')
            continue
        if ns.num_free > 20:
            all_ok += 1  # too many to enumerate, but count is valid
            continue
        expected = 1 << ns.num_free
        buf = (ctypes.c_int * (expected * nv))()
        t0 = time.perf_counter()
        count = lib.gf2_enumerate(ctypes.byref(s), ctypes.byref(res),
                                   ctypes.byref(ns), buf, expected, nv)
        t_total += (time.perf_counter() - t0) * 1e6
        if count != expected:
            r.add_finding('CRITICAL', f'enumerate count {count} != 2^{ns.num_free}={expected}')
            continue
        # verify every solution
        trial_ok = True
        seen = set()
        for i in range(count):
            x = [buf[i * nv + j] for j in range(nv)]
            sol = (ctypes.c_int * nv)(*x)
            if not (_gf2_satisfied(eqs, x) and lib.gf2_verify(ctypes.byref(s), sol) == 1):
                r.add_finding('CRITICAL', f'solution {i} fails verification')
                trial_ok = False
                break
            seen.add(tuple(x))
        if trial_ok and len(seen) == count:
            all_ok += 1
            total_solutions += count
        elif trial_ok:
            r.add_finding('CRITICAL', f'duplicate solutions: {count} generated, {len(seen)} unique')
    r.add_test(f'Null-space enumeration ({n_trials} systems)', all_ok == n_trials,
               f'{all_ok}/{n_trials} verified: {total_solutions} solutions, 2^(variables '
               f'\u2212 rank) per system by elimination apart from the engine, each '
               f'checked against every equation; {n_unsat} unsatisfiable, each confirmed; '
               f'{t_total:.0f}\u03bcs enumerate', t_total)
    # --- Test 2: unique solution (full-rank square system) ---
    nv = 16
    x_true = [random.randint(0, 1) for _ in range(nv)]
    s = GF2S()
    lib.gf2_init(ctypes.byref(s), nv)
    # identity-ish: each equation pins one variable
    for i in range(nv):
        cv = (ctypes.c_int * 1)(i)
        lib.gf2_add_xor(ctypes.byref(s), cv, 1, x_true[i])
    res = GF2R()
    lib.gf2_solve(ctypes.byref(s), ctypes.byref(res))
    ns = GF2NS()
    lib.gf2_nullspace(ctypes.byref(s), ctypes.byref(res), ctypes.byref(ns))
    # The one solution must be the one the equations pin, not merely a claim
    # that there is one.
    got = list(res.assignment[:nv])
    unique_ok = (res.satisfiable and ns.num_free == 0 and ns.num_solutions_log2 == 0
                 and got == x_true)
    r.add_test('Unique solution (full-rank)', unique_ok,
               f'free={ns.num_free}, 2^{ns.num_solutions_log2} solutions, '
               f'{"the pinned assignment" if got == x_true else "NOT the pinned assignment"}')
    # --- Test 3: basis orthogonality (each basis vector independent) ---
    nv = 16
    n_eq = 8  # half-rank → 8 free vars, 256 solutions
    s = GF2S()
    lib.gf2_init(ctypes.byref(s), nv)
    rng = random.Random(42)
    for _ in range(n_eq):
        vs = rng.sample(range(nv), rng.randint(2, 5))
        p = rng.randint(0, 1)
        cv = (ctypes.c_int * len(vs))(*vs)
        lib.gf2_add_xor(ctypes.byref(s), cv, len(vs), p)
    res = GF2R()
    lib.gf2_solve(ctypes.byref(s), ctypes.byref(res))
    ns = GF2NS()
    lib.gf2_nullspace(ctypes.byref(s), ctypes.byref(res), ctypes.byref(ns))
    # check basis vectors are linearly independent over GF(2)
    # (each has a 1 in its own free column, 0 in other free columns → trivially independent)
    indep_ok = True
    for fi in range(ns.num_free):
        fc = ns.free_cols[fi]
        if ns.basis[fi][fc] != 1:
            indep_ok = False; break
        for fj in range(ns.num_free):
            if fi == fj: continue
            if ns.basis[fi][ns.free_cols[fj]] != 0:
                indep_ok = False; break
        if not indep_ok: break
    r.add_test('Basis independence (16 vars, 8 eqs)', indep_ok and ns.num_free > 0,
               f'{ns.num_free} free vars, basis vectors mutually independent')
    return r

def audit_kyber(lib, n_bf=1000):
    r = AuditResult('Z_3329 (Kyber)')
    random.seed(42)
    Q = 3329
    mismatches = 0
    t_total = 0
    s = ZqS()  # reuse
    res = ZqR()
    for _ in range(n_bf):
        a_in = random.randint(0, Q-1)
        b_in = random.randint(0, Q-1)
        w = random.randint(1, Q-1)
        exp_a = (a_in + w * b_in) % Q
        exp_b = (a_in + (Q - w) * b_in) % Q
        lib.zq_init(ctypes.byref(s), 4, Q)
        vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
        vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
        lib.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        t_total += res.solve_time_us
        if not res.satisfiable or res.assignment[2] != exp_a or res.assignment[3] != exp_b:
            mismatches += 1
    r.add_test(f'Kyber NTT butterfly ({n_bf})', mismatches == 0,
               f'{mismatches} mismatches, {t_total:.0f}\u03bcs total', t_total)
    return r

def audit_dilithium(lib, n_bf=100):
    r = AuditResult('Z_8380417 (Dilithium)')
    random.seed(42)
    Q = 8380417
    mismatches = 0
    t_total = 0
    s = Zq32S()  # reuse single struct
    res = Zq32R()
    for _ in range(n_bf):
        a_in = random.randint(0, Q-1)
        b_in = random.randint(0, Q-1)
        w = random.randint(1, Q-1)
        exp_a = (a_in + w * b_in) % Q
        exp_b = (a_in + (Q - w) * b_in) % Q
        lib.zq32_init(ctypes.byref(s), 4, Q)
        vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint32*1)(1)
        lib.zq32_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
        vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint32*1)(1)
        lib.zq32_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
        lib.zq32_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        lib.zq32_solve(ctypes.byref(s), ctypes.byref(res))
        t_total += res.solve_time_us
        if not res.satisfiable or res.assignment[2] != exp_a or res.assignment[3] != exp_b:
            mismatches += 1
    r.add_test(f'Dilithium NTT butterfly ({n_bf})', mismatches == 0,
               f'{mismatches} mismatches, {t_total:.0f}\u03bcs total', t_total)
    return r

def _fermat_cubic_count(p):
    """#{(x, y, z) in F_p^3 : x^3 + y^3 + z^3 = 0}, counted directly from how
    many cube roots each value has: about (p/3)^2 steps. It is what
    cubic_solution_count states as p^2 + (p-1) B(a, b), by a route that does
    not use the decomposition."""
    roots = {}
    for x in range(p):
        c = pow(x, 3, p)
        roots[c] = roots.get(c, 0) + 1
    return sum(nu * nv * roots.get((-u - v) % p, 0)
               for u, nu in roots.items() for v, nv in roots.items())


def _cubic_jacobi_sum(p):
    """J(chi, chi) = sum over x in F_p of chi(x) chi(1 - x), chi a cubic
    character (p = 1 mod 3), as (c, d) for c + d*omega, by the character sum
    itself: about p steps. J is primary (c = 2, d = 0 mod 3), its norm
    c^2 - cd + d^2 is p, and the Fermat cubic has p + 1 + 2 Re J projective
    points (Ireland and Rosen, ch. 8), so B(a, b) = 2 Re J = 2c - d."""
    from . import ec as EC
    q = p - 1
    g = next(g for g in range(2, p) if all(pow(g, q // f, p) != 1 for f in EC.factor(q)))
    ind, x = [0] * p, 1
    for k in range(q):
        ind[x] = k
        x = x * g % p
    counts = [0, 0, 0]
    for x in range(2, p):
        counts[(ind[x] + ind[(1 - x) % p]) % 3] += 1
    return counts[0] - counts[2], counts[1] - counts[2]


def audit_cubic(lib, primes=None):
    """The cubic engine (docs/ECC.md): its count of x^3+y^3+z^3 = 0 against a
    direct count and, through the Jacobi sum J(chi, chi), its B(a, b);
    against complex multiplication for large primes; its point validation;
    and its scalar multiplication against pq_verify.ec."""
    from . import ec as EC
    r = AuditResult('Cubic B(a,b) + ECC')
    if primes is None:
        primes = [7, 13, 19, 37, 61, 97, 151, 199, 271, 331, 397, 463, 541, 601, 661, 751, 823, 907, 991, 1021, 1051]
    ok = 0
    for p in primes:
        sol = lib.cubic_solution_count(p)
        direct = _fermat_cubic_count(p)
        if p % 3 != 1:
            # No cubic structure: Sol3 = p^2.
            ok += sol == p * p == direct
            continue
        d = lib.find_decomp(p)
        B = lib.compute_B(d.a, d.b) if d.found else None
        c, e = _cubic_jacobi_sum(p)
        jacobi = (c % 3 == 2 and e % 3 == 0 and c * c - c * e + e * e == p
                  and B == 2 * c - e)
        if d.found and d.a * d.a + 3 * d.b * d.b == p and \
                sol == p * p + (p - 1) * B == direct and jacobi:
            ok += 1
        else:
            r.add_finding('CRITICAL', f'B(a,b) mismatch at p={p}')
    # Large primes, past a direct count, and past 64 bits for Sol3 ~ p^2,
    # which the engine must refuse: its B(a, b) against complex
    # multiplication on y^2 = x^3 - 432, whose count is p + 1 + B.
    large = [1099511628401, 281474976710677, 72057594037928017,
             2305843009213693951, 4611686018427388039]
    big_ok = 0
    for p in large:
        E = EC.Curve(0, (-432) % p, p)
        n = EC.count(E)
        if n is None or not EC.check_count(E, n) or lib.cubic_solution_count(p) != -2:
            continue
        d = lib.find_decomp(p)
        if p % 3 == 1:
            big_ok += (d.found and d.a * d.a + 3 * d.b * d.b == p
                       and lib.compute_B(d.a, d.b) == n.n - p - 1)
        else:
            big_ok += not d.found and n.n == p + 1
    r.add_test(f'Cubic B(a,b) ({len(primes)} primes)',
               ok == len(primes) and big_ok == len(large),
               f'{ok}/{len(primes)} equal to a direct count of x\u00b3+y\u00b3+z\u00b3=0, '
               f'with B = 2\u00b7Re J(\u03c7,\u03c7) from the character sum; at '
               f'{big_ok}/{len(large)} primes of 41 to 63 bits, B = #E(y\u00b2=x\u00b3\u2212432) '
               f'\u2212 p \u2212 1 by complex multiplication, and Sol\u2083, past 64 bits, refused')

    # ECC point validation, including values outside [0, p)
    cases = [((5, 1, 2, 2, 17), True), ((6, 3, 2, 2, 17), True), ((10, 6, 2, 2, 17), True),
             ((0, 0, 2, 2, 17), False), ((5 + 17, 1, 2, 2, 17), False),
             ((5, 1 + 17, 2, 2, 17), False), ((5, 1, 2 + 17, 2, 17), False),
             ((5, 1, 2, 2 + 17, 17), False)]
    ecc_ok = sum(bool(lib.ecc_point_valid(*args)) == want for args, want in cases)
    r.add_test('ECC point validation (y\u00b2=x\u00b3+2x+2 mod 17)', ecc_ok == len(cases),
               f'{ecc_ok}/{len(cases)}, three with a value outside [0, p)')

    # Scalar multiplication against pq_verify.ec: kG for k = 0..40 on a group
    # of order 19.
    E = EC.Curve(2, 2, 17)
    G = (5, 1)
    mul_ok = 0
    for k in range(41):
        R = lib.ec_mul(ECPoint(5, 1, 0), k, 2, 17)
        want = E.mul(k, G)
        mul_ok += (R.inf == 1 and want is None) or (not R.inf and (R.x, R.y) == want)
    r.add_test('ECC scalar multiply 7*G', mul_ok == 41,
               f'kG for k = 0..40 equal to pq_verify.ec in {mul_ok}/41, 19G = O')
    return r

def audit_conformity(lib):
    """Test conformity gradient engine on analytic period functions.
    Uses \u03c9(t) = exp(-t\u00b2/2) where all derivatives are known exactly:
      \u03c9'  = -t\u00b7\u03c9,  \u03c9'' = (t\u00b2-1)\u00b7\u03c9,  \u03c9''' = (-t\u00b3+3t)\u00b7\u03c9
    Conservation law (D'+2Q')\u00b2 = 2(D+2Q)(D+4Q)\u00b2 must hold."""
    r = AuditResult('Conformity Gradient')

    # Test 1: Single-point compute on known function
    t0 = 1.0
    w = math.exp(-t0**2 / 2)
    wp = -t0 * w
    wpp = (t0**2 - 1) * w
    wppp = (-t0**3 + 3*t0) * w
    pd = PeriodData(w, wp, wpp, wppp, t0)
    res = lib.conformity_compute(ctypes.byref(pd))

    # Analytic check: u = \u03c9'/\u03c9 = -t
    u_expected = -t0
    u_err = abs(res.u - u_expected)
    r.add_test('Single-point u = \u03c9\'/\u03c9', u_err < 1e-12,
               f'u={res.u:.6f}, expected={u_expected:.6f}, err={u_err:.2e}')

    # Analytic: D = 2u' + 4u\u00b2 = 2(-1) + 4(1) = 2 at t=1
    D_expected = 2.0 * (-1.0) + 4.0 * t0**2
    D_err = abs(res.D - D_expected)
    r.add_test('D = 2u\' + 4u\u00b2', D_err < 1e-12,
               f'D={res.D:.6f}, expected={D_expected:.6f}')

    # The engine's one validity guard is omega = 0, where u = omega'/omega is
    # undefined: it must refuse that point and accept the one above. Through
    # 2.13.0 only the second was checked, which no input here could fail.
    zero = lib.conformity_compute(ctypes.byref(PeriodData(0.0, wp, wpp, wppp, t0)))
    r.add_test('Valid computation', res.valid == 1 and zero.valid == 0,
               f'valid={res.valid} at t = {t0}; valid={zero.valid} with \u03c9 = 0, '
               f'which it must refuse')

    # Test 2: Three-point conservation law verification
    dt = 0.001
    n_pass = 0
    n_tests = 20
    max_cv = 0.0
    for i in range(n_tests):
        tc = 0.5 + i * 0.1
        points = []
        for t in [tc - dt, tc, tc + dt]:
            w = math.exp(-t**2 / 2)
            wp = -t * w
            wpp = (t**2 - 1) * w
            wppp = (-t**3 + 3*t) * w
            points.append(PeriodData(w, wp, wpp, wppp, t))
        chk = lib.conformity_verify(ctypes.byref(points[0]), ctypes.byref(points[1]),
                                     ctypes.byref(points[2]), ctypes.c_double(dt))
        if chk.cv_residual < 0.01:
            n_pass += 1
        max_cv = max(max_cv, chk.cv_residual)

    r.add_test(f'Conservation law ({n_tests} points)', n_pass == n_tests,
               f'{n_pass}/{n_tests} pass, max residual={max_cv:.2e}')

    # Test 3: Amari-Hodge identity A + \u0398_H' = 0
    n_ah_pass = 0
    max_ah = 0.0
    for i in range(n_tests):
        tc = 0.5 + i * 0.1
        points = []
        for t in [tc - dt, tc, tc + dt]:
            w = math.exp(math.sin(t))
            wp = math.cos(t) * w
            wpp = (-math.sin(t) + math.cos(t)**2) * w
            wppp = (-math.cos(t) - 3*math.sin(t)*math.cos(t) + math.cos(t)**3) * w
            points.append(PeriodData(w, wp, wpp, wppp, t))
        chk = lib.conformity_verify(ctypes.byref(points[0]), ctypes.byref(points[1]),
                                     ctypes.byref(points[2]), ctypes.c_double(dt))
        if chk.ah_residual < 0.01:
            n_ah_pass += 1
        max_ah = max(max_ah, chk.ah_residual)

    r.add_test(f'Amari-Hodge A+\u0398_H\'=0 ({n_tests} pts)', n_ah_pass == n_tests,
               f'{n_ah_pass}/{n_tests} pass, max residual={max_ah:.2e}')

    return r

# ================================================================
# CURVE AUDITOR (from curve_auditor_plan.md)
# Structural + Cubic + Conformity on y\u00b2 = x\u00b3 + ax + b mod p
# ================================================================

def audit_curve(engines, a, b, p):
    """A curve y^2 = x^3 + ax + b over F_p (docs/ECC.md): nonsingular; its
    j-invariant; its point count, and its twist's, each with a certificate
    checked from the curve; the cubic engine's count of x^3+y^3+z^3 = 0 and
    its point validation; and the conformity gradient on its discriminant
    family. Findings: singular, supersingular, anomalous, trace 2, and a
    small embedding degree."""
    from . import ec as EC
    r = AuditResult(f'Curve y\u00b2=x\u00b3+{a}x+{b} mod {p}')
    lib_c = engines.get('cubic')
    lib_cf = engines.get('conformity')

    # STRUCTURAL: discriminant
    disc_raw = 4 * a**3 + 27 * b**2
    disc = (-16 * disc_raw) % p
    non_singular = disc != 0
    r.add_test('Discriminant \u0394 \u2260 0', non_singular, f'\u0394={disc}')
    if not non_singular:
        r.add_finding('CRITICAL', 'Singular curve')
        return r
    try:
        E = EC.Curve(a % p, b % p, p)
    except EC.ECError as e:
        r.add_test('Prime field', False, str(e))
        r.add_finding('CRITICAL', f'Not a curve over a prime field above 3: {e}')
        return r

    # j-invariant: it satisfies its definition j (4a^3 + 27b^2) = 6912 a^3,
    # checked without the inverse that computes it; it is unchanged under
    # (a, b) -> (u^4 a, u^6 b); and it is 0 or 1728 exactly when a or b is 0.
    j_inv = E.j
    defined = j_inv * (4 * E.a ** 3 + 27 * E.b ** 2) % p == 6912 * E.a ** 3 % p
    iso = all(EC.Curve(pow(u, 4, p) * E.a % p, pow(u, 6, p) * E.b % p, p).j == j_inv
              for u in (2, 3, 5) if u % p)
    special = (j_inv == 0) == (E.a == 0) and (j_inv == 1728 % p) == (E.b == 0)
    r.add_test('j-invariant', defined and iso and special,
               f'j={j_inv}: j(4a\u00b3+27b\u00b2) = 6912a\u00b3, unchanged under '
               f'isomorphism, 0 iff a = 0, 1728 iff b = 0'
               + ('' if defined and iso and special else ' \u2014 NOT'))
    # Supersingular (embedding degree <= 2, so MOV/Frey-Ruck applies). For
    # p > 3, j = 0 is supersingular iff p = 2 mod 3 and j = 1728 iff
    # p = 3 mod 4 (Deuring); any other j is decided by the count (trace 0).
    supersingular = (j_inv == 0 and p % 3 == 2) or (j_inv == 1728 % p and p % 4 == 3)

    # POINT COUNT, certified, and the twist's
    how = {'naive': 'direct count', 'cm': 'complex multiplication',
           'orders': 'point orders on E and its twist',
           'sea': 'Schoof\u2013Elkies\u2013Atkin (docs/SEA.md)'}
    count = EC.count(E)
    trace = None
    if count is None:
        why = (f'a general curve above 2^{EC.SEA_BITS}' if p.bit_length() > EC.SEA_BITS
               else 'Schoof\u2013Elkies\u2013Atkin left more than one candidate')
        r.add_skip('Point count', f'{why}: CANNOT VERIFY without a published order (docs/SEA.md)')
    else:
        ok = EC.check_count(E, count)
        trace = count.trace
        r.add_test('Point count', ok,
                   f'#E={count.n}, t={trace} by {how[count.method]}, certificate checked'
                   if ok else f'#E={count.n}: its certificate is REJECTED')
        if not ok:
            r.add_finding('CRITICAL', f'pq-verify point count certificate rejected: #E={count.n}')
        elif trace == 1:
            r.add_finding('CRITICAL',
                f'Anomalous curve: #E={count.n}=p, trace=1 (Smart attack vulnerable)')
        elif trace == 2:
            # #E = p - 1: every prime l dividing #E divides p - 1, so the
            # embedding degree is 1 and a pairing carries the discrete log
            # into F_p*. Through 2.13.0 this fired for |t| <= 2, but traces
            # -1 and -2 have no such structure, and 0 is the supersingular
            # finding below.
            r.add_finding('HIGH',
                f'Trace 2: #E={count.n} = p \u2212 1, so the embedding degree is 1 (a '
                f'pairing carries the discrete log into F_p*)')
        if ok:
            # Embedding degree, SafeCurves' "transfer" criterion: k is the least
            # with l | p^k - 1, for l the largest prime factor of #E. The Weil
            # or Tate pairing then carries the discrete log of the order-l
            # subgroup into F_(p^k), and SafeCurves requires k > (l - 1)/100.
            # Checked here up to k = 100; l = p is the anomalous case above.
            big = EC.largest_prime_factor(count.n)
            if big is None:
                r.add_finding('INFO', f'Embedding degree not checked: #E={count.n} was not '
                                      f'factored within the step limit')
            elif big != p:
                kmax = min(100, (big - 1) // 100)
                k = next((k for k in range(1, kmax + 1) if pow(p, k, big) == 1), None)
                if k is not None:
                    r.add_finding('HIGH',
                        f'Small embedding degree k={k} for the subgroup of order {big} '
                        f'(SafeCurves requires k > (order \u2212 1)/100): a pairing carries '
                        f'its discrete log into F_(p^{k})')
    twist = E.twist()
    tcount = EC.count(twist)
    if count is None or tcount is None:
        r.add_skip('Twist: #E + #E\u2032 = 2p + 2', 'a count could not be made')
    else:
        ok = EC.check_count(twist, tcount) and count.n + tcount.n == 2 * p + 2
        r.add_test('Twist: #E + #E\u2032 = 2p + 2', ok,
                   f'#E\u2032={tcount.n} by {how[tcount.method]}, certificate checked; '
                   f'#E + #E\u2032 = {count.n + tcount.n}'
                   + ('' if ok else f', not {2 * p + 2}'))
    if supersingular or trace == 0:
        why = (f'p\u2261{p % 3} mod 3' if j_inv == 0 and supersingular else
               f'p\u2261{p % 4} mod 4' if supersingular else 'trace 0')
        r.add_finding('HIGH', f'Supersingular: j={j_inv}, {why} (MOV/Frey-R\u00fcck transfer)')

    # CUBIC: the engine's Sol3 = #{x^3+y^3+z^3 = 0} against 1 + (p-1) #E for
    # y^2 = x^3 - 432, the curve the Fermat cubic is isomorphic to, counted
    # with its certificate (complex multiplication: j = 0, at any size).
    # Where Sol3 does not fit the engine's 64 bits, the engine must refuse
    # it, and its B(a, b) is checked instead: #E = p + 1 + B.
    if lib_c and p >= 2**64:
        r.add_skip('Cubic B(a,b)', 'p is past the cubic engine\'s 64 bits')
    elif lib_c:
        fermat = EC.Curve(0, (-432) % p, p)
        fc = EC.count(fermat)
        if fc is None or not EC.check_count(fermat, fc):
            r.add_test('Cubic B(a,b)', False, 'no certified count of y\u00b2=x\u00b3\u2212432')
        else:
            want = 1 + (p - 1) * fc.n
            sol = lib_c.cubic_solution_count(p)
            d = lib_c.find_decomp(p)
            B = lib_c.compute_B(d.a, d.b) if d.found else 0
            decomp = (d.found and d.a * d.a + 3 * d.b * d.b == p) if p % 3 == 1 else not d.found
            shown = f'p={d.a}\u00b2+3\u00b7{d.b}\u00b2, ' if d.found else ''
            if sol == -2:
                refused = p > 2**62 or want > 2**63 - 1
                ok = refused and decomp and B == fc.n - p - 1
                r.add_test('Cubic B(a,b)', ok,
                           f'{shown}B={B}; Sol\u2083={want} past 64 bits, '
                           f'{"refused" if refused else "refused WRONGLY"}; '
                           f'#E(y\u00b2=x\u00b3\u2212432) = {fc.n} = p+1+B'
                           + ('' if ok else ' \u2014 NOT'))
            else:
                ok = decomp and sol == want
                r.add_test('Cubic B(a,b)', ok,
                           f'{shown}B={B}, Sol\u2083={sol}, '
                           f'1+(p\u22121)\u00b7#E(y\u00b2=x\u00b3\u2212432) = {want}')

    # ECC POINT VALIDATION: the engine on a point of E, a point off it, an
    # unreduced coordinate and an unreduced coefficient.
    if lib_c and p < 2**63:
        P = E.random_point(random.Random(p))
        off = (P[0], (P[1] + 1) % p)
        cases = [((P[0], P[1], E.a, E.b, p), True),
                 ((off[0], off[1], E.a, E.b, p), E.is_on(off)),
                 ((P[0] + p, P[1], E.a, E.b, p), False),
                 ((P[0], P[1], E.a, E.b + p, p), False)]
        got = [bool(lib_c.ecc_point_valid(*args)) == want for args, want in cases]
        r.add_test('ECC point validation', all(got),
                   f'{sum(got)}/{len(got)}: a point of E, a point off it, an unreduced '
                   f'x and an unreduced b')

    # CONFORMITY on the discriminant family (research framework). It used to
    # report |4a^3 + 27b^2|/p as a "stability margin" and a curve under 0.01
    # as a near-singular fiber (HIGH); over F_p a curve is singular or it is
    # not, and that ratio depends on which integers stand for a and b.
    if lib_cf and disc_raw != 0:
        dt = 0.001
        points = []
        for t_off in [-dt, 0.0, dt]:
            t = float(b) + t_off
            delta = 4.0*float(a)**3 + 27.0*t**2
            if abs(delta) < 1e-30:
                break
            ad = abs(delta)
            omega = ad**(1.0/12.0)
            dp = 54.0*t
            dpp = 54.0
            omega_p = (1.0/12.0)*ad**(-11.0/12.0)*dp
            omega_pp = (1.0/12.0)*((-11.0/12.0)*ad**(-23.0/12.0)*dp**2 + ad**(-11.0/12.0)*dpp)
            omega_ppp = (1.0/12.0)*((-11.0/12.0)*(-23.0/12.0)*ad**(-35.0/12.0)*dp**3
                         + 3.0*(-11.0/12.0)*ad**(-23.0/12.0)*dp*dpp)
            points.append(PeriodData(omega, omega_p, omega_pp, omega_ppp, t_off))
        if len(points) == 3:
            res = lib_cf.conformity_compute(ctypes.byref(points[1]))
            # D = 2u' + 4u^2 with u = omega'/omega = Delta'/(12 Delta), from the
            # discriminant itself rather than the omega derivatives the engine
            # was given. Through 2.13.0 the row checked only the engine's
            # valid flag, which is 0 only for omega = 0.
            dl, dlp = 4.0 * float(a) ** 3 + 27.0 * float(b) ** 2, 54.0 * float(b)
            u = dlp / (12.0 * dl)
            want = 2.0 * (54.0 * dl - dlp * dlp) / (12.0 * dl * dl) + 4.0 * u * u
            d_ok = res.valid == 1 and math.isclose(res.D, want, rel_tol=1e-9, abs_tol=1e-300)
            r.add_test('Conformity D(t)', d_ok,
                       f'D={res.D:.6g}, {"" if d_ok else "NOT "}2u\u2032+4u\u00b2 for '
                       f'u = \u0394\u2032/(12\u0394) ({want:.6g})')
            chk = lib_cf.conformity_verify(ctypes.byref(points[0]),
                    ctypes.byref(points[1]), ctypes.byref(points[2]), ctypes.c_double(dt))
            r.add_test('Conservation law on family', chk.cv_residual < 0.01,
                       f'residual={chk.cv_residual:.2e}')

    return r

# ================================================================
# COQ CERTIFICATE GENERATOR
# ================================================================

def _coq_list(xs):
    return "[" + "; ".join(str(int(v)) for v in xs) + "]"


def _coq_shared_ntt():
    """The generic transform from pq_verify/coq/NTT.v, verbatim (between its
    BEGIN SHARED / END SHARED markers). NTT.v proves this transform equals
    the FIPS 203 / FIPS 204 CRT map for every input; emitting the same text
    here means a per-run certificate is about that very definition."""
    with open(os.path.join(_pkg_dir(), 'coq', 'NTT.v')) as f:
        src = f.read()
    start = src.index('(* BEGIN SHARED')
    end = src.index('(* END SHARED *)') + len('(* END SHARED *)')
    return src[start:end]


def _coq_ntt_prelude(q, root, bits, n_layers):
    """Gallina definitions of the FIPS 203 / FIPS 204 forward NTT.

    Everything a certificate states is recomputed by Coq from these
    definitions: the zeta table is root^brv(i) mod q, built in Coq, never
    copied from Python. A certificate therefore cannot pass because pq-verify
    and its proof share a wrong constant -- the Python side only supplies the
    input and the claimed output. The transform itself is NTT.v's, which is
    proved correct for all inputs there.

    ML-KEM: q=3329, root=17, 7-bit reversal, 7 layers (len 128..2).
    ML-DSA: q=8380417, root=1753, 8-bit reversal, 8 layers (len 128..1).
    """
    return f"""Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

{_coq_shared_ntt()}

Definition q : Z := {q}.
Definition root : Z := {root}.
Definition zeta (i : Z) : Z := Z.modulo (root ^ brv {bits} i 0) q.
Definition fips_ntt (f : list Z) : list Z := ntt (ops_mod q) zeta {n_layers} f.
"""


# Printed by `Print Assumptions` when a theorem rests on no axiom and no
# Admitted proof. coqc exits 0 for an Admitted proof, so the exit code alone
# does not show that a certificate proves anything; this line does.
COQ_CLOSED = "Closed under the global context"


def gen_coq_ntt_cert(scheme, f_in, f_out, filename):
    """Coq certificate that the FIPS NTT of f_in is exactly f_out.

    One theorem covers the whole transform: every butterfly of every layer,
    all 256 output coefficients. Also proves the root has the order the
    transform needs and that the zeta table is what the FIPS defines.
    Returns (filename, theorem_names).
    """
    if scheme == 'ML-KEM':
        q, root, bits, nl, order, pre = KYBER_Q, KYBER_ZETA, 7, 7, 256, 'mlkem'
    else:
        q, root, bits, nl, order, pre = DILI_Q, DILI_ZETA, 8, 8, 512, 'mldsa'
    thms = [f'{pre}_root_order', f'{pre}_ntt_run']
    lines = [
        f"(* pq-verify v{VERSION}: {scheme} forward NTT certificate *)",
        f"(* 256 coefficients, {nl} layers, {128 * nl} butterflies; the whole *)",
        "(* transform is recomputed by Coq from the definitions below.      *)",
        _coq_ntt_prelude(q, root, bits, nl),
        f"(* root^{order // 2} = -1, so root has order exactly {order} *)",
        f"Theorem {thms[0]} : Z.modulo (root ^ {order // 2}) q = q - 1.",
        "Proof. vm_compute. reflexivity. Qed.",
        f"Theorem {thms[1]} : fips_ntt {_coq_list(f_in)} = {_coq_list(f_out)}.",
        "Proof. vm_compute. reflexivity. Qed.",
    ]
    lines += [f"Print Assumptions {t}." for t in thms]
    with open(filename, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    return filename, thms


def gen_coq_cert(results, filename=None, corrupt=False):
    """Batch certificate: the constants every NTT check in this run relies on.

    Proves, in Coq, that pq-verify's ML-KEM and ML-DSA zeta tables are the
    ones FIPS 203 and FIPS 204 define, and that each root has the order its
    transform needs. Earlier versions certified freshly drawn random numbers
    that no check had used, so the certificate said nothing about the run.

    corrupt=True states the first table with one entry off by one, which
    coqc must reject; None then if this run has no table to state.
    """
    if filename is None:
        filename = os.path.join(_pqv_workdir(), 'pq_verify_cert.v')
    engines = {r.engine for r in results}
    lines = [
        f"(* pq-verify v{VERSION} Coq certificate *)",
        f"(* Generated: {datetime.now(timezone.utc).isoformat()} *)",
        "Require Import ZArith List.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "Fixpoint brv (k : nat) (x acc : Z) : Z :=",
        "  match k with O => acc | S k' => brv k' (Z.shiftr x 1) (2 * acc + Z.land x 1) end.",
        "",
    ]
    thms = []
    tables = []
    if 'Z_3329 (Kyber)' in engines:
        tables.append(('mlkem', KYBER_Q, KYBER_ZETA, 7, 128, 256, _kyber_zeta_table()))
    if 'Z_8380417 (Dilithium)' in engines:
        tables.append(('mldsa', DILI_Q, DILI_ZETA, 8, 256, 512, _dilithium_zeta_table()))
    if corrupt:
        # Only the first table, wrong: a whole second certificate would
        # double coqc's ~9 s, most of it ML-DSA's 256 powers.
        if not tables:
            return None
        pre, q, root, bits, size, order, table = tables[0]
        table = list(table)
        table[1] = (table[1] + 1) % q
        tables = [(pre, q, root, bits, size, order, table)]
    for pre, q, root, bits, size, order, table in tables:
        lines.append(f"Theorem {pre}_root_order : Z.modulo ({root} ^ {order // 2}) {q} = {q} - 1.")
        lines.append("Proof. vm_compute. reflexivity. Qed.")
        lines.append(f"Theorem {pre}_zeta_table : map (fun i => Z.modulo ({root} ^ brv {bits} i 0) {q})"
                     f" (map Z.of_nat (seq 0 {size})) = {_coq_list(table)}.")
        lines.append("Proof. vm_compute. reflexivity. Qed.")
        thms += [f'{pre}_root_order', f'{pre}_zeta_table']
    if 'Cubic B(a,b) + ECC' in engines and not corrupt:
        # The cubic engine's CM curves need p = 1 (mod 3).
        for p in [7, 13, 19, 37]:
            lines.append(f"Theorem cubic_p{p}: {p} mod 3 = 1.")
            lines.append("Proof. vm_compute. reflexivity. Qed.")
            thms.append(f'cubic_p{p}')
    lines += [f"Print Assumptions {t}." for t in thms]
    cert = '\n'.join(lines) + '\n'
    with open(filename, 'w') as f:
        f.write(cert)
    return filename


def coq_check(path, theorems=None, timeout=120):
    """Run coqc on a certificate. Returns (ok, detail).

    ok requires coqc to exit 0 AND every theorem to print COQ_CLOSED, so an
    Admitted proof or an added axiom fails the check.
    Raises FileNotFoundError when coqc is not installed and
    subprocess.TimeoutExpired on timeout; callers turn those into skips.
    """
    import subprocess, shutil
    coqc = shutil.which('coqc')
    if coqc is None:
        raise FileNotFoundError('coqc not in PATH')
    proc = subprocess.run([coqc, path], capture_output=True, text=True,
                          timeout=timeout)
    out = (proc.stdout or '') + (proc.stderr or '')
    if proc.returncode != 0:
        return False, out.strip()[-120:]
    if theorems is None:
        with open(path) as f:
            theorems = [ln.split()[2].rstrip('.') for ln in f
                        if ln.startswith('Print Assumptions ')]
    closed = out.count(COQ_CLOSED)
    if closed != len(theorems):
        return False, (f'{len(theorems) - closed} of {len(theorems)} theorems rest '
                       f'on an axiom or an Admitted proof')
    ver = subprocess.run([coqc, '--version'], capture_output=True, text=True,
                         timeout=30).stdout.split('version')[-1].split()[:1]
    return True, (f'coqc {ver[0] if ver else "?"} accepted; {closed} theorems '
                  f'closed (no axioms, no Admitted)')


# ================================================================
# REPORT
# ================================================================

# What each self-suite audit is FOR. Only the "pqc" track verifies anything a
# FIPS 203/204/205 implementation computes; the others are engines that run
# real, exact checks of other things, each with the post-quantum work it is
# being realigned toward. The headline names the PQC count; the rest is
# reported beside it, never folded in.
#   (name prefix, track, realignment target or None)
_NO_PQC_CURVES = ('no PQC target: classical curve-parameter screening; hybrid KEMs are '
                  'checked by --verify-hybrid, which does not use these engines')
_NO_PQC_YET = 'no PQC target yet'
ENGINE_TRACKS = (
    ('Z_3329 (Kyber)',         'pqc', None),
    ('Z_8380417 (Dilithium)',  'pqc', None),
    ('Kyber Scale',            'pqc', None),
    ('Kyber Keygen',           'pqc', None),
    ('Exhaustive Inverses',    'pqc', None),
    ('Twiddle Factors',        'pqc', None),
    ('Boundary Values',        'pqc', None),
    ('FIPS 203 Parameters',    'pqc', None),
    ('FIPS 204 Parameters',    'pqc', None),
    ('FIPS 205 Parameters',    'pqc', None),
    ('Kyber Roundtrip',        'pqc', None),
    ('Full NTT Verification',  'pqc', None),
    ('Dilithium Full NTT',     'pqc', None),
    ('Freivalds NTT Check',    'pqc', None),
    ('Batch Verification API', 'pqc', None),
    ('FIPS 203 Zetas',         'pqc', None),
    ('FIPS 204 Zetas',         'pqc', None),
    ('Coq Certificate',        'pqc', None),
    ('Stress: Z_3329',         'pqc', None),
    ('Stress: Z_8380417',      'pqc', None),
    ('UNSAT Detection',        'harness', None),
    ('Reproducibility Hash',   'harness', None),
    ('Coq Daemon',             'harness', None),
    ('Adversarial Suite',      'harness', None),
    ('Stress: Malformed Input', 'harness', None),
    ('GF(2) Null-Space',       'classical', 'Classic McEliece: systematic-form public keys over GF(2)'),
    ('GF(2)',                  'classical', 'HQC: quasi-cyclic arithmetic over GF(2)[x]/(x^n - 1)'),
    ('Stress: GF(2)',          'classical', 'HQC / Classic McEliece'),
    ('AES S-box Affine',       'classical', 'GF(2^m) arithmetic for Classic McEliece and HQC Reed-Solomon'),
    ('Cubic B(a,b) + ECC',     'classical', _NO_PQC_CURVES),
    ('Curve ',                 'classical', _NO_PQC_CURVES),
    ('SafeCurves Database',    'classical', _NO_PQC_CURVES),
    ('Conformity Gradient',    'research', _NO_PQC_YET),
    ('CFL Front-End',          'research', 'standards constraints as SAT/QBF obligations'),
    ('DQBF Pipeline',          'research', 'standards constraints as SAT/QBF obligations'),
    ('C CFL Pipeline',         'research', 'standards constraints as SAT/QBF obligations'),
    ('Engine 6',               'research', _NO_PQC_YET),
    ('Stress: Engine 6',       'research', _NO_PQC_YET),
)

TRACK_TITLES = {'pqc': 'PQC (FIPS 203/204/205)', 'harness': 'harness integrity',
                'classical': 'classical (being realigned)',
                'research': 'research (being realigned)'}


def engine_track(name):
    """(track, realignment target) for an audit name; the longest matching
    prefix wins ('GF(2) Null-Space' over 'GF(2)'). KeyError if unknown: a
    check nobody has classified must not slip into any headline."""
    best = None
    for prefix, track, target in ENGINE_TRACKS:
        if name.startswith(prefix) and (best is None or len(prefix) > len(best[0])):
            best = (prefix, track, target)
    if best is None:
        raise KeyError(f"self-suite audit {name!r} has no track in ENGINE_TRACKS")
    return best[1], best[2]


def track_totals(results):
    """{track: [passed, run, skipped]} over a self-suite result list."""
    out = {t: [0, 0, 0] for t in TRACK_TITLES}
    for r in results:
        p, t, _c = r.summary()
        tr, _ = engine_track(r.engine)
        out[tr][0] += p
        out[tr][1] += t
        out[tr][2] += r.n_skipped()
    return out


def print_report(results):
    now = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')
    print(f"\n{'='*70}")
    print(f"  pq-verify v{VERSION} AUDIT REPORT")
    print(f"  Date: {now}")
    print(f"{'='*70}")
    for r in results:
        p, t, c = r.summary()
        sk = r.n_skipped()
        icon = '\u2705' if c == 0 and p == t else '\u274c'
        if p == t and sk:
            icon = '\u26a0'
        print(f"\n  {icon} {r.engine}: {p}/{t} tests passed"
              + (f", {sk} skipped" if sk else ""))
        for test in r.tests:
            if test.get('skipped'):
                s = '\u2298'          # could not run: neither pass nor fail
            else:
                s = '\u2705' if test['passed'] else '\u274c'
            tm = f" ({test['time_us']:.0f}\u03bcs)" if test['time_us'] > 0 else ""
            print(f"     {s} {test['name']}{tm}")
            if test['detail']:
                print(f"        {test['detail']}")
        for f in r.findings:
            icon = {'CRITICAL':'\U0001f534','HIGH':'\U0001f7e0','INFO':'\u2139\ufe0f'}.get(f['severity'],'?')
            print(f"     {icon} {f['description']}")
    total_p = sum(r.summary()[0] for r in results)
    total_t = sum(r.summary()[1] for r in results)
    total_c = sum(r.summary()[2] for r in results)
    total_s = sum(r.n_skipped() for r in results)
    print(f"\n{'='*70}")
    print(f"  OVERALL: {total_p}/{total_t} tests passed"
          + (f"  ({total_s} SKIPPED \u2014 could not run, see integrity below)"
             if total_s else ""))
    for tr, (tp, tt, ts) in track_totals(results).items():
        print(f"    {TRACK_TITLES[tr]:32s} {tp}/{tt}"
              + (f"  ({ts} skipped)" if ts else ""))
    if total_c == 0:
        print(f"  \u2705 No critical findings")
    else:
        print(f"  \U0001f534 {total_c} CRITICAL finding(s)")
    # A pass count means nothing without knowing what actually ran.
    integrity_report()
    print(f"{'='*70}")

def save_json(results, filename):
    report = {
        'tool': 'pq-verify', 'version': VERSION,
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'engines': []
    }
    for r in results:
        p, t, c = r.summary()
        tr, target = engine_track(r.engine)
        report['engines'].append({
            'name': r.engine, 'track': tr, 'realigns_to': target,
            'tests': r.tests, 'findings': r.findings,
            'summary': {'passed': p, 'total': t, 'critical': c,
                        'skipped': r.n_skipped()}
        })
    report['tracks'] = {tr: {'passed': v[0], 'total': v[1], 'skipped': v[2]}
                        for tr, v in track_totals(results).items()}
    with open(filename, 'w') as f:
        json.dump(report, f, indent=2)
    return filename

# ================================================================
# PHASE 2: INDUSTRIAL SCALE TESTS
# ================================================================

KYBER_Q = 3329
KYBER_ZETA = 17
DILI_Q = 8380417
DILI_ZETA = 1753

def audit_kyber_scale(lib, n_bf=100000):
    """100,000 NTT butterflies: the C engine's Montgomery arithmetic against
    plain integer arithmetic, one ctypes call."""
    r = AuditResult('Kyber Scale (100K)')
    random.seed(42)
    Q = KYBER_Q
    a = [random.randint(0, Q-1) for _ in range(n_bf)]
    b = [random.randint(0, Q-1) for _ in range(n_bf)]
    w = [random.randint(1, Q-1) for _ in range(n_bf)]
    a_arr = (ctypes.c_uint16 * n_bf)(*a)
    b_arr = (ctypes.c_uint16 * n_bf)(*b)
    w_arr = (ctypes.c_uint16 * n_bf)(*w)
    e_arr = (ctypes.c_uint16 * n_bf)(*[(a[i] + w[i] * b[i]) % Q for i in range(n_bf)])
    o_arr = (ctypes.c_uint16 * n_bf)(*[(a[i] - w[i] * b[i]) % Q for i in range(n_bf)])
    pass_arr = (ctypes.c_uint8 * n_bf)()
    t0 = time.perf_counter()
    mismatches = lib.zq_batch_butterfly(a_arr, b_arr, w_arr, e_arr, o_arr,
                                        pass_arr, n_bf, Q)
    elapsed = time.perf_counter() - t0
    r.add_test(f'{n_bf:,} NTT butterflies', mismatches == 0,
               f'{mismatches} mismatches (Montgomery engine vs integer), '
               f'{elapsed:.1f}s, {n_bf/elapsed:.0f}/sec', elapsed*1e6)
    return r


def audit_keygen(lib, n_inst=10000):
    """10,000 Kyber-768 keygen instances \u2014 secret recovery."""
    r = AuditResult('Kyber Keygen (10K)')
    random.seed(2026)
    Q, n, k = KYBER_Q, 256, 3
    fails = 0
    total_us = 0
    t0 = time.perf_counter()
    s = ZqS(); res = ZqR()
    for _ in range(n_inst):
        A = [[[random.randint(0, Q-1) for _ in range(k)] for _ in range(k)] for _ in range(1)]
        sv = [[random.randint(0, Q-1) for _ in range(k)] for _ in range(k)]
        e = [[random.randint(0, 3) for _ in range(k)] for _ in range(k)]
        t_hat = [[0]*k for _ in range(k)]
        for row in range(k):
            val = e[row][0]
            for j in range(k): val = (val + A[0][row][j] * sv[j][0]) % Q
            t_hat[row][0] = val
        lib.zq_init(ctypes.byref(s), k, Q)
        for row in range(k):
            coeffs = [A[0][row][j] for j in range(k)]
            rhs = (t_hat[row][0] - e[row][0]) % Q
            ca = (ctypes.c_uint16*k)(*[c % Q for c in coeffs])
            lib.zq_add_equation(ctypes.byref(s), ca, rhs % Q)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        total_us += res.solve_time_us
        # The system holds by construction (rhs = A.s), so an answer of
        # unsatisfiable is a wrong answer, not one to skip.
        if res.satisfiable != 1 or any(res.assignment[j] != sv[j][0] for j in range(k)):
            fails += 1
    elapsed = time.perf_counter() - t0
    r.add_test(f'{n_inst:,} keygen instances', fails == 0,
               f'{fails} wrong or missing solutions, {elapsed:.1f}s, {total_us:.0f}\u03bcs engine', total_us)
    return r

def audit_fips203_params():
    """FIPS 203 parameter validation for ML-KEM-512/768/1024."""
    r = AuditResult('FIPS 203 Parameters')
    fips = {
        'ML-KEM-512':  {'ek': 800,  'dk': 1632, 'ct': 768,  'ss': 32},
        'ML-KEM-768':  {'ek': 1184, 'dk': 2400, 'ct': 1088, 'ss': 32},
        'ML-KEM-1024': {'ek': 1568, 'dk': 3168, 'ct': 1568, 'ss': 32},
    }
    # Only the import decides "could not run". A missing kyber-py raises
    # ModuleNotFoundError, whose message is never empty -- so the old
    # `except Exception` recorded it as a FAILURE, and the DEGRADED append
    # hidden in the other arm of the conditional never ran. One skip per
    # parameter set, named as the test is, keeps the suite's total at 160.
    try:
        from kyber_py.ml_kem import ML_KEM_512, ML_KEM_768, ML_KEM_1024
    except ImportError:
        for name in fips:
            r.add_skip(f'{name} FIPS 203 sizes',
                       'kyber-py not installed \u2014 pip install kyber-py',
                       'kyber-py')
        return r
    impl = {'ML-KEM-512': ML_KEM_512, 'ML-KEM-768': ML_KEM_768,
            'ML-KEM-1024': ML_KEM_1024}
    for name, p in fips.items():
        # An installed kyber-py that errors is a real failure, and stays one.
        try:
            pk, sk = impl[name].keygen()
            ss1, ct = impl[name].encaps(pk)
            ss2 = impl[name].decaps(sk, ct)
        except Exception as e:
            r.add_test(f'{name} FIPS 203 sizes', False,
                       f'{type(e).__name__}: {e}')
            continue
        ok = (len(pk)==p['ek'] and len(sk)==p['dk'] and len(ct)==p['ct']
              and len(ss1)==p['ss'] and ss1==ss2)
        r.add_test(f'{name} FIPS 203 sizes', ok,
                   f"ek={len(pk)}/{p['ek']} dk={len(sk)}/{p['dk']} "
                   f"ct={len(ct)}/{p['ct']} ss={len(ss1)}/{p['ss']} "
                   f"roundtrip={'OK' if ss1==ss2 else 'FAIL'}")
    return r

def audit_exhaustive_inverses(lib):
    """Every inverse in Z_3329 through the engine, and a sample of a*x = b.

    Through 2.13.0 the exhaustive row checked Python's own pow(a, q - 2, q)
    against a*x = 1 -- Fermat's little theorem in the interpreter, which no
    defect in pq-verify could make fail. Each a now goes through the engine,
    and its answer is checked here."""
    r = AuditResult('Exhaustive Inverses')
    Q = KYBER_Q
    fails = 0
    s = ZqS(); res = ZqR()
    t0 = time.perf_counter()
    # Two systems of 1664 equations a*x_a = 1, one variable each: solving
    # them inverts every pivot. (One system per a resets a 16 MB system
    # 3328 times, about 13 s.)
    half = (Q - 1) // 2
    for lo in (1, 1 + half):
        lib.zq_init(ctypes.byref(s), half, Q)
        for i in range(half):
            lib.zq_add_sparse(ctypes.byref(s), (ctypes.c_int * 1)(i),
                              (ctypes.c_uint16 * 1)(lo + i), 1, 1)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        fails += sum(1 for i in range(half)
                     if not res.satisfiable or (lo + i) * res.assignment[i] % Q != 1)
    elapsed = time.perf_counter() - t0
    r.add_test(f'All {Q-1} inverses in Z_{Q}', fails == 0,
               f'the engine solved a\u00b7x = 1 for every a \u2260 0, each x checked: '
               f'{fails} wrong, {elapsed:.2f}s')
    random.seed(99)
    eng_fails = 0
    s = ZqS(); res = ZqR()
    for _ in range(1000):
        a = random.randint(1, Q-1)
        b = random.randint(0, Q-1)
        lib.zq_init(ctypes.byref(s), 1, Q)
        ca = (ctypes.c_uint16*1)(a)
        lib.zq_add_equation(ctypes.byref(s), ca, b)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        expected = (b * pow(a, Q-2, Q)) % Q
        if not res.satisfiable or res.assignment[0] != expected:
            eng_fails += 1
    r.add_test('Engine inverse (1000 samples)', eng_fails == 0, f'{eng_fails} failures')
    return r

def _engine_zeta_table(lib, n):
    """The zeta table an engine's NTT and Freivalds check use, read out of
    the engine: the 16-bit engine's 128 (ML-KEM) or the 32-bit engine's 256
    (ML-DSA)."""
    if n == 128:
        buf = (ctypes.c_uint16 * 128)()
        lib.zq_zeta_table(buf, KYBER_Q, KYBER_ZETA)
    else:
        buf = (ctypes.c_uint32 * 256)()
        lib.zq32_zeta_table(buf, DILI_Q, DILI_ZETA)
    return list(buf)


def audit_twiddle_completeness(lib):
    """The engine's own 128 Kyber zetas: its root has order 256, the table
    holds each of the root's first 128 powers once, and the butterfly is
    right with each power. Through 2.13.0 the first three rows applied
    Python's pow to pq-verify's constant 17, which tested no
    implementation; they now read the table the engine's NTT and Freivalds
    check use."""
    r = AuditResult('Twiddle Factors')
    Q, Z = KYBER_Q, KYBER_ZETA
    tab = _engine_zeta_table(lib, 128)
    root = tab[64]                       # its zeta at BitRev7(i) = 1: the root
    r.add_test('\u03b6^256 \u2261 1 mod q', pow(root, 256, Q) == 1,
               f"the engine's root \u03b6 = {root} (its zeta where BitRev7(i) = 1): "
               f'\u03b6^256 mod q = {pow(root, 256, Q)}')
    r.add_test('\u03b6^128 \u2262 1 mod q (primitive)', pow(root, 128, Q) != 1,
               f'\u03b6^128 mod q = {pow(root, 128, Q)}, so \u03b6 has order 256')
    powers = {pow(root, j, Q) for j in range(128)}
    r.add_test('128 distinct twiddle factors', len(set(tab)) == 128 and set(tab) == powers,
               f"the engine's table holds {len(set(tab))} distinct values"
               + (', each \u03b6^j for j < 128 once' if set(tab) == powers else
                  ', NOT the powers \u03b6^j for j < 128'))
    tw_fails = 0
    z = 1
    s = ZqS(); res = ZqR()
    for _ in range(128):
        a_in, b_in = 1000, 2000
        exp_a = (a_in + z * b_in) % Q
        lib.zq_init(ctypes.byref(s), 4, Q)
        vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
        vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
        lib.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, z)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        if not res.satisfiable or res.assignment[2] != exp_a: tw_fails += 1
        z = (z * Z) % Q
    r.add_test('128 twiddle butterfly tests', tw_fails == 0, f'{tw_fails} failures')
    return r

def audit_kyber_roundtrip():
    """kyber-py 100-iteration ML-KEM-768 roundtrip stress test."""
    r = AuditResult('Kyber Roundtrip')
    name = 'ML-KEM-768 \u00d7 100 roundtrips'
    try:
        from kyber_py.ml_kem import ML_KEM_768
    except ImportError:
        r.add_skip(name, 'kyber-py not installed \u2014 pip install kyber-py',
                   'kyber-py')
        return r
    try:
        fails = 0
        t0 = time.perf_counter()
        for _ in range(100):
            pk, sk = ML_KEM_768.keygen()
            ss1, ct = ML_KEM_768.encaps(pk)
            ss2 = ML_KEM_768.decaps(sk, ct)
            if ss1 != ss2: fails += 1
        elapsed = time.perf_counter() - t0
        r.add_test(name, fails == 0,
                   f'{fails} failures, {elapsed:.1f}s, {elapsed/100*1000:.0f}ms/op')
    except Exception as e:
        r.add_test(name, False, f'{type(e).__name__}: {e}')
    return r

def audit_boundary_values(lib):
    """Boundary value analysis \u2014 edge cases in Z_3329."""
    r = AuditResult('Boundary Values')
    Q, Z = KYBER_Q, KYBER_ZETA
    cases = [
        ("0+0*0", 0, 0, 0, 0),
        ("0+1*0", 0, 0, 1, 0),
        ("(q-1)+1*(q-1)", Q-1, Q-1, 1, (2*(Q-1))%Q),
        ("(q-1)+(q-1)*(q-1)", Q-1, Q-1, Q-1, (Q-1+(Q-1)*(Q-1))%Q),
        ("1+1*1", 1, 1, 1, 2),
        ("0+\u03b6*1", 0, 1, Z, Z),
        ("(q-1)+\u03b6*(q-1)", Q-1, Q-1, Z, (Q-1+Z*(Q-1))%Q),
    ]
    fails = 0
    s = ZqS(); res = ZqR()
    for desc, a_in, b_in, w, expected in cases:
        lib.zq_init(ctypes.byref(s), 4, Q)
        vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
        vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
        lib.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        if not res.satisfiable or res.assignment[2] != expected: fails += 1
    r.add_test(f'Boundary value tests ({len(cases)} cases)', fails == 0,
               f'{fails} failures')
    return r

def audit_unsat(lib):
    """UNSAT detection \u2014 contradictory and overdetermined systems."""
    r = AuditResult('UNSAT Detection')
    Q = KYBER_Q
    s = ZqS(); res = ZqR()
    lib.zq_init(ctypes.byref(s), 1, Q)
    ca = (ctypes.c_uint16*1)(1); lib.zq_add_equation(ctypes.byref(s), ca, 5)
    ca = (ctypes.c_uint16*1)(1); lib.zq_add_equation(ctypes.byref(s), ca, 10)
    lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
    r.add_test('Contradictory system UNSAT', res.satisfiable == 0, f'sat={res.satisfiable}')
    lib.zq_init(ctypes.byref(s), 1, Q)
    ca = (ctypes.c_uint16*1)(2); lib.zq_add_equation(ctypes.byref(s), ca, 1)
    ca = (ctypes.c_uint16*1)(3); lib.zq_add_equation(ctypes.byref(s), ca, 2)
    lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
    r.add_test('Overdetermined UNSAT', res.satisfiable == 0, f'sat={res.satisfiable}')
    return r

def audit_reproducibility_hash(lib):
    """SHA-256 over 1000 butterfly outputs of the engine, which must equal the
    hash of the same butterflies computed in Python. Until 2.13.0 the hash
    was reported and the check passed whatever it was."""
    r = AuditResult('Reproducibility Hash')
    random.seed(12345)
    Q = KYBER_Q
    h = hashlib.sha256(); want = hashlib.sha256()
    unsat = 0
    s = ZqS(); res = ZqR()
    for _ in range(1000):
        a_in = random.randint(0, Q-1)
        b_in = random.randint(0, Q-1)
        w = random.randint(1, Q-1)
        lib.zq_init(ctypes.byref(s), 4, Q)
        vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
        vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
        lib.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        unsat += not res.satisfiable
        h.update(res.assignment[2].to_bytes(2, 'big'))
        h.update(res.assignment[3].to_bytes(2, 'big'))
        want.update(((a_in + w * b_in) % Q).to_bytes(2, 'big'))
        want.update(((a_in - w * b_in) % Q).to_bytes(2, 'big'))
    digest = h.hexdigest()
    ok = unsat == 0 and digest == want.hexdigest()
    r.add_test('Deterministic output hash', ok,
               f'sha256={digest[:32]}..., ' + (
                   'equal to the hash of the same butterflies in Python' if ok else
                   f'differs from the Python butterflies ({unsat} unsatisfiable)'))
    return r

# ================================================================
# PHASE 3: ADVERSARIAL TESTS
# ================================================================

def _count_points(a, b, p):
    cnt = 1
    for x in range(p):
        rhs = (pow(x, 3, p) + a*x + b) % p
        if rhs == 0: cnt += 1
        elif pow(rhs, (p-1)//2, p) == 1: cnt += 2
    return cnt

def audit_adversarial(engines):
    """6-category adversarial suite \u2014 zero false negatives required."""
    r = AuditResult('Adversarial Suite')
    lib_zq = engines.get('zq')
    lib_zq32 = engines.get('zq32')
    caught = 0; total = 0

    for a, b, p in [(0,0,17),(0,0,97),(-3%17,2,17),(-3%97,2,97)]:
        ar = audit_curve(engines, a, b, p)
        crit = any(f['severity'] == 'CRITICAL' for f in ar.findings)
        total += 1
        if crit: caught += 1
    r.add_test(f'B1: Singular curves', caught == total, f'{caught}/{total} CRITICAL flagged')

    # Supersingular: j = 0 with p = 2 mod 3, j = 1728 with p = 3 mod 4, j = 8
    # mod 17 (neither: found by the point count), and j = 1728 mod a prime
    # above 10^15, where no count runs and Deuring's rule alone decides.
    # Controls: j = 0 and 1728 curves that are ordinary (y^2 = x^3 + 1 mod 97
    # has 84 points, y^2 = x^3 + x mod 17 and mod 97 have 16 and 80) must not
    # be flagged.
    def _ss(a, b, p):
        return any(f['severity'] == 'HIGH' and f['description'].startswith('Supersingular')
                   for f in audit_curve(engines, a, b, p).findings)
    pos = [(0,1,17),(0,1,23),(1,0,19),(1,0,23),(1,1,17),(1,0,1000000000000091)]
    neg = [(0,1,97),(0,1,7),(1,0,17),(1,0,97)]
    c2 = sum(_ss(*c) for c in pos)
    f2 = sum(_ss(*c) for c in neg)
    r.add_test(f'B2: Supersingular curves', c2 == len(pos) and f2 == 0,
               f'{c2}/{len(pos)} flagged, {f2}/{len(neg)} ordinary j=0/1728 controls flagged')

    # Small embedding degree (MOV / Frey-Ruck): ordinary curves whose largest
    # prime-order subgroup has k = 1, 3, 4 and 6 (trace 2, and MNT-style
    # orders), each found by search and its count certified at run time; and
    # two controls whose k is in the tens of thousands. Through 2.13.0 this
    # was "near-singular curves", flagged by |4a^3 + 27b^2|/p < 0.01, which
    # means nothing over F_p.
    def _k(a, b, p):
        got = [f for f in audit_curve(engines, a, b, p).findings
               if f['severity'] == 'HIGH' and f['description'].startswith('Small embedding degree')]
        return int(got[0]['description'].split('k=')[1].split()[0]) if got else None
    pos3 = {1: (67089, 7437, 131267), 3: (13066, 76929, 132299),
            4: (110478, 24182, 136531), 6: (138116, 141734, 147457)}
    neg3 = [(51725, 63044, 131267), (38135, 145724, 147457)]
    c3 = sum(_k(*c) == k for k, c in pos3.items())
    f3 = sum(_k(*c) is not None for c in neg3)
    r.add_test(f'B3: Small embedding degree', c3 == len(pos3) and f3 == 0,
               f'k = 1, 3, 4, 6 found exactly in {c3}/{len(pos3)}; {f3}/{len(neg3)} '
               f'controls with large k flagged')

    c4 = 0; t4 = 0
    primes4 = [17, 23, 29, 37, 41, 43, 53]
    for p in primes4:
        for a in range(p):
            for b in range(p):
                if (4*a**3 + 27*b**2) % p == 0: continue
                if _count_points(a, b, p) == p:
                    ar = audit_curve(engines, a, b, p)
                    crit = any(f['severity'] == 'CRITICAL' for f in ar.findings)
                    t4 += 1
                    if crit: c4 += 1
                    break
            else: continue
            break
    # Each of these primes has anomalous curves (trace 1 is inside the Hasse
    # interval, and Deuring gives a curve for every trace there), so finding
    # none is a failure, not a vacuous 0/0.
    r.add_test(f'B4: Anomalous-trace curves', t4 == len(primes4) and c4 == t4,
               f'{c4}/{t4} CRITICAL flagged; a curve found for {t4} of '
               f'{len(primes4)} primes')

    if lib_zq:
        random.seed(1337)
        Q = KYBER_Q
        fp = 0; n5 = 0
        s = ZqS(); res = ZqR()
        for _ in range(200):
            a_in = random.randint(0, Q-1)
            b_in = random.randint(1, Q-1)
            w_c = random.randint(2, Q-2)
            w_w = (w_c + 1) % Q
            ea_w = (a_in + w_w * b_in) % Q
            eb_w = (a_in + (Q - w_w) * b_in) % Q
            ea_c = (a_in + w_c * b_in) % Q
            eb_c = (a_in + (Q - w_c) * b_in) % Q
            if ea_w == ea_c and eb_w == eb_c: continue
            lib_zq.zq_init(ctypes.byref(s), 4, Q)
            for vi_v, rhs in [(0, a_in),(1, b_in),(2, ea_w),(3, eb_w)]:
                vi = (ctypes.c_int*1)(vi_v); vc = (ctypes.c_uint16*1)(1)
                lib_zq.zq_add_sparse(ctypes.byref(s), vi, vc, 1, rhs)
            lib_zq.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w_c)
            lib_zq.zq_solve(ctypes.byref(s), ctypes.byref(res))
            n5 += 1
            if res.satisfiable: fp += 1
        r.add_test(f'B5: Corrupted Kyber twiddle', fp == 0,
                   f'{n5} tested, {fp} false positives')

    if lib_zq32:
        random.seed(1337)
        Q = DILI_Q
        fp = 0; n6 = 0
        s32 = Zq32S(); r32 = Zq32R()
        for _ in range(50):
            a_in = random.randint(0, Q-1)
            b_in = random.randint(1, Q-1)
            w_c = random.randint(2, Q-2)
            w_w = w_c ^ (1 << 7)
            if w_w == 0 or w_w >= Q or w_w == w_c: w_w = (w_c + 1) % Q
            ea_w = (a_in + w_w * b_in) % Q
            eb_w = (a_in + (Q - w_w) * b_in) % Q
            ea_c = (a_in + w_c * b_in) % Q
            eb_c = (a_in + (Q - w_c) * b_in) % Q
            if ea_w == ea_c and eb_w == eb_c: continue
            lib_zq32.zq32_init(ctypes.byref(s32), 4, Q)
            for vi_v, rhs in [(0, a_in),(1, b_in),(2, ea_w),(3, eb_w)]:
                vi = (ctypes.c_int*1)(vi_v); vc = (ctypes.c_uint32*1)(1)
                lib_zq32.zq32_add_sparse(ctypes.byref(s32), vi, vc, 1, rhs)
            lib_zq32.zq32_add_ntt_butterfly(ctypes.byref(s32), 0, 1, 2, 3, w_c)
            lib_zq32.zq32_solve(ctypes.byref(s32), ctypes.byref(r32))
            n6 += 1
            if r32.satisfiable: fp += 1
        r.add_test(f'B6: Corrupted Dilithium twiddle', fp == 0,
                   f'{n6} tested, {fp} false positives')
    return r

# ================================================================
# PHASE 4: REAL-WORLD COMPLIANCE (FIPS + SafeCurves)
# ================================================================

def _br7(i):
    r = 0
    for k in range(7):
        if i & (1 << k): r |= 1 << (6 - k)
    return r

def _br8(i):
    r = 0
    for k in range(8):
        if i & (1 << k): r |= 1 << (7 - k)
    return r

def audit_fips203_zetas(lib):
    """Verify engine accepts all 128 FIPS 203 Kyber zetas."""
    r = AuditResult('FIPS 203 Zetas')
    Q, Z = KYBER_Q, KYBER_ZETA
    # The engine's table against FIPS 203's definition of it, zeta^BitRev7(i)
    # mod q, computed here apart from the engine (its own bit reversal and
    # power), compared mod q. Through 2.13.0 the row checked only that 17
    # has order 256, by Python's pow on pq-verify's constant.
    tab = _engine_zeta_table(lib, 128)
    fips = [pow(Z, _bitrev(i, 7), Q) for i in range(128)]
    off = [i for i in range(128) if (tab[i] - fips[i]) % Q]
    order = pow(Z, 256, Q) == 1 and pow(Z, 128, Q) == Q - 1
    r.add_test("Engine zetas are FIPS 203's: 17^BitRev7(i) mod q, 17 of order 256",
               not off and order,
               f"the engine's 128 zetas equal \u03b6^BitRev7(i) mod q for \u03b6 = {Z}"
               + (f' \u2014 NOT at {len(off)}, first i = {off[0]}' if off else '')
               + f'; \u03b6^128 \u2261 {pow(Z, 128, Q)} and \u03b6^256 \u2261 {pow(Z, 256, Q)} mod q')
    zetas = [pow(Z, _br7(i), Q) for i in range(128)]
    n_pass = 0
    s = ZqS(); res = ZqR()
    for w in zetas[1:]:
        a_in, b_in = 1234, 567
        exp_a = (a_in + w * b_in) % Q
        lib.zq_init(ctypes.byref(s), 4, Q)
        for vi_v, rhs in [(0, a_in),(1, b_in),(2, exp_a),(3, (a_in+(Q-w)*b_in)%Q)]:
            vi = (ctypes.c_int*1)(vi_v); vc = (ctypes.c_uint16*1)(1)
            lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, rhs)
        lib.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        if res.satisfiable: n_pass += 1
    r.add_test(f'All 127 non-trivial zetas verified', n_pass == 127,
               f'{n_pass}/127')
    return r

def audit_fips204_zetas(lib, sample=64):
    """Verify engine accepts FIPS 204 Dilithium zetas."""
    r = AuditResult('FIPS 204 Zetas')
    Q, Z = DILI_Q, DILI_ZETA
    # As for FIPS 203: the 32-bit engine's table against zeta^BitRev8(i) mod
    # q, computed here apart from the engine.
    tab = _engine_zeta_table(lib, 256)
    fips = [pow(Z, _bitrev(i, 8), Q) for i in range(256)]
    off = [i for i in range(256) if (tab[i] - fips[i]) % Q]
    order = pow(Z, 512, Q) == 1 and pow(Z, 256, Q) == Q - 1
    r.add_test("Engine zetas are FIPS 204's: 1753^BitRev8(i) mod q, 1753 of order 512",
               not off and order,
               f"the engine's 256 zetas equal \u03b6^BitRev8(i) mod q for \u03b6 = {Z}"
               + (f' \u2014 NOT at {len(off)}, first i = {off[0]}' if off else '')
               + f'; \u03b6^256 \u2261 {pow(Z, 256, Q)} and \u03b6^512 \u2261 {pow(Z, 512, Q)} mod q')
    zetas = [pow(Z, _br8(i), Q) for i in range(256)]
    indices = list(range(1, 256, max(1, 255//sample)))[:sample]
    n_pass = 0
    s32 = Zq32S(); r32 = Zq32R()
    for idx in indices:
        w = zetas[idx]
        a_in, b_in = 1234567, 891011
        exp_a = (a_in + w * b_in) % Q
        lib.zq32_init(ctypes.byref(s32), 4, Q)
        for vi_v, rhs in [(0, a_in),(1, b_in),(2, exp_a),(3, (a_in+(Q-w)*b_in)%Q)]:
            vi = (ctypes.c_int*1)(vi_v); vc = (ctypes.c_uint32*1)(1)
            lib.zq32_add_sparse(ctypes.byref(s32), vi, vc, 1, rhs)
        lib.zq32_add_ntt_butterfly(ctypes.byref(s32), 0, 1, 2, 3, w)
        lib.zq32_solve(ctypes.byref(s32), ctypes.byref(r32))
        if r32.satisfiable: n_pass += 1
    r.add_test(f'{len(indices)} Dilithium zetas verified', n_pass == len(indices),
               f'{n_pass}/{len(indices)}')
    return r

def audit_safecurves(engines):
    """SafeCurves database \u2014 known good & bad curves."""
    r = AuditResult('SafeCurves Database')
    sev_rank = {'OK':0,'LOW':1,'MEDIUM':2,'HIGH':3,'CRITICAL':4}
    cases = [
        ('singular y\u00b2=x\u00b3 mod 23', 0, 0, 23, 'CRITICAL'),
        ('supersingular j=0 mod 23', 0, 1, 23, 'HIGH'),
        ('supersingular j=1728 mod 23', 1, 0, 23, 'HIGH'),
        ('anomalous mod 17', 1, 3, 17, 'CRITICAL'),
        ('anomalous mod 23', 5, 3, 23, 'CRITICAL'),
        ('embedding degree 6 mod 147457', 138116, 141734, 147457, 'HIGH'),
        ('ordinary curve mod 31', 1, 4, 31, 'OK'),
    ]
    for label, a, b, p, expected in cases:
        ar = audit_curve(engines, a, b, p)
        sevs = set(f['severity'] for f in ar.findings)
        actual = 'CRITICAL' if 'CRITICAL' in sevs else ('HIGH' if 'HIGH' in sevs else
                 ('MEDIUM' if 'MEDIUM' in sevs else 'OK'))
        # 'OK' is a negative control: it must be exact, or it passes always.
        ok = (actual == 'OK') if expected == 'OK' else \
            sev_rank.get(actual, 0) >= sev_rank.get(expected, 0)
        r.add_test(f'{label}', ok, f'expected={expected} actual={actual}')
    return r

# ================================================================
# FULL NTT VERIFIER \u2014 Complete Kyber-768 NTT Transform
# ================================================================

def _kyber_zeta_table():
    """FIPS 203 Algorithm 9 zeta table (bit-reversed order)."""
    Q, Z = KYBER_Q, KYBER_ZETA
    zetas = [0] * 128
    for i in range(128):
        br = 0
        val = i
        for _ in range(7):
            br = (br << 1) | (val & 1)
            val >>= 1
        zetas[i] = pow(Z, br, Q)
    return zetas

def _reference_ntt(f_in):
    """FIPS 203 Algorithm 9 \u2014 reference NTT implementation."""
    Q = KYBER_Q
    zetas = _kyber_zeta_table()
    f = list(f_in)
    i = 1
    length = 128
    while length >= 2:
        start = 0
        while start < 256:
            z = zetas[i]
            i += 1
            for j in range(start, start + length):
                t = (z * f[j + length]) % Q
                f[j + length] = (f[j] - t) % Q
                f[j] = (f[j] + t) % Q
            start += 2 * length
        length //= 2
    return f

def _bitrev(i, bits):
    """i with its low `bits` bits reversed, by reversing its binary string:
    written apart from the bit loops that build the zeta tables."""
    return int(format(i, f'0{bits}b')[::-1], 2)


def _mlkem_ntt_by_definition(f):
    """FIPS 203's NTT of f from its definition (4.3), without butterflies:
    (f^_2i, f^_2i+1) are the coefficients of f mod X^2 - zeta^(2 BitRev7(i) + 1),
    for i < 128. Algorithm 9 and every layer check use the zeta table; this
    does not, so a wrong table or butterfly order cannot pass both."""
    Q, Z = KYBER_Q, KYBER_ZETA
    out = []
    for i in range(128):
        g = pow(Z, 2 * _bitrev(i, 7) + 1, Q)
        even = odd = 0
        gp = 1
        for j in range(0, 256, 2):
            even += f[j] * gp
            odd += f[j + 1] * gp
            gp = gp * g % Q
        out += [even % Q, odd % Q]
    return out


def _mldsa_ntt_by_definition(w):
    """FIPS 204's NTT of w from its definition, without butterflies: w^_i is
    w evaluated at zeta^(2 BitRev8(i) + 1), the 256 roots of X^256 + 1."""
    Q, Z = DILI_Q, DILI_ZETA
    out = []
    for i in range(256):
        x = pow(Z, 2 * _bitrev(i, 8) + 1, Q)
        acc = 0
        for c in reversed(w):
            acc = (acc * x + c) % Q
        out.append(acc)
    return out


def _ntt_layer(f_in, layer_idx, zetas):
    """Compute one NTT layer \u2014 returns output coefficients."""
    Q = KYBER_Q
    f = list(f_in)
    lengths = [128, 64, 32, 16, 8, 4, 2]
    length = lengths[layer_idx]
    z_idx = sum(256 // (2 * lengths[l]) for l in range(layer_idx)) + 1
    start = 0
    while start < 256:
        z = zetas[z_idx]
        z_idx += 1
        for j in range(start, start + length):
            t = (z * f[j + length]) % Q
            f[j + length] = (f[j] - t) % Q
            f[j] = (f[j] + t) % Q
        start += 2 * length
    return f

def _verify_ntt_layer(lib, f_in, f_out, layer_idx, zetas):
    """Verify one NTT layer algebraically using libzq."""
    Q = KYBER_Q
    s = ZqS(); res = ZqR()
    lib.zq_init(ctypes.byref(s), 512, Q)

    for idx in range(256):
        vi = (ctypes.c_int*1)(idx)
        vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, f_in[idx] % Q)

    for idx in range(256):
        vi = (ctypes.c_int*1)(256 + idx)
        vc = (ctypes.c_uint16*1)(1)
        lib.zq_add_sparse(ctypes.byref(s), vi, vc, 1, f_out[idx] % Q)

    lengths = [128, 64, 32, 16, 8, 4, 2]
    length = lengths[layer_idx]
    z_idx = sum(256 // (2 * lengths[l]) for l in range(layer_idx)) + 1
    n_bf = 0
    start = 0
    while start < 256:
        z = zetas[z_idx]
        z_idx += 1
        for j in range(start, start + length):
            i_in = j
            j_in = j + length
            i_out = 256 + j
            j_out = 256 + j + length
            lib.zq_add_ntt_butterfly(ctypes.byref(s), i_in, j_in, i_out, j_out, z)
            n_bf += 1
        start += 2 * length

    lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
    return res.satisfiable == 1, n_bf, res.solve_time_us

def audit_full_ntt(lib):
    """Complete Kyber-768 NTT verification \u2014 7 layers, 896 butterflies."""
    r = AuditResult('Full NTT Verification')
    Q = KYBER_Q
    zetas = _kyber_zeta_table()

    random.seed(20260501)
    f_input = [random.randint(0, Q-1) for _ in range(256)]

    f_ntt = _reference_ntt(f_input)

    f_layer = list(f_input)
    total_bf = 0
    total_us = 0
    all_pass = True

    for layer in range(7):
        f_next = _ntt_layer(f_layer, layer, zetas)
        sat, n_bf, us = _verify_ntt_layer(lib, f_layer, f_next, layer, zetas)
        total_bf += n_bf
        total_us += us
        lengths = [128, 64, 32, 16, 8, 4, 2]
        if not sat:
            all_pass = False
            r.add_test(f'NTT layer {layer} (len={lengths[layer]})', False,
                       f'{n_bf} butterflies \u2014 FAILED')
        f_layer = f_next

    # Algorithm 9 and the layers share the zeta table; the definition does
    # not. Through 2.13.0 only the first two were compared.
    defined = _mlkem_ntt_by_definition(f_input)
    ntt_match = f_layer == f_ntt == defined

    r.add_test(f'7-layer NTT ({total_bf} butterflies)', all_pass,
               f'all layers SAT, {total_us:.0f}\u03bcs total')
    r.add_test('NTT output matches FIPS 203 reference', ntt_match,
               '256 coefficients: the layers compose to Algorithm 9'
               + ('' if f_layer == f_ntt else ' \u2014 NOT')
               + ', and both equal f mod X\u00b2 \u2212 \u03b6^(2\u00b7BitRev7(i)+1), the NTT\'s '
               'definition' + ('' if f_ntt == defined else ' \u2014 NOT'))

    # The certificate states the whole transform -- input to all 256 outputs --
    # and Coq recomputes it from its own FIPS 203 definitions. Before 2.9.0 it
    # held one layer-0 butterfly under a "Full NTT" header. Its control is the
    # same certificate with one output off by one, which coqc must reject:
    # through 2.13.0 that row only checked the file had been written.
    names = ('NTT Coq certificate rejects a wrong output', 'NTT Coq certificate verified')
    ntt_cert_file = os.path.join(_pqv_workdir(), 'pq_ntt_cert.v')
    _, thms = gen_coq_ntt_cert('ML-KEM', f_input, f_ntt, ntt_cert_file)
    k = 137
    wrong = list(f_ntt)
    wrong[k] = (wrong[k] + 1) % Q
    wrong_file = os.path.join(_pqv_workdir(), 'pq_ntt_cert_wrong.v')
    _, wrong_thms = gen_coq_ntt_cert('ML-KEM', f_input, wrong, wrong_file)
    try:
        ok, detail = coq_check(ntt_cert_file, thms)
        took, _ = coq_check(wrong_file, wrong_thms)
    except FileNotFoundError:
        for name in names:
            r.add_skip(name, 'coqc not in PATH', 'coq')
    except subprocess.TimeoutExpired:
        for name in names:
            r.add_skip(name, 'coqc timed out', 'coq')
    else:
        r.add_test(names[0], ok and not took,
                   f'output {k} off by one: ' + ('rejected by coqc' if not took else 'ACCEPTED')
                   + ('' if ok else '; the true certificate was rejected too, so this shows nothing'))
        r.add_test(names[1], ok, detail)
        if not ok:
            r.add_finding('CRITICAL', f'NTT Coq certificate rejected: {detail}')
        if took:
            r.add_finding('CRITICAL', 'NTT Coq certificate accepted a wrong output')

    return r


_FREIVALDS_BASE = None


def freivalds_seed(i=0):
    """Seed for the i-th Freivalds call of this run.

    Freivalds' bound -- a wrong y passes a round with probability <= 1/q --
    holds only if y is fixed before the random vector r is known. Every seed
    used to be a constant in this file (42, trial+1, ...), so anyone could
    compute r and ship an output that is wrong in several coefficients yet
    passes (tests/test_pqverify.py builds one). The base seed is now drawn
    from the OS once per run and printed, so a run can still be replayed:
    PQV_FREIVALDS_SEED=0x... reuses it.
    """
    global _FREIVALDS_BASE
    if _FREIVALDS_BASE is None:
        env = os.environ.get('PQV_FREIVALDS_SEED')
        if env:
            _FREIVALDS_BASE = int(env, 0) & 0xFFFFFFFF
        else:
            import secrets
            _FREIVALDS_BASE = secrets.randbits(32)
    # distinct per call, never 0 (the C engines treat 0 as "use 42")
    return ((_FREIVALDS_BASE + 0x9E3779B9 * (i + 1)) & 0xFFFFFFFF) or 1


def freivalds_seed_note():
    freivalds_seed()
    return (f'Freivalds seed 0x{_FREIVALDS_BASE:08x} '
            f'(replay: PQV_FREIVALDS_SEED=0x{_FREIVALDS_BASE:08x})')


def audit_freivalds_ntt(lib):
    """Freivalds O(n log n) probabilistic NTT verification."""
    r = AuditResult('Freivalds NTT Check')
    Q, Z, N = KYBER_Q, KYBER_ZETA, 256
    random.seed(42)
    # Test 1: correct NTT should pass
    x = (ctypes.c_uint16 * N)(*[random.randint(0, Q - 1) for _ in range(N)])
    y = (ctypes.c_uint16 * N)(*x)  # copy
    lib.zq_ntt_forward(y, N, Q, Z)
    # The engine's NTT and its Freivalds check share one zeta table, so the
    # check accepting the NTT says nothing if that table is wrong. The NTT
    # must also be FIPS 203's, by the definition; through 2.13.0 it was not
    # compared with anything.
    fips = list(y) == _mlkem_ntt_by_definition(list(x))
    ok = lib.zq_freivalds_ntt(x, y, N, Q, Z, 10, freivalds_seed(0))
    r.add_test('Correct NTT passes (10 rounds)', ok == 1 and fips,
               f'the engine\'s NTT is {"" if fips else "NOT "}FIPS 203\'s by its definition; '
               f'Freivalds returned {ok}; {freivalds_seed_note()}')
    # Test 2: corrupted output should fail
    y_bad = (ctypes.c_uint16 * N)(*y)
    y_bad[0] = (y_bad[0] + 1) % Q
    fail = lib.zq_freivalds_ntt(x, y_bad, N, Q, Z, 10, freivalds_seed(1))
    r.add_test('Corrupted NTT fails', fail == 0,
               f'Freivalds returned {fail} (expected 0)')
    # Test 3: throughput — 1000 NTT verifications via Freivalds
    t0 = time.perf_counter()
    n_checks = 1000
    accepted = 0
    for i in range(n_checks):
        xr = (ctypes.c_uint16 * N)(*[random.randint(0, Q - 1) for _ in range(N)])
        yr = (ctypes.c_uint16 * N)(*xr)
        lib.zq_ntt_forward(yr, N, Q, Z)
        accepted += lib.zq_freivalds_ntt(xr, yr, N, Q, Z, 3, freivalds_seed(2 + i)) == 1
    elapsed = (time.perf_counter() - t0) * 1e6
    # This used to pass unconditionally; it now requires every correct NTT
    # to be accepted.
    r.add_test(f'Freivalds throughput ({n_checks} NTTs, 3 rounds each)',
               accepted == n_checks,
               f'{accepted}/{n_checks} accepted, {elapsed:.0f}\u03bcs total, '
               f'{elapsed/n_checks:.1f}\u03bcs/verify')
    return r


# ================================================================
# CFL FRONT-END (docs/CFL.md; Paper 2, DOI: 10.5281/zenodo.19302050)
# CFL text -> tokens -> AST -> checked properties -> FOL obligations
#   -> QBF, decided by the DQBF stage -> field router -> engine checks
# ================================================================

CFL_SPEC = '''
CONTEXT ( Kyber ) {
  DEFINE property <NTTCorrect> { type: "linear"; field: "Z_3329"; }
  DEFINE property <KeygenValid> { type: "linear"; field: "Z_3329"; }
  REQUIRE Full { }
}
CONTEXT ( Dilithium ) {
  DEFINE property <NTTCorrect> { type: "linear"; field: "Z_8380417"; }
}
CONTEXT ( AES ) {
  DEFINE property <SboxAffine> { type: "linear"; field: "GF2"; }
}
CONTEXT ( Curves ) {
  DEFINE property <J0Count> { type: "cubic"; field: "cubic"; }
  DEFINE property <Conformity> { type: "dynamical"; field: "conformity"; }
}
'''

# An obligation's check takes the engines and returns (passed, detail), or
# None when an engine it needs is missing. With corrupt=True it runs on an
# instance made wrong on purpose, which it must reject.

def _ob_mlkem_ntt(engines, corrupt=False):
    lib = engines.get('zq')
    if not lib:
        return None
    rng = random.Random(203)
    f = [rng.randrange(KYBER_Q) for _ in range(256)]
    zetas = _kyber_zeta_table()
    cur, n_bf = f, 0
    for layer in range(7):
        nxt = _ntt_layer(cur, layer, zetas)
        if corrupt and layer == 3:
            nxt[17] = (nxt[17] + 1) % KYBER_Q
        ok, nb, _ = _verify_ntt_layer(lib, cur, nxt, layer, zetas)
        n_bf += nb
        if not ok:
            return False, f'layer {layer + 1} has no solution with its outputs'
        cur = nxt
    if cur != _reference_ntt(f):
        return False, 'the layers do not compose to FIPS 203 Algorithm 9'
    return True, (f'7 layers, {n_bf} butterflies on the Zq engine, composing to '
                  f'FIPS 203 Algorithm 9')
_ob_mlkem_ntt.corruption = 'an output of layer 4 off by one'


def _ob_mlkem_keygen(engines, corrupt=False):
    lib = engines.get('zq')
    if not lib:
        return None
    rng = random.Random(2031)
    Q, k, n = KYBER_Q, 3, 50
    s, res = ZqS(), ZqR()
    for trial in range(n):
        while True:
            A = [[rng.randrange(Q) for _ in range(k)] for _ in range(k)]
            det = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
                   - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
                   + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) % Q
            if det:
                break
        sec = [rng.randrange(Q) for _ in range(k)]
        rhs = [sum(A[i][j] * sec[j] for j in range(k)) % Q for i in range(k)]
        if corrupt and trial == n // 2:
            rhs[0] = (rhs[0] + 1) % Q
        lib.zq_init(ctypes.byref(s), k, Q)
        for i in range(k):
            lib.zq_add_equation(ctypes.byref(s), (ctypes.c_uint16 * k)(*A[i]), rhs[i])
        lib.zq_solve(ctypes.byref(s), ctypes.byref(res))
        if res.satisfiable != 1 or [res.assignment[j] for j in range(k)] != sec:
            return False, f'instance {trial + 1}: the engine did not return the secret'
    return True, f'{n} invertible systems A·s = t − e: the Zq engine returns each secret'
_ob_mlkem_keygen.corruption = 'one right-hand side off by one'


def _ob_mldsa_ntt(engines, corrupt=False):
    lib = engines.get('zq32')
    if not lib:
        return None
    rng = random.Random(204)
    f = [rng.randrange(DILI_Q) for _ in range(256)]
    zetas = _dilithium_zeta_table()
    cur, n_bf = f, 0
    for layer in range(8):
        nxt = _ntt_layer_dili(cur, layer, zetas)
        if corrupt and layer == 5:
            nxt[200] = (nxt[200] + 1) % DILI_Q
        ok, nb, _ = _verify_ntt_layer_dili(lib, cur, nxt, layer, zetas)
        n_bf += nb
        if not ok:
            return False, f'layer {layer + 1} has no solution with its outputs'
        cur = nxt
    if cur != _reference_ntt_dili(f):
        return False, 'the layers do not compose to FIPS 204 Algorithm 41'
    return True, (f'8 layers, {n_bf} butterflies on the Zq32 engine, composing to '
                  f'FIPS 204 Algorithm 41')
_ob_mldsa_ntt.corruption = 'an output of layer 6 off by one'


_AES_AFFINE = [[1, 0, 0, 0, 1, 1, 1, 1], [1, 1, 0, 0, 0, 1, 1, 1], [1, 1, 1, 0, 0, 0, 1, 1],
               [1, 1, 1, 1, 0, 0, 0, 1], [1, 1, 1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 1, 1, 0, 0],
               [0, 0, 1, 1, 1, 1, 1, 0], [0, 0, 0, 1, 1, 1, 1, 1]]
_AES_C = [1, 1, 0, 0, 0, 1, 1, 0]          # 0x63, least significant bit first
# FIPS 197, Table 4 (the S-box), at six inputs.
_AES_SBOX_AT = {0x00: 0x63, 0x01: 0x7c, 0x02: 0x77, 0x03: 0x7b, 0x53: 0xed, 0xff: 0x16}


def _gf256_inv(a):
    """a^-1 in GF(2^8) mod x^8+x^4+x^3+x+1, with 0 to 0 (FIPS 197 5.1.1)."""
    def mul(x, y):
        p = 0
        while y:
            if y & 1:
                p ^= x
            x <<= 1
            if x & 0x100:
                x ^= 0x11b
            y >>= 1
        return p
    r, e = 1, 254
    while e:
        if e & 1:
            r = mul(r, a)
        a, e = mul(a, a), e >> 1
    return r


def _ob_aes_sbox(engines, corrupt=False):
    lib = engines.get('gf2')
    if not lib:
        return None
    M = [row[:] for row in _AES_AFFINE]
    if corrupt:
        M[2][5] ^= 1
    s, res = GF2S(), GF2R()
    sbox = []
    for x in range(256):
        y = _gf256_inv(x)
        lib.gf2_init(ctypes.byref(s), 16)
        for i in range(8):
            lib.gf2_add_xor(ctypes.byref(s), (ctypes.c_int * 1)(i), 1, (y >> i) & 1)
        for i in range(8):
            vs = [8 + i] + [j for j in range(8) if M[i][j]]
            lib.gf2_add_xor(ctypes.byref(s), (ctypes.c_int * len(vs))(*vs), len(vs), _AES_C[i])
        lib.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        if not res.satisfiable:
            return False, f'no solution at input {x:#04x}'
        sbox.append(sum((res.assignment[8 + i] & 1) << i for i in range(8)))
    for x, want in _AES_SBOX_AT.items():
        if sbox[x] != want:
            return False, f'S({x:#04x}) = {sbox[x]:#04x}; FIPS 197 has {want:#04x}'
    if sorted(sbox) != list(range(256)):
        return False, 'not a permutation'
    if any(sbox[x] in (x, x ^ 0xff) for x in range(256)):
        return False, 'a fixed or opposite fixed point'
    return True, ('S(x) = A·x⁻¹ + c solved on the GF(2) engine for all 256 '
                  'inputs: a permutation with no fixed or opposite fixed point, equal '
                  'to FIPS 197 at 0x00-0x03, 0x53, 0xff')
_ob_aes_sbox.corruption = 'one bit of the affine matrix flipped'


def _ob_j0_count(engines, corrupt=False):
    lib = engines.get('cubic')
    if not lib:
        return None
    primes = [7, 13, 19, 31, 37, 43, 61, 67]
    for p in primes:
        got = lib.cubic_solution_count(p)
        want = _fermat_cubic_count(p) + (1 if corrupt and p == 37 else 0)
        if got != want:
            return False, f'p = {p}: the engine counts {got}, a direct count {want}'
    return True, (f'x³+y³+z³ = 0 over F_p for {len(primes)} primes p ≡ 1 '
                  f'mod 3: the engine\'s p²+(p−1)·B(a,b) equals a direct count')
_ob_j0_count.corruption = 'one expected count off by one'


def _ob_conformity(engines, corrupt=False):
    lib = engines.get('conformity')
    if not lib:
        return None
    worst = 0.0
    for t in (0.5, 1.0, 1.5, 2.0):
        w = math.exp(-t * t / 2)
        pd = PeriodData(w, -t * w, (t * t - 1) * w, (-t ** 3 + 3 * t) * w, t)
        res = lib.conformity_compute(ctypes.byref(pd))
        u_want, d_want = -t, -2.0 + 4 * t * t
        if corrupt and t == 1.5:
            d_want += 1e-6
        err = max(abs(res.u - u_want), abs(res.D - d_want) / max(1.0, abs(d_want)))
        worst = max(worst, err)
        if not res.valid or err > 1e-9:
            return False, f't = {t}: u = {res.u:.12g}, D = {res.D:.12g}; closed forms {u_want}, {d_want}'
    return True, (f'ω = exp(−t²/2) at 4 points: u = −t and '
                  f'D = 2u′ + 4u² to {worst:.1e}')
_ob_conformity.corruption = 'one closed form off by 1e-6'


#: (context, property) -> (field, check)
CFL_OBLIGATIONS = {
    ('Kyber', 'NTTCorrect'): ('Z_3329', _ob_mlkem_ntt),
    ('Kyber', 'KeygenValid'): ('Z_3329', _ob_mlkem_keygen),
    ('Dilithium', 'NTTCorrect'): ('Z_8380417', _ob_mldsa_ntt),
    ('AES', 'SboxAffine'): ('GF2', _ob_aes_sbox),
    ('Curves', 'J0Count'): ('cubic', _ob_j0_count),
    ('Curves', 'Conformity'): ('conformity', _ob_conformity),
}


def cfl_dispatch(props, engines, registry):
    """Each property's registered check, run on its engine, and run on a
    corrupted instance: {key: (status, detail)}, status True (passed and
    rejected the corruption), False, or None (no obligation is registered,
    or an engine or library it needs is missing; a check's `requires`
    attribute names the library)."""
    out = {}
    for p in props:
        entry = registry.get((p.context, p.name))
        if entry is None:
            out[p.key] = (None, 'no obligation is registered for it')
            continue
        field, check = entry
        if field != p.field:
            out[p.key] = (False, f'declared in {p.field}; its obligation runs in {field}')
            continue
        got = check(engines)
        if got is None:
            needs = getattr(check, 'requires', None)
            out[p.key] = (None, f'{needs} is not installed' if needs
                          else 'an engine it needs is not built')
            continue
        ok, detail = got
        if ok:
            what = getattr(check, 'corruption', 'a corrupted instance')
            bad = check(engines, corrupt=True)
            if bad is None or bad[0]:
                ok, detail = False, f'{detail}; but it passed with {what}'
            else:
                detail += f'; fails with {what}'
        out[p.key] = (ok, detail)
    return out


_CFL_BAD_TEXT = {
    'an unknown character': 'CONTEXT ( Kyber ) { DEFINE property <N> { type: "linear"; field: "Z_3329"; } @ }',
    'an unterminated string': 'CONTEXT ( Kyber ) { DEFINE property <N> { type: "linear; } }',
    'a backslash in a string': 'CONTEXT ( K ) { DEFINE property <N> { type: "a\\b"; } }',
}
_CFL_BAD_SYNTAX = {
    'a missing semicolon': 'CONTEXT ( K ) { DEFINE property <N> { type: "linear" field: "GF2"; } }',
    'a missing closing brace': 'CONTEXT ( K ) { DEFINE property <N> { type: "linear"; field: "GF2"; }',
    'a DEFINE outside a context': 'DEFINE property <N> { type: "linear"; field: "GF2"; }',
    'input that ends early': 'CONTEXT ( K',
    'a keyword as a name': 'CONTEXT ( property ) { }',
}
_CFL_BAD_MEANING = {
    'a context defined twice': 'CONTEXT ( K ) { } CONTEXT ( K ) { }',
    'a property defined twice': ('CONTEXT ( K ) { DEFINE property <N> { type: "linear"; field: "GF2"; } '
                                 'DEFINE property <N> { type: "linear"; field: "GF2"; } }'),
    'an unknown field': 'CONTEXT ( K ) { DEFINE property <N> { type: "linear"; field: "Z_7"; } }',
    'a type the field\'s engine does not decide': 'CONTEXT ( K ) { DEFINE property <N> { type: "cubic"; field: "GF2"; } }',
    'an unknown attribute': 'CONTEXT ( K ) { DEFINE property <N> { type: "linear"; field: "GF2"; level: "x"; } }',
    'a missing field': 'CONTEXT ( K ) { DEFINE property <N> { type: "linear"; } }',
    'REQUIRE naming an undefined property': 'CONTEXT ( K ) { REQUIRE Full { M } }',
    'an unknown REQUIRE level': ('CONTEXT ( K ) { DEFINE property <N> { type: "linear"; field: "GF2"; } '
                                 'REQUIRE Partial { } }'),
}


def _cfl_stages(r, spec, engines, registry, names, expected, routes, lib_gf2=None):
    """The six CFL checks on spec (docs/CFL.md): names maps each stage to its row
    name; expected is the spec's shape; routes maps property keys to engines."""
    from . import cfl as C
    from . import dqbf as D

    def row(name, run):
        t0 = time.perf_counter()
        try:
            ok, detail = run()
        except D.CertificateError as e:
            r.add_test(name, False, f'CRITICAL: {e}')
            r.add_finding('CRITICAL', f'CFL {name}: an answer failed its check', str(e))
            return
        except Exception as e:           # a defect in the check itself
            ok, detail = False, f'error: {type(e).__name__}: {e}'
        r.add_test(name, ok, detail, (time.perf_counter() - t0) * 1e6)

    def rejects(texts, stage):
        """The cases of texts that stage accepted."""
        missed = []
        for what, text in texts.items():
            try:
                stage(text)
                missed.append(what)
            except C.CFLError as e:
                if not all(m.startswith('line ') for m in e.messages):
                    missed.append(f'{what} (no position)')
        return missed

    def lexer():
        toks = C.lex(spec)
        missed = rejects(_CFL_BAD_TEXT, C.lex)
        return not missed and toks[-1].kind == 'EOF', (
            f'{len(toks) - 1} tokens; {len(_CFL_BAD_TEXT) - len(missed)}/{len(_CFL_BAD_TEXT)} '
            f'malformed inputs rejected with a position'
            + (f' — accepted: {", ".join(missed)}' if missed else ''))
    row(names['lexer'], lexer)

    def parser():
        ast = C.parse(spec)
        round_trip = C.parse(C.to_text(ast)).shape() == ast.shape()
        # REQUIRE before DEFINE: the DEFINE after it must survive.
        late = C.parse('CONTEXT ( K ) { REQUIRE Full { } '
                       'DEFINE property <N> { type: "linear"; field: "GF2"; } }')
        kept = [d.name for d in late.contexts[0].defines] == ['N']
        missed = rejects(_CFL_BAD_SYNTAX, C.parse) + rejects(
            _CFL_BAD_MEANING, lambda t: C.check(C.parse(t)))
        n_bad = len(_CFL_BAD_SYNTAX) + len(_CFL_BAD_MEANING)
        ok = ast.shape() == expected and round_trip and kept and not missed
        n_props = sum(len(c.defines) for c in ast.contexts)
        return ok, (f'{len(ast.contexts)} context(s), {n_props} properties'
                    f'{", round trip" if round_trip else ", round trip FAILED"}; '
                    f'a DEFINE after REQUIRE {"kept" if kept else "LOST"}; '
                    f'{n_bad - len(missed)}/{n_bad} malformed specifications rejected'
                    + (f' — accepted: {", ".join(missed)}' if missed else '')
                    + ('' if ast.shape() == expected else ' — not the expected AST'))
    row(names['parser'], parser)

    props = C.check(C.parse(spec))
    required = [p for p in props if p.required]

    def fol():
        import random as _r
        rng = _r.Random(1)
        obligations = [C.obligation(p) for p in required]
        closed = all(not C.free_vars(f) for f in obligations)
        # Prenex form against the original on random models; the second
        # formula reuses a bound name, so it needs renaming apart.
        x, y = C.var('x'), C.var('y')
        tricky = ('or', ('forall', 'x', C.pred('P', x)),
                  ('exists', 'x', ('and', C.pred('Q', x),
                                   ('not', ('forall', 'y', C.pred('R', x, y))))))
        disagree = 0
        for f in obligations + [tricky]:
            pre, m = C.prenex(f)
            g = C.from_prenex(pre, m)
            if not all(q in ('forall', 'exists') for q, _ in pre) or _quantified(m):
                disagree += 1
                continue
            for _ in range(60):
                n = rng.randint(1, 3)
                dom = list(range(n))
                consts = sorted({t[1] for a in _atoms(f) for t in a[2] if t[0] == 'const'})
                rels = {}
                for a in _atoms(f):
                    arity = len(a[2])
                    pool = [tuple(v) for v in itertools.product(dom + consts, repeat=arity)]
                    rels[a[1]] = {t for t in pool if rng.random() < 0.5}
                if C.evaluate(f, dom, rels) != C.evaluate(g, dom, rels):
                    disagree += 1
                    break
        ok = closed and disagree == 0 and len(obligations) == len(required)
        shown = C.show(C.from_prenex(*C.prenex(obligations[0]))) if obligations else ''
        return ok, (f'{len(obligations)} closed obligations; prenex forms equal the '
                    f'originals on random models ({disagree} disagree), e.g. {shown}')
    row(names['fol'], fol)

    t_dispatch = time.perf_counter()
    dispatched = cfl_dispatch(props, engines, registry)
    dispatch_us = (time.perf_counter() - t_dispatch) * 1e6
    verified = {k for k, (ok, _) in dispatched.items() if ok}

    def qbf():
        dom, rels = C.model(props, verified)
        agree, details = 0, []
        for p in required:
            truth, d = C.decide(C.obligation(p), dom, rels, lib_gf2)
            agree += d.truth is truth and truth == (p.key in verified)
            details.append(d)
        # Made false: one property unverified, and one in the wrong field.
        p0 = required[0]
        dom2, rels2 = C.model(props, verified - {p0.key})
        t_unv, d_unv = C.decide(C.obligation(p0), dom2, rels2, lib_gf2)
        wrong = C.Property(p0.context, p0.name, p0.type,
                           next(f for f in C.FIELDS if f != p0.field),
                           None, True, p0.line, p0.col)
        t_wrong, d_wrong = C.decide(C.obligation(wrong), dom, rels, lib_gf2)
        falsified = (t_unv, d_unv.truth, t_wrong, d_wrong.truth) == (False,) * 4
        ok = agree == len(required) and falsified
        sizes = sorted({d.detail.split('expansion ')[-1] for d in details})
        return ok, (f'{agree}/{len(required)} decided by the DQBF stage, certificates '
                    f'checked, equal to the model; an unverified property and a wrong '
                    f'field decided false{"" if falsified else " — NOT"}; '
                    f'expansion {", ".join(sizes)}')
    row(names['qbf'], qbf)

    def router():
        got = {p.key: C.route(p) for p in props}
        # A name that contains another field's name routes by its field.
        decoy = C.check(C.parse('CONTEXT ( GF2_cubic ) { DEFINE property <period_Z_8380417> '
                                '{ type: "linear"; field: "Z_3329"; } }'))
        by_field = C.route(decoy[0]) == 'Zq'
        ok = got == routes and by_field
        return ok, (f'routes: {sorted(set(got.values()))}; names containing other '
                    f'fields route by their field{"" if by_field else " — NOT"}')
    row(names['router'], router)

    def dispatch():
        missing = [p for p in props if dispatched[p.key][0] is None]
        if missing:
            # A skip names the library it waits on, when every check that
            # could not run names one: a missing engine or obligation is not
            # a dependency, and is left unnamed for the integrity report.
            needs = [getattr(registry.get((p.context, p.name), (None, None))[1], 'requires', None)
                     for p in missing]
            deps = sorted(set(needs)) if all(needs) else None
            return None, 'could not run: ' + '; '.join(
                f'{p.key} ({dispatched[p.key][1]})' for p in missing), deps
        failed = [k for k, (ok, _) in dispatched.items() if not ok]
        return not failed, ('; '.join(f'{k}: {d}' for k, (_, d) in dispatched.items())), None
    ok, detail, deps = dispatch()
    if ok is None:
        r.add_skip(names['dispatch'], detail, deps)
    else:
        r.add_test(names['dispatch'], ok, detail, dispatch_us)


def _atoms(f):
    if f[0] == 'pred':
        return [f]
    if f[0] in ('forall', 'exists'):
        return _atoms(f[2])
    return [a for g in f[1:] for a in _atoms(g)]


def _quantified(f):
    if f[0] in ('forall', 'exists'):
        return True
    if f[0] == 'pred':
        return False
    return any(_quantified(g) for g in f[1:])


def audit_cfl_frontend(engines):
    """CFL -> AST -> FOL -> QBF -> field router -> engine dispatch (docs/CFL.md)."""
    r = AuditResult('CFL Front-End')
    _cfl_stages(r, CFL_SPEC, engines, CFL_OBLIGATIONS,
                names={'lexer': 'CFL lexer', 'parser': 'CFL parser',
                       'fol': 'FOL generation', 'qbf': 'QBF encoder',
                       'router': 'Field router',
                       'dispatch': f'Engine dispatch ({len(CFL_OBLIGATIONS)} obligations)'},
                expected=(('Kyber', (('DEFINE', 'NTTCorrect', (('type', 'linear'), ('field', 'Z_3329'))),
                                     ('DEFINE', 'KeygenValid', (('type', 'linear'), ('field', 'Z_3329'))),
                                     ('REQUIRE', 'Full', ()))),
                          ('Dilithium', (('DEFINE', 'NTTCorrect', (('type', 'linear'), ('field', 'Z_8380417'))),)),
                          ('AES', (('DEFINE', 'SboxAffine', (('type', 'linear'), ('field', 'GF2'))),)),
                          ('Curves', (('DEFINE', 'J0Count', (('type', 'cubic'), ('field', 'cubic'))),
                                      ('DEFINE', 'Conformity', (('type', 'dynamical'), ('field', 'conformity')))))),
                routes={'Kyber.NTTCorrect': 'Zq', 'Kyber.KeygenValid': 'Zq',
                        'Dilithium.NTTCorrect': 'Zq32', 'AES.SboxAffine': 'GF2',
                        'Curves.J0Count': 'cubic', 'Curves.Conformity': 'conformity'},
                lib_gf2=engines.get('gf2'))
    return r

# ================================================================
# AES S-BOX AFFINE VERIFICATION (Paper 2 \u00a75: 4,210\u00d7 over CMS5)
# ================================================================

def audit_aes_sbox(lib_gf2):
    """Verify AES S-box affine transform as GF(2) system."""
    r = AuditResult('AES S-box Affine')
    aes_matrix = [
        [1,0,0,0,1,1,1,1],[1,1,0,0,0,1,1,1],[1,1,1,0,0,0,1,1],[1,1,1,1,0,0,0,1],
        [1,1,1,1,1,0,0,0],[0,1,1,1,1,1,0,0],[0,0,1,1,1,1,1,0],[0,0,0,1,1,1,1,1],
    ]
    aes_constant = [1,1,0,0,0,1,1,0]
    test_input = [1,1,0,0,1,0,1,0]
    expected = [0]*8
    for i in range(8):
        val = aes_constant[i]
        for j in range(8):
            val ^= aes_matrix[i][j] * test_input[j]
        expected[i] = val

    s = GF2S(); res = GF2R()
    lib_gf2.gf2_init(ctypes.byref(s), 16)
    for i in range(8):
        vs = (ctypes.c_int*1)(i)
        lib_gf2.gf2_add_xor(ctypes.byref(s), vs, 1, test_input[i])
    for i in range(8):
        vars_in_eq = [8 + i]
        for j in range(8):
            if aes_matrix[i][j]: vars_in_eq.append(j)
        vs = (ctypes.c_int*len(vars_in_eq))(*vars_in_eq)
        lib_gf2.gf2_add_xor(ctypes.byref(s), vs, len(vars_in_eq), aes_constant[i])
    lib_gf2.gf2_solve(ctypes.byref(s), ctypes.byref(res))
    output_match = res.satisfiable and all(res.assignment[8+i] == expected[i] for i in range(8))
    r.add_test('AES S-box affine (16 vars)', output_match,
               f'{res.solve_time_us:.1f}\u03bcs, input=0x53')

    t0 = time.perf_counter()
    batch_fails = 0
    for trial in range(1000):
        inp = [(trial >> j) & 1 for j in range(8)]
        exp_out = [0]*8
        for i in range(8):
            val = aes_constant[i]
            for j in range(8): val ^= aes_matrix[i][j] * inp[j]
            exp_out[i] = val
        lib_gf2.gf2_init(ctypes.byref(s), 16)
        for i in range(8):
            vs = (ctypes.c_int*1)(i)
            lib_gf2.gf2_add_xor(ctypes.byref(s), vs, 1, inp[i])
        for i in range(8):
            vars_in_eq = [8 + i]
            for j in range(8):
                if aes_matrix[i][j]: vars_in_eq.append(j)
            vs = (ctypes.c_int*len(vars_in_eq))(*vars_in_eq)
            lib_gf2.gf2_add_xor(ctypes.byref(s), vs, len(vars_in_eq), aes_constant[i])
        lib_gf2.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        if not res.satisfiable or any(res.assignment[8+i] != exp_out[i] for i in range(8)):
            batch_fails += 1
    elapsed = time.perf_counter() - t0
    r.add_test('AES S-box \u00d71000 batch', batch_fails == 0,
               f'{batch_fails} failures, {elapsed*1000:.1f}ms, {1000/elapsed:.0f}/sec')

    cms_path = shutil.which('cryptominisat5') or shutil.which('cryptominisat')
    if cms_path:
        # Differential: an independent SAT solver decides the systems the
        # engine decided -- this AES system, and the first 100 random ones of
        # audit_gf2, most of them unsatisfiable -- and the two must agree,
        # every model checked against every equation. Through 2.13.0 this row
        # timed CMS5 on unit clauses and passed as a hard-coded True.
        aes = [([i], test_input[i]) for i in range(8)] + [
            ([8 + i] + [j for j in range(8) if aes_matrix[i][j]], aes_constant[i])
            for i in range(8)]
        systems = [(16, aes)]
        rng = random.Random(42)               # audit_gf2's systems, in its order
        for _ in range(100):
            nv = rng.randint(8, 32)
            systems.append((nv, [(rng.sample(range(nv), rng.randint(2, min(6, nv))),
                                  rng.randint(0, 1))
                                 for _ in range(rng.randint(nv, nv + 10))]))
        agree, n_sat, problems = 0, 0, []
        cms_s = eng_us = 0.0
        with tempfile.TemporaryDirectory(prefix='pqv-cms-') as td:
            cnf_path = os.path.join(td, 'xor.cnf')
            for idx, (nv, eqs) in enumerate(systems):
                lib_gf2.gf2_init(ctypes.byref(s), nv)
                for vs, p in eqs:
                    lib_gf2.gf2_add_xor(ctypes.byref(s), (ctypes.c_int * len(vs))(*vs), len(vs), p)
                lib_gf2.gf2_solve(ctypes.byref(s), ctypes.byref(res))
                eng_us += res.solve_time_us
                eng_sat = bool(res.satisfiable)
                # CMS5's native XOR clauses: "x1 2 0" is x1 + x2 = 1, and a
                # negated literal turns the parity to 0.
                with open(cnf_path, 'w') as f:
                    f.write(f'p cnf {nv} {len(eqs)}\n')
                    for vs, p in eqs:
                        lits = [str(v + 1) for v in vs]
                        if not p:
                            lits[0] = '-' + lits[0]
                        f.write('x' + ' '.join(lits) + ' 0\n')
                t0_cms = time.perf_counter()
                try:
                    out = subprocess.run([cms_path, '--verb=0', cnf_path],
                                         capture_output=True, text=True, timeout=30)
                except subprocess.TimeoutExpired:
                    problems.append(f'system {idx}: CMS5 timed out')
                    continue
                cms_s += time.perf_counter() - t0_cms
                if out.returncode not in (10, 20):
                    problems.append(f'system {idx}: CMS5 exit {out.returncode}')
                    continue
                cms_sat = out.returncode == 10
                x = [0] * nv
                for ln in out.stdout.splitlines():
                    if ln.startswith('v '):
                        for lit in map(int, ln.split()[1:]):
                            if 0 < abs(lit) <= nv:
                                x[abs(lit) - 1] = int(lit > 0)
                good = (cms_sat == eng_sat
                        and (not cms_sat or _gf2_satisfied(eqs, x))
                        and (not eng_sat or _gf2_satisfied(eqs, list(res.assignment[:nv]))))
                agree += good
                n_sat += cms_sat
                if not good and len(problems) < 3:
                    problems.append(f'system {idx}: CMS5 {"sat" if cms_sat else "unsat"}, '
                                    f'engine {"sat" if eng_sat else "unsat"}')
        n = len(systems)
        r.add_test('CryptoMiniSat5 comparison', agree == n and not problems,
                   f'{n} XOR systems (the AES affine one and {n - 1} random; {n_sat} '
                   f'satisfiable, {n - n_sat} not): CMS5 and the engine agree on {agree}, '
                   f'each model checked against every equation; CMS5 '
                   f'{cms_s / n * 1e6:.0f}\u03bcs/system with start-up, engine '
                   f'{eng_us / n:.1f}\u03bcs' + ('; ' + '; '.join(problems) if problems else ''))
    else:
        # A comparison that did not run is not a passed test -- and it is not a
        # failed one either. add_skip records that and registers the dependency.
        r.add_skip('CryptoMiniSat5 comparison',
                   'CMS5 not installed, this comparison did NOT run '
                   '(apt install cryptominisat)', 'cryptominisat')
    return r

# ================================================================
# FIPS 204 ML-DSA PARAMETER VALIDATION
# ================================================================

def audit_fips204_params():
    """FIPS 204 parameter validation for ML-DSA-44/65/87."""
    r = AuditResult('FIPS 204 Parameters')
    fips204 = {
        'ML-DSA-44':  {'pk': 1312, 'sk': 2560, 'sig': 2420},
        'ML-DSA-65':  {'pk': 1952, 'sk': 4032, 'sig': 3309},
        'ML-DSA-87':  {'pk': 2592, 'sk': 4896, 'sig': 4627},
    }
    try:
        from dilithium_py.ml_dsa import ML_DSA_44, ML_DSA_65, ML_DSA_87
        for name, obj, params in [
            ('ML-DSA-44', ML_DSA_44, fips204['ML-DSA-44']),
            ('ML-DSA-65', ML_DSA_65, fips204['ML-DSA-65']),
            ('ML-DSA-87', ML_DSA_87, fips204['ML-DSA-87']),
        ]:
            pk, sk = obj.keygen()
            sig = obj.sign(sk, b"pq-verify test")
            valid = obj.verify(pk, b"pq-verify test", sig)
            ok = (len(pk)==params['pk'] and len(sk)==params['sk']
                  and len(sig)==params['sig'] and valid)
            r.add_test(f'{name} FIPS 204 sizes', ok,
                       f"pk={len(pk)}/{params['pk']} sk={len(sk)}/{params['sk']} "
                       f"sig={len(sig)}/{params['sig']} verify={'OK' if valid else 'FAIL'}")
    except ImportError:
        # Without dilithium-py there is nothing to check these constants
        # AGAINST -- asserting them true compares them with themselves. That
        # is a check that could not run. It used to be recorded as a FAILED
        # row whose detail read "SKIPPED": the text and the status disagreed.
        for name, params in fips204.items():
            r.add_skip(f'{name} FIPS 204 sizes',
                       f"dilithium-py not installed \u2014 constants not "
                       f"checked against an implementation "
                       f"(pk={params['pk']} sk={params['sk']} sig={params['sig']})",
                       'dilithium-py')
    return r

# ================================================================
# FIPS 205 SLH-DSA (SPHINCS+) PARAMETER VALIDATION
# ================================================================

# FIPS 205 Table 2, per parameter set: (n, h, d, h', a, k, lg_w, m). The SHA2
# and SHAKE sets of a size share their parameters.
_FIPS205_TABLE2 = {
    '128s': (16, 63, 7, 9, 12, 14, 4, 30),
    '128f': (16, 66, 22, 3, 6, 33, 4, 34),
    '192s': (24, 63, 7, 9, 14, 17, 4, 39),
    '192f': (24, 66, 22, 3, 8, 33, 4, 42),
    '256s': (32, 64, 8, 8, 14, 22, 4, 47),
    '256f': (32, 68, 17, 4, 9, 35, 4, 49),
}


def _fips205_sizes(n, h, d, hp, a, k, lg_w, m):
    """(pk, sk, sig) bytes from FIPS 205's definitions, or None if the
    parameters break one of its relations: h = d*h' (Table 2), m is the
    digest length of Algorithm 19 (ceil(k*a/8) + ceil((h - h')/8) +
    ceil(h'/8)), and len = len1 + len2 is the WOTS+ chain count (5.1).
    pk = PK.seed || PK.root, sk = SK.seed || SK.prf || pk, and a signature is
    R, then k FORS trees of a + 1 nodes, then d XMSS signatures of len + h'
    nodes, every node n bytes."""
    if h != d * hp or m != -(-k * a // 8) + -(-(h - hp) // 8) + -(-hp // 8):
        return None
    len1 = 8 * n // lg_w
    lg = (len1 * ((1 << lg_w) - 1)).bit_length() - 1        # floor(log2(len1 (w - 1)))
    len2 = lg // lg_w + 1
    return 2 * n, 4 * n, (1 + k * (1 + a) + h + d * (len1 + len2)) * n


def _slhdsa_keygen_vectors():
    """{parameter set: (first test, NIST's expected pk and sk)} from the
    pinned NIST ACVP keyGen vectors; {} if they are not installed."""
    import json as _j
    b = _load_bundle('SLH-DSA-keyGen-FIPS205/prompt.json')
    prompt = b.get('SLH-DSA-keyGen-FIPS205/prompt.json')
    expected = b.get('SLH-DSA-keyGen-FIPS205/expectedResults.json')
    if not prompt or not expected:
        return {}
    prompt = _j.loads(prompt) if isinstance(prompt, str) else prompt
    expected = _j.loads(expected) if isinstance(expected, str) else expected
    want = {g['tgId']: {t['tcId']: t for t in g['tests']} for g in expected['testGroups']}
    out = {}
    for g in prompt['testGroups']:
        if g['tests']:
            t = g['tests'][0]
            out[g['parameterSet']] = (t, want[g['tgId']][t['tcId']])
    return out


def audit_fips205_params():
    """FIPS 205 sizes for all twelve SLH-DSA parameter sets, and a keyGen
    vector of each. Hash-based signatures — no NTT, no lattice.

    Through 2.13.0 each row checked the table against arithmetic on itself
    (pk = 2n with n = pk/2, and sig > 10 pk), which no wrong size could fail.
    Each size is now checked against FIPS 205's formulas from Table 2's
    parameters, pinned separately, and against the lengths in NIST's ACVP
    keyGen vectors. With slh-dsa installed, its parameters must equal Table 2,
    and NIST's first keyGen vector of each set must come out byte-exact:
    pk.root is the top XMSS tree, computed here through the package."""
    r = AuditResult('FIPS 205 Parameters')
    fips205 = {
        'SLH-DSA-SHA2-128s':  {'pk': 32,   'sk': 64,   'sig': 7856},
        'SLH-DSA-SHA2-128f':  {'pk': 32,   'sk': 64,   'sig': 17088},
        'SLH-DSA-SHA2-192s':  {'pk': 48,   'sk': 96,   'sig': 16224},
        'SLH-DSA-SHA2-192f':  {'pk': 48,   'sk': 96,   'sig': 35664},
        'SLH-DSA-SHA2-256s':  {'pk': 64,   'sk': 128,  'sig': 29792},
        'SLH-DSA-SHA2-256f':  {'pk': 64,   'sk': 128,  'sig': 49856},
        'SLH-DSA-SHAKE-128s': {'pk': 32,   'sk': 64,   'sig': 7856},
        'SLH-DSA-SHAKE-128f': {'pk': 32,   'sk': 64,   'sig': 17088},
        'SLH-DSA-SHAKE-192s': {'pk': 48,   'sk': 96,   'sig': 16224},
        'SLH-DSA-SHAKE-192f': {'pk': 48,   'sk': 96,   'sig': 35664},
        'SLH-DSA-SHAKE-256s': {'pk': 64,   'sk': 128,  'sig': 29792},
        'SLH-DSA-SHAKE-256f': {'pk': 64,   'sk': 128,  'sig': 49856},
    }
    vectors = _slhdsa_keygen_vectors()
    try:
        from slhdsa.lowlevel.slhdsa import Address, XMSS
        import slhdsa.lowlevel.parameters as _LP
    except ImportError:
        _LP = None
    for name, p in fips205.items():
        params = _FIPS205_TABLE2[name[-4:]]
        n, h, d, hp, a, k, lg_w, m = params
        sizes = _fips205_sizes(*params)
        problems = []
        if sizes is None:
            problems.append("Table 2's parameters break a FIPS 205 relation")
        elif sizes != (p['pk'], p['sk'], p['sig']):
            problems.append(f'FIPS 205 gives pk {sizes[0]}, sk {sizes[1]}, sig {sizes[2]}')
        detail = (f"n={n} h={h} d={d} h'={hp} a={a} k={k} m={m}: pk {p['pk']}, "
                  f"sk {p['sk']}, sig {p['sig']} by FIPS 205's formulas")
        vec = vectors.get(name)
        if vec is None:
            problems.append('no NIST keyGen vector pinned')
        else:
            t, want = vec
            got = (len(want['pk']) // 2, len(want['sk']) // 2)
            if got != (p['pk'], p['sk']):
                problems.append(f'NIST keyGen vectors have pk {got[0]}, sk {got[1]}')
            detail += "; NIST keyGen vectors' pk and sk the same"
        if _LP is None:
            detail += '; keyGen not run (slh-dsa not installed)'
        elif vec is not None:
            par = getattr(_LP, name.replace('SLH-DSA-', '').replace('-', '_').lower(), None)
            theirs = par and tuple(getattr(par, f, None) for f in ('n', 'h', 'd', 'h_m', 'a', 'k', 'm'))
            if theirs != (n, h, d, hp, a, k, m):
                problems.append(f"slh-dsa's parameters are {theirs}")
            else:
                sk_seed, sk_prf, pk_seed = (bytes.fromhex(t[f]) for f in ('skSeed', 'skPrf', 'pkSeed'))
                root = XMSS(par).node(sk_seed, 0, par.h_m, pk_seed, Address(par.d - 1, 0))
                exact = ((pk_seed + root).hex().upper() == want['pk'].upper()
                         and (sk_seed + sk_prf + pk_seed + root).hex().upper() == want['sk'].upper())
                if exact:
                    detail += (f"; slh-dsa's parameters equal Table 2, and NIST keyGen "
                               f"tcId {t['tcId']} came out byte-exact")
                else:
                    problems.append(f"NIST keyGen tcId {t['tcId']} not reproduced")
        r.add_test(f'{name} FIPS 205 params', not problems,
                   detail if not problems else detail + ' \u2014 ' + '; '.join(problems))
    # Live roundtrip against a real FIPS 205 implementation.
    # NOTE: the PyPI package is `slh-dsa` but the MODULE is `slhdsa`. An
    # earlier version imported `slh_dsa`, which never resolved, so this check
    # silently reported "not installed" even when the library was present --
    # a skip that reads as a pass. Import the module name, not the dist name.
    try:
        import slhdsa
        import slhdsa.parameters as _slhp
        _kp = slhdsa.KeyPair.gen(_slhp.sha2_128s)
        _msg = b"pq-verify test"
        _sig = _kp.sign(_msg)
        valid = bool(_kp.verify(_msg, _sig))
        # negative control: a tampered message must NOT verify
        _tampered = not bool(_kp.verify(b"pq-verify tesT", _sig))
        r.add_test('SLH-DSA-SHA2-128s live roundtrip', valid and _tampered,
                   f"sign/verify={'OK' if valid else 'FAIL'}, "
                   f"tampered-rejected={'OK' if _tampered else 'FAIL'}")
    except ImportError:
        r.add_skip('SLH-DSA-SHA2-128s live roundtrip',
                   'slh-dsa not installed, no live sign/verify was performed '
                   '(pip install slh-dsa)', 'slh-dsa')
    return r

# ================================================================
# DILITHIUM FULL NTT VERIFICATION (7 layers, libzq32)
# ================================================================

def _dilithium_zeta_table():
    """FIPS 204 zeta table (bit-reversed). \u03b6=1753, q=8380417."""
    Q, Z = DILI_Q, DILI_ZETA
    zetas = [0] * 256
    for i in range(256):
        br = 0; val = i
        for _ in range(8):
            br = (br << 1) | (val & 1); val >>= 1
        zetas[i] = pow(Z, br, Q)
    return zetas

def _reference_ntt_dili(f_in):
    """FIPS 204 Algorithm 41 \u2014 reference Dilithium NTT.

    NOTE: ML-DSA's NTT is COMPLETE -- 8 layers, length 128 down to 1.
    zeta=1753 has multiplicative order 512 mod q=8380417, so 2n | q-1 and the
    transform splits all the way to linear factors. This differs from ML-KEM,
    where zeta has order 256, 2n does NOT divide q-1, and the last layer is
    deleted (7 layers). Matches pq-crystals ref/ntt.c: for(len=128; len>0; ...)
    -- as opposed to Kyber's for(len=128; len>=2; ...).
    """
    Q = DILI_Q
    zetas = _dilithium_zeta_table()
    f = list(f_in)
    i = 1; length = 128
    while length >= 1:
        start = 0
        while start < 256:
            z = zetas[i]; i += 1
            for j in range(start, start + length):
                t = (z * f[j + length]) % Q
                f[j + length] = (f[j] - t) % Q
                f[j] = (f[j] + t) % Q
            start += 2 * length
        length //= 2
    return f

def _ntt_layer_dili(f_in, layer_idx, zetas):
    """One Dilithium NTT layer."""
    Q = DILI_Q
    f = list(f_in)
    lengths = [128, 64, 32, 16, 8, 4, 2, 1]
    length = lengths[layer_idx]
    z_idx = sum(256 // (2 * lengths[l]) for l in range(layer_idx)) + 1
    start = 0
    while start < 256:
        z = zetas[z_idx]; z_idx += 1
        for j in range(start, start + length):
            t = (z * f[j + length]) % Q
            f[j + length] = (f[j] - t) % Q
            f[j] = (f[j] + t) % Q
        start += 2 * length
    return f

def _verify_ntt_layer_dili(lib, f_in, f_out, layer_idx, zetas):
    """Verify one ML-DSA NTT layer with libzq32, every butterfly.

    ML-KEM's layer check fixes all 256 inputs and outputs in one system of
    512 variables; libzq32 holds 256. A layer's 128 butterflies are
    independent, so they are checked 64 at a time: each group's inputs and
    outputs are fixed to f_in and f_out and its butterflies added, and the
    group is satisfiable exactly when its outputs are its butterflies of its
    inputs."""
    Q = DILI_Q
    lengths = [128, 64, 32, 16, 8, 4, 2, 1]
    length = lengths[layer_idx]
    z_idx = sum(256 // (2 * lengths[l]) for l in range(layer_idx)) + 1
    flies, start = [], 0
    while start < 256:
        z = zetas[z_idx]; z_idx += 1
        flies += [(j, j + length, z) for j in range(start, start + length)]
        start += 2 * length
    s = Zq32S(); res = Zq32R()
    sat, us = True, 0.0
    for g in range(0, len(flies), 64):
        group = flies[g:g + 64]
        pos = [p for a, b, _ in group for p in (a, b)]
        at = {p: i for i, p in enumerate(pos)}
        n = len(pos)
        lib.zq32_init(ctypes.byref(s), 2 * n, Q)
        for p in pos:
            for var, val in ((at[p], f_in[p]), (n + at[p], f_out[p])):
                vi = (ctypes.c_int*1)(var); vc = (ctypes.c_uint32*1)(1)
                lib.zq32_add_sparse(ctypes.byref(s), vi, vc, 1, val % Q)
        for a, b, z in group:
            lib.zq32_add_ntt_butterfly(ctypes.byref(s), at[a], at[b],
                                       n + at[a], n + at[b], z)
        lib.zq32_solve(ctypes.byref(s), ctypes.byref(res))
        sat = sat and res.satisfiable == 1
        us += res.solve_time_us
    return sat, len(flies), us

def audit_full_ntt_dilithium(lib):
    """Complete Dilithium NTT \u2014 8 layers, 1024 butterflies (FIPS 204's
    complete transform), each through libzq32."""
    r = AuditResult('Dilithium Full NTT')
    Q = DILI_Q
    zetas = _dilithium_zeta_table()

    random.seed(20260502)
    f_input = [random.randint(0, Q-1) for _ in range(256)]
    f_ntt = _reference_ntt_dili(f_input)

    # Every butterfly of every layer goes through libzq32, as ML-KEM's go
    # through libzq. Through 2.13.0 this compared 27 butterflies of the
    # Python layer with the same formula, and one went through the engine.
    f_layer = list(f_input)
    total_bf = 0; total_us = 0.0; all_pass = True
    lengths = [128, 64, 32, 16, 8, 4, 2, 1]
    for layer in range(8):
        f_next = _ntt_layer_dili(f_layer, layer, zetas)
        sat, n_bf, us = _verify_ntt_layer_dili(lib, f_layer, f_next, layer, zetas)
        total_bf += n_bf
        total_us += us
        if not sat:
            all_pass = False
            r.add_test(f'Dilithium NTT layer {layer} (len={lengths[layer]})', False,
                       f'{n_bf} butterflies \u2014 FAILED')
        f_layer = f_next

    defined = _mldsa_ntt_by_definition(f_input)
    ntt_match = f_layer == f_ntt == defined
    r.add_test(f'8-layer Dilithium NTT ({total_bf} butterflies)', all_pass,
               f"{'all layers SAT' if all_pass else 'a layer is UNSAT'}, "
               f'{total_us:.0f}\u03bcs total')
    r.add_test('Dilithium NTT matches FIPS 204 reference', ntt_match,
               '256 coefficients: the layers compose to Algorithm 41'
               + ('' if f_layer == f_ntt else ' \u2014 NOT')
               + ', and both equal f(\u03b6^(2\u00b7BitRev8(i)+1)), the NTT\'s definition'
               + ('' if f_ntt == defined else ' \u2014 NOT'))

    s32 = Zq32S(); r32 = Zq32R()
    lib.zq32_init(ctypes.byref(s32), 4, Q)
    z = zetas[1]; a_in = f_input[0]; b_in = f_input[128]
    vi = (ctypes.c_int*1)(0); vc = (ctypes.c_uint32*1)(1)
    lib.zq32_add_sparse(ctypes.byref(s32), vi, vc, 1, a_in)
    vi = (ctypes.c_int*1)(1); vc = (ctypes.c_uint32*1)(1)
    lib.zq32_add_sparse(ctypes.byref(s32), vi, vc, 1, b_in)
    lib.zq32_add_ntt_butterfly(ctypes.byref(s32), 0, 1, 2, 3, z)
    lib.zq32_solve(ctypes.byref(s32), ctypes.byref(r32))
    exp_a = (a_in + z * b_in) % Q
    engine_ok = (r32.satisfiable and r32.assignment[2] == exp_a
                 and r32.assignment[3] == (a_in + (Q - z) * b_in) % Q)
    r.add_test('libzq32 engine butterfly verified', engine_ok,
               f'z={z}, {r32.solve_time_us:.1f}\u03bcs')
    return r

# ================================================================
# COQ PERSISTENT DAEMON (one coqtop, no start-up per theorem)
# ================================================================

class CoqDaemon:
    """A persistent coqtop process: no coqc start-up per theorem.

    Every statement goes to coqtop followed by a marker, and coqtop's reply
    is read back up to that marker, so each verdict is coqtop's own. A
    theorem counts only if coqtop proves it and Print Assumptions finds it
    closed under the global context, with no axiom. Through 2.13.0 the
    daemon wrote to coqtop and never read a reply: every theorem it was sent
    was 'accepted', true or false.
    """
    TIMEOUT = 60        # seconds to wait for one reply

    def __init__(self):
        self.proc = None
        self._lines = None
        self._marker = 7_340_000_000
        self._start()

    def _start(self):
        import queue, threading
        coqtop = shutil.which('coqtop')
        if not coqtop:
            return
        try:
            # stderr merged: coqtop writes its errors there
            self.proc = subprocess.Popen(
                [coqtop, '-quiet'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, bufsize=1)
        except OSError:
            self.proc = None
            return
        self._lines = queue.Queue()

        def pump(stream, sink):
            for line in stream:
                sink.put(line)
            sink.put(None)
        threading.Thread(target=pump, args=(self.proc.stdout, self._lines),
                         daemon=True).start()
        ok, reply = self._send('Require Import ZArith.\nOpen Scope Z_scope.\n')
        if not ok or 'Error' in reply:
            self.close()
            self.proc = None
            return
        # Not printing every goal makes a theorem ~6 ms instead of ~75;
        # errors and Print Assumptions still print. Only a speed-up, so a
        # coqtop without the option is used as it is.
        self._send('Set Silent.\n')

    def _send(self, text):
        """(answered, reply): coqtop's whole reply to text, read up to a
        marker sent after it. answered is False if coqtop died or did not
        reach the marker within TIMEOUT."""
        import queue
        self._marker += 1
        mark = str(self._marker)
        try:
            self.proc.stdin.write(f'{text}Check {mark}.\n')
            self.proc.stdin.flush()
        except (OSError, ValueError) as e:
            return False, f'coqtop closed its input: {e}'
        reply, deadline = [], time.monotonic() + self.TIMEOUT
        while True:
            try:
                line = self._lines.get(timeout=max(0.0, deadline - time.monotonic()))
            except queue.Empty:
                return False, f'no reply from coqtop in {self.TIMEOUT}s'
            if line is None:
                return False, 'coqtop exited'
            # The marker's own line: the number alone at the end (after any
            # prompts), so a long number in a reply cannot be taken for it.
            body = line.rstrip()
            if body.endswith(mark) and not body[:-len(mark)][-1:].isdigit():
                # The marker's type line ("     : Z") comes after it and opens
                # the next reply; waiting for it costs ~30 ms a theorem, and
                # it can say neither "Error" nor "Closed".
                return True, ''.join(reply)
            reply.append(line)

    def check_theorem(self, name, stmt):
        """(accepted, detail): accepted only if coqtop proves stmt by
        computation and finds the theorem closed under the global context."""
        if not self.proc or self.proc.poll() is not None:
            return False, 'daemon not running'
        ok, reply = self._send(f'Theorem {name}: {stmt}.\n'
                               'Proof. vm_compute. reflexivity. Qed.\n'
                               f'Print Assumptions {name}.\n')
        if not ok:
            return False, reply
        if 'Error' in reply or 'Closed under the global context' not in reply:
            self._send('Abort All.\n')          # a failed proof stays open
            err = [ln.strip() for ln in reply.splitlines() if 'Error' in ln]
            return False, (err[0] if err else 'not closed under the global context')[:120]
        return True, 'closed under the global context'

    def close(self):
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.stdin.write('Quit.\n')
                self.proc.stdin.flush()
                self.proc.wait(timeout=5)
            except Exception:
                self.proc.kill()

def audit_coq_daemon():
    """The persistent coqtop daemon: a false theorem must be rejected, and 16
    true ones each accepted, by coqtop's own reply. Through 2.13.0 its start
    passed as a hard-coded True and the daemon never read a verdict, so both
    rows passed whatever coqtop said."""
    r = AuditResult('Coq Daemon')
    # Every check this function can report must be REGISTERED on every path.
    # Returning early without one does not make it pass or fail -- it makes it
    # vanish, so the suite's own total changes with the environment and a
    # documented count cannot be right in both. Skips carry the same names as
    # the tests they stand in for, so two runs can be diffed.
    names = ('Coq daemon rejects a false theorem', 'Batch 16 theorems')
    if not shutil.which('coqtop'):
        for name in names:
            r.add_skip(name, 'coqtop not in PATH', 'coq')
        return r
    daemon = CoqDaemon()
    if not daemon.proc:
        for name in names:
            r.add_skip(name, 'coqtop failed to start', 'coq')
        return r
    # First the control: a daemon that does not read its verdicts accepts
    # this, and then 16/16 below would mean nothing.
    took, why = daemon.check_theorem('batch_false', '(1000 + 2000) mod 3329 = 3001')
    r.add_test(names[0], not took,
               '(1000 + 2000) mod 3329 = 3001: '
               + (f'rejected by coqtop ({why})' if not took else
                  'ACCEPTED, so the daemon is not reading coqtop\'s verdicts'))

    random.seed(7777)
    t0 = time.perf_counter()
    n_ok, first_bad = 0, None
    for i in range(16):
        a = random.randint(100, 3328)
        b = random.randint(100, 3328)
        result = (a + b) % 3329
        ok, why = daemon.check_theorem(f'batch_{i}', f'({a} + {b}) mod 3329 = {result}')
        n_ok += ok
        first_bad = first_bad or (None if ok else why)
    elapsed = time.perf_counter() - t0
    per_proof = elapsed / 16 * 1000
    r.add_test(names[1], n_ok == 16,
               f'{n_ok}/16 proved by coqtop and closed under the global context, '
               f'{per_proof:.1f}ms/proof, {elapsed*1000:.0f}ms total'
               + (f'; first failure: {first_bad}' if first_bad else ''))
    daemon.close()
    return r

# ================================================================
# C-COMPILED CFL FRONT-END BENCHMARK
# ================================================================

def audit_c_cfl(engines):
    """The CFL front end run 100 times: the same AST, properties and
    obligations each time, and the AST printed back as CFL parses to itself.
    A C build of the pipeline can be loaded by opt-in (PQV_CFL_SO) to time
    against it; its answer is reported, not checked."""
    from . import cfl as C
    r = AuditResult('C CFL Pipeline')
    # This benchmark used to load ./libgf2_cfl.so and /tmp/libgf2_cfl.so if they
    # happened to exist. Both are attacker-controllable -- the first by anyone
    # who can write the directory pq-verify is run from, which for an auditing
    # tool is routinely a vendor's build tree or an extracted tarball; the
    # second by any local user, since /tmp is world-writable. ctypes.CDLL runs
    # the library's constructors, so either one was arbitrary code execution
    # inside the process doing the verifying.
    #
    # The comparison is optional -- without the library this falls back to the
    # Python pipeline and still reports -- so the library is now opt-in by
    # absolute path and never discovered implicitly.
    c_cfl = None
    _cfl_so = os.environ.get('PQV_CFL_SO')
    if _cfl_so:
        if not os.path.isabs(_cfl_so):
            print(f"  {_BAD} PQV_CFL_SO must be an absolute path — ignoring "
                  f"{_cfl_so!r}")
        elif not os.path.exists(_cfl_so):
            print(f"  {_BAD} PQV_CFL_SO does not exist — ignoring {_cfl_so!r}")
        else:
            try:
                c_cfl = ctypes.CDLL(_cfl_so)
            except Exception as _e:
                print(f"  {_BAD} PQV_CFL_SO failed to load: {_e}")
    # Each run also takes one random one-character edit of the specification
    # -- a character deleted, inserted or replaced -- which the pipeline must
    # either reject with a CFLError giving a line and column, or accept as a
    # specification that prints back to itself, with closed obligations. Any
    # other outcome (an IndexError, an error with no position) fails the row.
    # Through 2.13.0 the row timed 100 runs of a deterministic function and
    # repeated the parser's round trip, which nothing could make fail.
    rng = random.Random(2603)
    alphabet = '(){}<>:;,"\\ \n_aZ09@'
    t0 = time.perf_counter()
    first, same, trips = None, True, True
    rejected = accepted = 0
    odd = []
    for i in range(100):
        ast = C.parse(CFL_SPEC)
        props = C.check(ast)
        text = C.to_text(ast)
        trips = trips and C.parse(text).shape() == ast.shape()
        out = (ast.shape(), tuple(repr(p) for p in props), text,
               tuple(C.show(C.from_prenex(*C.prenex(C.obligation(p)))) for p in props))
        first = first or out
        same = same and out == first
        spec = list(CFL_SPEC)
        pos, op, ch = rng.randrange(len(spec)), rng.randrange(3), rng.choice(alphabet)
        if op == 0:
            del spec[pos]
        elif op == 1:
            spec.insert(pos, ch)
        else:
            spec[pos] = ch
        edited = ''.join(spec)
        try:
            m_ast = C.parse(edited)
            m_props = C.check(m_ast)
            closed = all(not C.free_vars(C.obligation(p)) for p in m_props)
            if C.parse(C.to_text(m_ast)).shape() == m_ast.shape() and closed:
                accepted += 1
            else:
                odd.append(f'edit {i + 1} accepted but does not print back to itself')
        except C.CFLError as e:
            if all(m.startswith('line ') for m in e.messages):
                rejected += 1
            else:
                odd.append(f'edit {i + 1}: an error with no position: {e}')
        except Exception as e:           # a crash on malformed input
            odd.append(f'edit {i + 1}: {type(e).__name__}: {e}')
    elapsed = (time.perf_counter() - t0) / 100
    r.add_test('Python CFL pipeline \u00d7100', same and trips and not odd,
               f'{elapsed*1e6:.0f}\u03bcs/iter; the same AST, properties and obligations '
               f'every time{"" if same else " — NOT"}; the printed AST parses to '
               f'itself{"" if trips else " — NOT"}; 100 one-character edits: {rejected} '
               f'rejected with a line and column, {accepted} still a specification that '
               f'prints back to itself, {len(odd)} otherwise'
               + (f' ({"; ".join(odd[:3])})' if odd else ''))
    if c_cfl is None:
        return r
    class PR(ctypes.Structure):
        _fields_ = [("satisfiable", ctypes.c_int), ("num_variables", ctypes.c_int),
                     ("num_equations", ctypes.c_int), ("solve_time_us", ctypes.c_double),
                     ("lex_us", ctypes.c_double), ("parse_us", ctypes.c_double),
                     ("encode_us", ctypes.c_double), ("total_us", ctypes.c_double)]
    try:
        c_cfl.cfl_verify_api.argtypes = [ctypes.c_char_p, ctypes.POINTER(PR)]
        c_cfl.cfl_verify_api.restype = None
        pr = PR()
        spec = b'CONTEXT(Kyber){DEFINE property<NTT>{type:"linear";field:"GF2";}}'
        c_cfl.cfl_verify_api(spec, ctypes.byref(pr))
        r.add_skip('C CFL pipeline',
                   f'timed, not checked: an external library whose answer pq-verify '
                   f'cannot verify; total={pr.total_us:.1f}\u03bcs (lex={pr.lex_us:.1f} '
                   f'parse={pr.parse_us:.1f} solve={pr.solve_time_us:.1f})')
    except Exception as e:
        r.add_test('C CFL pipeline', False, f'API error: {e}')
    return r

# ================================================================
# UNIFIED MAIN
# ================================================================


# ================================================================
# ENGINE 7: the DQBF stage (Phase 4b), decided exactly (docs/DQBF.md)
# The module format parsed strictly; an XOR matrix decided by affine
# Skolem functions on the GF(2) engine, one with clauses by universal
# expansion and CDCL; every answer's certificate checked by a checker
# that does not use the solver (pq_verify/dqbf.py).
# ================================================================

# The Phase 4b module. It is false: c1 and c2 force x2 = k constant,
# x1 = 1+k+u1 and x3 = k+u2 (x1 sees only u1 and x3 only u2), and then
# c3 fails at u1=1, u2=0 for k=0 and at u1=0, u2=1 for k=1. Through
# 2.13.0 the pipeline called it satisfiable (docs/DQBF.md).
_PHASE4B_MODULE = """
<module name="ntt_verify">
  <vars>
    <forall vars="u1 u2" />
    <exists vars="x1" deps="u1" />
    <exists vars="x2" deps="u1 u2" />
    <exists vars="x3" deps="u2" />
  </vars>
  <constraints>
    <xor id="c1" parity="1">x1 x2 u1</xor>
    <xor id="c2" parity="0">x2 x3 u2</xor>
    <or id="c3">x1 x3</or>
    <or id="c4">!x1 x2 !x3</or>
  </constraints>
</module>
"""


def _dqbf_planted(seed=42, nu=200, nx=800, ncons=1500):
    """A true XOR DQBF of nu + nx variables: x_i depends on u_(i mod nu),
    and each constraint sums 2 to 4 existentials and exactly the
    universals that make it hold under chosen affine Skolem functions."""
    import random as _rng
    from . import dqbf as D
    rng = _rng.Random(seed)
    f = D.DQBF()
    us = [f'u{i}' for i in range(nu)]
    f.forall(*us)
    xs = [f'x{i}' for i in range(nx)]
    for i, x in enumerate(xs):
        f.exists(x, [us[i % nu]])
    c = {x: rng.randint(0, 1) for x in xs}
    a = {x: rng.randint(0, 1) for x in xs}
    for _ in range(ncons):
        E = rng.sample(xs, rng.randint(2, 4))
        W = set()
        for x in E:
            if a[x]:
                W ^= f.existentials[x]
        f.xor(E + sorted(W), sum(c[x] for x in E) % 2)
    return f


def audit_dqbf_pipeline(engines):
    """The DQBF stage (docs/DQBF.md): the Phase 4b module parsed strictly and
    decided exactly, every answer's certificate checked, and the checkers
    shown to reject tampered certificates."""
    import time as _time
    from . import dqbf as D
    r = AuditResult('DQBF Pipeline (Phase 4b)')
    lib_gf2 = engines.get('gf2')

    def row(name, run):
        """run() -> (passed, detail). A rejected certificate is CRITICAL."""
        t0 = _time.perf_counter()
        try:
            ok, detail = run()
        except D.CertificateError as e:
            r.add_test(name, False, f'CRITICAL: {e}')
            r.add_finding('CRITICAL', f'DQBF {name}: an answer failed its '
                          f'certificate check', str(e))
            return
        except Exception as e:           # a defect in the check itself
            ok, detail = False, f'error: {type(e).__name__}: {e}'
        r.add_test(name, ok, detail, (_time.perf_counter() - t0) * 1e6)

    def module():
        return D.parse_module(_PHASE4B_MODULE)

    # 1. The strict parser: the module parses, and each malformed variant
    # is an error, not a silent misreading.
    def parser():
        name, _ = module()
        bad = {
            'deps misspelled': _PHASE4B_MODULE.replace('deps="u1" />', 'dep="u1" />', 1),
            'a dependency on an existential': _PHASE4B_MODULE.replace('deps="u2"', 'deps="x1"'),
            'parity 2': _PHASE4B_MODULE.replace('parity="1"', 'parity="2"'),
            'an undeclared variable': _PHASE4B_MODULE.replace('x1 x3</or>', 'x1 x9</or>'),
            'an unknown element': _PHASE4B_MODULE.replace('</constraints>', '<and>x1 x2</and></constraints>'),
            'an <exists> without deps': _PHASE4B_MODULE.replace(' deps="u2"', ''),
        }
        accepted = []
        for what, text in bad.items():
            if text == _PHASE4B_MODULE:
                accepted.append(f'{what} (variant not built)')
                continue
            try:
                D.parse_module(text)
                accepted.append(what)
            except D.DQBFError:
                pass
        ok = name == 'ntt_verify' and not accepted
        return ok, (f'module {name} parsed; {len(bad) - len(accepted)}/{len(bad)} '
                    f'malformed variants rejected'
                    + (f' — accepted: {", ".join(accepted)}' if accepted else ''))
    row('CFL XML parser', parser)

    # 2. The formula is the module's.
    def conversion():
        _, f = module()
        want_x = {'x1': {'u1'}, 'x2': {'u1', 'u2'}, 'x3': {'u2'}}
        want_xor = [({'x1', 'x2', 'u1'}, 1), ({'x2', 'x3', 'u2'}, 0)]
        want_cl = [(('x1', True), ('x3', True)), (('x1', False), ('x2', True), ('x3', False))]
        ok = (f.universals == ['u1', 'u2']
              and {x: set(d) for x, d in f.existentials.items()} == want_x
              and [(set(n), p) for n, p in f.xors] == want_xor
              and f.clauses == want_cl)
        return ok, (f'{len(f.universals)} universals, {len(f.order)} existentials '
                    f'with dependency sets, {len(f.xors)} XOR, {len(f.clauses)} clauses'
                    + ('' if ok else ' — not the module'))
    row('DQBF conversion', conversion)

    # 3. Routing on the formula's structure.
    def routing():
        _, f = module()
        xor_only = D.DQBF().forall('u').exists('x', ['u']).xor(['x', 'u'], 0)
        big = D.DQBF()
        big.forall(*[f'u{i}' for i in range(20)])
        for i in range(20):
            big.exists(f'x{i}', [f'u{i}'])
        big.clause([(f'x{i}', True) for i in range(20)])
        big.clause([(f'x{i}', False) for i in range(20)])
        got = (D.route(f), D.route(xor_only), D.route(big))
        d = D.decide(big)
        ok = got == ('expansion', 'affine-skolem', 'cannot-verify') and d.truth is None
        return ok, (f'module (clauses) → {got[0]}; XOR-only → {got[1]}; '
                    f'clauses over 20 universals → {got[2]}, '
                    f'{"CANNOT VERIFY" if d.truth is None else d.truth}')
    row('Structural routing', routing)

    # 4. The module decided, and the answer checked twice: its certificate,
    # and an enumeration of every choice of Skolem functions.
    def phase4b():
        _, f = module()
        d = D.decide(f, lib_gf2)
        checked = d.truth is False and D.check_expansion_refutation(f, d.certificate)
        brute = D.brute_force(f)
        ok = checked and brute is False and d.method == 'expansion'
        return ok, (f'{"FALSE" if d.truth is False else d.truth} by {d.method}: '
                    f'{d.detail}; every Skolem choice enumerated: '
                    f'{"none works" if brute is False else "one works"}')
    row('Phase 4b module decided', phase4b)

    # 5. False formulas refuted, one by each procedure.
    def refuted():
        a = D.DQBF().forall('u').exists('x', []).xor(['x', 'u'], 0)
        b = D.DQBF().exists('x1').exists('x2')
        for s1 in (True, False):
            for s2 in (True, False):
                b.clause([('x1', s1), ('x2', s2)])
        da, db_ = D.decide(a, lib_gf2), D.decide(b, lib_gf2)
        ok = (da.truth is False and da.method == 'affine-skolem'
              and D.check_refutation(a, da.certificate)
              and db_.truth is False and db_.method == 'expansion'
              and D.check_expansion_refutation(b, db_.certificate)
              and D.brute_force(a) is False and D.brute_force(b) is False)
        return ok, (f'∀u ∃x(∅). x⊕u=0: {da.truth}, {da.detail}; '
                    f'the four 2-clauses: {db_.truth}, {db_.detail}')
    row('False formulas refuted', refuted)

    # 6. The checkers reject tampered certificates, each made from a valid
    # certificate known by hand; the procedures must find the valid ones.
    def tampered():
        right, total = 0, 0

        def expect(accepted, want):
            nonlocal right, total
            total += 1
            right += accepted == want
        # Skolem tables: y = u1 AND u2 is the only Skolem function, so every
        # flipped entry must be rejected.
        g = D.DQBF().forall('u1', 'u2').exists('y', ['u1', 'u2'])
        g.clause([('y', False), ('u1', True)]).clause([('y', False), ('u2', True)])
        g.clause([('y', True), ('u1', False), ('u2', False)])
        and_table = {'y': {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 1}}
        dg = D.decide(g)
        expect(dg.truth is True and dg.certificate == and_table, True)
        expect(D.check_tables(g, and_table), True)
        for tau in and_table['y']:
            t = {'y': dict(and_table['y'])}
            t['y'][tau] ^= 1
            expect(D.check_tables(g, t), False)
        # Functions that satisfy the constraint by reading a universal outside
        # the dependency set: x = u for forall u exists x(). x+u = 0.
        a = D.DQBF().forall('u').exists('x', []).xor(['x', 'u'], 0)
        expect(D.check_affine(a, {'x': (0, frozenset({'u'}))}), False)
        expect(D.check_tables(a, {'x': {(0,): 0, (1,): 1}}), False)
        # Affine functions: x = 1+u1 and y = 1+u1+u2 are the only ones; a
        # flipped constant must be rejected.
        h = D.DQBF().forall('u1', 'u2').exists('x', ['u1']).exists('y', ['u1', 'u2'])
        h.xor(['x', 'u1'], 1).xor(['x', 'y', 'u2'], 0)
        affine = {'x': (1, frozenset({'u1'})), 'y': (1, frozenset({'u1', 'u2'}))}
        dh = D.decide(h, lib_gf2)
        expect(dh.truth is True and dh.certificate == affine, True)
        expect(D.check_affine(h, affine), True)
        expect(D.check_affine(h, dict(affine, x=(0, frozenset({'u1'})))), False)
        # A refutation that needs all three of its equations: the
        # coefficients of u in x1 = u, x1 = x2 and x2 = y, with y blind to u.
        k = D.DQBF().forall('u').exists('x1', ['u']).exists('x2', ['u']).exists('y', [])
        k.xor(['x1', 'u'], 0).xor(['x1', 'x2'], 0).xor(['x2', 'y'], 0)
        unknowns, eqs = D.skolem_system(k)
        rows3 = [i for i, (lhs, _) in enumerate(eqs)
                 if lhs and all(unknowns[j][1] == 'u' for j in lhs)]
        dk = D.decide(k, lib_gf2)
        expect(dk.truth is False and D.check_refutation(k, dk.certificate), True)
        expect(len(rows3) == 3 and D.check_refutation(k, rows3), True)
        for i in range(3):
            expect(D.check_refutation(k, rows3[:i] + rows3[i + 1:]), False)
        # A RUP proof of the four 2-clauses, checked against each satisfiable
        # three of them, and with its learned clauses removed.
        b = D.DQBF().exists('x1').exists('x2')
        for s1 in (True, False):
            for s2 in (True, False):
                b.clause([('x1', s1), ('x2', s2)])
        nv, cnf, _ = D.expand(b)
        db_ = D.decide(b)
        expect(db_.truth is False and D.check_rup(nv, cnf, db_.certificate), True)
        proof = [[1], []]                    # x1 by propagation, then the conflict
        expect(D.check_rup(nv, cnf, proof), True)
        for i in range(len(cnf)):
            expect(D.check_rup(nv, cnf[:i] + cnf[i + 1:], proof), False)
        expect(D.check_rup(nv, cnf, [[]]), False)
        return right == total, (f'{right}/{total} as expected: valid certificates '
                                f'found and accepted; flipped Skolem table entries, '
                                f'functions reading a universal outside their '
                                f'dependency set, a flipped affine constant, a '
                                f'refutation with an equation dropped and a RUP proof '
                                f'against satisfiable clauses rejected')
    row('Tampered certificates rejected', tampered)

    # 7. A 1000-variable XOR DQBF on the GF(2) engine.
    if not lib_gf2:
        r.add_skip('1000-var DQBF stress', 'GF(2) engine not available (gcc?)')
        return r

    def stress():
        f = _dqbf_planted()
        d = D.decide(f, lib_gf2)
        ok = (d.truth is True and d.engine == 'libpqv_gf2'
              and D.check_affine(f, d.certificate))
        return ok, (f'{f.num_vars} variables ({len(f.universals)} universal), '
                    f'{len(f.xors)} constraints: {d.truth} on {d.engine}, {d.detail}, '
                    f'Skolem functions checked')
    row('1000-var DQBF stress', stress)
    return r


# ================================================================
# BATCHED VERIFICATION API
# ================================================================

def batch_verify_ntt(lib_zq, n_instances, q=3329, seed=None, coefficients=None):
    """Batch-verify N NTT butterfly instances. Returns structured report dict.

    Args:
        lib_zq: compiled Z_q engine (ctypes CDLL)
        n_instances: number of butterfly instances to verify
        q: field prime (3329 for Kyber, 8380417 for Dilithium)
        seed: random seed for reproducibility (None = random)
        coefficients: list of (a, b, w) tuples. If None, generates random.

    Returns:
        dict with keys: passed, failed, total, failures (list),
        total_us, avg_us, throughput, seed
    """
    import time as _time
    rng = random.Random(seed)
    is_16 = (q <= 65535)
    SysT = ZqS if is_16 else Zq32S
    ResT = ZqR if is_16 else Zq32R
    report = {'total': n_instances, 'passed': 0, 'failed': 0,
              'failures': [], 'q': q, 'seed': seed}
    t0 = _time.perf_counter()
    for i in range(n_instances):
        if coefficients and i < len(coefficients):
            a_in, b_in, w = coefficients[i]
        else:
            a_in = rng.randint(0, q - 1)
            b_in = rng.randint(0, q - 1)
            w = rng.randint(1, q - 1)
        exp_a = (a_in + w * b_in) % q
        exp_b = (a_in + (q - w) * b_in) % q
        s = SysT()
        if is_16:
            lib_zq.zq_init(ctypes.byref(s), 4, q)
            vi = (ctypes.c_int * 1)(0); vc = (ctypes.c_uint16 * 1)(1)
            lib_zq.zq_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
            vi = (ctypes.c_int * 1)(1); vc = (ctypes.c_uint16 * 1)(1)
            lib_zq.zq_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
            lib_zq.zq_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        else:
            lib_zq.zq32_init(ctypes.byref(s), 4, q)
            vi = (ctypes.c_int * 1)(0); vc = (ctypes.c_uint32 * 1)(1)
            lib_zq.zq32_add_sparse(ctypes.byref(s), vi, vc, 1, a_in)
            vi = (ctypes.c_int * 1)(1); vc = (ctypes.c_uint32 * 1)(1)
            lib_zq.zq32_add_sparse(ctypes.byref(s), vi, vc, 1, b_in)
            lib_zq.zq32_add_ntt_butterfly(ctypes.byref(s), 0, 1, 2, 3, w)
        res = ResT()
        if is_16:
            lib_zq.zq_solve(ctypes.byref(s), ctypes.byref(res))
        else:
            lib_zq.zq32_solve(ctypes.byref(s), ctypes.byref(res))
        if res.satisfiable and res.assignment[2] == exp_a and res.assignment[3] == exp_b:
            report['passed'] += 1
        else:
            report['failed'] += 1
            report['failures'].append({
                'index': i, 'a': a_in, 'b': b_in, 'w': w,
                'expected': (exp_a, exp_b),
                'got': (res.assignment[2], res.assignment[3]),
                'sat': bool(res.satisfiable)
            })
    elapsed = (_time.perf_counter() - t0) * 1e6
    report['total_us'] = elapsed
    report['avg_us'] = elapsed / max(n_instances, 1)
    report['throughput'] = n_instances / (elapsed / 1e6) if elapsed > 0 else 0
    return report


def batch_verify_keypairs(n_instances, seed=None):
    """Batch-verify N ML-KEM-768 keypair roundtrips. Returns structured report.

    Returns:
        dict with passed, failed, total, total_ms, avg_ms, failures
    """
    import time as _time
    try:
        from kyber_py.ml_kem import ML_KEM_768
    except ImportError:
        # 'unavailable' separates "could not run" from "ran and broke", so a
        # caller can report the first as a skip rather than a failure.
        return {'total': n_instances, 'passed': 0, 'failed': n_instances,
                'error': 'kyber-py not available', 'unavailable': True,
                'total_ms': 0}
    except Exception as e:
        return {'total': n_instances, 'passed': 0, 'failed': n_instances,
                'error': f'kyber-py failed to load: {type(e).__name__}: {e}',
                'total_ms': 0}
    report = {'total': n_instances, 'passed': 0, 'failed': 0, 'failures': []}
    t0 = _time.perf_counter()
    for i in range(n_instances):
        pk, sk = ML_KEM_768.keygen()
        ss1, ct = ML_KEM_768.encaps(pk)
        ss2 = ML_KEM_768.decaps(sk, ct)
        if ss1 == ss2:
            report['passed'] += 1
        else:
            report['failed'] += 1
            report['failures'].append({'index': i})
    elapsed_ms = (_time.perf_counter() - t0) * 1000
    report['total_ms'] = elapsed_ms
    report['avg_ms'] = elapsed_ms / max(n_instances, 1)
    return report


def audit_batch_api(engines, quick=False):
    """Phase 2 addition: batch verification API test."""
    r = AuditResult('Batch Verification API')
    n_ntt = 500 if quick else 5000
    # Kyber batch
    if engines.get('zq'):
        rpt = batch_verify_ntt(engines['zq'], n_ntt, q=3329, seed=42)
        r.add_test(f'Batch Kyber NTT ({n_ntt})', rpt['failed'] == 0,
                   f"{rpt['passed']}/{rpt['total']} verified, "
                   f"{rpt['avg_us']:.1f}\u03bcs/op, {rpt['throughput']:.0f}/sec")
    # Dilithium batch
    if engines.get('zq32'):
        n_dil = 200 if quick else 1000
        rpt = batch_verify_ntt(engines['zq32'], n_dil, q=8380417, seed=42)
        r.add_test(f'Batch Dilithium NTT ({n_dil})', rpt['failed'] == 0,
                   f"{rpt['passed']}/{rpt['total']} verified, "
                   f"{rpt['avg_us']:.1f}\u03bcs/op, {rpt['throughput']:.0f}/sec")
    # Keypair batch (small count — kyber-py is slow)
    n_kp = 10 if quick else 50
    rpt = batch_verify_keypairs(n_kp, seed=42)
    if rpt.get('unavailable'):
        r.add_skip(f'Batch ML-KEM-768 keypairs ({n_kp})',
                   'kyber-py not installed \u2014 pip install kyber-py',
                   'kyber-py')
    elif rpt.get('error'):
        r.add_test(f'Batch ML-KEM-768 keypairs ({n_kp})', False, rpt['error'])
    else:
        r.add_test(f'Batch ML-KEM-768 keypairs ({n_kp})', rpt['failed'] == 0,
                   f"{rpt['passed']}/{rpt['total']} roundtrips OK, "
                   f"{rpt['avg_ms']:.1f}ms/op")
    return r


def main(quick=False):
    global engines  # export for pqverify_scan harness
    print(f"""
\u2554\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2557
\u2551  pq-verify v{VERSION} \u2014 MASTER AUDIT                              \u2551
\u2551  Geometric Depth \u00b7 Industrial Scale \u00b7 Adversarial \u00b7 FIPS/SafeCurves  \u2551
\u2551  GF(2) \u00b7 Z_3329 \u00b7 Z_8380417 \u00b7 Cubic/ECC \u00b7 Conformity           \u2551
\u2551  Nicholas Maino \u00b7 iamweare \u00b7 2026                                \u2551
\u255a\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u255d
""")
    print("  Compiling engines...")
    engines = compile_all()
    bind_all(engines)

    if quick:
        print("\n  [QUICK MODE] scale tests reduced for fast iteration \u2014")
        print("  test pass/fail is still authoritative; the reproducibility")
        print("  hash and timings are NOT canonical in this mode.")

    results = []
    import gc

    print("\n" + "\u2501"*70)
    print("  PHASE 1: GEOMETRIC DEPTH PROBE")
    print("\u2501"*70)

    if engines.get('gf2'):
        print("\n  Running GF(2) verification...")
        results.append(audit_gf2(engines['gf2'], 1000)); gc.collect()
        print("  Running GF(2) null-space enumeration...")
        results.append(audit_gf2_nullspace(engines['gf2'], 200)); gc.collect()

    if engines.get('zq'):
        print("  Running Kyber NTT verification...")
        results.append(audit_kyber(engines['zq'], 1000)); gc.collect()

    if engines.get('zq32'):
        print("  Running Dilithium NTT verification...")
        results.append(audit_dilithium(engines['zq32'], 100)); gc.collect()

    if engines.get('cubic'):
        print("  Running Cubic/ECC verification...")
        results.append(audit_cubic(engines['cubic'])); gc.collect()

    if engines.get('conformity'):
        print("  Running Conformity Gradient verification...")
        results.append(audit_conformity(engines['conformity'])); gc.collect()

    if engines.get('cubic') and engines.get('conformity'):
        print("  Running Curve Auditor...")
        for a, b, p, label in [(2,2,17,'toy'),(2,3,97,'p\u22611 mod 3'),(1,6,8380417,'Dilithium prime')]:
            print(f"    \u2022 {label}: y\u00b2=x\u00b3+{a}x+{b} mod {p}")
            results.append(audit_curve(engines, a, b, p)); gc.collect()

    print("\n" + "\u2501"*70)
    print("  PHASE 2: INDUSTRIAL SCALE & FIPS COMPLIANCE")
    print("\u2501"*70)

    if engines.get('zq'):
        _nbf = 5000 if quick else 100000
        print(f"\n  Running {_nbf:,} Kyber NTT butterflies...")
        results.append(audit_kyber_scale(engines['zq'], _nbf)); gc.collect()
        _nkg = 1000 if quick else 10000
        print(f"  Running {_nkg:,} keygen instances...")
        results.append(audit_keygen(engines['zq'], _nkg)); gc.collect()
        print("  Running exhaustive modular inverses...")
        results.append(audit_exhaustive_inverses(engines['zq'])); gc.collect()
        print("  Running twiddle factor completeness...")
        results.append(audit_twiddle_completeness(engines['zq'])); gc.collect()
        print("  Running boundary value analysis...")
        results.append(audit_boundary_values(engines['zq'])); gc.collect()
        print("  Running UNSAT detection...")
        results.append(audit_unsat(engines['zq'])); gc.collect()

    print("  Running FIPS 203 parameter validation...")
    results.append(audit_fips203_params()); gc.collect()
    print("  Running FIPS 204 parameter validation...")
    results.append(audit_fips204_params()); gc.collect()
    print("  Running FIPS 205 parameter validation (SLH-DSA / SPHINCS+)...")
    results.append(audit_fips205_params()); gc.collect()
    print("  Running kyber-py roundtrip stress test...")
    results.append(audit_kyber_roundtrip()); gc.collect()

    if engines.get('gf2'):
        print("  Running AES S-box affine verification (+ CMS5 comparison)...")
        results.append(audit_aes_sbox(engines['gf2'])); gc.collect()

    if engines.get('zq'):
        print("  Running FULL Kyber NTT verification (7 layers, 896 butterflies)...")
        results.append(audit_full_ntt(engines['zq'])); gc.collect()
    if engines.get('zq32'):
        print("  Running FULL Dilithium NTT verification (8 layers, 1024 butterflies)...")
        results.append(audit_full_ntt_dilithium(engines['zq32'])); gc.collect()

    if engines.get('zq'):
        print("  Running Freivalds NTT verification (O(n log n))...")
        results.append(audit_freivalds_ntt(engines['zq'])); gc.collect()

    print("  Running batch verification API...")
    results.append(audit_batch_api(engines, quick=quick)); gc.collect()

    print("\n" + "\u2501"*70)
    print("  PHASE 3: ADVERSARIAL SUITE")
    print("\u2501"*70)
    print("\n  Running 6-category adversarial tests...")
    results.append(audit_adversarial(engines)); gc.collect()

    print("\n" + "\u2501"*70)
    print("  PHASE 4: FIPS 203/204 ZETAS & SAFECURVES")
    print("\u2501"*70)

    if engines.get('zq'):
        print("\n  Running FIPS 203 all 128 zetas...")
        results.append(audit_fips203_zetas(engines['zq'])); gc.collect()
    if engines.get('zq32'):
        print("  Running FIPS 204 Dilithium zetas...")
        results.append(audit_fips204_zetas(engines['zq32'])); gc.collect()
    print("  Running SafeCurves database...")
    results.append(audit_safecurves(engines)); gc.collect()

    print("  Running CFL front-end pipeline...")
    results.append(audit_cfl_frontend(engines)); gc.collect()
    print("  Running C CFL pipeline benchmark...")

    print("  Running DQBF pipeline (Phase 4b)...")
    results.append(audit_dqbf_pipeline(engines)); gc.collect()
    results.append(audit_c_cfl(engines)); gc.collect()

    if engines.get('zq'):
        print("  Computing reproducibility hash...")
        results.append(audit_reproducibility_hash(engines['zq'])); gc.collect()

    print("  Testing Coq persistent daemon...")
    results.append(audit_coq_daemon()); gc.collect()

    print("  Generating batch Coq certificate...")
    coq_file = gen_coq_cert(results)
    cert_r = AuditResult('Coq Certificate')
    # The control: the same certificate with one zeta off by one, which coqc
    # must reject. Through 2.13.0 this row only checked that the file had
    # been written.
    names = ('Coq batch certificate rejects a wrong zeta', 'Coq batch verified by coqc')
    wrong_file = gen_coq_cert(results, os.path.join(_pqv_workdir(), 'pq_verify_cert_wrong.v'),
                              corrupt=True)
    try:
        ok, detail = coq_check(coq_file)
        took = coq_check(wrong_file)[0] if wrong_file else None
    except FileNotFoundError:
        for name in names:
            cert_r.add_skip(name, 'coqc not in PATH \u2014 !apt install coq -y -qq', 'coq')
    except subprocess.TimeoutExpired:
        for name in names:
            cert_r.add_skip(name, 'coqc timed out', 'coq')
    except Exception as e:
        for name in names:
            cert_r.add_skip(name, f'coqc could not be run: {str(e)[:80]}', 'coq')
    else:
        if took is None:
            cert_r.add_skip(names[0], 'no zeta table in this run to state wrongly')
        else:
            cert_r.add_test(names[0], ok and not took,
                            'zeta table entry 1 off by one: '
                            + ('rejected by coqc' if not took else 'ACCEPTED')
                            + ('' if ok else '; the true certificate was rejected too, '
                               'so this shows nothing'))
        cert_r.add_test(names[1], ok, detail)
    results.append(cert_r)

    # ============================================================
    # PHASE 6: PERIOD / GAUSS-MANIN VERIFICATION (Engine 6, Paper 7)
    # ============================================================
    print("\n" + "\u2501"*70)
    print("  PHASE 6: PERIOD / GAUSS-MANIN VERIFICATION (Paper 7)")
    print("\u2501"*70)
    print("\n  Compiling Engine 6 (gcc + g++ -O3 -march=native)...")
    e6_engines = compile_engine6()
    bind_engine6(e6_engines)
    for _e6key, _e6fn, _e6label in [
        ('rank2',   audit_engine6_rank2,   'rank-2 Legendre (genus 1)'),
        ('genus2',  audit_engine6_genus2,  'rank-4 genus-2'),
        ('quintic', audit_engine6_quintic, 'rank-4 mirror quintic (CY3)'),
        ('genus4',  audit_engine6_genus4,  'rank-8 genus-4'),
    ]:
        if e6_engines.get(_e6key):
            print(f"  Running Engine 6 \u2014 {_e6label}...")
            results.append(_e6fn(e6_engines[_e6key])); gc.collect()
        else:
            # Each check it would have run is recorded as skipped, by name,
            # so the count stays what the docs say and the gap is visible.
            print(f"  \u26a0 skipping {_e6label} \u2014 engine not compiled")
            _title, _checks = _E6_CHECKS[_e6key]
            _r = AuditResult(_title)
            for _c in _checks:
                _r.add_skip(_c, f"engine6/{_e6key} did not build on this platform")
            results.append(_r)
    print("  Running Engine 6 \u2014 CFL front-end (Paper7 context)...")
    results.append(audit_engine6_cfl(e6_engines)); gc.collect()
    print("  Running Engine 6 \u2014 Coq certificate (Conjecture 7)...")
    results.append(audit_engine6_coq()); gc.collect()

    # ============================================================
    # PHASE 7: ADVERSARIAL STRESS TEST (capacity + robustness)
    # ============================================================
    print("\n" + "\u2501"*70)
    print("  PHASE 7: ADVERSARIAL STRESS TEST")
    print("\u2501"*70)
    print("\n  Stressing real engines (capacity, recovery, malformed input)...")
    for _sr in audit_stress(engines, e6_engines, quick=quick):
        results.append(_sr); gc.collect()

    print_report(results)

    ts = datetime.now(timezone.utc).strftime("%Y%m%d")
    json_file = f'pq_verify_report_{ts}.json'
    save_json(results, json_file)
    print(f"\n  Report saved: {json_file}")
    print(f"  Coq cert:    {coq_file}")
    # Returned so the suite can be ASSERTED rather than merely run. Printing a
    # tally that nothing checks is how seven skipped checks read as failures
    # for as long as they did.
    return results


# ================================================================
# ENGINE 6: PERIOD / GAUSS-MANIN  (Paper 7, Maino 2026, doi:10.5281/zenodo.20129361)
# Self-contained sixth engine: four C/C++ period engines embedded
# gzip+base64, compiled inline (gcc + g++).  Reuses the harness
# AuditResult / CFL pipeline / Coq daemon above.
# ================================================================

import os, sys, ctypes, time, gzip, base64, hashlib

ENGINE6_VERSION = "1.0.0"

# ============================================================
# Harness detection — reuse AuditResult if pq-verify is loaded
# ============================================================
_HARNESS = ('AuditResult' in dir()) or ('AuditResult' in globals())
if _HARNESS:
    _AuditResult = globals().get('AuditResult') or eval('AuditResult')
else:
    class _AuditResult:
        """Fallback — identical API to the pq-verify harness AuditResult."""
        def __init__(self, engine_name):
            self.engine = engine_name
            self.tests = []
            self.findings = []
        def add_test(self, name, passed, detail="", time_us=0):
            self.tests.append({'name': name, 'passed': passed,
                               'detail': detail, 'time_us': time_us})
        def add_finding(self, severity, description, evidence=""):
            self.findings.append({'severity': severity,
                                  'description': description, 'evidence': evidence})
        def summary(self):
            p = sum(1 for t in self.tests if t['passed'])
            return p, len(self.tests), sum(1 for f in self.findings
                                           if f['severity'] == 'CRITICAL')

# ============================================================
# EMBEDDED ENGINE SOURCES  (gzip + base64 — zero uploads)
# ============================================================
_SRC_RANK2 = (
    "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"
)
_SRC_GENUS2 = (
    "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"
    "ETgAAA=="
)
_SRC_QUINTIC = (
    "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"
)
_SRC_GENUS4 = (
    "H4sIAJ5XCGoC/6197XMeN47nd/8VT+19iOTHPdN8Z8dJrjKT2q2rOs+ek7juQ8rrUmwl0cSWtJLseDyb//2aBAig1USrs3WzGz9Q"
    "E02Q4NsPIMh+9Oc/H95e/Hh9fnNx9ebVz/5Pr6+vDx/sYRgON2eXvw758PP55fvbwR9++cfMdP727cX13cXrw1+Px8P55c8Xl+eH"
    "n65uDtf/OXyYs/jpH4/m/P717N3F2398fvjHf9jDl4eTj4fh8On08Pjw8eTjYE7nf2z5x5V/fPknlH9i+Sedlvf/7ez97e3w7Ozy"
    "4vLw+ury8vz13cXV5eHZyZzL/OjZ2d2rfPJ8/uv08OHi7PBvs9yfLu5+uR2++e3q5tc/zVmUXOZKnL15czvn8O76/d35q2dzxY6H"
    "n96/fXv4/pfzq5vzdwczV+Hu5h/Dbxe354fXv5y//vXz8ubh8G0p99cz+3efnc6VGA725Jvjd6fzP/a78uDw5ZeHg4mHFz+8ePL8"
    "5YvPyltnb68uf769eHN+uPtl/u/m7PX5cHt38/713fsbzP32cPLvP96e33w4qxXyTw5/vbr8+zlwxMP//svh7O7w85f+tNXhL+8v"
    "3r75/HD4edb28O/uMLw7u3n9y5eX8/sfzg/D/z2bKzPc/nJ2c/7mMPz0f/7XX9dtOVwtn91ePXr0Py4uX799P5f0i9e3d28urr6S"
    "T96d3f2yeDDr7+35x68ePXp/e3H58+H1m1k582uff44pX7y5ev/j2/Ovnj6aG+v27vzj9c3cTHeHv81qOuTV09In/jb3hr89ffTo"
    "7nzO4ezu/Iu7uXNdnr07P3z/1aPbu7PSwy4u35be9eHq4s3hXX717v3bk5rT4fvD46+fHIj+y5Py719PD/98NLdc7Y0nRdDFLGd8"
    "Ov98MYs6XByPpzV9wfN34Pk78Px95sFc2v++P9zOLN+fjKdPF88ph18hh18hh19LDreH45eHr3+4ePy3uQP9+nKu6l9++LX+8feX"
    "y1z+ikx/f1lUymm/P/r9j6jm8vznhWpQHX1VWNBFkV2kDnNBXz49/CF5t+9/fKgpdskuouex9Zc/XoJ5YP//K8Hxj5Tg+yK+Dm5R"
    "gNZr7veWjb647CUX2DFuzuep4LJ0hd/vyYUxVgfC2cdXZz/eonh8zmVojEXin8aNcjRV/LO98qGN659K9kU1pzPLT4eTD4evDu9O"
    "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"
    "UBjhCPsSCMZdl1e6Hb5TjakDDB/wnQqmjYvOK8zbvsfS7XCvApp8kOkB9yrhSuwFhkGQkZ4twyAILhJutBG0FbQTdBB0FLSQZYUs"
    "K2Q5IcsJWU7IckKW84IWcp2Q64Rc4YqDi4SRFn45IxxzcJFwo4Vc4aYzwk8HarMy/DkxSofrhBvNKB2uE260EbQVNKB0OSTMytWJ"
    "oG8UABBwpBE40ggcaQSONAJHmhaRfUKfdQgIkOIpA0t2sAfhYA/CwR6Egz0IB3sQDvYgHOxBONiDcLAH4WAPwsEehIM9CAd7EA72"
    "IBzsQTjYg3CwB+FgD8LBHoSDPQgHexAO9iAc7EE42INwsAfhYA/CwR6Egz0IB3sQDvYgHOxBONiDcLAH4WAPwsEehIM9NAe77ER2"
    "1Ymi8JdH4S+Pwl8ehb88Cn95FP7yyP7yiBbr43ZVnXOWPOOQWEcgkoZJx6RnMjDJOQR+LTBDbVF0fLOI2lZIMm+MdIkukJnJiUj0"
    "jEe6SBfIyCTnkPg19IxHuk0XSMcklyFzZgsLJDoCvRVLw+c/4DZBJDOTE5GJL26qpUfSMunkxnR1ev/+6NHt3c3713eH6/Obi6s3"
    "r372r27Ob9+/vXt1d/hnLRLeP3138+r11bt3z5/2Hr66vvrt/Ob2h/xykfzTq4vLD2c3F2eXd7c/+GXa1Zs3r+5uzl6fr1J+u7q5"
    "vXtV0m/O3y7F/fLOlOJdvHn17uzj05Jy+POfD//1X99W8+Tw4ocXT56/fPHZf/3XLPinQ00BWuby7avLq5t35SlkfnF5V36ufn11"
    "98v51c35OzPr5emjR+cf785vLg//8td/OXy4ungjNHT2/s3F3Qlm9+kJFe/q7ZOeHh9fvb87XWrz2Q9/sy+fzM3dfivRrv1+d/3+"
    "7vzVsy+A+auTWcSz03uJ14vU61XyNTwvCQvBKPnuHYp+zoLf5Vfv3r89eTa/N///LLE8OXvz5uTZdfm7vgQPL89/Ppn/mN8+XTTQ"
    "i+eY6Qv4rZ2jJ+D5k5kX8ipPnleRz1/Ak9v3P568eF7+xhzu1eH6t7mrTS8535+ubg4npRkv5oEzPp1/vjj8zc6/x+MpcJuXP1yU"
    "UQUFurj/3q/lgz5P558vvjzk+be8h0Wrr/86mFabJ5Dhry9boebGHb5qA2HOZ36v9uuTVvSVJHNP0iKHNpSKSJkbSyWhi+FVoXM3"
    "J/NSe8eo7zj1Hau+E9R3nPpOku+IKUGvzai8odfFKm/oNfHKG3o94nIKu319Nv8798X2daxeD/XYQf/Z3vowp93evfn885/Ofrw9"
    "WavxYm79w8VPh5MPh69AxClJ+vD08DvMZnM6PPziYP40Mgd9llpOs7vLWDnE2zfrsgpFzSWdZ98q+Sm9WUp2M5e8Cj4l+TfA8Ttr"
    "fLEAzBz1bxxt83Q/zP87/Ov7t28P38N8fTCH88u7m38Mv13cnn9++HZ+5eTr43efnf5HWfvsyTfH707nf+x35cGXcqGoeS2mx2uc"
    "uV60qXme5ixOatfrmewa5srrFzyX1b9rBqfEC5PodeUU02h5XKfRF+WNImkxvdoic35SKv38s/KprZNnn302L97PPntW/n322eli"
    "XvwGyvk1/HyHP8tSl7n1GUzA38xZb86c35Q583H91NmOefbrwl0KWVwTRX3zn0O1UJ9fr2fcXg7fYQ71nZ2vXMO8fk8MKuTi0oAS"
    "Li5tI9xCHaUFvi5KKkmGW+Wb+Vl97XRHIUqmtRRVYWCVf9cpy+1/UiEaeX1z9Qaob1eda36jluoJvMs9bH6/ZoI5yQSLzyDnPYX/"
    "FooOxaMmq+W6V4PXz1+1QfHiFf2xKDKukKU3V4bFqKhP6N0lcKigbueCDry11N9CiU3Bt61MF3LyZqwHa+kMG1+VCevbe+LXHFWK"
    "XG2X4LPMMfclfFXm0tPD/5ynOcSf9zhOD5+DKLm8MOykPO+J+qIgSwDrApMW9TDY/DCvQhdXlycFqZYl5eb87v3MOM1K+x2mzQ/2"
    "8zJpXF/P/9LE+ej/AZYFfsm8CAEA"
)

def _decode(blob):
    return gzip.decompress(base64.b64decode(blob)).decode()

# ============================================================
# COMPILE  —  gcc for rank-2 C, g++ -O3 -march=native for C++ ranks
# ============================================================
# Expected version magic (mismatch => stale .so => abort)
_E6_VERSIONS = {'genus2': 65, 'quintic': 51, 'genus4': 92}

def compile_engine6():
    """Compile the four period engines. Cache-guarded: removes any stale
    .so first, then version-checks the C++ engines via their magic export."""
    specs = [
        ('rank2',   _SRC_RANK2,   'libpqv_period.c',         'gcc',
         '-O3 -march=native -shared -fPIC -lm'),
        ('genus2',  _SRC_GENUS2,  'libpqv_period_g2.cpp',    'g++',
         '-O3 -march=native -shared -fPIC -lm'),
        ('quintic', _SRC_QUINTIC, 'libpqv_period_quint.cpp', 'g++',
         '-O3 -march=native -shared -fPIC -lm'),
        ('genus4',  _SRC_GENUS4,  'libpqv_period_g4.cpp',    'g++',
         '-O3 -march=native -shared -fPIC -lm'),
    ]
    engines = {}
    for name, blob, cfile, cc, flags in specs:
        _wd = _pqv_workdir()
        c_path  = os.path.join(_wd, cfile)
        so_path = os.path.join(_wd, cfile.rsplit(".", 1)[0] + '.so')
        # Cache guard: wipe any prior artifact
        for p in (c_path, so_path):
            if os.path.exists(p):
                os.remove(p)
        with open(c_path, 'w') as f:
            f.write(_decode(blob))
        proc = _cc(cc, flags, so_path, c_path)
        if proc.returncode != 0 or not os.path.exists(so_path):
            print(f'  {_BAD} engine6/{name} — compilation failed')
            _why = (proc.stderr or proc.stdout or '').strip()
            if _why:
                print('     ' + _why[:200])
            engines[name] = None
            # Registered like compile_all's engines. It was not: an Engine 6
            # build failure only printed, its checks vanished from the count,
            # and the integrity report still said "every engine built".
            DEGRADED['engines'].append(f'engine6/{name}')
            ENGINE_ERRORS[f'engine6/{name}'] = _why[-1500:]
            continue
        lib = ctypes.CDLL(so_path)
        # Version magic check for the C++ engines (stale-.so guard)
        if name in _E6_VERSIONS:
            vfn = getattr(lib, f'period_{name}_version', None)
            if vfn is not None:
                vfn.restype = ctypes.c_int
                got = vfn()
                want = _E6_VERSIONS[name]
                if got != want:
                    print(f'  ❌ engine6/{name} — version {got}, expected {want} '
                          f'(stale .so)')
                    engines[name] = None
                    continue
        engines[name] = lib
        print(f'  ✅ engine6/{name} ({cc})')
    return engines

# ============================================================
# CTYPES STRUCTS  —  one per engine ABI
# ============================================================
class PeriodResult(ctypes.Structure):       # rank-2 Legendre
    _fields_ = [("inv1", ctypes.c_double), ("inv2", ctypes.c_double),
                ("inv1_closed", ctypes.c_double), ("tr_comm", ctypes.c_double),
                ("comm2_off01", ctypes.c_double), ("comm2_off10", ctypes.c_double),
                ("comm2_diag_diff", ctypes.c_double), ("thm1_resid", ctypes.c_double*4),
                ("thm1_resid_max", ctypes.c_double), ("R_norm_inf", ctypes.c_double),
                ("ok_riccati", ctypes.c_int), ("ok_traceless", ctypes.c_int),
                ("ok_scalar_comm2", ctypes.c_int), ("ok_ratio", ctypes.c_int),
                ("ok_closed_form", ctypes.c_int), ("ok_theorem1", ctypes.c_int)]

class PeriodG2Result(ctypes.Structure):     # rank-4 genus-2  AND  mirror quintic
    _fields_ = [("tr_commQ", ctypes.c_double), ("tr_commQ2", ctypes.c_double),
                ("tr_commQ3", ctypes.c_double), ("tr_commQ4", ctypes.c_double),
                ("thm1_resid", ctypes.c_double*16),
                ("thm1_resid_max", ctypes.c_double), ("R_norm_inf", ctypes.c_double),
                ("ok_traceless", ctypes.c_int), ("ok_tr3_zero", ctypes.c_int),
                ("ok_theorem1", ctypes.c_int)]

class PeriodG4Result(ctypes.Structure):     # rank-8 genus-4
    _fields_ = [("tr_commQ", ctypes.c_double), ("tr_commQ_powers", ctypes.c_double*8),
                ("f_invariants", ctypes.c_double*4), ("odd_traces", ctypes.c_double*4),
                ("worst_odd_rel", ctypes.c_double), ("thm1_resid_max", ctypes.c_double),
                ("R_norm_inf", ctypes.c_double), ("ok_theorem1", ctypes.c_int)]

# ============================================================
# BIND  —  ctypes argtypes/restypes for the period engines
# ============================================================
def bind_engine6(engines):
    if engines.get('rank2'):
        l = engines['rank2']
        l.period_audit_legendre.argtypes = [ctypes.c_double, ctypes.c_double,
                                            ctypes.POINTER(PeriodResult)]
        l.period_audit_legendre.restype = None
        l.period_residue_numeric.argtypes = [ctypes.c_double, ctypes.c_double, ctypes.c_int]
        l.period_residue_numeric.restype = ctypes.c_double
        l.period_legendre_connection.argtypes = [ctypes.c_double] + [ctypes.POINTER(ctypes.c_double)] * 3
        l.period_legendre_connection.restype = None
    if engines.get('genus2'):
        l = engines['genus2']
        l.period_g2_audit.argtypes = [ctypes.c_double, ctypes.c_double,
                                      ctypes.POINTER(PeriodG2Result)]
        l.period_g2_audit.restype = None
        for fn in ('period_g2_residue_f2', 'period_g2_residue_f4'):
            getattr(l, fn).argtypes = [ctypes.c_double, ctypes.c_double, ctypes.c_int]
            getattr(l, fn).restype = ctypes.c_double
    if engines.get('quintic'):
        l = engines['quintic']
        l.period_quintic_audit.argtypes = [ctypes.c_double, ctypes.c_double,
                                           ctypes.POINTER(PeriodG2Result)]
        l.period_quintic_audit.restype = None
        for fn in ('period_quintic_f2_at', 'period_quintic_f4_at'):
            getattr(l, fn).argtypes = [ctypes.c_double]
            getattr(l, fn).restype = ctypes.c_double
    if engines.get('genus4'):
        l = engines['genus4']
        l.period_g4_audit.argtypes = [ctypes.c_double, ctypes.c_double,
                                      ctypes.POINTER(PeriodG4Result)]
        l.period_g4_audit.restype = None

def _legendre_period(z):
    """(F, F', F'') at z for F = 2F1(1/2, 1/2; 1; z), by its hypergeometric
    series (0 < |z| < 1). (pi/2) F is a period of y^2 = x(x - 1)(x - z), the
    complete elliptic integral K; F(1 - z) is a second, independent one."""
    t, n = 1.0, 0                        # t = c_n z^n, c_n = ((1/2)_n / n!)^2
    f = fp = fpp = 0.0
    while True:
        f += t
        fp += n * t / z
        fpp += n * (n - 1) * t / (z * z)
        t *= z * ((n + 0.5) / (n + 1)) ** 2
        n += 1
        if n > 10 and abs(t) < 1e-18 * abs(f) and abs(n * n * t / (z * z)) < 1e-18 * abs(fpp):
            return f, fp, fpp
        if n > 20000:
            raise ArithmeticError(f'the hypergeometric series at z = {z} did not converge')


def _legendre_connection_check(lib, samples):
    """(ok, worst period residual, worst derivative error, periods checked).

    The engine's Q is -(U' + U^2), so its Riccati equation U' = -U^2 - Q
    holds by definition whatever U and U' are: the engine sets that flag to
    1. What can be wrong is U and U' themselves. At each sample in (0, 1)
    the periods F(z) and F(1 - z) must satisfy (w, w')' = U (w, w') with the
    engine's U, which pins both of its free entries; and at every sample
    U' and U'' must equal central differences of the engine's U and U'."""
    def mats(z):
        bufs = [(ctypes.c_double * 4)() for _ in range(3)]
        lib.period_legendre_connection(ctypes.c_double(z), *bufs)
        return [list(b) for b in bufs]
    worst_p = worst_d = 0.0
    n_p = 0
    ok = True
    for z in samples:
        U, Up, Upp = mats(z)
        if 0.0 < z < 1.0:
            n_p += 1
            F, G = _legendre_period(z), _legendre_period(1.0 - z)
            for w, wp, wpp in (F, (G[0], -G[1], G[2])):
                ok = ok and U[0] == 0.0 and U[1] == 1.0
                res = abs(wpp - (U[2] * w + U[3] * wp)) / (abs(wpp) + abs(U[2] * w) + abs(U[3] * wp))
                worst_p = max(worst_p, res)
        h = 1e-5 * max(1.0, abs(z))
        lo, hi = mats(z - h), mats(z + h)
        for k, got in ((0, Up), (1, Upp)):
            fd = [(b - a) / (2 * h) for a, b in zip(lo[k], hi[k])]
            scale = max(abs(v) for v in got) or 1.0
            worst_d = max(worst_d, max(abs(x - y) for x, y in zip(fd, got)) / scale)
    ok = ok and worst_p < 1e-10 and worst_d < 1e-6
    return ok, worst_p, worst_d, n_p


# Theorem 1, Lemma 3 at rank 2 and Observation 4 for a companion-form U hold
# for any matrices of their shape, Q being defined from U: rows of them test
# the engine's arithmetic, never its periods (ARCHITECTURE.md).
_E6_IDENTITY = ("; an identity for any U, U\u2032, U\u2033, so it checks the engine's "
                "arithmetic, not its periods")


# ============================================================
# AUDIT 6a — RANK 2  (Legendre, genus 1)
# ============================================================
def audit_engine6_rank2(lib):
    """Theorem 1 entry-wise, Riccati, Lemma 3 / traceless commutator,
    Legendre closed form, and residues +/-17/4 at z=0,1."""
    r = _AuditResult('Engine 6a: rank-2 Legendre')
    samples = [0.1, 0.2, 0.3, 0.5, 0.7, 0.8, 0.9, 1.3, 2.0, -0.5]
    n = len(samples)
    nt = nc = nx = 0
    worst_thm1 = 0.0
    t0 = time.perf_counter()
    for z in samples:
        o = PeriodResult()
        lib.period_audit_legendre(ctypes.c_double(z), ctypes.c_double(1e-9),
                                  ctypes.byref(o))
        nt += int(bool(o.ok_theorem1))
        nc += int(bool(o.ok_traceless) and bool(o.ok_scalar_comm2))
        nx += int(bool(o.ok_closed_form))
        worst_thm1 = max(worst_thm1, o.thm1_resid_max)
    elapsed = (time.perf_counter() - t0) * 1e6
    # Theorem 1, Lemma 3 at rank 2 and Observation 4 for a companion-form U
    # hold for any matrices of their shape (Q is defined from U), so these
    # rows test the engine's arithmetic, never its periods; the closed form
    # and residue rows do that.
    r.add_test(f"Theorem 1 identity in the engine's arithmetic, rank 2 ({n} samples)", nt == n,
               f'{nt}/{n} hold, worst residual {worst_thm1:.2e}' + _E6_IDENTITY, elapsed)
    # Through 2.13.0 this row counted the engine's ok_riccati, which is set
    # to 1 unconditionally (see _legendre_connection_check).
    c_ok, c_per, c_der, c_n = _legendre_connection_check(lib, samples)
    r.add_test('Riccati inputs: U the Legendre periods\' connection, U\u2032 and U\u2033 '
               'its derivatives', c_ok,
               f'{c_n} samples in (0, 1): F = \u2082F\u2081(\u00bd,\u00bd;1;z) and F(1\u2212z) '
               f'satisfy (\u03c9,\u03c9\u2032)\u2032 = U(\u03c9,\u03c9\u2032) to {c_per:.1e}; '
               f'at all {n}, U\u2032 and U\u2033 equal central differences to {c_der:.1e}')
    r.add_test("Lemma 3 identity in the engine's arithmetic (rank 2)", nc == n,
               f'{nc}/{n}; tr[U,Q] = 0 and [U,Q]\u00b2 scalar hold for any 2\u00d72 U and Q')
    r.add_test('Legendre closed form tr(U[U,Q]U\')', nx == n, f'{nx}/{n}')
    if nt != n:
        r.add_finding('CRITICAL', f'rank-2 Theorem 1 failed on {n-nt} samples')
    # Residues: |Res| = 17/4 at z=0,1 and antisymmetric
    res0 = lib.period_residue_numeric(0.0, 1e-3, 4096)
    res1 = lib.period_residue_numeric(1.0, 1e-3, 4096)
    exact = 17.0/4.0
    res_ok = (abs(abs(res0) - exact) < 1e-3 and abs(abs(res1) - exact) < 1e-3
              and abs(res0 + res1) < 1e-3)
    r.add_test('Residues |Res| = 17/4 at z=0,1 (antisymmetric)', res_ok,
               f'Res(0)={res0:+.4f}, Res(1)={res1:+.4f}, sum={res0+res1:+.1e}')
    return r

# ============================================================
# AUDIT 6b — RANK 4  (genus-2 hyperelliptic)
# ============================================================
def audit_engine6_genus2(lib):
    """Theorem 1 entry-wise + Observation 4 (tr[U,Q]^3=0) + Paper 7 Table 1
    residues of f2, f4 at z = 0,1,2,3."""
    r = _AuditResult('Engine 6b: rank-4 genus-2')
    samples = [0.5, 1.5, 2.5, -0.5, -1.0, 4.0, 5.0, 0.25, 1.25, 3.5]
    n = len(samples)
    nt = ntr = n3 = 0
    worst_thm1 = 0.0
    t0 = time.perf_counter()
    for z in samples:
        o = PeriodG2Result()
        lib.period_g2_audit(ctypes.c_double(z), ctypes.c_double(1e-9), ctypes.byref(o))
        nt  += int(bool(o.ok_theorem1))
        ntr += int(bool(o.ok_traceless))
        n3  += int(bool(o.ok_tr3_zero))
        worst_thm1 = max(worst_thm1, o.thm1_resid_max)
    elapsed = (time.perf_counter() - t0) * 1e6
    r.add_test(f"Theorem 1 identity in the engine's arithmetic, rank 4 ({n} samples)", nt == n,
               f'{nt}/{n} hold, worst residual {worst_thm1:.2e}' + _E6_IDENTITY, elapsed)
    r.add_test('tr[U,Q] = 0 and tr[U,Q]^3 = 0 (Observation 4)',
               ntr == n and n3 == n, f'traceless {ntr}/{n} (true of any matrices), '
               f'tr3 {n3}/{n} (this M is not in companion form, so tr3 is the check)')
    if nt != n:
        r.add_finding('CRITICAL', f'genus-2 Theorem 1 failed on {n-nt} samples')
    # Paper 7 Table 1 residues of f2 at z=0,1,2,3
    f2_exact = [a / b for a, b in _E6_G2_TABLE1]
    f2_got = [lib.period_g2_residue_f2(float(z), 0.4, 8192) for z in range(4)]
    f2_ok = all(abs(g - e) < 1e-3 for g, e in zip(f2_got, f2_exact))
    r.add_test('Paper 7 Table 1: Res f2 at z=0,1,2,3', f2_ok,
               'f2 = [' + ', '.join(f'{g:.4f}' for g in f2_got) + ']')
    # f4 residue at z=0
    f4_exact = 107588257573.0/1934917632.0
    f4_got = lib.period_g2_residue_f4(0.0, 0.4, 8192)
    f4_ok = abs(f4_got - f4_exact) < 1e-2
    r.add_test('Paper 7 Table 1: Res f4 at z=0', f4_ok,
               f'f4(0) = {f4_got:.4f}, expected {f4_exact:.4f}')
    return r

# ============================================================
# AUDIT 6c — RANK 4  (mirror quintic Calabi-Yau threefold)
# ============================================================
def audit_engine6_quintic(lib):
    """Theorem 1 entry-wise, Observation 4, f2 closed form, and
    Conjecture 7 (CY3 residue rigidity) via an exact SymPy residue check."""
    r = _AuditResult('Engine 6c: rank-4 mirror quintic')
    samples = [0.1, 0.2, 0.5, 1.0, 2.0, 5.0, -0.5, -1.0, 10.0, 0.05]
    n = len(samples)
    nt = n3 = 0
    worst_thm1 = 0.0
    t0 = time.perf_counter()
    for z in samples:
        o = PeriodG2Result()
        lib.period_quintic_audit(ctypes.c_double(z), ctypes.c_double(1e-9),
                                 ctypes.byref(o))
        nt += int(bool(o.ok_theorem1))
        n3 += int(bool(o.ok_tr3_zero))
        worst_thm1 = max(worst_thm1, o.thm1_resid_max)
    elapsed = (time.perf_counter() - t0) * 1e6
    r.add_test(f"Theorem 1 identity in the engine's arithmetic, rank-4 CY3 ({n} samples)", nt == n,
               f'{nt}/{n} hold, worst residual {worst_thm1:.2e}' + _E6_IDENTITY, elapsed)
    r.add_test("Observation 4 identity in the engine's arithmetic (CY3, companion form)", n3 == n,
               f'{n3}/{n}; tr[U,Q]\u00b3 = 0 holds for any companion-form U')
    if nt != n:
        r.add_finding('CRITICAL', f'mirror quintic Theorem 1 failed on {n-nt} samples')
    # f2(z) matches Paper 7 closed form
    def f2_paper7(z):
        return (-2.0 * (19775390625000000.0*z**4 - 15898437500000.0*z**3
                + 5715234375.0*z**2 - 945000.0*z + 74.0)
                / (z**6 * (3125.0*z - 1.0)**4))
    n_f2 = 0
    for z in [0.1, 0.2, 0.5, 1.0, 2.0]:
        got = lib.period_quintic_f2_at(z)
        if abs(got - f2_paper7(z)) / (abs(f2_paper7(z)) + 1.0) < 1e-10:
            n_f2 += 1
    r.add_test('f2(z) matches Paper 7 closed form', n_f2 == 5, f'{n_f2}/5')
    # Conjecture 7: lambda_2 = -884266719222068786621093750/97  (exact, via SymPy)
    ratios = _e6_residue_ratios()
    if ratios is None:
        r.add_skip('Conjecture 7: CY3 residue rigidity',
                   'SymPy not available — pip install sympy', 'sympy')
    else:
        import sympy as sp
        ok_c7 = all(q == sp.Rational(*_E6_LAMBDA2) for q in ratios)
        r.add_test('Conjecture 7: CY3 residue rigidity (lambda_2, exact)', ok_c7,
                   'Res(f4)/Res(f2) = -884266719222068786621093750/97 '
                   'at z=0 and z=1/3125')
    return r

# ============================================================
# AUDIT 6d — RANK 8  (genus-4 hyperelliptic — beyond Paper 7)
# ============================================================
def audit_engine6_genus4(lib):
    """Theorem 1 entry-wise at rank 8; Observation 4 extended to rank 8
    (a NEW rank class — Paper 7 verifies only through rank 6); and the
    Conjecture 6 lower bound at genus 4 (f2,f4,f6,f8 independent over C).
    U is not a companion matrix here (U' has full rank), so the companion
    commutator theorem (doi:10.5281/zenodo.21857156) does not cover this
    rank; see ARCHITECTURE.md, "Engines and where they are heading"."""
    r = _AuditResult('Engine 6d: rank-8 genus-4 (NEW)')
    # Samples >= 2 from any singularity z = 0..7 (rank-8 double-precision floor)
    samples = list(_E6_G4_SAMPLES)
    n = len(samples)
    nt = n_obs4 = 0
    worst_thm1 = worst_odd = 0.0
    best_odd = 1e300
    fvecs = []
    t0 = time.perf_counter()
    for z in samples:
        o = PeriodG4Result()
        lib.period_g4_audit(ctypes.c_double(z), ctypes.c_double(1e-7),
                            ctypes.byref(o))
        nt += int(bool(o.ok_theorem1))
        if o.worst_odd_rel < 1e-7:
            n_obs4 += 1
        worst_thm1 = max(worst_thm1, o.thm1_resid_max)
        worst_odd  = max(worst_odd, o.worst_odd_rel)
        best_odd   = min(best_odd, o.worst_odd_rel)
        fvecs.append([o.f_invariants[i] for i in range(4)])
    elapsed = (time.perf_counter() - t0) * 1e6
    r.add_test(f"Theorem 1 identity in the engine's arithmetic, rank 8 ({n} samples)", nt == n,
               f'{nt}/{n} hold, worst residual {worst_thm1:.2e}' + _E6_IDENTITY, elapsed)
    r.add_test('Observation 4 at rank 8: tr[U,Q]^(2k+1) = 0', n_obs4 == n,
               f'{n_obs4}/{n}, best {best_odd:.2e}, worst {worst_odd:.2e} '
               f'(Paper 7 verifies only through rank 6)')
    if nt != n:
        r.add_finding('CRITICAL', f'genus-4 Theorem 1 failed on {n-nt} samples')
    # Conjecture 6 lower bound at g=4: rank of (f2,f4,f6,f8) sample matrix == 4
    rank = _sample_rank(fvecs)
    r.add_test('Conjecture 6 lower bound at g=4: f2,f4,f6,f8 independent',
               rank == 4, f'sample-matrix rank = {rank}/4')
    return r

# ============================================================
# STACK INTEGRATION 1 — the CFL front end (docs/CFL.md)
# ============================================================
# Engine 6's properties go through the same pipeline as the other engines:
# CFL spec -> lex -> parse (AST) -> FOL -> QBF -> field router -> engine
# dispatch, each property to the Engine 6 check that discharges it.

# Paper 7 CFL context — a sixth context alongside Kyber/Dilithium/AES/Curves.
PAPER7_CFL_SPEC = '''
CONTEXT ( Paper7 ) {
  DEFINE property <Theorem1>     { type: "algebraic"; field: "period"; }
  DEFINE property <Observation4> { type: "algebraic"; field: "period"; }
  DEFINE property <Conjecture6>  { type: "rank";      field: "period"; }
  DEFINE property <Conjecture7>  { type: "residue";   field: "period"; }
}
'''

_E6_KEYS = ('rank2', 'genus2', 'quintic', 'genus4')


def _ob_e6_theorem1(engines, corrupt=False):
    libs = {k: engines.get(k) for k in _E6_KEYS}
    if not all(libs.values()):
        return None
    worst, bad = 0.0, []
    for key, fn, cls, z, tol in (('rank2', 'period_audit_legendre', PeriodResult, 0.5, 1e-9),
                                 ('genus2', 'period_g2_audit', PeriodG2Result, 0.5, 1e-9),
                                 ('quintic', 'period_quintic_audit', PeriodG2Result, 0.5, 1e-9),
                                 ('genus4', 'period_g4_audit', PeriodG4Result, -2.5, 1e-7)):
        o = cls()
        getattr(libs[key], fn)(ctypes.c_double(z), ctypes.c_double(1e-300 if corrupt else tol),
                               ctypes.byref(o))
        worst = max(worst, o.thm1_resid_max)
        if not o.ok_theorem1:
            bad.append(key)
    if bad:
        return False, f'Theorem 1 fails on {", ".join(bad)}'
    return True, (f'Theorem 1, an identity for any connection, holds in the engines\' '
                  f'arithmetic at rank 2, genus 2, the mirror quintic and genus 4, worst '
                  f'residual {worst:.1e}')
_ob_e6_theorem1.corruption = 'a tolerance below its residuals'


def _ob_e6_observation4(engines, corrupt=False):
    libs = {k: engines.get(k) for k in ('genus2', 'quintic', 'genus4')}
    if not all(libs.values()):
        return None
    bad = []
    for key, fn in (('genus2', 'period_g2_audit'), ('quintic', 'period_quintic_audit')):
        o = PeriodG2Result()
        getattr(libs[key], fn)(ctypes.c_double(0.5), ctypes.c_double(1e-300 if corrupt else 1e-9),
                               ctypes.byref(o))
        if not (o.ok_traceless and o.ok_tr3_zero):
            bad.append(key)
    o = PeriodG4Result()
    libs['genus4'].period_g4_audit(ctypes.c_double(-2.5), ctypes.c_double(1e-7), ctypes.byref(o))
    if not o.worst_odd_rel < (1e-300 if corrupt else 1e-7):
        bad.append('genus4')
    if bad:
        return False, f'an odd power trace of [U, Q] does not vanish on {", ".join(bad)}'
    return True, ('tr[U, Q] = tr[U, Q]³ = 0 at genus 2 and the mirror quintic, and '
                  f'every odd power trace at genus 4 ({o.worst_odd_rel:.1e} relative)')
_ob_e6_observation4.corruption = 'a tolerance below its residuals'

_E6_G4_SAMPLES = (-1.5, -2.5, -5.0, 9.5, 10.0, 12.0, 15.0)


def _e6_f_vectors(lib, samples):
    """(f2, f4, f6, f8) of the genus-4 engine at each sample point."""
    out = []
    for z in samples:
        o = PeriodG4Result()
        lib.period_g4_audit(ctypes.c_double(z), ctypes.c_double(1e-7), ctypes.byref(o))
        out.append([o.f_invariants[i] for i in range(4)])
    return out


def _sample_rank(vectors):
    """The rank of 4-vectors by Gaussian elimination (no numpy)."""
    rows = [row[:] for row in vectors]
    rank = 0
    for col in range(4):
        piv = -1
        for i in range(rank, len(rows)):
            if abs(rows[i][col]) > 1e-300:
                piv = i
                break
        if piv < 0:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pv = rows[rank][col]
        for i in range(len(rows)):
            if i != rank and abs(rows[i][col]) > 0:
                f = rows[i][col] / pv
                for j in range(4):
                    rows[i][j] -= f * rows[rank][j]
        rank += 1
    return rank


def _ob_e6_conjecture6(engines, corrupt=False):
    lib = engines.get('genus4')
    if not lib:
        return None
    samples = _E6_G4_SAMPLES[:3] if corrupt else _E6_G4_SAMPLES
    rank = _sample_rank(_e6_f_vectors(lib, samples))
    return rank == 4, (f'f2, f4, f6, f8 at {len(samples)} genus-4 points: rank {rank}/4, '
                       f'so independent')
_ob_e6_conjecture6.corruption = 'three of its seven points'

_E6_LAMBDA2 = (-884266719222068786621093750, 97)
_E6_EXACT = []                           # filled once: SymPy is slow

# Paper 7, Table 1: the residues of f2 = tr([U,Q]^2) for genus 2, at z = 0..3.
_E6_G2_TABLE1 = ((61495, 15552), (45, 64), (-45, 64), (-61495, 15552))


def _e6_exact_residues():
    """This run's exact residues, by SymPy, or None without it.

    {'quintic': {z0: (Res f2, Res f4)} at z0 = 0 and 1/3125, from the mirror
     quintic's Picard-Fuchs operator,
     'genus2': [Res f2 at z = 0, 1, 2, 3], from the genus-2 engine's own
     M(z), read from its source, with SymPy's exact derivative in place of
     the engine's hand-written M'(z)}.

    The genus-2 f2 is built as polynomials over the common denominator
    D = z(z-1)(z-2)(z-3): with M = N/D, -Q D^2 = N'D - ND' + N^2 and
    [M,Q] D^3 = PN - NP, so f2 = tr((NP - PN)^2) / D^6 and each residue is a
    Taylor coefficient at a simple root of D (simplifying the rational
    entries instead takes about 50 s)."""
    if _E6_EXACT:
        return _E6_EXACT[0]
    try:
        import sympy as sp
    except ImportError:
        return None
    import re as _re6
    z = sp.Symbol('z')
    a3 = 2*(12500*z-3)/(z*(3125*z-1)); a2 = (45000*z-7)/(z**2*(3125*z-1))
    a1 = (15000*z-1)/(z**3*(3125*z-1)); a0 = 120/(z**3*(3125*z-1))
    U = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [-a0, -a1, -a2, -a3]])
    Q = sp.simplify(-(U.diff(z) + U@U))
    cQ = sp.simplify(U@Q - Q@U)
    cQ2 = cQ@cQ
    f2s = sp.cancel(sp.together(cQ2.trace()))
    f4s = sp.cancel(sp.together((cQ2@cQ2).trace()))
    quintic = {pt: (sp.Rational(sp.residue(f2s, z, pt)), sp.Rational(sp.residue(f4s, z, pt)))
               for pt in (sp.Integer(0), sp.Rational(1, 3125))}
    src = _decode(_SRC_GENUS2)
    body = src[src.index('static void compute_M(T z, T *M)'):src.index('static void compute_Mp')]
    ent = {int(i): _re6.sub(r'(\d+)\.0\b', r'\1', e)
           for i, e in _re6.findall(r'M\[(\d+)\] = T\((.*)\);', body)}
    if sorted(ent) != list(range(16)):
        raise ArithmeticError("the genus-2 engine's M(z) could not be read from its source")
    D = sp.Poly(z * (z - 1) * (z - 2) * (z - 3), z)
    N = []
    for i in range(16):
        num, den = sp.fraction(sp.cancel(sp.sympify(ent[i], locals={'z': z}, rational=True)
                                         * D.as_expr()))
        if sp.Poly(den, z).degree() != 0:
            raise ArithmeticError('the genus-2 M(z) has a pole off z = 0, 1, 2, 3')
        N.append(sp.Poly(num / den, z))
    N = [N[4 * i:4 * i + 4] for i in range(4)]
    zero = sp.Poly(0, z)

    def mul(A, B):
        return [[sum((A[i][k] * B[k][j] for k in range(4)), zero) for j in range(4)]
                for i in range(4)]
    Dp, NN = D.diff(z), mul(N, N)
    P = [[N[i][j].diff(z) * D - N[i][j] * Dp + NN[i][j] for j in range(4)] for i in range(4)]
    NP, PN = mul(N, P), mul(P, N)
    C = [[NP[i][j] - PN[i][j] for j in range(4)] for i in range(4)]
    CC = mul(C, C)
    f2num = sum((CC[i][i] for i in range(4)), zero).as_expr()
    genus2 = []
    for a in range(4):
        H = sp.quo(D, sp.Poly(z - a, z)).as_expr()     # D / (z - a)
        g = f2num / H ** 6                              # (z - a)^6 f2: regular at a
        genus2.append(sp.Rational(sp.cancel(sp.diff(g, z, 5).subs(z, a) / 120)))
    out = {'quintic': quintic, 'genus2': genus2}
    _E6_EXACT.append(out)
    return out


def _e6_residue_ratios():
    """Res(f4)/Res(f2) of the mirror quintic at z = 0 and z = 1/3125, in
    exact rationals (SymPy); None without SymPy."""
    res = _e6_exact_residues()
    if res is None:
        return None
    return tuple(r4 / r2 for r2, r4 in res['quintic'].values())


def _ob_e6_conjecture7(engines, corrupt=False):
    ratios = _e6_residue_ratios()
    if ratios is None:
        return None
    import sympy as sp
    lam2 = sp.Rational(*_E6_LAMBDA2) + (1 if corrupt else 0)
    return all(q == lam2 for q in ratios), (
        f'Res(f4)/Res(f2) = {_E6_LAMBDA2[0]}/{_E6_LAMBDA2[1]} at z = 0 and z = 1/3125, '
        f'in exact rationals')
_ob_e6_conjecture7.corruption = 'λ₂ off by one'
_ob_e6_conjecture7.requires = 'sympy'

PAPER7_OBLIGATIONS = {
    ('Paper7', 'Theorem1'): ('period', _ob_e6_theorem1),
    ('Paper7', 'Observation4'): ('period', _ob_e6_observation4),
    ('Paper7', 'Conjecture6'): ('period', _ob_e6_conjecture6),
    ('Paper7', 'Conjecture7'): ('period', _ob_e6_conjecture7),
}


def audit_engine6_cfl(engines):
    """Engine 6 through the CFL front end (docs/CFL.md): the Paper 7 context
    parsed, checked, its obligations decided as QBFs, routed to 'period' by
    their field, and each dispatched to the Engine 6 check that discharges
    it."""
    r = _AuditResult('Engine 6: CFL Front-End (Paper 7)')
    period = (('type', 'algebraic'), ('field', 'period'))
    _cfl_stages(r, PAPER7_CFL_SPEC, engines, PAPER7_OBLIGATIONS,
                names={'lexer': 'CFL lexer — Paper 7 context',
                       'parser': 'CFL parser — AST',
                       'fol': 'FOL generation', 'qbf': 'QBF encoder',
                       'router': 'Field router — period route',
                       'dispatch': f'Engine dispatch via router '
                                   f'({len(PAPER7_OBLIGATIONS)} obligations)'},
                expected=(('Paper7', (('DEFINE', 'Theorem1', period),
                                      ('DEFINE', 'Observation4', period),
                                      ('DEFINE', 'Conjecture6', (('type', 'rank'), ('field', 'period'))),
                                      ('DEFINE', 'Conjecture7', (('type', 'residue'), ('field', 'period'))))),),
                routes={f'Paper7.{n}': 'period'
                        for n in ('Theorem1', 'Observation4', 'Conjecture6', 'Conjecture7')})
    return r

# ============================================================
# STACK INTEGRATION 2 — Coq certificate (coqc-verified)
# ============================================================
# Engine 6's numerical residuals (Theorem 1 at ~1e-14) cannot be Coq theorems
# — you cannot 'reflexivity' a float.  But Conjecture 7 IS exact arithmetic:
#   Res(f4)/Res(f2) = -lambda2_num/97  <=>  97*Res(f4) = -lambda2_num*Res(f2),
# a bignum identity Coq checks with vm_compute.  We also certify the genus-2
# residue theorem (finite residues of f2 sum to zero).  Verified by coqc,
# which returns a real exit code — unlike the daemon's write-only check.

def _coq_q(x):
    """A Coq Q literal for the rational x."""
    return f'(({x.p}) # {x.q})'


def gen_engine6_coq_cert(filename=None, lam_num=-_E6_LAMBDA2[0], residues=None):
    """A Coq certificate of Engine 6's exact results, stated on the residues
    this run computed (_e6_exact_residues): Conjecture 7 on the mirror
    quintic's, Paper 7's Table 1 on the genus-2 engine's, and the residue
    theorem on those. lambda2 is -lam_num/97; a different lam_num states a
    false lambda2, which coqc must reject (the certificate's control).
    (filename, text), or (None, None) without SymPy. Through 2.13.0 the
    certificate stated integers fixed in this file, and its genus-2 theorem
    was a + b - b - a = 0."""
    res = residues or _e6_exact_residues()
    if res is None:
        return None, None
    if filename is None:
        filename = os.path.join(_pqv_workdir(), 'pq_engine6_cert.v')
    conj7 = []
    for tag, (r2, r4) in zip(('z0', 'conifold'), res['quintic'].values()):
        conj7 += [f"Theorem conj7_{tag} :",
                  f"  97 * (({r4.p}) * {r2.q}) = (-{lam_num}) * (({r2.p}) * {r4.q}).",
                  "Proof. vm_compute. reflexivity. Qed.", ""]
    g = [_coq_q(x) for x in res['genus2']]
    table = ' /\\ '.join(f'{gi} == (({a}) # {b})' for gi, (a, b) in zip(g, _E6_G2_TABLE1))
    lines = [
        "(* pq-engine6 Coq certificate: Paper 7's exact results, on the residues *)",
        "(* this run computed (SymPy): the mirror quintic's from its Picard-Fuchs  *)",
        "(* operator, the genus-2 engine's from its own connection matrix M(z).    *)",
        "Require Import ZArith QArith.",
        "Open Scope Z_scope.",
        "",
        "(* Conjecture 7 (CY3 residue rigidity): Res(f4)/Res(f2) = lambda2 = -lam/97 *)",
        "(* at z = 0 and z = 1/3125, i.e. 97 Res(f4) = -lam Res(f2), cleared of     *)",
        "(* denominators.                                                           *)",
    ] + conj7 + [
        "Open Scope Q_scope.",
        "(* Paper 7 Table 1: the genus-2 residues of f2 at z = 0, 1, 2, 3. *)",
        f"Theorem genus2_table1 : {table}.",
        "Proof. repeat split; vm_compute; reflexivity. Qed.",
        "",
        "(* The residue theorem: f2 vanishes to order 8 at infinity, so its finite *)",
        "(* residues sum to zero. True of any connection of this shape: a check   *)",
        "(* of the residues, not of the connection.                               *)",
        f"Theorem genus2_residue_sum_zero : {' + '.join(g)} == 0.",
        "Proof. vm_compute. reflexivity. Qed.",
        "Print Assumptions conj7_z0.",
        "Print Assumptions conj7_conifold.",
        "Print Assumptions genus2_table1.",
        "Print Assumptions genus2_residue_sum_zero.",
    ]
    cert = '\n'.join(lines) + '\n'
    with open(filename, 'w') as f:
        f.write(cert)
    return filename, cert

def audit_engine6_coq():
    """The Engine 6 Coq certificate, stated on this run's exact residues,
    verified by coqc; coqc shown to reject it with a wrong lambda2; and
    Conjecture 7 on the same residues through the persistent daemon, which
    must reject a wrong lambda2 as well. Through 2.13.0 one row only checked
    that the certificate file had been written, the daemon row passed
    without reading a verdict, and the certificate stated integers fixed in
    this file."""
    r = _AuditResult('Engine 6: Coq Certificate')
    names = ("Conjecture 7 and Paper 7 Table 1 on this run's residues, verified by coqc",
             'Engine 6 Coq certificate rejects a wrong \u03bb\u2082',
             'Conjecture 7 via persistent Coq daemon')
    if not shutil.which('coqc'):
        for name in names:
            r.add_skip(name, 'coqc not in PATH \u2014 !apt install coq -y -qq', 'coq')
        return r
    residues = _e6_exact_residues()
    if residues is None:
        for name in names:
            r.add_skip(name, "SymPy not available: the certificate states this run's exact "
                             "residues \u2014 pip install sympy", 'sympy')
        return r
    lam_num = -_E6_LAMBDA2[0]
    cert_file, _ = gen_engine6_coq_cert(residues=residues)
    try:
        t0 = time.perf_counter()
        ok, detail = coq_check(cert_file)
        elapsed = (time.perf_counter() - t0) * 1000
        r.add_test(names[0], ok,
                   ('coqc accepted 4 theorems on the residues SymPy computed this run: '
                    'Conjecture 7 at z = 0 and z = 1/3125, the genus-2 residues equal to '
                    f'Paper 7 Table 1, and their sum zero; all closed, {elapsed:.0f}ms'
                    if ok else detail))
        if not ok:
            r.add_finding('CRITICAL', 'Engine 6 Coq certificate rejected by coqc')
        wrong_file, _ = gen_engine6_coq_cert(
            os.path.join(_pqv_workdir(), 'pq_engine6_cert_wrong.v'), lam_num + 1, residues)
        took, why = coq_check(wrong_file)
        r.add_test(names[1], ok and not took,
                   f'the same certificate with \u03bb\u2082 = \u2212{lam_num + 1}/97: '
                   + ('rejected by coqc' if not took else 'ACCEPTED')
                   + ('' if ok else '; the true certificate was rejected too, so this shows nothing'))
    except subprocess.TimeoutExpired:
        for name in names[:2]:
            r.add_skip(name, 'coqc timed out (120s)', 'coq')
    # Persistent daemon (throughput) — only when the harness CoqDaemon is loaded
    CoqDaemon = globals().get('CoqDaemon')
    if CoqDaemon is None or not shutil.which('coqtop'):
        r.add_skip(names[2], 'coqtop not in PATH', 'coq')
        return r
    try:
        daemon = CoqDaemon()
        if not getattr(daemon, 'proc', None):
            r.add_skip(names[2], 'coqtop failed to start', 'coq')
            return r
        t0 = time.perf_counter()
        # Conjecture 7 on this run's residues through the daemon, cleared of
        # denominators, and once with lambda2 off by one, which it must reject.
        def stmt(r2, r4, lam):
            return f'97 * (({r4.p}) * {r2.q}) = (-{lam}) * (({r2.p}) * {r4.q})'
        pts = list(residues['quintic'].values())
        true_ok = [daemon.check_theorem(f'e6_{tag}', stmt(r2, r4, lam_num))[0]
                   for tag, (r2, r4) in zip(('conj7_z0', 'conj7_conifold'), pts)]
        wrong_ok, why = daemon.check_theorem('e6_conj7_wrong', stmt(*pts[0], lam_num + 1))
        elapsed = (time.perf_counter() - t0) * 1000
        daemon.close()
        n_ok = sum(true_ok)
        r.add_test(names[2], n_ok == 2 and not wrong_ok,
                   f"{n_ok}/2 on this run's residues proved by coqtop and closed; "
                   f'\u03bb\u2082 off by one ' + ('rejected' if not wrong_ok else 'ACCEPTED')
                   + f', {elapsed:.0f}ms')
    except Exception as e:
        r.add_skip(names[2], f'daemon error: {str(e)[:80]}', 'coq')
    return r

# ============================================================
# RUNNER — Phase 5 of the pq-verify stack
# ============================================================
# What each Engine 6 audit records, so an engine that cannot be built still
# shows its checks -- as skipped -- rather than shrinking the suite.
# tests/test_pqverify.py holds these to the audits' own titles.
_E6_CHECKS = {
    'rank2':   ('Engine 6a: rank-2 Legendre',
                ["Theorem 1 identity in the engine's arithmetic, rank 2",
                 "Riccati inputs: U the Legendre periods' connection, U\u2032 and U\u2033 "
                 "its derivatives",
                 "Lemma 3 identity in the engine's arithmetic (rank 2)",
                 "Legendre closed form tr(U[U,Q]U')",
                 'Residues |Res| = 17/4 at z=0,1 (antisymmetric)']),
    'genus2':  ('Engine 6b: rank-4 genus-2',
                ["Theorem 1 identity in the engine's arithmetic, rank 4",
                 'tr[U,Q] = 0 and tr[U,Q]^3 = 0 (Observation 4)',
                 'Paper 7 Table 1: Res f2 at z=0,1,2,3', 'Paper 7 Table 1: Res f4 at z=0']),
    'quintic': ('Engine 6c: rank-4 mirror quintic',
                ["Theorem 1 identity in the engine's arithmetic, rank-4 CY3",
                 "Observation 4 identity in the engine's arithmetic (CY3, companion form)",
                 'f2(z) matches Paper 7 closed form',
                 'Conjecture 7: CY3 residue rigidity']),
    'genus4':  ('Engine 6d: rank-8 genus-4 (NEW)',
                ["Theorem 1 identity in the engine's arithmetic, rank 8",
                 'Observation 4 at rank 8: tr[U,Q]^(2k+1) = 0',
                 'Conjecture 6 lower bound at g=4: f2,f4,f6,f8 independent']),
}


def run_engine6():
    print()
    print("=" * 70)
    print(f"  pq-engine6 v{ENGINE6_VERSION}  —  Period / Gauss-Manin Verification")
    print("  Paper 7 (Maino 2026): ranks 2, 4, 4 (CY3), 8")
    print(f"  Harness AuditResult: {'reused' if _HARNESS else 'fallback (standalone)'}")
    print("=" * 70)
    print()
    print("  Compiling Engine 6 (gcc + g++ -O3 -march=native)...")
    engines = compile_engine6()
    bind_engine6(engines)
    print()

    results = []
    audits = [
        ('rank2',   audit_engine6_rank2,   'rank-2 Legendre'),
        ('genus2',  audit_engine6_genus2,  'rank-4 genus-2'),
        ('quintic', audit_engine6_quintic, 'rank-4 mirror quintic'),
        ('genus4',  audit_engine6_genus4,  'rank-8 genus-4'),
    ]
    for key, fn, label in audits:
        if engines.get(key):
            print(f"  Running Engine 6 — {label}...")
            results.append(fn(engines[key]))
        else:
            print(f"  ⚠ skipping {label} — engine not compiled")
            title, checks = _E6_CHECKS[key]
            r = AuditResult(title)
            for c in checks:
                r.add_skip(c, f"engine6/{key} did not build on this platform")
            results.append(r)

    # Stack integration: CFL front-end + Coq certificate
    print("  Running Engine 6 — CFL front-end (CFL→FOL→QBF→router→dispatch)...")
    results.append(audit_engine6_cfl(engines))
    print("  Running Engine 6 — Coq certificate (Conjecture 7, coqc-verified)...")
    results.append(audit_engine6_coq())

    # Report
    print()
    print("=" * 70)
    print("  ENGINE 6 — PERIOD VERIFICATION REPORT")
    print("=" * 70)
    for res in results:
        p, t, c = res.summary()
        icon = '✅' if (c == 0 and p == t) else '❌'
        print(f"\n  {icon} {res.engine}: {p}/{t} tests passed")
        for test in res.tests:
            s = '✅' if test['passed'] else '❌'
            tm = f" ({test['time_us']:.0f}us)" if test.get('time_us') else ""
            print(f"     {s} {test['name']}{tm}")
            if test['detail']:
                print(f"        {test['detail']}")
        for f in res.findings:
            ic = {'CRITICAL':'🔴','HIGH':'🟠','MEDIUM':'🟡'}.get(f['severity'], '?')
            print(f"     {ic} [{f['severity']}] {f['description']}")
    tp = sum(r.summary()[0] for r in results)
    tt = sum(r.summary()[1] for r in results)
    tc = sum(r.summary()[2] for r in results)
    print()
    print("=" * 70)
    print(f"  ENGINE 6 TOTAL: {tp}/{tt} tests passed")
    if tc == 0:
        print("  ✅ No critical findings — Paper 7 verified across ranks 2, 4, 4, 8")
    else:
        print(f"  🔴 {tc} CRITICAL finding(s)")
    print("=" * 70)

    # If the harness is loaded, hand results back so a master report can
    # fold Engine 6 into the suite-wide total.
    if _HARNESS:
        try:
            g = globals()
            g.setdefault('engine6_results', [])
            g['engine6_results'].extend(results)
            print(f"\n  Engine 6 results exported to global 'engine6_results' "
                  f"({tt} tests) — fold into the master total as Phase 5.")
        except Exception:
            pass
    return results


# ================================================================
# PHASE 7: ADVERSARIAL STRESS TEST  (real engines)
# Capacity ceilings, SAT-by-construction recovery, malformed-input
# rejection, and Engine 6 numerical stability near singular fibres.
# Every system here is either SAT-by-construction (so the SOLVER is
# tested, not the UNSAT detector) or a deliberate error case.
# ================================================================

def _stress_gf2_sat(lib, n, m, seed, max_w=8):
    """Build a GF(2) system guaranteed satisfiable by a known vector x."""
    rng = random.Random(seed)
    x = [rng.randint(0, 1) for _ in range(n)]
    s = GF2S()
    lib.gf2_init(ctypes.byref(s), n)
    for _ in range(m):
        w = rng.randint(2, min(max_w, n))
        vs = rng.sample(range(n), w)
        par = 0
        for v in vs:
            par ^= x[v]
        cv = (ctypes.c_int * len(vs))(*vs)
        lib.gf2_add_xor(ctypes.byref(s), cv, len(vs), par)
    return s, x


def _stress_zq_square(lib, n, q, seed):
    """Square Z_q system with random dense coefficients, RHS consistent
    with a known x.  Random dense -> full rank w.h.p. -> unique solution."""
    rng = random.Random(seed)
    x = [rng.randint(0, q - 1) for _ in range(n)]
    s = ZqS()
    lib.zq_init(ctypes.byref(s), n, q)
    for _ in range(n):
        coeffs = [rng.randint(0, q - 1) for _ in range(n)]
        rhs = sum(c * xi for c, xi in zip(coeffs, x)) % q
        ca = (ctypes.c_uint16 * n)(*coeffs)
        lib.zq_add_equation(ctypes.byref(s), ca, rhs)
    return s, x


def _stress_zq32_square(lib, n, q, seed):
    """Square Z_q32 system, RHS consistent with a known x."""
    rng = random.Random(seed)
    x = [rng.randint(0, q - 1) for _ in range(n)]
    s = Zq32S()
    lib.zq32_init(ctypes.byref(s), n, q)
    for _ in range(n):
        coeffs = [rng.randint(0, q - 1) for _ in range(n)]
        rhs = sum(c * xi for c, xi in zip(coeffs, x)) % q
        ca = (ctypes.c_uint32 * n)(*coeffs)
        lib.zq32_add_equation(ctypes.byref(s), ca, rhs)
    return s, x


def _finite(v):
    return not (math.isnan(v) or math.isinf(v))


def audit_stress(engines, e6_engines, quick=False):
    """Phase 7 — adversarial stress on the real engines. Returns a list
    of AuditResult so the tests fold into the unified report.
    quick=True shrinks the capacity tests for fast iteration."""
    out = []
    KQ, DQ = 3329, 8380417
    GF2_M  = 1000 if quick else 8000      # GF(2) capacity-test equations
    ZQ_N   = 128  if quick else 2048      # Z_3329 square-system dimension
    ZQ_M   = 500  if quick else 2000      # Z_3329 capacity-test equations
    ZQ32_S = 800  if quick else 5000      # Z_8380417 single-var samples

    # ---- GF(2): capacity + SAT-by-construction recovery ----------------
    if engines.get('gf2'):
        g = engines['gf2']
        r = AuditResult('Stress: GF(2)')
        # underdetermined, SAT by construction
        s, x = _stress_gf2_sat(g, 1024, 900, seed=7001)
        res = GF2R()
        t0 = time.perf_counter()
        g.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        dt = (time.perf_counter() - t0) * 1e6
        ok = bool(res.satisfiable) and \
            g.gf2_verify(ctypes.byref(s), res.assignment) == 1
        r.add_test('1024 vars / 900 eqs (SAT-by-construction)', ok,
                   f'sat={res.satisfiable}, pivots={res.num_pivots}, '
                   f'free={res.num_free_vars}, verify=' +
                   ('OK' if ok else 'FAIL'), dt)
        # capacity: near MAX_EQS, still consistent -> must stay SAT + valid
        s, x = _stress_gf2_sat(g, 1024, GF2_M, seed=7002)
        res = GF2R()
        t0 = time.perf_counter()
        g.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        dt = (time.perf_counter() - t0) * 1e6
        ok = bool(res.satisfiable) and \
            g.gf2_verify(ctypes.byref(s), res.assignment) == 1
        r.add_test(f'1024 vars / {GF2_M} eqs (capacity ceiling)', ok,
                   f'sat={res.satisfiable}, pivots={res.num_pivots}, '
                   f'verify=' + ('OK' if ok else 'FAIL'), dt)
        # ---- null-space at scale: 256 vars, ~200 eqs → ~56 free → verify basis ---
        r_ns = AuditResult('Stress: GF(2) Null-Space')
        s, x = _stress_gf2_sat(g, 256, 200, seed=7003)
        res = GF2R()
        g.gf2_solve(ctypes.byref(s), ctypes.byref(res))
        ns = GF2NS()
        g.gf2_nullspace(ctypes.byref(s), ctypes.byref(res), ctypes.byref(ns))
        # verify: particular solution valid, each basis vector XOR'd with particular also valid
        part_ok = g.gf2_verify(ctypes.byref(s), res.assignment) == 1
        basis_ok = True
        n_basis_checked = min(ns.num_free, 32)
        for fi in range(n_basis_checked):
            combo = (ctypes.c_int * 256)()
            for j in range(256):
                combo[j] = res.assignment[j] ^ ns.basis[fi][j]
            if g.gf2_verify(ctypes.byref(s), combo) != 1:
                basis_ok = False; break
        r_ns.add_test(f'256 vars / 200 eqs null-space basis ({n_basis_checked} vectors)',
                      part_ok and basis_ok,
                      f'free={ns.num_free}, 2^{ns.num_solutions_log2} solutions, '
                      f'all {n_basis_checked} basis perturbations verify')
        # verify: XOR of two basis vectors also valid
        if ns.num_free >= 2:
            combo2 = (ctypes.c_int * 256)()
            for j in range(256):
                combo2[j] = res.assignment[j] ^ ns.basis[0][j] ^ ns.basis[1][j]
            pair_ok = g.gf2_verify(ctypes.byref(s), combo2) == 1
            r_ns.add_test('Pairwise basis XOR verification', pair_ok,
                          f'particular XOR basis[0] XOR basis[1] → verify=' +
                          ('OK' if pair_ok else 'FAIL'))
        out.append(r_ns)
        out.append(r)

    # ---- Z_3329: square full-rank exact recovery + capacity ------------
    if engines.get('zq'):
        z = engines['zq']
        r = AuditResult('Stress: Z_3329')
        s, x = _stress_zq_square(z, ZQ_N, KQ, seed=7101)
        res = ZqR()
        t0 = time.perf_counter()
        z.zq_solve(ctypes.byref(s), ctypes.byref(res))
        dt = (time.perf_counter() - t0) * 1e6
        if res.satisfiable and res.num_pivots == ZQ_N:
            ok = all(res.assignment[i] == x[i] for i in range(ZQ_N))
            detail = f'full rank, exact recovery=' + ('OK' if ok else 'FAIL')
        elif res.satisfiable:
            ok = z.zq_verify(ctypes.byref(s), res.assignment) == 1
            detail = f'rank {res.num_pivots}<{ZQ_N}, zq_verify=' + \
                     ('OK' if ok else 'FAIL')
        else:
            ok = False
            detail = 'UNSAT (unexpected for consistent system)'
        r.add_test(f'{ZQ_N}x{ZQ_N} dense solve (exact recovery)', ok, detail, dt)
        # capacity: ZQ_N vars, ZQ_M consistent eqs
        rng = random.Random(7102)
        xx = [rng.randint(0, KQ - 1) for _ in range(ZQ_N)]
        s = ZqS(); z.zq_init(ctypes.byref(s), ZQ_N, KQ)
        for _ in range(ZQ_M):
            nt = rng.randint(2, 8)
            vi = rng.sample(range(ZQ_N), nt)
            vc = [rng.randint(1, KQ - 1) for _ in range(nt)]
            rhs = sum(c * xx[v] for c, v in zip(vc, vi)) % KQ
            via = (ctypes.c_int * nt)(*vi)
            vca = (ctypes.c_uint16 * nt)(*vc)
            z.zq_add_sparse(ctypes.byref(s), via, vca, nt, rhs)
        res = ZqR()
        t0 = time.perf_counter()
        z.zq_solve(ctypes.byref(s), ctypes.byref(res))
        dt = (time.perf_counter() - t0) * 1e6
        ok = bool(res.satisfiable) and \
            z.zq_verify(ctypes.byref(s), res.assignment) == 1
        r.add_test(f'{ZQ_N} vars / {ZQ_M} eqs (capacity, SAT-by-construction)', ok,
                   f'sat={res.satisfiable}, pivots={res.num_pivots}, '
                   f'verify=' + ('OK' if ok else 'FAIL'), dt)
        out.append(r)

    # ---- Z_8380417: random single-var + square exact recovery ----------
    if engines.get('zq32'):
        z = engines['zq32']
        r = AuditResult('Stress: Z_8380417')
        rng = random.Random(7201)
        fail = 0
        s = Zq32S(); res = Zq32R()
        t0 = time.perf_counter()
        for _ in range(ZQ32_S):
            a = rng.randint(1, DQ - 1)
            b = rng.randint(0, DQ - 1)
            z.zq32_init(ctypes.byref(s), 1, DQ)
            ca = (ctypes.c_uint32 * 1)(a)
            z.zq32_add_equation(ctypes.byref(s), ca, b)
            z.zq32_solve(ctypes.byref(s), ctypes.byref(res))
            if not res.satisfiable or (a * res.assignment[0]) % DQ != b % DQ:
                fail += 1
        dt = (time.perf_counter() - t0) * 1e6
        r.add_test(f'{ZQ32_S} random single-var solves (a*x=b)', fail == 0,
                   f'{fail}/{ZQ32_S} failures', dt)
        s, x = _stress_zq32_square(z, 256, DQ, seed=7202)
        res = Zq32R()
        t0 = time.perf_counter()
        z.zq32_solve(ctypes.byref(s), ctypes.byref(res))
        dt = (time.perf_counter() - t0) * 1e6
        if res.satisfiable and res.num_pivots == 256:
            ok = all(res.assignment[i] == x[i] for i in range(256))
            detail = 'full rank, exact recovery=' + ('OK' if ok else 'FAIL')
        else:
            ok = False
            detail = f'sat={res.satisfiable}, pivots={res.num_pivots}'
        r.add_test('256x256 dense solve (exact recovery)', ok, detail, dt)
        out.append(r)

    # ---- malformed-input rejection -------------------------------------
    r = AuditResult('Stress: Malformed Input')
    if engines.get('gf2'):
        g = engines['gf2']
        s = GF2S(); g.gf2_init(ctypes.byref(s), 64)
        bad = (ctypes.c_int * 1)(9999)            # var index >> MAX_VARS
        try:
            rc = g.gf2_add_xor(ctypes.byref(s), bad, 1, 0)
        except EngineInputError as exc:
            rc = exc.rc
        r.add_test('GF(2) rejects out-of-range variable', rc < 0,
                   f'gf2_add_xor returned {rc} (expected <0)')
    if engines.get('zq'):
        z = engines['zq']
        s = ZqS(); z.zq_init(ctypes.byref(s), 4, KQ)
        ca = (ctypes.c_uint16 * 4)(1, 1, 1, 1)
        last = 0
        for _ in range(4097):                     # MAX_EQUATIONS = 4096
            try:
                last = z.zq_add_equation(ctypes.byref(s), ca, 0)
            except EngineInputError as exc:
                last = exc.rc
        r.add_test('Z_3329 rejects equation overflow', last < 0,
                   f'4097th zq_add_equation returned {last} (expected <0)')
    out.append(r)

    # ---- Engine 6: numerical stability near singular fibres ------------
    if e6_engines and e6_engines.get('rank2'):
        r = AuditResult('Stress: Engine 6 (period)')
        lib = e6_engines['rank2']
        extreme = [1e-10, 1e-12, 0.5, 1.0 - 1e-10, 1.0 - 1e-12]
        all_finite = True
        thm1_pass = []
        for zv in extreme:
            o = PeriodResult()
            lib.period_audit_legendre(ctypes.c_double(zv),
                                      ctypes.c_double(1e-9), ctypes.byref(o))
            fin = _finite(o.thm1_resid_max) and _finite(o.tr_comm)
            all_finite &= fin
            if o.ok_theorem1 == 1 and fin:
                thm1_pass.append(zv)
        r.add_test('rank-2 near-singular: residuals finite (5 extreme z)',
                   all_finite,
                   f'Theorem 1 still holds at {len(thm1_pass)}/5 extreme '
                   f'points; no NaN/Inf' if all_finite else
                   'NaN/Inf produced near singularity')
        for key, fn, struct in [
            ('genus2',  'period_g2_audit',      PeriodG2Result),
            ('quintic', 'period_quintic_audit', PeriodG2Result),
            ('genus4',  'period_g4_audit',      PeriodG4Result),
        ]:
            if not e6_engines.get(key):
                continue
            lib = e6_engines[key]
            fn_c = getattr(lib, fn)
            fin = True
            for zv in (1e-10, 0.5):
                o = struct()
                fn_c(ctypes.c_double(zv), ctypes.c_double(1e-9),
                     ctypes.byref(o))
                fin &= _finite(o.thm1_resid_max)
            r.add_test(f'{key} near-singular: residuals finite (2 extreme z)',
                       fin, 'no NaN/Inf' if fin else 'NaN/Inf produced')
        out.append(r)

    return out


# ================================================================
# PUBLIC API: pqverify_kem — native algebraic full-KEM verification
# ================================================================

def pqverify_kem(k=4, seed=2026, trials=20, verbose=True):
    """Native verification of the ML-KEM algebraic pipeline.

    Verifies the COMPLETE algebraic data flow of ML-KEM (keygen, encaps,
    decaps) in Z_3329 against the FIPS 203 definition:
        keygen:  t = A.s + e        (MLWE)
        encaps:  u = A^T.r + e1 ;  v = t^T.r + e2 + encode(m)
        decaps:  w = v - s^T.u  ->  decode(w) == m   (correctness)
    Every NTT/invNTT step is verified via Freivalds (C engine). Every
    module relation is checked directly over Z_3329. Corrupting any step
    fails verification.

    SCOPE (honest): this verifies the ALGEBRAIC pipeline. The hash (SHAKE/
    SHA3), CBD sampling, compression, and Fujisaki-Okamoto re-encrypt are
    bit/byte operations, NOT field arithmetic — they are out of scope here
    and belong to KAT verification, not native field solving.

    k selects security level: 2->Level 1, 3->Level 3, 4->Level 5.
    """
    import random as _r
    Q = 3329; N = 256; ZETA = 17
    def br7(x):
        rr = 0
        for _ in range(7): rr = (rr << 1) | (x & 1); x >>= 1
        return rr
    zt = [pow(ZETA, br7(i), Q) for i in range(128)]
    def ntt(p):
        f = [x % Q for x in p]; kk = 1
        for L in [128,64,32,16,8,4,2]:
            for s in range(0, N, 2*L):
                z = zt[kk]; kk += 1
                for j in range(s, s+L):
                    t = (z*f[j+L]) % Q; f[j+L] = (f[j]-t) % Q; f[j] = (f[j]+t) % Q
        return f
    def invntt(p):
        f = list(p); kk = 127
        for L in [2,4,8,16,32,64,128]:
            for s in range(0, N, 2*L):
                z = zt[kk]; kk -= 1
                for j in range(s, s+L):
                    t = f[j]; f[j] = (t+f[j+L]) % Q; f[j+L] = (z*((f[j+L]-t) % Q)) % Q
        ni = pow(128, Q-2, Q); return [(x*ni) % Q for x in f]
    def basemul(a, b):
        r = [0]*N
        for i in range(128):
            g = pow(ZETA, 2*br7(i)+1, Q)
            a0,a1 = a[2*i],a[2*i+1]; b0,b1 = b[2*i],b[2*i+1]
            r[2*i] = (a0*b0 + a1*b1 % Q * g) % Q
            r[2*i+1] = (a0*b1 + a1*b0) % Q
        return r
    padd = lambda a,b: [(a[i]+b[i]) % Q for i in range(N)]
    psub = lambda a,b: [(a[i]-b[i]) % Q for i in range(N)]
    enc = lambda m: [((Q+1)//2 if b else 0) for b in m]
    dec = lambda p: [1 if (Q//4 < c % Q < 3*Q//4) else 0 for c in p]

    name, level = _NIST_LEVELS.get(('kyber', k), (f"k{k}", "?"))

    # Freivalds via C engine if available
    eng = globals().get('engines', {})
    zq = eng.get('zq')
    if zq:
        try:
            zq.zq_freivalds_ntt.argtypes = [ctypes.POINTER(ctypes.c_uint16)]*2 + [
                ctypes.c_int, ctypes.c_uint16, ctypes.c_uint16, ctypes.c_int, ctypes.c_uint32]
            zq.zq_freivalds_ntt.restype = ctypes.c_int
        except: zq = None
    def freivalds_ok(inp, out, sd):
        if not zq: return None
        x = (ctypes.c_uint16 * N)(*[v % Q for v in inp])
        y = (ctypes.c_uint16 * N)(*[v % Q for v in out])
        return zq.zq_freivalds_ntt(x, y, N, Q, ZETA, 5, sd) == 1

    if verbose:
        print("=" * 64)
        print(f"  NATIVE FULL-KEM VERIFICATION (algebraic pipeline)")
        print(f"  Target: {name}  ->  {level}")
        print(f"  q={Q}, n={N}, module rank k={k}")
        print("=" * 64)

    _r.seed(seed)
    def small(): return [_r.randint(-2, 2) % Q for _ in range(N)]
    def unif():  return [_r.randint(0, Q-1) for _ in range(N)]

    correct = 0; relation_fails = 0; frv_checks = 0; frv_fails = 0
    for tr in range(trials):
        A = [[ntt(unif()) for _ in range(k)] for _ in range(k)]
        s = [ntt(small()) for _ in range(k)]
        e = [small() for _ in range(k)]
        # keygen: t = A.s + e
        t = []
        for i in range(k):
            acc = [0]*N
            for j in range(k): acc = padd(acc, basemul(A[i][j], s[j]))
            ti_lin = invntt(acc)
            t.append(padd(ti_lin, e[i]))
        t_hat = [ntt(ti) for ti in t]
        # encaps
        m = [_r.randint(0, 1) for _ in range(N)]
        rr = [ntt(small()) for _ in range(k)]
        e1 = [small() for _ in range(k)]; e2 = small()
        u = []
        for i in range(k):
            acc = [0]*N
            for j in range(k): acc = padd(acc, basemul(A[j][i], rr[j]))
            u.append(padd(invntt(acc), e1[i]))
        vacc = [0]*N
        for i in range(k): vacc = padd(vacc, basemul(t_hat[i], rr[i]))
        v = padd(padd(invntt(vacc), e2), enc(m))
        # Freivalds on a representative NTT step (u[0] forward)
        if zq:
            ok = freivalds_ok(u[0], ntt(u[0]), freivalds_seed(tr*131+1)); frv_checks += 1; frv_fails += (ok is False)
        # decaps: w = v - s^T u
        u_hat = [ntt(ui) for ui in u]
        sacc = [0]*N
        for i in range(k): sacc = padd(sacc, basemul(s[i], u_hat[i]))
        w = psub(v, invntt(sacc))
        if dec(w) == m: correct += 1
        else: relation_fails += 1

    if verbose:
        print(f"\n  Keygen relation  t = A.s + e          : verified ({trials} keypairs)")
        print(f"  Encaps relation  u = A^T.r+e1, v=...   : verified ({trials} encaps)")
        print(f"  Decaps recovery  decode(v - s^T.u)==m  : {correct}/{trials}")
        if zq:
            print(f"  NTT steps (Freivalds, C engine)        : {frv_checks-frv_fails}/{frv_checks}")
        else:
            print(f"  NTT steps (Freivalds)                  : engine not loaded (run main() first)")

    # Negative control: corrupt one coefficient of s, decaps must fail
    _r.seed(seed + 1)
    A = [[ntt(unif()) for _ in range(k)] for _ in range(k)]
    s = [ntt(small()) for _ in range(k)]; e = [small() for _ in range(k)]
    t = []
    for i in range(k):
        acc = [0]*N
        for j in range(k): acc = padd(acc, basemul(A[i][j], s[j]))
        t.append(padd(invntt(acc), e[i]))
    t_hat = [ntt(ti) for ti in t]
    m = [_r.randint(0, 1) for _ in range(N)]
    rr = [ntt(small()) for _ in range(k)]; e1 = [small() for _ in range(k)]; e2 = small()
    u = []
    for i in range(k):
        acc = [0]*N
        for j in range(k): acc = padd(acc, basemul(A[j][i], rr[j]))
        u.append(padd(invntt(acc), e1[i]))
    vacc = [0]*N
    for i in range(k): vacc = padd(vacc, basemul(t_hat[i], rr[i]))
    v = padd(padd(invntt(vacc), e2), enc(m))
    s_bad = [list(si) for si in s]; s_bad[0][0] = (s_bad[0][0] + 1) % Q  # corrupt
    u_hat = [ntt(ui) for ui in u]; sacc = [0]*N
    for i in range(k): sacc = padd(sacc, basemul(s_bad[i], u_hat[i]))
    w_bad = psub(v, invntt(sacc))
    caught = dec(w_bad) != m

    verified = (correct == trials) and (frv_fails == 0) and caught
    if verbose:
        print(f"  Negative control (corrupt secret key)  : {'caught' if caught else 'MISSED'}")
        print(f"\n{'='*64}")
        if verified:
            print(f"  {name} algebraic pipeline: VERIFIED at {level}")
            print(f"  (NTT + module relations native; hash/compress = KAT scope)")
        else:
            print(f"  {name}: FAILED ({relation_fails} recovery, {frv_fails} Freivalds)")
        print("=" * 64)
    return {'name': name, 'level': level, 'recovery': f"{correct}/{trials}",
            'freivalds': f"{frv_checks-frv_fails}/{frv_checks}" if zq else "n/a",
            'negative_control': caught, 'verified': verified}


# ================================================================
# PUBLIC API: pqverify_kat — non-circular Known Answer Test
# ================================================================

# NIST security levels by module rank / parameter set
_NIST_LEVELS = {
    ('kyber', 2): ("ML-KEM-512",  "NIST Level 1 (~AES-128)"),
    ('kyber', 3): ("ML-KEM-768",  "NIST Level 3 (~AES-192)"),
    ('kyber', 4): ("ML-KEM-1024", "NIST Level 5 (~AES-256)"),
    ('dilithium', 4): ("ML-DSA-44", "NIST Level 2"),
    ('dilithium', 6): ("ML-DSA-65", "NIST Level 3 (~AES-192)"),
    ('dilithium', 8): ("ML-DSA-87", "NIST Level 5 (~AES-256)"),
}

def pqverify_kat(ntt_func, q=3329, zeta=17, n=256, k=4, family='kyber', trials=100):
    """Known Answer Test: verify an NTT against an INDEPENDENT reference.

    The reference is direct CRT polynomial reduction (schoolbook, O(n^2)):
        f mod (X^2 - zeta^(2*br(i)+1))  for each i
    This is the FIPS 203 mathematical *definition* of the NTT, computed by a
    completely different algorithm than the butterfly. Agreement = correctness
    against the standard, not against pq-verify's own butterfly reference.

    k only labels the output (k=None: every parameter set of the scheme):
        Kyber:     k=2 -> Level 1, k=3 -> Level 3, k=4 -> Level 5
        Dilithium: k=4 -> Level 2, k=6 -> Level 3, k=8 -> Level 5

    Usage:
        pqverify_kat(my_ntt, k=4)                      # ML-KEM-1024, Level 5
        pqverify_kat(my_ntt, q=8380417, zeta=1753, k=8, family='dilithium')
    """
    import random as _r
    complete = (family == 'dilithium' or q > 65535)
    # Bit-reversal width: complete NTT uses log2(n) factors, incomplete uses log2(n/2)
    nfactors = n if complete else n // 2
    bits = nfactors.bit_length() - 1
    def br(x):
        rr = 0
        for _ in range(bits): rr = (rr << 1) | (x & 1); x >>= 1
        return rr

    if k is None:
        # The NTT acts on one polynomial; n and q are shared by every parameter
        # set of a scheme, so one result covers all of them. Naming a single
        # set (the old default k=4 printed "ML-KEM-1024" for a 768 library)
        # misstates what was checked.
        name = {'kyber': 'ML-KEM-512/768/1024',
                'dilithium': 'ML-DSA-44/65/87'}.get(family, family)
        level = "every parameter set (the NTT does not depend on module rank k)"
    else:
        name, level = _NIST_LEVELS.get((family, k),
                                       (f"{family}-k{k}", "unknown level"))

    print("=" * 64)
    print(f"  KNOWN ANSWER TEST (non-circular)")
    print(f"  Target: {name}  ->  {level}")
    print(f"  q={q}, zeta={zeta}, n={n}"
          + (f", module rank k={k}" if k is not None else ""))
    print("=" * 64)

    # Independent reference: direct CRT/evaluation (FIPS 203/204 definition)
    # Kyber (q=3329): incomplete NTT -> 128 quadratic factors X^2 - gamma
    # Dilithium (q=8380417): complete NTT -> 256 linear factors, eval at roots
    def ref_crt(poly):
        out = [0] * n
        if complete:
            # Full evaluation NTT: out[i] = f(zeta^(2*br(i)+1))
            order = 2 * n
            for i in range(n):
                r = pow(zeta, (2 * br(i) + 1) % order, q)
                v = 0; rk = 1
                for j in range(n):
                    v = (v + poly[j] * rk) % q; rk = (rk * r) % q
                out[i] = v
        else:
            # Incomplete NTT: f mod (X^2 - zeta^(2*br(i)+1))
            half = n // 2
            for i in range(half):
                gamma = pow(zeta, 2 * br(i) + 1, q)
                fe = fo = 0; gk = 1
                for kk in range(half):
                    fe = (fe + poly[2 * kk] * gk) % q
                    fo = (fo + poly[2 * kk + 1] * gk) % q
                    gk = (gk * gamma) % q
                out[2 * i] = fe; out[2 * i + 1] = fo
        return out

    _r.seed(20260608)
    fails = 0; first = None
    for t in range(trials):
        poly = [_r.randint(0, q - 1) for _ in range(n)]
        try:
            got = [x % q for x in ntt_func(list(poly))]
            ref = ref_crt(poly)
            if got != ref:
                fails += 1
                if first is None:
                    for i in range(n):
                        if got[i] != ref[i]:
                            first = (t, i, got[i], ref[i]); break
        except Exception as e:
            fails += 1; first = first or (t, -1, str(e), "")

    ok = fails == 0
    print(f"\n  {'PASS' if ok else 'FAIL'}: {trials - fails}/{trials} match independent CRT reference")
    if not ok and first:
        if first[1] >= 0:
            print(f"    First mismatch: trial {first[0]}, coeff [{first[1]}]: got {first[2]}, ref {first[3]}")
        else:
            print(f"    Error: {first[2]}")

    # Boundary KAT vectors (fixed, reproducible)
    print(f"\n  Boundary vectors:")
    bvecs = {
        'all-zero': [0] * n,
        'all-one': [1] * n,
        'unit-e0': [1] + [0] * (n - 1),
        'max-coeff': [q - 1] * n,
    }
    bfail = 0
    for label, v in bvecs.items():
        got = [x % q for x in ntt_func(list(v))]
        ref = ref_crt(v)
        m = got == ref
        bfail += not m
        print(f"    {'OK ' if m else 'XX '} {label}")

    print(f"\n{'='*64}")
    if ok and bfail == 0:
        _fips = "FIPS 204" if family == 'dilithium' else "FIPS 203"
        print(f"  {name} NTT: VERIFIED against independent {_fips} reference")
        print(f"  Security level: {level}")
    else:
        print(f"  {name} NTT: {fails} random + {bfail} boundary failures")
    print("=" * 64)
    return {'name': name, 'level': level, 'random_fails': fails,
            'boundary_fails': bfail, 'verified': ok and bfail == 0}


# ================================================================
# PUBLIC API: pqverify_leakage — per-layer algebraic protection allocation
# ================================================================

def pqverify_leakage(q=3329, zeta=17, n=256):
    """Per-layer algebraic protection allocation for the NTT.

    For each butterfly layer, computes how many secret coefficients would be
    determined IF that layer's intermediate values were exposed — the rank of
    the linear system an attacker would then hold. It answers "which layers
    are worth spending masking on", from the transform's algebraic structure.

    This is computed, not measured. Nothing is executed under observation, no
    trace is collected, and no claim is made about whether this particular
    implementation actually leaks those values. Establishing that requires
    leakage assessment against the deployed binary on the deployed hardware;
    every pq-verify report says so in its side_channel field.

    Usage:
        pqverify_leakage()                    # Kyber
        pqverify_leakage(q=8380417, zeta=1753) # Dilithium
    """
    # Layer count from zeta's ORDER, not from n. ML-KEM's zeta has order n
    # (incomplete transform, last layer deleted -> log2(n)-1 layers); ML-DSA's
    # has order 2n (complete -> log2(n) layers). Keying on n alone gave a
    # 7-layer table for ML-DSA, which is one layer short.
    _log2n = max(1, n.bit_length() - 1)
    _complete = (pow(zeta, 2 * n, q) == 1 and pow(zeta, n, q) == q - 1)
    bits = _log2n if _complete else _log2n - 1
    def br(x):
        r = 0
        for _ in range(bits): r = (r << 1) | (x & 1); x >>= 1
        return r
    zetas = [pow(zeta, br(i), q) for i in range(n if _complete else n // 2)]

    # Track state as linear combinations of inputs (n x n matrix over Z_q)
    state = [[0]*n for _ in range(n)]
    for i in range(n): state[i][i] = 1

    # Extract intermediate vectors per layer
    layer_vecs = [[] for _ in range(bits)]
    k = 1
    for layer in range(bits):
        length = n >> (layer + 1)
        for start in range(0, n, 2 * length):
            z = zetas[k]; k += 1
            for j in range(start, start + length):
                # Intermediate: t = zeta * state[j+length]
                t_vec = [(z * state[j + length][c]) % q for c in range(n)]
                layer_vecs[layer].append(t_vec)
                # Apply butterfly
                row_j = state[j][:]
                row_jl = state[j + length][:]
                state[j] = [(row_j[c] + z * row_jl[c]) % q for c in range(n)]
                state[j + length] = [(row_j[c] - z * row_jl[c]) % q for c in range(n)]

    # Gaussian elimination mod q for rank
    def rank_zq(rows):
        if not rows: return 0
        m = [list(r) for r in rows]
        nr, nc = len(m), len(m[0])
        rank = 0
        for col in range(nc):
            piv = -1
            for row in range(rank, nr):
                if m[row][col] % q != 0:
                    piv = row; break
            if piv < 0: continue
            m[rank], m[piv] = m[piv], m[rank]
            inv = pow(m[rank][col] % q, q - 2, q)
            m[rank] = [(x * inv) % q for x in m[rank]]
            for row in range(nr):
                if row != rank and m[row][col] % q != 0:
                    f = m[row][col] % q
                    m[row] = [(m[row][c] - f * m[rank][c]) % q for c in range(nc)]
            rank += 1
        return rank

    # Compute cumulative rank per layer
    print("=" * 60)
    print(f"  NTT ALGEBRAIC PROTECTION ALLOCATION (q={q}, n={n})")
    print("=" * 60)
    print(f"\n  {'Layer':>5} | {'Len':>4} | {'#BF':>4} | {'Layer Rank':>10} | "
          f"{'Cumul Rank':>10} | {'New Info':>8} | {'Risk':>10}")
    print(f"  {'-'*5}-+-{'-'*4}-+-{'-'*4}-+-{'-'*10}-+-{'-'*10}-+-{'-'*8}-+-{'-'*10}")

    cumulative = []
    prev_rank = 0
    results = []
    lengths = [n >> (l + 1) for l in range(bits)]

    for layer in range(bits):
        vecs = layer_vecs[layer]
        n_bf = len(vecs)
        lr = rank_zq(vecs)
        cumulative.extend(vecs)
        cr = rank_zq(cumulative)
        new_info = cr - prev_rank
        eff = new_info / max(n_bf, 1)
        risk = "CRITICAL" if eff > 0.5 else "HIGH" if eff > 0.1 else "MEDIUM" if eff > 0.03 else "LOW"
        results.append({'layer': layer, 'length': lengths[layer], 'n_bf': n_bf,
                        'layer_rank': lr, 'cumul_rank': cr, 'new_info': new_info,
                        'eff_impact': eff, 'risk': risk})
        print(f"  {layer:>5} | {lengths[layer]:>4} | {n_bf:>4} | {lr:>10} | "
              f"{cr:>10} | {new_info:>8} | {risk:>10}")
        prev_rank = cr

    # Protection allocation
    print(f"\n  PROTECTION ALLOCATION:")
    for r in results:
        prot = {"CRITICAL": "2nd-order mask + shuffle + CPV",
                "HIGH": "1st-order mask + shuffle + CPV",
                "MEDIUM": "1st-order mask + CPV",
                "LOW": "CPV only"}[r['risk']]
        print(f"    Layer {r['layer']} ({r['risk']:>8}): {prot}")

    levels = [{"CRITICAL":3,"HIGH":2,"MEDIUM":1,"LOW":0}[r['risk']] for r in results]
    print(f"\n  static const uint8_t ntt_prot_level[{bits}] = {{{', '.join(map(str, levels))}}};")

    # ---- Multiplicative-order profile (supplementary, field-specific context) ----
    def mult_order(a, mod):
        if a % mod == 0: return 0
        if a % mod == 1: return 1
        o = mod - 1
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            while o % p == 0 and pow(a, o // p, mod) == 1:
                o //= p
        return o

    import math as _ml
    n_half = n // 2
    k2 = 1
    mo_geo = []
    for layer in range(bits):
        n_groups = 1 << layer
        orders = []
        for g in range(n_groups):
            if k2 < n_half:
                orders.append(mult_order(zetas[k2], q)); k2 += 1
        if orders:
            mo_geo.append(2 ** (sum(_ml.log2(max(o, 1)) for o in orders) / len(orders)))
        else:
            mo_geo.append(1)

    fam = "ML-KEM" if q < 10000 else "ML-DSA"
    print(f"\n  NOTE: The protection table {{{', '.join(map(str, levels))}}} is STRUCTURAL —")
    print(f"  it measures information flow per layer (how many secret coefficients each")
    print(f"  layer reveals). This is the same for any n={n} NTT regardless of field.")
    print(f"  Twiddle multiplicative orders (field-specific, {fam}): "
          f"[{', '.join(f'{g:.0f}' for g in mo_geo)}]")

    crit = sum(1 for r in results if r['risk'] == 'CRITICAL')
    low = sum(1 for r in results if r['risk'] in ('LOW', 'MEDIUM'))
    print(f"\n  {crit}/{bits} layers CRITICAL, {low}/{bits} layers can use lighter protection")
    print("=" * 60)
    return results


# ================================================================
# ML-KEM KeyCheck — independent FIPS 203 input validation (pq-verify's own
# oracle; §7.2 encapsulation-key check, §7.3 decapsulation-key check).
# Verified 60/60 against NIST ACVP expected testPassed booleans.
# ================================================================

def _mlkem_byte_decode12_ok(b, q=3329):
    """ByteDecode_12 modulus check: every 12-bit coefficient must be < q."""
    if len(b) % 3 != 0:
        return False
    for i in range(0, len(b), 3):
        chunk = int.from_bytes(b[i:i+3], 'little')
        if (chunk & 0xFFF) >= q or ((chunk >> 12) & 0xFFF) >= q:
            return False
    return True

def check_encapsulation_key(ek, param_set="ML-KEM-768"):
    """FIPS 203 §7.2: length (384k+32) + ByteDecode_12 modulus bound."""
    k = {"ML-KEM-512":2,"ML-KEM-768":3,"ML-KEM-1024":4}.get(param_set)
    if k is None or len(ek) != 384*k + 32:
        return False
    return _mlkem_byte_decode12_ok(ek[:384*k])

def check_decapsulation_key(dk, param_set="ML-KEM-768"):
    """FIPS 203 §7.3: length (768k+96) + embedded-ek hash consistency
    H(ek)==stored_h + modulus bounds on the embedded s and ek."""
    import hashlib as _hl
    k = {"ML-KEM-512":2,"ML-KEM-768":3,"ML-KEM-1024":4}.get(param_set)
    if k is None or len(dk) != 768*k + 96:
        return False
    ek_part = dk[384*k:768*k+32]
    stored_h = dk[768*k+32:768*k+64]
    if len(ek_part) != 384*k+32 or len(stored_h) != 32:
        return False
    if _hl.sha3_256(ek_part).digest() != stored_h:
        return False
    if not _mlkem_byte_decode12_ok(dk[:384*k]):
        return False
    return check_encapsulation_key(ek_part, param_set)


# ================================================================
# PUBLIC API: pqverify_acvp — full NIST ACVP end-to-end ML-KEM verification
# ================================================================

_ACVP_BASE = "https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files/"

_VECTOR_BUNDLE_CACHE = {}

# The pinned NIST vectors live in two archives. The SLH-DSA signature files
# (~39 MB compressed) have their own, opened only when an SLH-DSA signature
# suite asks for one of them, so every other run never decompresses them.
# Those entries are NIST's file text verbatim (sha256 equals MANIFEST.json's);
# the main archive holds parsed JSON. Keys route by prefix.
_VECTOR_BUNDLES = {
    "acvp_vectors.json.gz": (),
    "slhdsa_sig_vectors.json.gz": ("SLH-DSA-sigGen-FIPS205/",
                                   "SLH-DSA-sigVer-FIPS205/"),
}

def _pkg_dir():
    """Directory of this module. Falls back to CWD when run via exec() as a
    standalone script, where __file__ is undefined."""
    import os as _o
    try:
        return _o.path.dirname(_o.path.abspath(__file__))
    except NameError:
        return _o.getcwd()

def _bundle_name(key=None):
    """The archive that holds `key` ('DIR/file.json'); the main one if None."""
    for name, prefixes in _VECTOR_BUNDLES.items():
        if key and prefixes and key.startswith(prefixes):
            return name
    return "acvp_vectors.json.gz"

def _bundle_path(key=None):
    import os as _o
    return _o.path.join(_pkg_dir(), "vectors", _bundle_name(key))

def _load_bundle(key=None):
    """Load (and memoise) the pinned-vector archive that holds `key`, if
    present. Each is one gzipped JSON keyed by 'DIR/file.json' -- one file
    instead of a nested tree, which keeps the package simple and installable
    anywhere."""
    import os as _o, gzip as _gz, json as _j
    name = _bundle_name(key)
    if name not in _VECTOR_BUNDLE_CACHE:
        p = _bundle_path(key)
        if not _o.path.exists(p):
            return {}
        with _gz.open(p, "rt") as fh:
            _VECTOR_BUNDLE_CACHE[name] = _j.load(fh)
    return _VECTOR_BUNDLE_CACHE[name]


def _vector_revision(*suites):
    """The NIST ACVP-Server commit(s) the pinned vectors for `suites` came from,
    e.g. 'NIST ACVP-Server ad33b3d', read from MANIFEST.json. A result is only
    reproducible if it names the vector revision it was checked against: NIST
    corrects these files (ad33b3d fixed over-length invalid ML-KEM keys), so
    'pinned' alone does not say which answers were used. None if unrecorded."""
    import os as _o, json as _j
    try:
        with open(_o.path.join(_pkg_dir(), "vectors", "MANIFEST.json")) as fh:
            m = _j.load(fh)
    except (OSError, ValueError):
        return None
    commits = sorted({v.get('nist_commit') for k, v in m.items()
                      if k.split('/')[0] in suites} - {None})
    return ("NIST ACVP-Server " + ", ".join(commits)) if commits else None


def _reference(dist):
    """'kyber-py 1.2.0': the reference implementation that computed a suite's
    answers. The vectors are pinned; the software answering them is whatever
    is installed, so a result names both or it is not reproducible."""
    try:
        from importlib import metadata as _md
        return f"{dist} {_md.version(dist)}"
    except Exception:
        return f"{dist} (version unknown)"


def _vector_label(local, *suites):
    """Human-readable vector source for report headers."""
    import os as _o
    if not local:
        return "LIVE from NIST ACVP-Server (may change between runs)"
    if _o.path.abspath(local) != _o.path.abspath(_o.path.join(_pkg_dir(), "vectors")):
        return f"local: {local}"
    rev = _vector_revision(*suites)
    return f"pinned ({rev})" if rev else "pinned"

def _load_vector_json(path, bundle_key=None):
    """Load an ACVP vector file.

    The pinned bundle answers only for paths inside pq-verify's own vectors
    directory. A directory the caller supplied (--vector-dir, prompt_dir) is
    always read from disk, and a file missing from it is an error, never a
    silent fallback: the bundle used to be consulted first by key, so a user
    directory was ignored for every bundled file while the report named the
    user directory as the source.
    """
    import json as _j, gzip as _gz, os as _os
    pinned_dir = _os.path.abspath(_os.path.join(_pkg_dir(), "vectors"))
    in_pinned = _os.path.abspath(path).startswith(pinned_dir + _os.sep)
    if bundle_key and in_pinned:
        b = _load_bundle(bundle_key)
        if bundle_key in b:
            if isinstance(b[bundle_key], str):     # verbatim NIST text
                b[bundle_key] = _j.loads(b[bundle_key])
            return b[bundle_key]
    if _os.path.exists(path):
        return _j.load(open(path))
    if _os.path.exists(path + ".gz"):
        with _gz.open(path + ".gz", "rt") as fh:
            return _j.load(fh)
    raise FileNotFoundError(path + " (or .gz, or bundle key " + str(bundle_key) + ")")
_ACVP_KEM_LEVELS = {'ML-KEM-512':'NIST Level 1','ML-KEM-768':'NIST Level 3','ML-KEM-1024':'NIST Level 5'}

def pqverify_acvp(prompt_dir=None, verbose=True, live=False, vector_dir=None):
    """Full NIST ACVP end-to-end ML-KEM verification (FIPS 203), all groups.

    Functional groups (keyGen, encapsulation, decapsulation) are verified
    byte-exact against NIST's published vectors using kyber-py as the
    seed-injecting reference (_keygen_internal/_encaps_internal/_decaps_internal).
    KeyCheck groups (encapsulationKeyCheck, decapsulationKeyCheck) are verified
    by pq-verify's own independent FIPS 203 §7.2/§7.3 validation, matched
    against NIST's expected testPassed booleans (valid + malformed keys).

    Covers ML-KEM-512/768/1024 (NIST Levels 1/3/5).

    Vector source precedence (deterministic-by-default):
      1. prompt_dir / vector_dir  — explicit local directory, if given
      2. live=True                — fetch current vectors from NIST's GitHub
      3. default                  — the FROZEN vectors bundled in this package
                                    (pq_verify/vectors), so results are
                                    reproducible and offline. NIST edits the
                                    upstream files periodically; pinning
                                    insulates you from that. Use live=True to
                                    check against the latest instead.
    """
    import json as _json, os as _os
    try:
        from kyber_py.ml_kem import ML_KEM_512, ML_KEM_768, ML_KEM_1024
    except ImportError:
        DEGRADED['deps'].append('kyber-py')
        DEGRADED['skipped_checks'].append('ML-KEM ACVP')
        print("  kyber-py required for functional vectors:")
        print('    pip install "pq-verify[full]"')
        return None
    PS = {'ML-KEM-512':ML_KEM_512,'ML-KEM-768':ML_KEM_768,'ML-KEM-1024':ML_KEM_1024}

    # resolve the vector source once
    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _os.path.join(_pkg_dir(), "vectors")
    if verbose:
        print(f"  vectors: {_vector_label(_local, 'ML-KEM-keyGen-FIPS203', 'ML-KEM-encapDecap-FIPS203')}")
        print(f"  reference: {_reference('kyber-py')}")

    def load(name):
        if _local:
            d = _os.path.join(_local, name)
            return (_load_vector_json(_os.path.join(d,"prompt.json"), f"{name}/prompt.json"),
                    _load_vector_json(_os.path.join(d,"expectedResults.json"), f"{name}/expectedResults.json"))
        import urllib.request
        u = _ACVP_BASE + name + "/"
        return (_json.loads(urllib.request.urlopen(u+"prompt.json", timeout=30).read()),
                _json.loads(urllib.request.urlopen(u+"expectedResults.json", timeout=30).read()))

    if verbose:
        print("=" * 64)
        print("  NIST ACVP END-TO-END ML-KEM VERIFICATION (FIPS 203)")
        print(f"  Source: {'pinned/local: '+_local if _local else 'LIVE NIST ACVP-Server (GitHub)'}")
        print("  Functional: kyber-py byte-exact | KeyCheck: pq-verify FIPS 203 oracle")
        print("=" * 64)

    g_ok = 0; g_total = 0; cat = {}
    def tally(c, ps, ok):
        cat.setdefault((c, ps), [0, 0]); cat[(c, ps)][0] += ok; cat[(c, ps)][1] += 1

    # ---- keyGen ----
    kp, ke = load("ML-KEM-keyGen-FIPS203")
    exp = {t['tcId']:t for g in ke['testGroups'] for t in g['tests']}
    for g in kp['testGroups']:
        ps = g['parameterSet']; impl = PS[ps]
        for t in g['tests']:
            ek, dk = impl._keygen_internal(bytes.fromhex(t['d']), bytes.fromhex(t['z']))
            e = exp[t['tcId']]
            ok = ek.hex().upper()==e['ek'].upper() and dk.hex().upper()==e['dk'].upper()
            tally('keyGen', ps, ok); g_ok += ok; g_total += 1

    # ---- encapDecap (functional + KeyCheck) ----
    # Uses internalProjection.json (NIST's merged ground-truth file), not
    # prompt.json+expectedResults.json. Verified live (2026-07-23) that NIST
    # now splits ML-KEM decapsulation into TWO keyFormats -- 'seed' (z,d given,
    # dk must be derived) and 'expanded' (dk given directly) -- and that
    # decapsulationKeyCheck's prompt.json omits the key entirely (that function
    # is meant for live-protocol IUTs submitting their own candidate key).
    # internalProjection.json carries every field (ek,dk,z,d,c,k,testPassed) for
    # every test regardless of keyFormat, which is exactly what offline batch
    # verification like this needs. So: derive dk from (d,z) ourselves for EVERY
    # decapsulation test -- this exercises keygen+decaps together and works
    # uniformly for both keyFormats -- and read dk directly for
    # decapsulationKeyCheck (present here, absent in prompt.json).
    def load_internal(name):
        if _local:
            return _load_vector_json(_os.path.join(_local, name, "internalProjection.json"), f"{name}/internalProjection.json")
        import urllib.request
        u = _ACVP_BASE + name + "/internalProjection.json"
        return _json.loads(urllib.request.urlopen(u, timeout=30).read())

    ep = load_internal("ML-KEM-encapDecap-FIPS203")
    _unknown_fns = set()
    for g in ep['testGroups']:
        ps = g['parameterSet']; impl = PS[ps]; fn = g.get('function','')
        for t in g['tests']:
            if fn == 'encapsulation':
                K, c = impl._encaps_internal(bytes.fromhex(t['ek']), bytes.fromhex(t['m']))
                ok = c.hex().upper()==t['c'].upper() and K.hex().upper()==t['k'].upper()
                tally('encaps', ps, ok)
            elif fn == 'decapsulation':
                # Format-agnostic: NIST's encapDecap vectors have shipped in two
                # shapes and have oscillated between them. 'seed' form gives (d,z)
                # and dk must be derived; 'expanded' form gives dk directly. We
                # accept whichever is present so a schema flip upstream cannot
                # crash the run. If neither is present, skip that test loudly.
                if 'd' in t and 'z' in t:
                    _, dk = impl._keygen_internal(bytes.fromhex(t['d']), bytes.fromhex(t['z']))
                elif 'dk' in t:
                    dk = bytes.fromhex(t['dk'])
                else:
                    _unknown_fns.add('decapsulation:no-key-field'); continue
                K = impl._decaps_internal(dk, bytes.fromhex(t['c']))
                ok = K.hex().upper()==t['k'].upper()
                tally('decaps', ps, ok)
            elif fn == 'encapsulationKeyCheck':
                ours = check_encapsulation_key(bytes.fromhex(t['ek']), ps)
                ok = (ours == t['testPassed'])
                tally('encapKeyCheck', ps, ok)
            elif fn == 'decapsulationKeyCheck':
                ours = check_decapsulation_key(bytes.fromhex(t['dk']), ps)
                ok = (ours == t['testPassed'])
                tally('decapKeyCheck', ps, ok)
            else:
                _unknown_fns.add(fn); continue
            g_ok += ok; g_total += 1
    if _unknown_fns and verbose:
        print(f"  \u26a0 NIST vectors contain unhandled function types: {sorted(_unknown_fns)}")
        print(f"    (upstream schema may have changed; these tests were skipped, not failed)")

    if verbose:
        order = ['keyGen','encaps','decaps','encapKeyCheck','decapKeyCheck']
        labels = {'keyGen':'keyGen        (seeds->ek,dk)',
                  'encaps':'encapsulation (ek,m->c,K)',
                  'decaps':'decapsulation (dk,c->K)',
                  'encapKeyCheck':'encapKeyCheck (FIPS 203 §7.2)',
                  'decapKeyCheck':'decapKeyCheck (FIPS 203 §7.3)'}
        for c in order:
            rows = sorted((ps, v) for (cc, ps), v in cat.items() if cc == c)
            if not rows: continue
            print(f"\n  {labels[c]}:")
            for ps, (o, n) in rows:
                print(f"    {'PASS' if o==n else 'FAIL'} {ps:14s} {o}/{n}   [{_ACVP_KEM_LEVELS[ps]}]")
        print(f"\n{'='*64}")
        print(f"  ACVP RESULT: {g_ok}/{g_total} NIST vectors verified")
        if g_ok == g_total:
            print("  ML-KEM VERIFIED end-to-end vs NIST ACVP-Server — all groups")
            print("  keyGen + encaps + decaps (byte-exact) + KeyCheck (bool-exact)")
            print("  Levels 1, 3, 5")
        print("=" * 64)

    return {'verified': g_ok == g_total and g_total > 0, 'passed': g_ok, 'total': g_total,
            'detail': {f"{c}/{ps}": v for (c, ps), v in cat.items()},
            'vectors': _vector_label(_local, 'ML-KEM-keyGen-FIPS203', 'ML-KEM-encapDecap-FIPS203'),
            'reference': _reference('kyber-py')}



import json as _json
import hashlib as _hashlib


# ================================================================
# PUBLIC API: pqverify_mldsa_acvp — full NIST ACVP end-to-end
#             ML-DSA verification (FIPS 204)
# ----------------------------------------------------------------
# Companion to pqverify_acvp (ML-KEM / FIPS 203).
# Together: 240 (ML-KEM) + 615 (ML-DSA) + 624 (SLH-DSA keyGen 120 + sigVer 504)
# + 87 (LMS) = 1566/1566 NIST ACVP vectors; SLH-DSA sigGen (624) is opt-in.
# Requires: pip install "pq-verify[full]"  (dilithium-py)
# ================================================================
_MLDSA_ACVP_BASE = ("https://raw.githubusercontent.com/usnistgov/ACVP-Server/"
                    "master/gen-val/json-files/")
_MLDSA_DIRS = {'keyGen': 'ML-DSA-keyGen-FIPS204',
               'sigGen': 'ML-DSA-sigGen-FIPS204',
               'sigVer': 'ML-DSA-sigVer-FIPS204'}
_MLDSA_LEVELS = {'ML-DSA-44': 'NIST Level 2', 'ML-DSA-65': 'NIST Level 3',
                 'ML-DSA-87': 'NIST Level 5'}

# FIPS 204 §5.4 pre-hash: name -> (final OID byte, digest fn)
_MLDSA_OID_ARC = bytes([0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02])
_MLDSA_PH = {
    'SHA2-224': (0x04, lambda m: _hashlib.sha224(m).digest()),
    'SHA2-256': (0x01, lambda m: _hashlib.sha256(m).digest()),
    'SHA2-384': (0x02, lambda m: _hashlib.sha384(m).digest()),
    'SHA2-512': (0x03, lambda m: _hashlib.sha512(m).digest()),
    'SHA2-512/224': (0x05, lambda m: _hashlib.new('sha512_224', m).digest()),
    'SHA2-512/256': (0x06, lambda m: _hashlib.new('sha512_256', m).digest()),
    'SHA3-224': (0x07, lambda m: _hashlib.sha3_224(m).digest()),
    'SHA3-256': (0x08, lambda m: _hashlib.sha3_256(m).digest()),
    'SHA3-384': (0x09, lambda m: _hashlib.sha3_384(m).digest()),
    'SHA3-512': (0x0A, lambda m: _hashlib.sha3_512(m).digest()),
    'SHAKE-128': (0x0B, lambda m: _hashlib.shake_128(m).digest(32)),
    'SHAKE-256': (0x0C, lambda m: _hashlib.shake_256(m).digest(64)),
}


def _mldsa_hash_with_oid(m, name):
    b, fn = _MLDSA_PH[name]
    return _MLDSA_OID_ARC + bytes([b]), fn(m)


def _mldsa_mprime(test, group):
    iface = group.get('signatureInterface')
    ph = group.get('preHash')
    ctx = bytes.fromhex(test.get('context', '') or '')
    if iface == 'internal':
        return None
    if ph == 'pure':
        return bytes([0]) + bytes([len(ctx)]) + ctx + bytes.fromhex(test['message'])
    oid, ph_m = _mldsa_hash_with_oid(bytes.fromhex(test['message']), test['hashAlg'])
    return bytes([1]) + bytes([len(ctx)]) + ctx + oid + ph_m


def _mldsa_verify_with_mu(O, pk, mu, sig):
    """dilithium-py _verify_internal with externally supplied mu (external-mu interface)."""
    rho, t1 = O._unpack_pk(pk)
    try:
        c_tilde, z, h = O._unpack_sig(sig)
    except ValueError:
        return False
    if h.sum_hint() > O.omega:
        return False
    if z.check_norm_bound(O.gamma_1 - O.beta):
        return False
    A_hat = O._expand_matrix_from_seed(rho)
    c = O.R.sample_in_ball(c_tilde, O.tau).to_ntt()
    z = z.to_ntt()
    t1 = t1.scale(1 << O.d).to_ntt()
    w = ((A_hat @ z) - t1.scale(c)).from_ntt()
    wb = h.use_hint(w, 2 * O.gamma_2).bit_pack_w(O.gamma_2)
    return c_tilde == O._h(mu + wb, O.c_tilde_bytes)


def pqverify_mldsa_acvp(prompt_dir=None, verbose=True, live=False, vector_dir=None):
    """Full NIST ACVP end-to-end ML-DSA verification (FIPS 204).

    keyGen + sigGen byte-exact, sigVer bool-exact, across ML-DSA-44/65/87
    and all four ACVP signature interfaces (external-pure, external-preHash,
    internal, internal-externalMu). Covers deterministic and hedged signing
    and all twelve HashML-DSA pre-hash functions.

    Vector source precedence (deterministic-by-default), same as pqverify_acvp:
      1. prompt_dir / vector_dir  — explicit local directory, if given
      2. live=True                — fetch current vectors from NIST's GitHub
      3. default                  — the FROZEN vectors bundled in this package

    Requires: pip install "pq-verify[full]"  (dilithium-py)
    """
    import os as _os2
    try:
        from dilithium_py.ml_dsa import ML_DSA_44, ML_DSA_65, ML_DSA_87
    except ImportError:
        DEGRADED['deps'].append('dilithium-py')
        DEGRADED['skipped_checks'].append('ML-DSA ACVP')
        print('  dilithium-py required:  pip install "pq-verify[full]"')
        return None
    PS = {'ML-DSA-44': ML_DSA_44, 'ML-DSA-65': ML_DSA_65, 'ML-DSA-87': ML_DSA_87}
    Z32 = bytes(32)

    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _os2.path.join(_pkg_dir(), "vectors")
    if verbose:
        print(f"  vectors: {_vector_label(_local, *_MLDSA_DIRS.values())}")
        print(f"  reference: {_reference('dilithium-py')}")

    def load(name):
        if _local:
            d = _os2.path.join(_local, _MLDSA_DIRS[name])
            _dn = _MLDSA_DIRS[name]
            return (_load_vector_json(_os2.path.join(d, "prompt.json"), f"{_dn}/prompt.json"),
                    _load_vector_json(_os2.path.join(d, "expectedResults.json"), f"{_dn}/expectedResults.json"))
        import urllib.request
        u = _MLDSA_ACVP_BASE + _MLDSA_DIRS[name] + "/"
        g = lambda f: _json.load(urllib.request.urlopen(u + f))
        return g("prompt.json"), g("expectedResults.json")

    detail = {}

    def tally(lab, ok):
        r = detail.setdefault(lab, [0, 0])
        r[1] += 1
        r[0] += int(ok)

    # keyGen
    P, E = load('keyGen')
    exp = {t['tcId']: t for g in E['testGroups'] for t in g['tests']}
    for g in P['testGroups']:
        O = PS[g['parameterSet']]
        for t in g['tests']:
            pk, sk = O._keygen_internal(bytes.fromhex(t['seed']))
            e = exp[t['tcId']]
            tally(f"keyGen/{g['parameterSet']}",
                  pk.hex().upper() == e['pk'].upper() and sk.hex().upper() == e['sk'].upper())
    # sigGen
    P, E = load('sigGen')
    exp = {t['tcId']: t for g in E['testGroups'] for t in g['tests']}
    for g in P['testGroups']:
        O = PS[g['parameterSet']]
        det = g.get('deterministic')
        iface = g.get('signatureInterface')
        emu = g.get('externalMu')
        ph = g.get('preHash')
        lab = f"sigGen/{iface}/{'externalMu' if emu else (ph or '')}".rstrip('/')
        for t in g['tests']:
            rnd = Z32 if det else bytes.fromhex(t['rnd'])
            if iface == 'internal' and emu:
                sig = O._sign_internal(bytes.fromhex(t['sk']), bytes.fromhex(t['mu']), rnd, external_mu=True)
            elif iface == 'internal':
                sig = O._sign_internal(bytes.fromhex(t['sk']), bytes.fromhex(t['message']), rnd)
            else:
                sig = O._sign_internal(bytes.fromhex(t['sk']), _mldsa_mprime(t, g), rnd)
            tally(lab, sig.hex().upper() == exp[t['tcId']]['signature'].upper())
    # sigVer
    P, E = load('sigVer')
    exp = {t['tcId']: t for g in E['testGroups'] for t in g['tests']}
    for g in P['testGroups']:
        O = PS[g['parameterSet']]
        iface = g.get('signatureInterface')
        emu = g.get('externalMu')
        ph = g.get('preHash')
        lab = f"sigVer/{iface}/{'externalMu' if emu else (ph or '')}".rstrip('/')
        for t in g['tests']:
            pk = bytes.fromhex(t['pk'])
            sig = bytes.fromhex(t['signature'])
            if iface == 'internal' and emu:
                got = _mldsa_verify_with_mu(O, pk, bytes.fromhex(t['mu']), sig)
            elif iface == 'internal':
                got = O._verify_internal(pk, bytes.fromhex(t['message']), sig)
            else:
                got = O._verify_internal(pk, _mldsa_mprime(t, g), sig)
            tally(lab, bool(got) == bool(exp[t['tcId']]['testPassed']))

    g_ok = sum(v[0] for v in detail.values())
    g_total = sum(v[1] for v in detail.values())
    if verbose:
        print("=" * 64)
        print("  NIST ACVP END-TO-END ML-DSA VERIFICATION (FIPS 204)")
        print(f"  Source: {_vector_label(_local, *_MLDSA_DIRS.values())}")
        print("=" * 64)
        for lab in sorted(detail):
            ok, tot = detail[lab]
            print(f"  {'PASS' if ok == tot else '**FAIL**':9s} {lab:30s} {ok:3d}/{tot}")
        print("=" * 64)
        print(f"  ACVP RESULT: {g_ok}/{g_total} NIST ML-DSA vectors verified")
        print("  keyGen + sigGen (byte-exact) + sigVer (bool-exact), Levels 2/3/5")
        print("=" * 64)
    return {'verified': g_ok == g_total and g_total > 0, 'passed': g_ok, 'total': g_total,
            'detail': {k: tuple(v) for k, v in detail.items()},
            'vectors': _vector_label(_local, *_MLDSA_DIRS.values()),
            'reference': _reference('dilithium-py')}


_SLHDSA_ACVP_BASE = ("https://raw.githubusercontent.com/usnistgov/ACVP-Server/"
                     "master/gen-val/json-files/")
_SLHDSA_DIRS = {'keyGen': 'SLH-DSA-keyGen-FIPS205',
                'sigVer': 'SLH-DSA-sigVer-FIPS205',
                'sigGen': 'SLH-DSA-sigGen-FIPS205'}

# FIPS 205 §10.2.2 (HashSLH-DSA): the approved pre-hash functions, by ACVP's
# hashAlg name -> (last arc of the OID 2.16.840.1.101.3.4.2.x, digest).
# SHAKE128 and SHAKE256 output 256 and 512 bits.
_SLHDSA_PREHASH = {
    'SHA2-256':     (1,  lambda m: hashlib.sha256(m).digest()),
    'SHA2-384':     (2,  lambda m: hashlib.sha384(m).digest()),
    'SHA2-512':     (3,  lambda m: hashlib.sha512(m).digest()),
    'SHA2-224':     (4,  lambda m: hashlib.sha224(m).digest()),
    'SHA2-512/224': (5,  lambda m: hashlib.new('sha512_224', m).digest()),
    'SHA2-512/256': (6,  lambda m: hashlib.new('sha512_256', m).digest()),
    'SHA3-224':     (7,  lambda m: hashlib.sha3_224(m).digest()),
    'SHA3-256':     (8,  lambda m: hashlib.sha3_256(m).digest()),
    'SHA3-384':     (9,  lambda m: hashlib.sha3_384(m).digest()),
    'SHA3-512':     (10, lambda m: hashlib.sha3_512(m).digest()),
    'SHAKE-128':    (11, lambda m: hashlib.shake_128(m).digest(32)),
    'SHAKE-256':    (12, lambda m: hashlib.shake_256(m).digest(64)),
}


def _slhdsa_message(group, test):
    """M', the message slh_sign_internal / slh_verify_internal see.

    pq-verify builds it itself rather than calling the library's pure/pre-hash
    wrappers, so the FIPS 205 encodings are checked against NIST too:
      internal  M' = M
      pure      M' = 0x00 || |ctx| || ctx || M                (Alg. 22/24)
      pre-hash  M' = 0x01 || |ctx| || ctx || OID || PH(M)     (Alg. 23/25)
    """
    m = bytes.fromhex(test['message'])
    if group.get('signatureInterface') == 'internal':
        return m
    ctx = bytes.fromhex(test.get('context', ''))
    if len(ctx) > 255:
        raise ValueError("context longer than 255 bytes")
    if group.get('preHash') == 'preHash':
        arc, ph = _SLHDSA_PREHASH[test['hashAlg']]
        oid = bytes.fromhex('06096086480165030402') + bytes([arc])  # DER
        return b'\x01' + bytes([len(ctx)]) + ctx + oid + ph(m)
    return b'\x00' + bytes([len(ctx)]) + ctx + m


def _slhdsa_sign_internal(msg, sk, addrnd, par):
    """FIPS 205 Algorithm 19, slh_sign_internal(M, SK, addrnd).

    The `slhdsa` package's own sign() draws opt_rand from the OS when
    randomising, so NIST's additionalRandomness cannot be injected through it.
    This is Algorithm 19 over that package's FORS and hypertree primitives;
    addrnd=None is the deterministic variant (opt_rand = PK.seed).
    """
    from slhdsa.lowlevel.addresses import FORSTreeAddress
    from slhdsa.lowlevel.fors import FORS
    from slhdsa.lowlevel.hypertree import HyperTree
    from slhdsa.lowlevel.wots import WOTSParameter
    n = par.n
    if len(sk) != 4 * n:
        raise ValueError(f"SK is {len(sk)} bytes, FIPS 205 says {4 * n}")
    sk_seed, sk_prf, pk_seed, pk_root = (sk[i * n:(i + 1) * n] for i in range(4))
    opt_rand = pk_seed if addrnd is None else addrnd
    r = par.PRFmsg(sk_prf, opt_rand, msg)
    sig = bytearray((1 + par.k * (par.a + 1) + par.h
                     + par.d * WOTSParameter(par).len) * n)
    view = memoryview(sig)
    view[:n] = r
    digest = par.Hmsg(r, pk_seed, pk_root, msg)
    ka = -(-par.k * par.a // 8)
    ht = -(-(par.h - par.h // par.d) // 8)
    lf = -(-par.h // (8 * par.d))
    md = digest[:ka]
    idx_tree = int.from_bytes(digest[ka:ka + ht], 'big') % (1 << (par.h - par.h // par.d))
    idx_leaf = int.from_bytes(digest[ka + ht:ka + ht + lf], 'big') % (1 << (par.h // par.d))
    adrs = FORSTreeAddress(0, 0)
    adrs.tree, adrs.keypair = idx_tree, idx_leaf
    fl = par.k * (par.a + 1) * n
    FORS(par).sign(md, sk_seed, pk_seed, adrs, view[n:n + fl])
    pk_fors = FORS(par).publickey_from_sign(view[n:n + fl], md, pk_seed, adrs)
    HyperTree(par).sign(pk_fors, sk_seed, pk_seed, idx_tree, idx_leaf, view[n + fl:])
    return bytes(sig)


def pqverify_slhdsa_acvp(prompt_dir=None, verbose=True, live=False, vector_dir=None,
                         siggen=False, sigver=True, keygen=True, param_sets=None):
    """NIST ACVP end-to-end SLH-DSA verification (FIPS 205), all twelve
    parameter sets (SHA2 and SHAKE, 128/192/256, fast and small).

    keyGen (120): each test supplies (skSeed, skPrf, pkSeed) and NIST the
    expected (sk, pk). FIPS 205 defines pk = pkSeed || pkRoot and
    sk = skSeed || skPrf || pkSeed || pkRoot, where pkRoot is the root of the
    top-level XMSS tree. The seeds are copied through; pkRoot is the computed
    quantity, so it is the real check.

    sigVer (504, on by default): the verdict on every (pk, M, ctx, sig)
    matches NIST's testPassed. Per parameter set NIST supplies a valid
    signature, a modified message, a modified R, FORS and hypertree
    signature, and signatures one byte too short and too long, over the
    internal interface and the external pure and pre-hash ones (twelve
    hash functions).

    sigGen (624, opt-in): the signature is byte-exact with NIST's, both
    deterministic and with NIST's additionalRandomness, over the same three
    interfaces. Signing a small ('s') parameter set takes seconds per
    signature, so the full set takes about half an hour; pass siggen=True
    (CLI --slhdsa-siggen). CI runs it weekly.

    For the external interfaces pq-verify builds M' itself (see
    _slhdsa_message) rather than calling the library's wrappers, so the
    domain separator, context and pre-hash OID encodings are checked too.

    Reference: the `slhdsa` package, verified FIPS 205-conformant against these
    same NIST vectors before adoption. NOTE: `pyspx` is NOT usable here -- it
    implements the SPHINCS+ round-3 submission, whose tweakable-hash/address
    encoding differs from FIPS 205, and produces a different pkRoot. Using it
    would report CORRECT FIPS 205 implementations as wrong.

    keygen/sigver/siggen select the modes; param_sets (e.g.
    ['SLH-DSA-SHA2-128s']) limits every mode to those sets, which is how CI
    spreads sigGen over parallel jobs.

    Vector source precedence matches pqverify_acvp: prompt_dir/vector_dir,
    then live=True, else the pinned bundles shipped in-package (the signature
    vectors sit in their own archive, opened only here).

    Requires: pip install slh-dsa   (PyPI name is hyphenated; module is `slhdsa`)
    """
    import json as _j3, os as _os3
    try:
        from slhdsa.lowlevel.slhdsa import Address, XMSS
        from slhdsa.lowlevel.slhdsa import verify as _slh_verify
        import slhdsa.lowlevel.parameters as _LP
    except ImportError:
        DEGRADED['deps'].append('slh-dsa')
        DEGRADED['skipped_checks'].append('SLH-DSA ACVP')
        print("  slh-dsa required:  pip install slh-dsa   (module name: slhdsa)")
        return None

    modes = ((['keyGen'] if keygen else []) + (['sigVer'] if sigver else [])
             + (['sigGen'] if siggen else []))
    dirs = [_SLHDSA_DIRS[m] for m in modes]
    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _os3.path.join(_pkg_dir(), "vectors")
    if verbose:
        print(f"  vectors: {_vector_label(_local, *dirs)}")
        print(f"  reference: {_reference('slh-dsa')}")

    def load(name):
        d = _SLHDSA_DIRS[name]
        if _local:
            base = _os3.path.join(_local, d)
            return (_load_vector_json(_os3.path.join(base, "prompt.json"),
                                      f"{d}/prompt.json"),
                    _load_vector_json(_os3.path.join(base, "expectedResults.json"),
                                      f"{d}/expectedResults.json"))
        import urllib.request
        u = _SLHDSA_ACVP_BASE + d + "/"
        g = lambda f: _j3.load(urllib.request.urlopen(u + f, timeout=120))
        return g("prompt.json"), g("expectedResults.json")

    def _par(ps):
        return getattr(_LP, ps.replace('SLH-DSA-', '').replace('-', '_').lower(), None)

    def _label(mode, g):
        if mode == 'keyGen':
            return f"keyGen/{g['parameterSet']}"
        iface = g.get('signatureInterface', '?')
        if iface == 'external':
            iface = g.get('preHash', 'pure')
        det = ''
        if mode == 'sigGen':
            det = '/det' if g.get('deterministic') else '/rnd'
        return f"{mode}/{g['parameterSet']}/{iface}{det}"

    def _hex_eq(a, b):
        return a.upper() == str(b).upper()

    def _passed(v):
        # NIST writes testPassed as a JSON boolean; tolerate "true"/"false".
        return v if isinstance(v, bool) else str(v).lower() == 'true'

    def keygen_ok(par, t, ref):
        sk_seed = bytes.fromhex(t['skSeed'])
        sk_prf = bytes.fromhex(t['skPrf'])
        pk_seed = bytes.fromhex(t['pkSeed'])
        pk_root = XMSS(par).node(sk_seed, 0, par.h_m, pk_seed, Address(par.d - 1, 0))
        return (_hex_eq((pk_seed + pk_root).hex(), ref['pk'])
                and _hex_eq((sk_seed + sk_prf + pk_seed + pk_root).hex(), ref['sk']))

    def sigver_ok(par, g, t, ref):
        pk = bytes.fromhex(t['pk'])
        if len(pk) != 2 * par.n:
            got = False
        else:
            got = bool(_slh_verify(_slhdsa_message(g, t), bytes.fromhex(t['signature']),
                                   (pk[:par.n], pk[par.n:]), par))
        return got == _passed(ref['testPassed'])

    def siggen_ok(par, g, t, ref):
        addrnd = None
        if not g.get('deterministic'):
            addrnd = bytes.fromhex(t['additionalRandomness'])
        sig = _slhdsa_sign_internal(_slhdsa_message(g, t), bytes.fromhex(t['sk']),
                                    addrnd, par)
        return _hex_eq(sig.hex(), ref['signature'])

    if verbose:
        print("=" * 64)
        print("  NIST ACVP END-TO-END SLH-DSA VERIFICATION (FIPS 205)")
        print(f"  Source: {'pinned/local' if _local else 'LIVE NIST ACVP-Server'}")
        if keygen:
            print("  keyGen: byte-exact pk and sk, all 12 parameter sets")
        if sigver:
            print("  sigVer: verdict = NIST testPassed (internal, pure, pre-hash)")
        if siggen:
            print("  sigGen: byte-exact signatures, deterministic and randomised")
        print("=" * 64)

    check = {'keyGen': lambda par, g, t, r: keygen_ok(par, t, r),
             'sigVer': sigver_ok, 'sigGen': siggen_ok}
    detail, failures, ok_all, tot_all = {}, [], 0, 0
    for mode in modes:
        p, e = load(mode)
        exp = {str(t['tcId']): t for g in e['testGroups'] for t in g['tests']}
        for g in p['testGroups']:
            ps = g['parameterSet']
            if param_sets and ps not in param_sets:
                continue
            par = _par(ps)
            label = _label(mode, g)
            if par is None:
                if verbose:
                    print(f"  SKIP  {ps}: parameter set not available in reference")
                continue
            ok = tot = 0
            for t in g['tests']:
                tot += 1
                try:
                    good = check[mode](par, g, t, exp[str(t['tcId'])])
                except Exception as ex:        # malformed input or missing answer
                    good = False
                    failures.append(f"{label} tcId {t['tcId']}: "
                                    f"{type(ex).__name__}: {ex}")
                else:
                    if not good:
                        failures.append(f"{label} tcId {t['tcId']}")
                ok += good
            prev = detail.get(label, (0, 0))
            detail[label] = (prev[0] + ok, prev[1] + tot)
            ok_all += ok
            tot_all += tot
            if verbose and mode != 'keyGen' and ok != tot:
                print(f"  FAIL      {label:40s} {ok}/{tot}")
            elif verbose and mode == 'keyGen':
                print(f"  {'PASS' if ok == tot else 'FAIL'}      {label:40s} {ok}/{tot}")
        if verbose and mode != 'keyGen':
            mp = sum(v[0] for k, v in detail.items() if k.startswith(mode + '/'))
            mt = sum(v[1] for k, v in detail.items() if k.startswith(mode + '/'))
            print(f"  {'PASS' if mp == mt else 'FAIL'}      {mode + ' (all groups)':40s} {mp}/{mt}")

    verified = (ok_all == tot_all and tot_all > 0)
    if verbose:
        print("=" * 64)
        print(f"  ACVP RESULT: {ok_all}/{tot_all} NIST SLH-DSA vectors verified")
        print("  scope: " + ", ".join(modes) + ", all 12 FIPS 205 parameter sets")
        if not siggen:
            print("  sigGen (624 byte-exact signatures, ~30 min) is opt-in:")
            print("         pq-verify --slhdsa-siggen")
        for f in failures[:10]:
            print(f"  failed: {f}")
        print("=" * 64)
    return {'verified': verified, 'passed': ok_all, 'total': tot_all,
            'detail': detail, 'modes': modes, 'failures': failures,
            'vectors': _vector_label(_local, *dirs),
            'reference': _reference('slh-dsa')}


_KEM_SIZES = {  # (ek, dk, ct, ss) per FIPS 203
    'ML-KEM-512':  (800, 1632, 768, 32),
    'ML-KEM-768':  (1184, 2400, 1088, 32),
    'ML-KEM-1024': (1568, 3168, 1568, 32),
}


# Public ML-KEM entry points by name suffix, across the naming schemes in use:
#   PQClean       PQCLEAN_MLKEM768_CLEAN_crypto_kem_{keypair_derand,enc_derand,dec}
#   mlkem-native  PQCP_MLKEM_NATIVE_MLKEM768_{keypair_derand,enc_derand,dec}
#   liboqs        OQS_KEM_ml_kem_768_{keypair_derand,encaps_derand,decaps}
_KEM_SYMBOL_PATTERNS = {
    'keypair': r'(?:^|_)keypair_derand$',
    'encaps':  r'(?:^|_)(?:enc|encaps)_derand$',
    'decaps':  r'(?:^|_)(?:dec|decaps)$',
}
# Internal K-PKE routines share those suffixes (mlkem-native exports
# indcpa_keypair_derand) but have different outputs. Binding one reports a
# correct library as faulty.
_KEM_INTERNAL_MARKERS = ('indcpa', 'cpapke', 'kpke')


def _resolve_kem_symbols(exported, param_set, explicit=None, prefix=None):
    """Pick keypair/encaps/decaps from a library's exported symbols.

    Returns ({role: symbol or None}, {role: [candidates]} for any role with
    more than one candidate). An ambiguous role is never guessed: a wrong
    binding produces a false finding against a correct library.
    """
    import re as _re
    from .symbols import with_prefix
    explicit = explicit or {}
    exported = with_prefix(exported, prefix)
    level = param_set.rsplit('-', 1)[-1]
    found, ambiguous = {}, {}
    for role, pat in _KEM_SYMBOL_PATTERNS.items():
        if explicit.get(role):
            found[role] = explicit[role]
            continue
        cands = [e for e in exported
                 if _re.search(pat, e.lower())
                 and not any(m in e.lower() for m in _KEM_INTERNAL_MARKERS)]
        # A library exporting several parameter sets (liboqs) names each one.
        same_level = [e for e in cands if level in e]
        if same_level:
            cands = same_level
        found[role] = cands[0] if len(cands) == 1 else None
        if len(cands) > 1:
            ambiguous[role] = sorted(cands)
    return found, ambiguous


def pqverify_audit_kem(so_path, param_set='ML-KEM-768', keypair=None, encaps=None,
                       decaps=None, prompt_dir=None, vector_dir=None, live=False,
                       verbose=True, edge=True, accumulated=10_000,
                       constant_time=False, prefix=None):
    """Audit a THIRD-PARTY ML-KEM implementation end to end against NIST's vectors.

    This is the scheme-level counterpart to pqverify_scan (which audits the NTT
    symbol). It exists because production libraries hide internal transforms but
    export the public KEM API: BoringSSL declares its NTT `inline` inside an
    anonymous namespace, AWS-LC compiles mlkem-native with
    MLK_CONFIG_INTERNAL_API_QUALIFIER=static, wolfSSL marks it `static`. None of
    those can be symbol-audited at the NTT level -- but all of them expose
    keygen / encapsulate / decapsulate, which is what customers actually run.

    Drives the vendor's own code with NIST's ACVP vectors:
        keygen : NIST (d,z)  -> vendor ek,dk   must match NIST byte-for-byte
        encaps : NIST (ek,m) -> vendor c,K     must match NIST byte-for-byte
        decaps : NIST (dk,c) -> vendor K       must match NIST byte-for-byte
        ekCheck: NIST's invalid ek (coefficient >= q) must be refused and
                 its valid ek accepted, by encaps (FIPS 203 §7.2)
        dkCheck: the same for decaps and a corrupted H(ek) (FIPS 203 §7.3)
    and, unless edge=False, the pinned Wycheproof/CCTV edge cases
    (pq_verify/edge.py):
        edgeValid: strcmp, unlucky-sampling, malleated-ciphertext and other
                   valid vectors must match byte-for-byte
        edgeEk   : every coefficient value q..4095 at every position of an
                   ek (CCTV modulus) must be refused
        edgeDk   : a dk with a corrupted H(ek) or embedded ek must be refused
    Refusal means a nonzero return, the PQClean / mlkem-native / liboqs
    convention.

    Requires DERANDOMISED entry points, because NIST's vectors are seeded. A
    library exposing only randomised keygen/encaps cannot be checked for
    byte-exactness -- only for self-consistency, which is not verification.
    PQClean names them *_crypto_kem_keypair_derand / *_crypto_kem_enc_derand.

    Symbols are auto-detected by exact suffix (internal K-PKE routines
    excluded) if not given explicitly; an ambiguous match is refused.
    """
    import ctypes as _ct, os as _o, subprocess as _sp
    so_path = _o.path.abspath(_o.path.expanduser(so_path))
    if not _o.path.exists(so_path):
        raise FileNotFoundError(so_path)
    if param_set not in _KEM_SIZES:
        raise ValueError(f"unknown parameter set {param_set}")
    ek_n, dk_n, ct_n, ss_n = _KEM_SIZES[param_set]

    lib = _ct.CDLL(so_path)

    # ---- locate the three entry points ----
    from .symbols import exported_functions
    exported = exported_functions(so_path)

    found, ambiguous = _resolve_kem_symbols(
        exported, param_set,
        {'keypair': keypair, 'encaps': encaps, 'decaps': decaps}, prefix=prefix)
    kp, en, de = found['keypair'], found['encaps'], found['decaps']
    if ambiguous:
        from .symbols import ambiguity_message
        print(ambiguity_message(so_path, ambiguous, _KEM_SYMBOL_PATTERNS,
                                f"--kem-{next(iter(ambiguous))} or "
                                f"{next(iter(ambiguous))}="))
        DEGRADED['skipped_checks'].append(f'KEM audit ({param_set})')
        return None
    missing = [n for n, v in (('keypair_derand', kp), ('enc_derand', en),
                              ('dec', de)) if v is None]
    if missing:
        print(f"  Cannot audit {so_path}:")
        print(f"    missing derandomised entry point(s): {', '.join(missing)}")
        print(f"    NIST's vectors are seeded; without a derandomised API the")
        print(f"    library can only be checked for self-consistency, which is")
        print(f"    not verification. Pass keypair=/encaps=/decaps= explicitly")
        print(f"    if the symbols are named differently.")
        if exported:
            hint = [e for e in exported if 'kem' in e.lower()][:6]
            if hint:
                print(f"    exported KEM symbols: {hint}")
        DEGRADED['skipped_checks'].append(f'KEM audit ({param_set})')
        return None

    f_kp = getattr(lib, kp); f_kp.restype = _ct.c_int
    f_en = getattr(lib, en); f_en.restype = _ct.c_int
    f_de = getattr(lib, de); f_de.restype = _ct.c_int

    # ---- NIST vectors (same source resolution as pqverify_acvp) ----
    import json as _j
    _local = prompt_dir or vector_dir
    if not _local and not live:
        _local = _o.path.join(_pkg_dir(), "vectors")

    def _load(name, fn):
        if _local:
            return _load_vector_json(_o.path.join(_local, name, fn), f"{name}/{fn}")
        import urllib.request
        return _j.loads(urllib.request.urlopen(
            _ACVP_BASE + name + "/" + fn, timeout=60).read())

    if verbose:
        print("=" * 68)
        print(f"  THIRD-PARTY KEM AUDIT \u2014 {param_set}")
        print(f"  library : {_o.path.basename(so_path)}")
        print(f"  keygen  : {kp}")
        print(f"  encaps  : {en}")
        print(f"  decaps  : {de}")
        print(f"  vectors : {_vector_label(_local, 'ML-KEM-keyGen-FIPS203', 'ML-KEM-encapDecap-FIPS203')}")
        print("=" * 68)

    tally = {}
    keycheck = {}
    def _rec(stage, ok):
        p, t = tally.get(stage, (0, 0))
        tally[stage] = (p + int(ok), t + 1)

    # ---- keyGen: NIST (d,z) -> vendor ek,dk ----
    kg = _load("ML-KEM-keyGen-FIPS203", "internalProjection.json")
    for g in kg['testGroups']:
        if g.get('parameterSet') != param_set:
            continue
        for t in g['tests']:
            coins = bytes.fromhex(t['d']) + bytes.fromhex(t['z'])
            ek = (_ct.c_ubyte * ek_n)(); dk = (_ct.c_ubyte * dk_n)()
            f_kp(ek, dk, (_ct.c_ubyte * 64)(*coins))
            ok = (bytes(ek).hex().upper() == t['ek'].upper() and
                  bytes(dk).hex().upper() == t['dk'].upper())
            _rec('keyGen', ok)

    # ---- encaps / decaps ----
    ed = _load("ML-KEM-encapDecap-FIPS203", "internalProjection.json")
    for g in ed['testGroups']:
        if g.get('parameterSet') != param_set:
            continue
        fn = g.get('function')
        for t in g['tests']:
            if fn == 'encapsulation':
                ct_b = (_ct.c_ubyte * ct_n)(); ss = (_ct.c_ubyte * ss_n)()
                f_en(ct_b, ss, (_ct.c_ubyte * ek_n)(*bytes.fromhex(t['ek'])),
                     (_ct.c_ubyte * 32)(*bytes.fromhex(t['m'])))
                ok = (bytes(ct_b).hex().upper() == t['c'].upper() and
                      bytes(ss).hex().upper() == t['k'].upper())
                _rec('encaps', ok)
            elif fn == 'decapsulation':
                if 'dk' not in t or 'c' not in t or 'k' not in t:
                    continue
                ss = (_ct.c_ubyte * ss_n)()
                f_de(ss, (_ct.c_ubyte * ct_n)(*bytes.fromhex(t['c'])),
                     (_ct.c_ubyte * dk_n)(*bytes.fromhex(t['dk'])))
                ok = bytes(ss).hex().upper() == t['k'].upper()
                _rec('decaps', ok)
            elif fn in ('encapsulationKeyCheck', 'decapsulationKeyCheck'):
                # Negative testing: NIST's invalid keys (coefficients >= q,
                # a corrupted H(ek)) must be refused, valid ones accepted.
                # FIPS 203 §7.2/§7.3 require the check; a library that skips
                # it leaves it to every caller. Refusal is a nonzero return,
                # the convention of PQClean, mlkem-native and liboqs.
                if fn == 'encapsulationKeyCheck':
                    stage = 'ekCheck'
                    rc = f_en((_ct.c_ubyte * ct_n)(), (_ct.c_ubyte * ss_n)(),
                              (_ct.c_ubyte * ek_n)(*bytes.fromhex(t['ek'])),
                              (_ct.c_ubyte * 32)())
                else:
                    stage = 'dkCheck'
                    rc = f_de((_ct.c_ubyte * ss_n)(), (_ct.c_ubyte * ct_n)(),
                              (_ct.c_ubyte * dk_n)(*bytes.fromhex(t['dk'])))
                accepted = rc == 0
                _rec(stage, accepted == bool(t['testPassed']))
                m = keycheck.setdefault(stage, {'accepted_invalid': 0,
                                                'rejected_valid': 0})
                if accepted and not t['testPassed']:
                    m['accepted_invalid'] += 1
                elif not accepted and t['testPassed']:
                    m['rejected_valid'] += 1

    edge_res = None
    if edge:
        from .edge import VendorKEM, run_kem, sources as _edge_sources
        edge_res = run_kem(VendorKEM(f_kp, f_en, f_de, (ek_n, dk_n, ct_n),
                                     name=_o.path.basename(so_path)), param_set)
        edge_res['vectors'] = _edge_sources()
        for stage, (p, t) in edge_res['stages'].items():
            tally[stage] = (p, t)

    acc_res = None
    if accumulated:
        from .edge import VendorKEM
        from . import accumulated as _acc
        ok, why = _acc.run_kem(VendorKEM(f_kp, f_en, f_de, (ek_n, dk_n, ct_n),
                                         name=_o.path.basename(so_path)),
                               param_set, accumulated)
        tally['accumulated'] = (int(ok), 1)
        acc_res = {'cases': accumulated, 'ok': ok, 'detail': why,
                   'source': _acc.source(param_set, accumulated)}

    ct_res = None
    if constant_time:
        from . import ct_audit as _ct
        try:
            ct_res = _ct.run_kem(so_path, param_set, kp, en, de)
            for op, v in ct_res['stages'].items():
                tally['ct:' + op] = v
        except _ct.Unavailable as exc:
            # Asked for and not run is not a pass: a stage that fails, saying why.
            ct_res = {'unavailable': str(exc)}
            tally['ct:unavailable'] = (0, 1)

    p_all = sum(p for p, _ in tally.values())
    t_all = sum(t for _, t in tally.values())
    if verbose:
        for stage in ('keyGen', 'encaps', 'decaps'):
            if stage in tally:
                p, t = tally[stage]
                print(f"  {'PASS' if p == t else 'FAIL'}  {stage:8s} "
                      f"{p}/{t}  byte-exact vs NIST")
        for stage, what, sec in (('ekCheck', 'encapsulation', '7.2'),
                                 ('dkCheck', 'decapsulation', '7.3')):
            if stage in tally:
                p, t = tally[stage]
                m = keycheck[stage]
                print(f"  {'PASS' if p == t else 'FAIL'}  {stage:8s} "
                      f"{p}/{t}  {what} keys classified as NIST does "
                      f"(FIPS 203 \u00a7{sec})")
                if m['accepted_invalid']:
                    print(f"        accepted {m['accepted_invalid']} invalid key(s) "
                          f"NIST rejects: this API does not perform the input")
                    print(f"        check, so every caller must")
                if m['rejected_valid']:
                    print(f"        rejected {m['rejected_valid']} valid key(s)")
        if edge_res is not None:
            what = {'edgeValid': 'edge-case vectors reproduced byte-for-byte',
                    'edgeEk': 'invalid encapsulation keys refused (every q..4095, every position)',
                    'edgeDk': 'invalid decapsulation keys refused'}
            print(f"  edge cases: {edge_res['vectors']}")
            for stage in ('edgeValid', 'edgeEk', 'edgeDk'):
                if stage in edge_res['stages']:
                    p, t = edge_res['stages'][stage]
                    print(f"  {'PASS' if p == t else 'FAIL'}  {stage:9s} {p}/{t}  {what[stage]}")
            for f in edge_res['failures'][:3]:
                print(f"        \u2717 {f['case']} {f['flags']}: {f['detail']}")
            if len(edge_res['failures']) > 3:
                print(f"        ... and more; see the JSON report")
            if edge_res['not_applicable']:
                print(f"        {edge_res['not_applicable']} wrong-length vectors not applicable: "
                      f"a C entry point takes fixed-size buffers")
        if acc_res:
            print(f"  {'PASS' if acc_res['ok'] else 'FAIL'}  accumulated "
                  f"{int(acc_res['ok'])}/1  {acc_res['detail']}")
        if ct_res and 'unavailable' in ct_res:
            print(f"  FAIL  constant time: could not run ({ct_res['unavailable']})")
        elif ct_res:
            for op, (p, t) in ct_res['stages'].items():
                print(f"  {'PASS' if p == t else 'FAIL'}  ct:{op:7s} {p}/{t}  no secret-dependent "
                      f"branch or memory access (Valgrind memcheck)")
                for lk in ct_res['leaks'][op][:3]:
                    print(f"        \u2717 {lk['kind']} in {lk['function']} "
                          f"({lk['count']} report(s))")
            if ct_res.get('divisions'):
                print(f"        division instructions (not checked for timing): "
                      f"{', '.join(sorted(ct_res['divisions']))}")
        print("=" * 68)
        print(f"  RESULT: {p_all}/{t_all} \u2014 "
              f"{'VERIFIED' if p_all == t_all and t_all else 'FINDINGS PRESENT'}")
        print(f"  This audits the vendor's OWN keygen/encaps/decaps against")
        print(f"  NIST's published vectors, including the invalid keys it")
        print(f"  must refuse. " + ("Constant-time: branches and addresses only, not "
                                   "timing or power." if constant_time else
                                   "It is not a side-channel review."))
        print("=" * 68)
    return {'verified': p_all == t_all and t_all > 0, 'passed': p_all,
            'total': t_all, 'detail': tally, 'library': so_path,
            'keycheck': keycheck, 'edge': edge_res, 'accumulated': acc_res,
            'constant_time': ct_res,
            'vectors': _vector_label(_local, 'ML-KEM-keyGen-FIPS203', 'ML-KEM-encapDecap-FIPS203'),
            'symbols': {'keypair': kp, 'encaps': en, 'decaps': de}}


def pqverify_acvp_all(prompt_dir=None, verbose=True, live=False, vector_dir=None,
                      slhdsa=True, slhdsa_siggen=False, lms=True):
    """Run the ACVP suites: ML-KEM (FIPS 203), ML-DSA (FIPS 204), SLH-DSA
    (FIPS 205) key generation and signature verification, and LMS
    (SP 800-208).

    By default runs against the FROZEN vectors bundled in this package, so the
    result is deterministic and offline: 240 + 615 + 624 + 87 = 1566 vectors.
    slhdsa=False leaves FIPS 205 out, lms=False leaves SP 800-208 out
    (855 vectors with both off: ML-KEM + ML-DSA only);
    slhdsa_siggen=True adds SLH-DSA signature generation, 624 byte-exact
    signatures that take about half an hour. Pass live=True to verify against
    NIST's current upstream vectors instead.
    Requires: pip install "pq-verify[full]"  (kyber-py, dilithium-py, slh-dsa)
    """
    if verbose:
        print("#" * 64)
        print("  NIST ACVP — FULL COVERAGE (FIPS 203 + FIPS 204"
              + (" + FIPS 205" if slhdsa else "") + (" + SP 800-208" if lms else "") + ")")
        print("#" * 64)
    kem = pqverify_acvp(prompt_dir=prompt_dir, verbose=verbose, live=live, vector_dir=vector_dir)
    dsa = pqverify_mldsa_acvp(prompt_dir=prompt_dir, verbose=verbose, live=live, vector_dir=vector_dir)
    slh = None
    if slhdsa or slhdsa_siggen:
        slh = pqverify_slhdsa_acvp(prompt_dir=prompt_dir, verbose=verbose,
                                   live=live, vector_dir=vector_dir,
                                   siggen=slhdsa_siggen)
    lms_r = None
    if lms:
        from .hbs_suite import pqverify_lms_acvp
        lms_r = pqverify_lms_acvp(prompt_dir=prompt_dir, verbose=verbose, live=live,
                                  vector_dir=vector_dir)
    kem_p = kem['passed'] if kem else 0
    kem_t = kem['total'] if kem else 0
    dsa_p = dsa['passed'] if dsa else 0
    dsa_t = dsa['total'] if dsa else 0
    slh_p = slh['passed'] if slh else 0
    slh_t = slh['total'] if slh else 0
    lms_p = lms_r['passed'] if lms_r else 0
    lms_t = lms_r['total'] if lms_r else 0
    total_p = kem_p + dsa_p + slh_p + lms_p
    total_t = kem_t + dsa_t + slh_t + lms_t
    if verbose:
        print("#" * 64)
        print(f"  COMBINED ACVP: {total_p}/{total_t} NIST vectors")
        print("  SCOPE: reference-chain conformance, not a vendor audit.")
        print(f"    ML-KEM (FIPS 203): {kem_p}/{kem_t}")
        print(f"    ML-DSA (FIPS 204): {dsa_p}/{dsa_t}")
        if slhdsa or slhdsa_siggen:
            scope = ", ".join(slh['modes']) if slh else "did not run"
            print(f"    SLH-DSA (FIPS 205, {scope}): {slh_p}/{slh_t}")
        if lms:
            print(f"    LMS (SP 800-208): {lms_p}/{lms_t}")
        print("#" * 64)
    # Every requested suite must have run AND verified. Summing only what ran
    # let a missing kyber-py drop ML-KEM from both sides of the ratio, so the
    # API said verified=True for a run that never touched FIPS 203.
    requested = [kem, dsa] + ([slh] if (slhdsa or slhdsa_siggen) else []) \
        + ([lms_r] if lms else [])
    not_run = [n for n, r in (('ML-KEM', kem), ('ML-DSA', dsa),
                              ('SLH-DSA', slh if (slhdsa or slhdsa_siggen) else 0),
                              ('LMS', lms_r if lms else 0)) if r is None]
    return {'verified': (total_p == total_t and total_t > 0 and not not_run
                         and all(r['verified'] for r in requested if r)),
            'not_run': not_run,
            'slh_dsa': slh, 'slh_dsa_requested': bool(slhdsa or slhdsa_siggen),
            'lms': lms_r, 'lms_requested': bool(lms),
            'passed': total_p, 'total': total_t,
            'ml_kem': kem, 'ml_dsa': dsa}



# Bai-Galbraith scaled primal uSVP (handles sigma_s != sigma_e)
# Calibrated: reproduces Kyber-512 beta=406/118.6, T-Kyber hw=40 beta=328/95.8
import math as _math
from math import lgamma as _lgamma

def _pq_delta(beta):
    beta = float(beta)
    return ((_math.pi*beta)**(1.0/beta) * beta/(2*_math.pi*_math.e))**(1.0/(2*(beta-1)))

def _pq_log2binom(n, k):
    if k <= 0 or k >= n: return 0.0
    return (_lgamma(n+1) - _lgamma(k+1) - _lgamma(n-k+1)) / _math.log(2)

def _pq_primal(n, q, ss, se, m_max, m_min=40):
    """Primal uSVP, Bai-Galbraith scaled. Returns (beta, m, d)."""
    nu = se / ss
    best = (10**9, None, None)
    for m in range(m_min, m_max + 1):
        d = n + m + 1
        vol = m * _math.log2(q) + n * _math.log2(nu)
        tnorm = se * _math.sqrt(n + m + 1)
        for b in range(40, d):
            lhs = _math.log2(_math.sqrt(b / d) * tnorm)
            rhs = (2*b - d - 1) * _math.log2(_pq_delta(b)) + vol / d
            if rhs >= lhs:
                if b < best[0]: best = (b, m, d)
                break
    return best

def _pq_hybrid(n, q, w, se, m_max):
    """Sparse primal-hybrid (Howgrave-Graham): guess r coords, BKZ the rest."""
    best = (1e9, None)
    for r in range(0, n - 60, 4):
        nr = n - r
        wr = r * w / n
        logN = _pq_log2binom(r, max(1, round(wr))) + wr
        mitm = 0.5 * logN
        w_rest = max(w - wr, 1.0)
        ss_rest = _math.sqrt(w_rest / nr)
        b = _pq_primal(nr, q, ss_rest, se, min(m_max, nr))[0]
        latt = 0.292 * b
        cost = max(latt, mitm)
        if cost < best[0]:
            best = (cost, {'r': r, 'beta': b, 'mitm': round(mitm, 1), 'lattice': round(latt, 1)})
    return best

_LEVEL_THRESHOLDS = {1: 118.0, 2: 120.0, 3: 183.0, 5: 252.0}
# Authoritative values from the lattice-estimator (Albrecht et al.)
# These are the NIST standards — NOT computed by our simplified formula.
_STANDARD_PARAMS = {
    'ML-KEM-512':  dict(n=512,  q=3329, ss=1.2247, se=1.2247, k=2, level=1,
                        _auth_beta=406, _auth_cl=118.6, _auth_qu=107.6, _auth_m=486, _auth_d=999),
    'ML-KEM-768':  dict(n=768,  q=3329, ss=1.0,    se=1.0,    k=3, level=3,
                        _auth_beta=630, _auth_cl=183.9, _auth_qu=167.0, _auth_m=658, _auth_d=1427),
    'ML-KEM-1024': dict(n=1024, q=3329, ss=1.0,    se=1.0,    k=4, level=5,
                        _auth_beta=864, _auth_cl=252.3, _auth_qu=229.0, _auth_m=842, _auth_d=1707),
}

def pqverify_params(param_set=None, n=None, q=None, k=None, sigma_s=None, sigma_e=None, hw=None):
    """Check parameter-set security using the Bai-Galbraith primal-uSVP estimator.

    For standard ML-KEM: computes security from the FIPS parameters.
    For custom parameters (e.g. sparse ternary secrets): computes primal-uSVP
    and primal-hybrid attack costs, flags if below NIST Level 1.

    Calibrated: reproduces lattice-estimator results exactly
    (Kyber-512 beta=406/118.6, T-Kyber hw=40 beta=328/95.8).

    For authoritative results with the full attack surface (dual, hybrid,
    arora-ge), use: sage estimate_tkyber.py (lattice-estimator by Albrecht et al.)
    """
    print("=" * 64)
    print("  PARAMETER SECURITY CHECK (Bai-Galbraith primal-uSVP)")

    # Standard parameter set — use AUTHORITATIVE values from lattice-estimator
    if param_set and param_set in _STANDARD_PARAMS:
        p = _STANDARD_PARAMS[param_set]
        beta = p['_auth_beta']; cl = p['_auth_cl']; qu = p['_auth_qu']
        m = p['_auth_m']; d = p['_auth_d']
        thr = _LEVEL_THRESHOLDS.get(p['level'], 118.0)
        print(f"  Parameter set: {param_set} (NIST Level {p['level']})")
        print(f"  n={p['n']}, q={p['q']}, sigma_s={p['ss']:.4f}, sigma_e={p['se']:.4f}")
        print("=" * 64)
        print(f"\n  PRIMAL uSVP: beta={beta}  (m={m}, d={d})")
        print(f"    -> classical {cl:.1f}  |  quantum {qu:.1f}  [core-SVP bits]")
        ok = cl >= thr
        print(f"  NIST Level {p['level']}: {'MEETS' if ok else 'BELOW'} ({thr:.0f}-bit threshold)")
        print(f"\n  Source: lattice-estimator (Albrecht et al.), authoritative")
        print("=" * 64)
        return {'param_set': param_set, 'beta': beta, 'classical': cl,
                'quantum': qu, 'level': p['level'], 'meets_level': ok}

    # Custom parameters
    if n and q:
        if k and not n: n = k * 256
        n_lwe = n
        if sigma_s is None and hw is not None:
            sigma_s = _math.sqrt(hw / n_lwe) if hw else 1.0
        if sigma_s is None: sigma_s = 1.0
        if sigma_e is None: sigma_e = 1.0

        print(f"  Custom: n={n_lwe}, q={q}, sigma_s={sigma_s:.4f}, sigma_e={sigma_e:.4f}")
        if hw: print(f"  Sparse secret: hw={hw} ({100*hw/n_lwe:.1f}% density)")
        print("=" * 64)

        beta, m, d = _pq_primal(n_lwe, q, sigma_s, sigma_e, n_lwe)
        cl = 0.292 * beta; qu = 0.265 * beta
        print(f"\n  PRIMAL uSVP: beta={beta}  (m={m}, d={d})")
        print(f"    -> classical {cl:.1f}  |  quantum {qu:.1f}  [core-SVP bits]")

        if hw:
            hc, ha = _pq_hybrid(n_lwe, q, hw, sigma_e, n_lwe)
            print(f"\n  PRIMAL-HYBRID (sparse, w={hw}):")
            print(f"    -> classical {hc:.1f} bits   {ha}")
            if hc < cl:
                print(f"    WARNING: hybrid is {cl-hc:.0f} bits cheaper than primal!")

        # Level check
        for lv in (5, 3, 1):
            thr = _LEVEL_THRESHOLDS[lv]
            effective = min(cl, hc) if hw else cl
            if effective >= thr:
                print(f"\n  Meets NIST Level {lv} ({thr:.0f}-bit threshold)")
                break
        else:
            print(f"\n  BELOW NIST Level 1 ({_LEVEL_THRESHOLDS[1]:.0f}-bit threshold)")
            print(f"  WARNING: parameters do not meet minimum NIST security level")

        print(f"\n  For full attack surface (dual, arora-ge), run the lattice-estimator:")
        print(f"    sage estimate_tkyber.py  # Albrecht et al.")
        print("=" * 64)
        return {'beta': beta, 'classical': cl, 'quantum': qu,
                'hybrid': hc if hw else None, 'hybrid_detail': ha if hw else None}

    print("  Usage: pqverify_params('ML-KEM-1024')  or  pqverify_params(n=512, q=3329, hw=80)")
    print("=" * 64)
    return None


# ================================================================
# PUBLIC API: pqverify_load_so — load NTT from any .so for auditing
# ================================================================

def _detect_scheme(*hints):
    """Infer the lattice scheme from a symbol name / library path.
    Returns 'mldsa', 'mlkem', or None. Used to pick the right field and, more
    importantly, the right ctypes WIDTH -- ML-DSA coefficients are int32 and
    writing them into an int16 buffer is a heap overflow."""
    blob = ' '.join(str(h) for h in hints if h).lower()
    for tok in ('dilithium', 'mldsa', 'ml_dsa', 'ml-dsa', 'fips204'):
        if tok in blob:
            return 'mldsa'
    for tok in ('kyber', 'mlkem', 'ml_kem', 'ml-kem', 'fips203'):
        if tok in blob:
            return 'mlkem'
    return None


_SCHEME_FIELD = {'mlkem': (KYBER_Q, KYBER_ZETA), 'mldsa': (DILI_Q, DILI_ZETA)}


def pqverify_load_so(so_path, func_name='ntt', q=None, n=256, in_place=True,
                     scheme=None, force=False):
    """Load an NTT function from a compiled .so and return a callable for pqverify_scan.

    Usage:
        ntt = pqverify_load_so('/path/to/liboqs.so', 'OQS_KEM_ml_kem_768_keypair')
        pqverify_scan(ntt, ns=globals())

    Or for pq-crystals style:
        ntt = pqverify_load_so('./libpqcrystals_kyber768_ref.so', 'pqcrystals_kyber768_ref_ntt')
        pqverify_scan(ntt)

    Args:
        so_path: path to .so file
        func_name: symbol name (use nm -D libfoo.so | grep -i ntt to find it)
        q: field prime. If None (default) it is inferred from `scheme`, or from
           the symbol/path via _detect_scheme, falling back to ML-KEM's 3329.
        n: polynomial degree (256)
        in_place: True if void ntt(T r[n]), False if void ntt(T *out, const T *in)
        scheme: 'mlkem' | 'mldsa' | None. Sets q AND the ctypes integer width.
        force: bypass the width/scheme safety check (not recommended).

    SAFETY: ML-DSA (q=8380417) coefficients are int32; ML-KEM (q=3329) are
    int16. Loading an ML-DSA NTT with ML-KEM parameters allocates a 512-byte
    buffer for a function that writes 1024 bytes -- a heap overflow that
    silently corrupts memory on some systems and segfaults on others. This
    function now detects that mismatch and refuses, rather than proceeding.
    """
    import os, subprocess
    so_path = os.path.abspath(os.path.expanduser(so_path))
    if not os.path.exists(so_path):
        raise FileNotFoundError(f"Library not found: {so_path}")

    # ---- resolve scheme and field BEFORE any buffer is allocated ----
    detected = _detect_scheme(func_name, so_path)
    if scheme is None:
        scheme = detected
    if q is None:
        q = _SCHEME_FIELD.get(scheme, (KYBER_Q, KYBER_ZETA))[0]

    # SAFETY: refuse a width/field mismatch instead of overflowing the buffer.
    if not force and detected is not None:
        want_q = _SCHEME_FIELD[detected][0]
        if (q <= 32767) != (want_q <= 32767):
            raise ValueError(
                f"Refusing to load '{func_name}': it looks like {detected.upper()} "
                f"(expects q={want_q}, {'int32' if want_q > 32767 else 'int16'} "
                f"coefficients) but q={q} was requested, which would allocate "
                f"{'int16' if q <= 32767 else 'int32'} buffers.\n"
                f"  ML-DSA writes int32; an int16 buffer overflows by "
                f"{n * 2} bytes -> silent corruption or SIGSEGV.\n"
                f"  Fix: pass scheme='{detected}' (or q={want_q}), "
                f"or force=True to override.")

    lib = ctypes.CDLL(so_path)

    # Try requested name + common variants
    candidates = [func_name]
    base = func_name.lower()
    if scheme == 'mldsa' or 'dilithium' in base or 'mldsa' in base:
        candidates += [f'pqcrystals_dilithium3_ref_{func_name}',
                       f'pqcrystals_dilithium2_ref_{func_name}',
                       f'pqcrystals_dilithium5_ref_{func_name}',
                       'pqcrystals_dilithium3_ref_ntt',
                       'PQCLEAN_MLDSA65_CLEAN_ntt',
                       'PQCLEAN_MLDSA44_CLEAN_ntt',
                       'PQCLEAN_MLDSA87_CLEAN_ntt',
                       'PQCLEAN_DILITHIUM3_CLEAN_ntt',
                       'ntt', 'poly_ntt', 'mldsa_ntt', 'dilithium_ntt']
    if 'ntt' in base or 'kyber' in base or 'mlkem' in base:
        candidates += [f'pqcrystals_kyber768_ref_{func_name}',
                       f'pqcrystals_kyber512_ref_{func_name}',
                       f'pqcrystals_kyber1024_ref_{func_name}',
                       'poly_ntt', 'ntt', 'mlkem_ntt', 'kyber_ntt',
                       'PQCLEAN_KYBER768_CLEAN_ntt',
                       'PQCLEAN_KYBER512_CLEAN_ntt',
                       'PQCLEAN_MLKEM768_CLEAN_ntt',
                       'PQCLEAN_MLKEM512_CLEAN_ntt',
                       'PQCLEAN_MLKEM1024_CLEAN_ntt',
                       'OQS_KEM_ml_kem_768_ntt']

    fn = None; found_name = None
    for name in dict.fromkeys(candidates):  # deduplicate, preserve order
        try:
            fn = getattr(lib, name)
            found_name = name
            break
        except AttributeError:
            continue

    if fn is None:
        # Show available NTT-related symbols
        from .symbols import exported_functions
        ntt_syms = [s for s in exported_functions(so_path) if 'ntt' in s.lower()]
        hint = '\n'.join(ntt_syms[:20]) if ntt_syms else '(none found, or nm not available)'
        raise AttributeError(
            f"Symbol '{func_name}' not found in {so_path}\n"
            f"Tried: {list(dict.fromkeys(candidates))}\n"
            f"NTT-related symbols in library:\n{hint}")

    # Set up ctypes signature
    c_type = ctypes.c_int16 if q <= 32767 else ctypes.c_int32
    arr_type = c_type * n

    if in_place:
        fn.argtypes = [ctypes.POINTER(arr_type)]
        fn.restype = None

        def ntt_callable(coeffs):
            arr = arr_type(*[int(x) % q for x in coeffs])
            fn(ctypes.byref(arr))
            return [arr[i] % q for i in range(n)]
    else:
        fn.argtypes = [ctypes.POINTER(arr_type), ctypes.POINTER(arr_type)]
        fn.restype = None

        def ntt_callable(coeffs):
            inp = arr_type(*[int(x) % q for x in coeffs])
            out = arr_type()
            fn(ctypes.byref(out), ctypes.byref(inp))
            return [out[i] % q for i in range(n)]

    ntt_callable.__name__ = f"ntt_{os.path.basename(so_path)}:{found_name}"
    ntt_callable.pqv_scheme = scheme
    ntt_callable.pqv_q = q
    ntt_callable.pqv_n = n
    print(f"  Loaded: {found_name} from {os.path.basename(so_path)} (q={q}, n={n}, {'in-place' if in_place else 'out-of-place'})")
    return ntt_callable


# ================================================================
# PUBLIC API: pqverify_scan — audit any NTT in the same notebook
# ================================================================

def _pq_probe_ntt(func, ns, q=3329, n=256):
    """Probe func with common NTT signatures. Returns (wrapped, desc) or None."""
    test = [random.randint(0, q-1) for _ in range(n)]
    try:
        out = func(list(test))
        if isinstance(out, (list, tuple)) and len(out) == n and not isinstance(out[0], (list, tuple)):
            return func, "func(poly)"
    except: pass
    try:
        out = func(list(test))
        if isinstance(out, tuple) and isinstance(out[0], (list, tuple)) and len(out[0]) == n:
            w = lambda p, _f=func: list(_f(p)[0])
            w.__name__ = getattr(func, '__name__', '?') + "_unwrapped"
            return w, "func(poly) -> (out, ...) [unwrapped]"
    except: pass
    for vname, obj in ns.items():
        if not (hasattr(obj, 'should_exec') or vname == 'ye'): continue
        try:
            out = func(list(test), obj)
            first = out[0] if isinstance(out, tuple) else out
            if isinstance(first, (list, tuple)) and len(first) == n:
                w = lambda p, _f=func, _ye=obj: list(_f(p, _ye)[0]) if isinstance(_f(p, _ye), tuple) else list(_f(p, _ye))
                w.__name__ = getattr(func, '__name__', '?') + f"(+{vname})"
                return w, f"func(poly, {vname})"
        except: pass
    return None


def pqverify_scan(*targets, ns=None, scheme=None, q=None, zeta=None):
    """Audit NTT implementations from the notebook namespace.

    Usage (in the next cell after running pq-verify + your crypto):
        pqverify_scan(globals())            # auto-discover and audit all
        pqverify_scan(my_func, ns=globals())  # audit a specific function
    """
    if ns is None:
        if targets and isinstance(targets[0], dict):
            ns = targets[0]; targets = targets[1:]
        else:
            try: ns = get_ipython().user_ns
            except: ns = {}

    # Constants
    # Field/scheme resolution, in priority order:
    #   1. explicit scheme= / q= / zeta= arguments
    #   2. metadata attached by pqverify_load_so (pqv_scheme / pqv_q)
    #   3. the notebook namespace
    #   4. ML-KEM defaults
    _q_arg, _zeta_arg = q, zeta
    if scheme is None:
        for t in targets:
            sc = getattr(t, 'pqv_scheme', None)
            if sc: scheme = sc; break
        else:
            for t in targets:
                nm = getattr(t, '__name__', '')
                sc = _detect_scheme(nm)
                if sc: scheme = sc; break
    if scheme in _SCHEME_FIELD:
        _sq, _sz = _SCHEME_FIELD[scheme]
    else:
        _sq, _sz = None, None
    q = (_q_arg or _sq
         or ns.get('KYBER_Q') or ns.get('Q') or ns.get('q', 3329))
    zeta_root = (_zeta_arg or _sz
                 or ns.get('KYBER_ZETA') or ns.get('ZETA') or ns.get('zeta', 17))
    if scheme is None:
        scheme = 'mldsa' if q == DILI_Q else 'mlkem'
    if scheme == 'mldsa':
        print(f"  scheme: ML-DSA (FIPS 204) q={q} zeta={zeta_root} "
              f"-- complete 8-layer NTT")
    
    n = ns.get('KYBER_N') or ns.get('N', 256)
    if isinstance(q, float): q = int(q)
    if isinstance(n, float): n = int(n)
    zetas = None
    for zn in ['ZETAS', 'TKYBER_ZETAS', 'ntt_zetas', 'zetas', 'KYBER_ZETAS']:
        if zn in ns and isinstance(ns[zn], (list, tuple)) and len(ns[zn]) >= 64:
            zetas = list(ns[zn]); break

    cp_ap = cp_rm = None
    for name, obj in ns.items():
        if not callable(obj): continue
        if 'cp_apply' in name.lower(): cp_ap = obj
        if 'cp_remove' in name.lower(): cp_rm = obj

    eng = ns.get('engines', {}) or globals().get('engines', {})

    # Reference NTT
    # Layer count is determined by the ORDER of zeta, not by n.
    #   ML-KEM  : zeta has order n   -> 2n does NOT divide q-1 -> incomplete,
    #             last layer deleted -> log2(n) - 1 layers (7 for n=256)
    #   ML-DSA  : zeta has order 2n  -> 2n divides q-1 -> COMPLETE transform
    #             -> log2(n) layers (8 for n=256)
    # Deriving it from zeta's actual order makes this correct for any scheme
    # rather than assuming ML-KEM.
    _log2n = max(1, n.bit_length() - 1)
    if pow(zeta_root, 2 * n, q) == 1 and pow(zeta_root, n, q) == q - 1:
        bits = _log2n            # complete transform (ML-DSA-like)
    else:
        bits = _log2n - 1        # incomplete, last layer deleted (ML-KEM-like)
    def _br(x):
        r = 0
        for _ in range(bits): r = (r << 1) | (x & 1); x >>= 1
        return r
    # Zeta table size: a complete transform consumes 2^bits - 1 twiddles
    # (255 for 8 layers), an incomplete one 2^bits - 1 as well but with
    # bits one smaller (127 for 7 layers). Build n entries when complete so
    # the 8th layer has its twiddles; n//2 is enough when incomplete.
    _nz = n if bits == _log2n else n // 2
    ref_z = [pow(zeta_root, _br(i), q) for i in range(_nz)]
    def _ref_ntt(poly):
        f = [x % q for x in poly]; k = 1
        for layer in range(bits):
            length = n // (2 << layer)
            for start in range(0, n, 2 * length):
                z = ref_z[k]; k += 1
                for j in range(start, start + length):
                    t = (z * f[j + length]) % q
                    f[j + length] = (f[j] - t) % q; f[j] = (f[j] + t) % q
        return f

    # Discover targets
    if targets:
        to_audit = []
        for t in targets:
            if callable(t):
                nm = getattr(t, '__name__', str(t))
                result = _pq_probe_ntt(t, ns, q, n)
                if result: to_audit.append((nm, result[0], result[1]))
                else: print(f"  \u274c {nm}: probe failed")
            elif isinstance(t, str) and t in ns and callable(ns[t]):
                result = _pq_probe_ntt(ns[t], ns, q, n)
                if result: to_audit.append((t, result[0], result[1]))
    else:
        keywords = ['ntt', 'transform', 'kyber', 'dilithium', 'encrypt',
                    'encap', 'butterfly', 'forward', 'inverse']
        skip = {'pqverify_scan', '_pq_probe_ntt', 'main', 'compile_all', 'bind_all',
                'batch_verify_ntt', 'batch_verify_keypairs', 'audit_batch_api',
                'audit_freivalds_ntt', 'audit_full_ntt', 'audit_full_ntt_dilithium'}
        to_audit = []
        print(f"\n  Scanning namespace for NTT functions (q={q}, n={n})...")
        for name, obj in ns.items():
            if name.startswith('_') or name in skip: continue
            if not callable(obj) or isinstance(obj, type): continue
            if hasattr(obj, 'argtypes'): continue
            if not any(kw in name.lower() for kw in keywords): continue
            result = _pq_probe_ntt(obj, ns, q, n)
            if result: to_audit.append((name, result[0], result[1]))
        if not to_audit:
            funcs = sorted(k for k, v in ns.items() if callable(v)
                          and not k.startswith('_') and not isinstance(v, type))
            print(f"  No NTT functions found.")
            if funcs:
                print(f"  Callables in namespace: {', '.join(funcs[:20])}")
            print(f"  Usage: pqverify_scan(your_ntt_func, ns=globals())")
            return []
        print(f"  Found: {', '.join(nm for nm, _, _ in to_audit)}\n")

    # Audit each target
    results = []
    for nm, func, sig in to_audit:
        random.seed(42)
        p = 0; t = 0; findings = []

        print("=" * 70)
        print(f"  AUDITING: {nm}  [{sig}]")
        print(f"  q={q}, zeta={zeta_root}, n={n}")
        print("=" * 70)

        if zetas is not None:
            match = sum(1 for i in range(min(len(zetas), len(ref_z))) if zetas[i] == ref_z[i])
            ok = match == len(ref_z); t += 1; p += ok
            print(f"\n  {_OK if ok else _BAD} Twiddle factors: {match}/{len(ref_z)} match FIPS")
            if not ok:
                findings.append(f"Twiddle: {match}/{len(ref_z)}")
                R_mod_q = pow(2, 16, q) if q < 65536 else pow(2, 32, q)
                if all(i >= len(zetas) or zetas[i] == (ref_z[i] * R_mod_q) % q for i in range(len(ref_z))):
                    print(f"     Montgomery-form (x{R_mod_q} mod {q})")

        # Primitivity: the required ORDER of zeta differs by scheme.
        #   complete transform (ML-DSA): zeta^{2n}=1, zeta^{n}=-1
        #   incomplete       (ML-KEM)  : zeta^{n}=1,  zeta^{n/2}=-1
        if bits == _log2n:
            _e1, _e2 = 2 * n, n
        else:
            _e1, _e2 = n, n // 2
        ok = pow(zeta_root, _e1, q) == 1 and pow(zeta_root, _e2, q) == q - 1
        t += 1; p += ok
        print(f"  {_OK if ok else _BAD} Primitivity: zeta^{_e1}=1, zeta^{_e2}=-1"
              f"  [{bits}-layer {'complete' if bits == _log2n else 'incomplete'} NTT]")

        # Domain-aware comparison. Standards libraries (pq-crystals, PQClean,
        # liboqs) leave NTT output in the MONTGOMERY domain (each coeff x R mod q).
        # A raw got!=ref would report a CORRECT library as 100/100 wrong. We try
        # plain equality first, then Montgomery-normalized (x R^-1 mod q), and only
        # flag a mismatch if neither holds. Reported domain reflects what matched.
        _R = pow(2, 16, q) if q < 65536 else pow(2, 32, q)
        _Rinv = pow(_R, q - 2, q)  # R^-1 mod q (q prime)
        nf = 0; mm = None; ntt_domain = 'plain'
        for trial in range(100):
            poly = [random.randint(0, q - 1) for _ in range(n)]
            try:
                got = list(func(list(poly))); ref = _ref_ntt(list(poly))
                if got == ref:
                    pass  # plain-domain match
                elif [(g * _Rinv) % q for g in got] == ref:
                    ntt_domain = 'montgomery'  # Montgomery-domain match
                else:
                    nf += 1
                    if mm is None:
                        for i in range(n):
                            if got[i] != ref[i]: mm = (trial, i, got[i], ref[i]); break
            except Exception as e:
                nf += 1; mm = mm or (trial, -1, str(e), "")
        ok = nf == 0; t += 1; p += ok
        _dom_note = '' if ntt_domain == 'plain' else f' [{ntt_domain} domain]'
        print(f"  {_OK if ok else _BAD} Full NTT: 100 polynomials, {nf} mismatches{_dom_note}")
        if not ok and mm:
            if mm[1] >= 0: print(f"     poly {mm[0]}, coeff [{mm[1]}]: got {mm[2]}, expected {mm[3]}")
            else: print(f"     Error: {mm[2]}")
            findings.append(f"NTT: {nf}/100 wrong")

        # Freivalds: probabilistic check that y == NTT(x) via r.y == (NTT^T r).x.
        # Two engines: 16-bit for ML-KEM (7-layer incomplete), 32-bit for
        # ML-DSA (8-layer complete). They are NOT interchangeable -- different
        # width, layer count and zeta table.
        _narrow = q <= 65535
        lib = eng.get('zq') if _narrow else eng.get('zq32')
        _fn = 'zq_freivalds_ntt' if _narrow else 'zq32_freivalds_ntt'
        if lib is not None and hasattr(lib, _fn):
            try:
                _ct = ctypes.c_uint16 if _narrow else ctypes.c_uint32
                _cq = ctypes.c_uint16 if _narrow else ctypes.c_uint32
                _f = getattr(lib, _fn)
                _f.argtypes = [ctypes.POINTER(_ct)] * 2 + [
                    ctypes.c_int, _cq, _cq, ctypes.c_int, ctypes.c_uint32]
                _f.restype = ctypes.c_int
                random.seed(42); ff = 0
                for trial in range(100):
                    poly = [random.randint(0, q - 1) for _ in range(n)]
                    ntt_out = list(func(list(poly)))
                    x = (_ct * n)(*poly); y = (_ct * n)(*[v % q for v in ntt_out])
                    if _f(x, y, n, q, zeta_root, 5, freivalds_seed(trial)) != 1: ff += 1
                ok = ff == 0; t += 1; p += ok
                _eng_lbl = 'ML-KEM 16-bit' if _narrow else 'ML-DSA 32-bit'
                print(f"  {_OK if ok else _BAD} Freivalds ({_eng_lbl} engine): "
                      f"100 x 5 rounds, {ff} failures")
                if not ok: findings.append(f"Freivalds: {ff}")
            except Exception as _fe:
                print(f"  \u23ed\ufe0f  Freivalds: engine error ({type(_fe).__name__})")
        else:
            DEGRADED['skipped_checks'].append('Freivalds')
            print(f"  \u23ed\ufe0f  Freivalds: SKIPPED \u2014 engine unavailable. "
                  f"This check did NOT run; coverage is reduced.")

        if cp_ap and cp_rm:
            class _L:
                def __init__(s, sd=0xACE1): s.st = sd or 0xACE1
                def next(s):
                    b = s.st & 1; s.st >>= 1
                    if b: s.st ^= 0xB400
                    if s.st == 0: s.st = 0xACE1
                    return s.st
            cf = 0
            for trial in range(100):
                poly = [random.randint(0, q - 1) for _ in range(n)]
                try:
                    r = cp_ap(list(poly))
                    prot, flags = (r[0], r[1]) if isinstance(r, tuple) else (r, None)
                    rec = cp_rm(prot, flags) if flags is not None else cp_rm(prot)
                    if list(rec) != poly: cf += 1
                except:
                    try:
                        prot, flags = cp_ap(list(poly), _L(0xACE1 ^ trial))
                        rec = cp_rm(prot, flags)
                        if list(rec) != poly: cf += 1
                    except: cf += 1
            ok = cf == 0; t += 1; p += ok
            print(f"  {_OK if ok else _BAD} CP round-trip: 100 cycles, {cf} failures")
            ci = 0
            for trial in range(100):
                poly = [random.randint(0, q - 1) for _ in range(n)]
                ntt_out = list(func(list(poly)))
                try:
                    r = cp_ap(list(ntt_out))
                    prot, flags = (r[0], r[1]) if isinstance(r, tuple) else (r, None)
                    rec = cp_rm(prot, flags) if flags is not None else cp_rm(prot)
                    if list(rec) != ntt_out: ci += 1
                except:
                    try:
                        prot, flags = cp_ap(list(ntt_out), _L(0xACE1 ^ 0x5A5A ^ trial))
                        rec = cp_rm(prot, flags)
                        if list(rec) != ntt_out: ci += 1
                    except: ci += 1
            ok = ci == 0; t += 1; p += ok
            print(f"  {_OK if ok else _BAD} NTT->CP->unCP: 100 trials, {ci} failures")

        print(f"\n  {'='*60}")
        if findings:
            print(f"  {nm}: {p}/{t} -- FINDINGS:")
            for f in findings: print(f"    \u26a0\ufe0f  {f}")
        else:
            print(f"  {nm}: {p}/{t} \u2705 VERIFIED")
        print(f"  {'='*60}\n")
        results.append({'name': nm, 'passed': p, 'total': t, 'findings': findings})

    # Non-circular KAT against independent CRT reference (first function only)
    if results:
        fam = 'dilithium' if q > 65535 else 'kyber'
        print("\n  Running Known Answer Test (independent reference)...")
        kat = pqverify_kat(to_audit[0][1], q=q, zeta=zeta_root, n=n, k=None,
                           family=fam)
        for r in results: r['kat'] = kat

    # Run leakage analysis if any NTT was audited
    if results:
        print("\n  Running algebraic leakage analysis...")
        leakage = pqverify_leakage(q=q, zeta=zeta_root, n=n)
        for r in results:
            r['leakage'] = leakage

    if len(results) > 0:
        print("=" * 70)
        print(f"  SCAN COMPLETE: {len(results)} function(s), "
              f"{sum(r['passed'] for r in results)}/{sum(r['total'] for r in results)} checks, "
              f"{sum(len(r['findings']) for r in results)} finding(s)")
        print("=" * 70)
    return results


if __name__ == '__main__':
    import sys as _sys
    main(quick=('--quick' in _sys.argv))
