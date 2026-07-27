#define _POSIX_C_SOURCE 200809L
#include <float.h>
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "npy.h"

static void fail(const char *s) { fprintf(stderr, "kl_frustration_scan: %s\n", s); exit(2); }
static inline double min3(double a, double b, double c) { return fmin(a, fmin(b, c)); }
static inline double second3(double a, double b, double c) {
    double lo = min3(a,b,c), hi = fmax(a,fmax(b,c)); return a + b + c - lo - hi;
}
static inline unsigned argmin3(double a, double b, double c) { return a <= b && a <= c ? 0U : (b <= c ? 1U : 2U); }
static inline double pm(double a, double b, double c, double beta) {
    double m = min3(a,b,c);
    return m * exp(-log((pow(m/a,beta)+pow(m/b,beta)+pow(m/c,beta))/3.0)/beta);
}
static int power3_level(uint64_t n) {
    int e = 0; if (!n) return -1;
    while (n % 3 == 0) { n /= 3; ++e; }
    return n == 1 ? e + 1 : -1;
}
static inline uint64_t transport(uint64_t i, uint64_t n) { return (4*i+2)%n; }
static inline uint64_t branch(uint64_t i, uint64_t n) {
    uint64_t p=n/3; unsigned k=(unsigned)(i%3);
    return k==0 ? (4*(i/3))%p : (2*((i-2)/3)+1)%p;
}

int main(int argc, char **argv) {
    if (argc != 4) fail("usage: VECTOR.npy LAMBDA OUTPUT.tsv");
    double lambda=strtod(argv[2],NULL); if (!(lambda>1 && lambda<2)) fail("lambda must be in (1,2)");
    npy_view v; v.fd=-1; int rc=npy_open_1d(argv[1],&v); if(rc) { fprintf(stderr,"NPY error %d\n",rc); return 2; }
    int level=power3_level(v.count); if(level<4) fail("vector length is not 3^(k-1), k>=4");
    uint64_t n=v.count,c=n/3,b=c/3;
    double *g=NULL,*gg=NULL;
    if(posix_memalign((void**)&g,64,(size_t)c*sizeof(double)) || posix_memalign((void**)&gg,64,(size_t)b*sizeof(double))) fail("allocation failed");
    int bad=0;
#pragma omp parallel for schedule(static) reduction(|:bad)
    for(uint64_t i=0;i<c;++i){ double a=npy_get(&v,i),d=npy_get(&v,i+c),e=npy_get(&v,i+2*c); if(!(a>0&&d>0&&e>0)) bad=1; g[i]=min3(a,d,e); }
    if(bad) fail("input is not finite and positive");
#pragma omp parallel for schedule(static)
    for(uint64_t i=0;i<b;++i) gg[i]=min3(g[i],g[i+b],g[i+2*b]);
    long double total=0,G=0;
#pragma omp parallel for reduction(+:total)
    for(uint64_t i=0;i<n;++i) total+=(long double)npy_get(&v,i);
#pragma omp parallel for reduction(+:G)
    for(uint64_t i=0;i<c;++i) G+=(long double)g[i];
    const double alpha=log(3.0)/log(2.0),tau=pow(lambda,-2),w2=pow(lambda,alpha-2),w8=pow(lambda,alpha-1);
    const double betas[]={8,16,32,64,128,256}; enum{NB=6};
    long double local=0,fr=0,curv[NB]={0},err[NB]={0}; unsigned long long edges=0,mismatch=0;
#pragma omp parallel for schedule(static) reduction(+:local,fr,edges,mismatch) reduction(+:curv[:NB],err[:NB])
    for(uint64_t r=0;r<c;++r){
        unsigned kind=(unsigned)(r%3); if(kind==1) continue; ++edges;
        double w=kind==0?w2:w8;
        uint64_t tf=transport(r,c), bf=branch(r,c);
        unsigned sig[3]={9,9,9};
        for(unsigned d=0;d<3;++d){ uint64_t rr=r+(uint64_t)d*c; uint64_t ft=transport(rr,n),fb=branch(rr,n); sig[ft/c]=(unsigned)(fb/b); }
        double A[3],Z[3],aa[3],zz[3];
        for(unsigned d=0;d<3;++d){ aa[d]=npy_get(&v,tf+(uint64_t)d*c); A[d]=aa[d]-g[tf]; zz[d]=g[bf+(uint64_t)d*b]; Z[d]=zz[d]-gg[bf]; }
        unsigned ia=argmin3(A[0],A[1],A[2]),iz=argmin3(Z[0],Z[1],Z[2]);
        double h=DBL_MAX; for(unsigned d=0;d<3;++d) h=fmin(h,tau*A[d]+w*Z[sig[d]]); local+=h;
        if(sig[ia]!=iz){ ++mismatch; fr+=fmin(tau*second3(A[0],A[1],A[2]),w*second3(Z[0],Z[1],Z[2])); }
        double xa[3], yz[3], sum[3]; for(unsigned d=0;d<3;++d){ xa[d]=tau*aa[d]; yz[d]=w*zz[sig[d]]; sum[d]=xa[d]+yz[d]; }
        for(unsigned q=0;q<NB;++q){ double be=betas[q]; curv[q]+=pm(sum[0],sum[1],sum[2],be)-pm(xa[0],xa[1],xa[2],be)-pm(yz[0],yz[1],yz[2],be); err[q]+=(exp(log(3.0)/be)-1.0)*min3(sum[0],sum[1],sum[2]); }
    }
    long double eps=(total-3*G)/total, target=((long double)(w2+w8)*G/2)*eps*eps;
    FILE*out=fopen(argv[3],"a"); if(!out) fail("cannot open output");
    fprintf(out,"# file=%s kind=%d k=%d states=%llu lambda=%.17g threads=%d\n",argv[1],(int)v.kind,level,(unsigned long long)n,lambda,omp_get_max_threads());
    fprintf(out,"SUMMARY\teps=%.18Lg\tedges=%llu\tmismatch=%llu\thard=%.18Lg\tfr=%.18Lg\ttarget=%.18Lg\thard_ratio=%.18Lg\tfr_ratio=%.18Lg\n",eps,edges,mismatch,local,fr,target,local/target,fr/target);
    for(unsigned q=0;q<NB;++q) fprintf(out,"CURVATURE\tbeta=%.0f\th=%.18Lg\terror=%.18Lg\tnet_over_target=%.18Lg\thard_delta=%.18Lg\n",betas[q],curv[q],err[q],(curv[q]-err[q])/target,curv[q]-local);
    double *profile=g; uint64_t len=c; long double fine_total=total;
    for(int depth=1;len>=1;++depth){ long double s=0;
#pragma omp parallel for reduction(+:s)
        for(uint64_t i=0;i<len;++i) s+=(long double)profile[i];
        long double e=(fine_total-3*s)/fine_total; fprintf(out,"PROFILE\tdepth=%d\tcount=%llu\ttotal=%.18Lg\tepsilon=%.18Lg\n",depth,(unsigned long long)len,s,e);
        if(len<3) break;
        fine_total=s;
        uint64_t next=len/3;
#pragma omp parallel for schedule(static)
        for(uint64_t i=0;i<next;++i) profile[i]=min3(profile[i],profile[i+next],profile[i+2*next]); len=next;
    }
    fclose(out); free(g); free(gg); npy_close(&v); return 0;
}
