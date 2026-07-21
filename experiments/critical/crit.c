/* crit.c — the BB-cryptid CRITICAL-DRIFT experiment.
 *
 * Generalized Collatz map of modulus d:  f(dq+i) = a_i*q + b_i,  i = m mod d,
 * plus a "cryptid" functional: a parity counter c that integrates per-parity
 * weights (w_even on even values, w_odd on odd) and "halts" the first time it
 * crosses a boundary c <= -L.  This is the Antihydra genre (Antihydra = the 3/2
 * map with counter weights (+2,-1), boundary c<=-1).
 *
 * WHY GENERAL d.  The naive zero log-drift line prod_i a_i = d^d is
 * ARITHMETICALLY DEGENERATE: it forces some a_i to share a factor with d, so
 * the branch (a_i q + b_i) mod d is q-independent and the itinerary stops
 * mixing (e.g. d=2, (1,4): odd->odd forever, entropy 0).  Genuine MIXING needs
 * gcd(a_i,d)=1 for all i, which makes prod a_i coprime to d, so it can NEVER
 * equal d^d: exact criticality and mixing are mutually exclusive on this family.
 * The clean near-critical MIXING family is  f(dq+i) = a*q + i  with a = d-1
 * (subcritical, eff. drift ~ -1/d) or a = d+1 (supercritical, ~ +1/d),
 * gcd(a,d)=1: the log-value drift ln(a/d) -> 0 as d grows, giving a fine sweep
 * of effective drift across (but never touching) criticality.
 *
 * Per seed n in [1,N] we measure in one pass:
 *   (A) EXCURSION of the value: tau = first step orbit drops below n;
 *       h = floor(log2(max value / n)) over that excursion.
 *   (B) CRYPTID counter: tc = first step the parity counter reaches c <= -L.
 *   (C) parity block statistics (window K): block entropy, a proxy for the
 *       symbolic complexity a regular certificate must track.
 * Orbit runs until value overflow (>2^100, "escape"), both tau & tc resolved,
 * or STEPCAP steps.
 *
 * Build: cc -O2 -Wall -Wextra -o crit crit.c -lm            (macOS, sequential)
 *        gcc -O3 -march=native -fopenmp -o crit crit.c -lm  (Linux, parallel)
 * Usage: ./crit LABEL d a0 b0 a1 b1 ... a{d-1} b{d-1} wE wO L N STEPCAP OUTDIR
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef unsigned __int128 u128;
typedef int64_t   i64;
typedef uint64_t  u64;

#define MAXV (((u128)1) << 100)
#define DMAX 32
#define NBIN 64        /* log2 bins for tau/tc                */
#define HBIN 128       /* integer log2 bins for excursion height */
#define KWIN 12        /* parity block-entropy window          */
#define KMASK ((1u << KWIN) - 1)
#define NGRAM (1u << KWIN)

static int  D;
static u64  A[DMAX], B[DMAX];
static i64  WE, WO;        /* counter increments on even / odd values */
static i64  L;
static u64  STEPCAP;

typedef struct {
    u64 tau_bin[NBIN];
    u64 tc_bin[NBIN];
    u64 h_bin[HBIN];
    u64 n_drop, n_escape, n_cap;
    u64 n_hit, n_nohit;
    double sum_ltau, sum_h, sum_ltc;
    u64 odd_steps, tot_steps;
    u64 res[DMAX];              /* residue-visit counts (for effective drift) */
    u64 gram[NGRAM];
    u64 gram_tot;
} Acc;

static void acc_zero(Acc *a) { memset(a, 0, sizeof *a); }

__attribute__((unused))
static void acc_merge(Acc *d, const Acc *s) {
    for (int i=0;i<NBIN;i++){ d->tau_bin[i]+=s->tau_bin[i]; d->tc_bin[i]+=s->tc_bin[i]; }
    for (int i=0;i<HBIN;i++) d->h_bin[i]+=s->h_bin[i];
    d->n_drop+=s->n_drop; d->n_escape+=s->n_escape; d->n_cap+=s->n_cap;
    d->n_hit+=s->n_hit; d->n_nohit+=s->n_nohit;
    d->sum_ltau+=s->sum_ltau; d->sum_h+=s->sum_h; d->sum_ltc+=s->sum_ltc;
    d->odd_steps+=s->odd_steps; d->tot_steps+=s->tot_steps;
    for (int i=0;i<DMAX;i++) d->res[i]+=s->res[i];
    for (u64 i=0;i<NGRAM;i++) d->gram[i]+=s->gram[i];
    d->gram_tot+=s->gram_tot;
}

static inline int ilog2_u64(u64 v){ int b=0; while(v>>=1) b++; return b; }

static void run_seed(u64 n, Acc *a) {
    u128 x=n, exc=n;
    i64  c=0;
    u64  steps=0;
    int  dropped=0, hit=0;
    u64  tau=0, tc=0;
    unsigned gramwin=0; int gramfill=0;
    for (;;) {
        if (x > MAXV) { a->n_escape++; break; }
        int par = (int)(x & 1);
        int i = (D==2) ? par : (int)(x % (u128)D);
        u128 q = (D==2) ? (x>>1) : (x / (u128)D);
        /* parity stream / block entropy / residue visits */
        a->tot_steps++; if (par) a->odd_steps++;
        a->res[i]++;
        gramwin = ((gramwin<<1)|(unsigned)par)&KMASK;
        if (gramfill<KWIN) gramfill++; else { a->gram[gramwin]++; a->gram_tot++; }
        /* counter */
        c += (par ? WO : WE);
        if (!hit && c <= -L) { hit=1; tc=steps+1; }
        /* value */
        x = (u128)A[i]*q + (u128)B[i];
        steps++;
        if (x>exc) exc=x;
        if (!dropped && x < (u128)n) { dropped=1; tau=steps; }
        if (dropped && hit) break;
        if (steps>=STEPCAP) break;
    }
    if (dropped) {
        a->n_drop++;
        int b=ilog2_u64(tau); if(b>=NBIN)b=NBIN-1;
        a->tau_bin[b]++; a->sum_ltau+=log2((double)tau);
    } else if (x>MAXV) { /* escape counted */ }
    else a->n_cap++;
    {
        double hh=log2((double)(long double)exc/(double)n);
        if (hh<0) hh=0;
        int hb=(int)floor(hh); if(hb>=HBIN)hb=HBIN-1; if(hb<0)hb=0;
        a->h_bin[hb]++; a->sum_h+=hh;
    }
    if (hit) {
        a->n_hit++;
        int b=ilog2_u64(tc); if(b>=NBIN)b=NBIN-1;
        a->tc_bin[b]++; a->sum_ltc+=log2((double)tc);
    } else a->n_nohit++;
}

/* effective log-value drift under the MEASURED residue-visit frequencies would
 * need per-residue counts; we report the naive uniform-residue drift here and
 * measure the excursion statistics empirically. */
static double naive_drift(void) {
    double s=0;
    for (int i=0;i<D;i++){ u64 a=A[i]?A[i]:1; s+=log((double)a/(double)D); }
    return s/(double)D;
}

static void block_entropy(const Acc *a, double *hK_per_sym, double *cond) {
    double tot=(double)a->gram_tot;
    if (tot<1.0){ *hK_per_sym=0; *cond=0; return; }
    double HK=0.0;
    static double pref[1u<<(KWIN-1)];
    memset(pref,0,sizeof pref);
    for (u64 g=0;g<NGRAM;g++){
        if(!a->gram[g])continue;
        double p=(double)a->gram[g]/tot;
        HK-=p*log2(p);
        pref[g>>1]+=(double)a->gram[g];
    }
    double Hpref=0.0;
    for (u64 g=0; g<(1u<<(KWIN-1)); g++){
        if(pref[g]<=0)continue;
        double p=pref[g]/tot; Hpref-=p*log2(p);
    }
    *hK_per_sym=HK/(double)KWIN;
    *cond=HK-Hpref;
}

static u64 median_from_bins(const u64 *bin,int nb,u64 total){
    if(!total)return 0;
    u64 half=total/2, run=0;
    for(int b=0;b<nb;b++){ run+=bin[b]; if(run>=half) return (u64)1<<b; }
    return (u64)1<<(nb-1);
}

int main(int argc,char**argv){
    if (argc<4){ fprintf(stderr,"usage: %s LABEL d a0 b0 ... wE wO L N STEPCAP OUTDIR\n",argv[0]); return 1; }
    const char *label=argv[1];
    D=atoi(argv[2]);
    if (D<2||D>DMAX){ fprintf(stderr,"bad d\n"); return 1; }
    int ai=3;
    for (int i=0;i<D;i++){ A[i]=(u64)atoll(argv[ai++]); B[i]=(u64)atoll(argv[ai++]); }
    WE=(i64)atoll(argv[ai++]); WO=(i64)atoll(argv[ai++]);
    L =(i64)atoll(argv[ai++]);
    u64 N=(u64)atoll(argv[ai++]);
    STEPCAP=(u64)atoll(argv[ai++]);
    const char *outdir=argv[ai++];

    Acc total; acc_zero(&total);
#ifdef _OPENMP
#pragma omp parallel
    {
        Acc loc; acc_zero(&loc);
#pragma omp for schedule(dynamic,4096)
        for (u64 n=1;n<=N;n++) run_seed(n,&loc);
#pragma omp critical
        acc_merge(&total,&loc);
    }
#else
    for (u64 n=1;n<=N;n++) run_seed(n,&total);
#endif

    char path[512];
    snprintf(path,sizeof path,"%s/ccdf_%s.csv",outdir,label);
    FILE *f=fopen(path,"w");
    if(!f){ fprintf(stderr,"cannot open %s\n",path); return 2; }
    fprintf(f,"metric,bin_log2_lo,count,ccdf\n");
    { u64 t=total.n_drop,acc=0;
      for(int b=0;b<NBIN;b++){ if(!t)break; acc+=total.tau_bin[b];
        double cc=(double)(t-acc)/(double)t;
        if(total.tau_bin[b]||cc>0) fprintf(f,"tau,%d,%llu,%.8g\n",b,(unsigned long long)total.tau_bin[b],cc);} }
    { u64 t=total.n_hit,acc=0;
      for(int b=0;b<NBIN;b++){ if(!t)break; acc+=total.tc_bin[b];
        double cc=(double)(t-acc)/(double)t;
        if(total.tc_bin[b]||cc>0) fprintf(f,"tc,%d,%llu,%.8g\n",b,(unsigned long long)total.tc_bin[b],cc);} }
    { u64 t=0; for(int b=0;b<HBIN;b++)t+=total.h_bin[b];
      u64 acc=0;
      for(int b=0;b<HBIN;b++){ if(!t)break; acc+=total.h_bin[b];
        double cc=(double)(t-acc)/(double)t;
        if(total.h_bin[b]||cc>0) fprintf(f,"h,%d,%llu,%.8g\n",b,(unsigned long long)total.h_bin[b],cc);} }
    fclose(f);

    double vdrift=naive_drift();
    /* effective log-value drift under measured residue-visit frequencies */
    double edrift=0.0;
    { u64 rt=0; for(int i=0;i<D;i++) rt+=total.res[i];
      if (rt) for(int i=0;i<D;i++){ u64 a=A[i]?A[i]:1;
        edrift += ((double)total.res[i]/(double)rt)*log((double)a/(double)D); } }
    double cdrift=0.5*(double)(WE+WO);
    double p_odd=total.tot_steps?(double)total.odd_steps/(double)total.tot_steps:0.0;
    double cdrift_meas=(1.0-p_odd)*(double)WE + p_odd*(double)WO;
    double hK,cond; block_entropy(&total,&hK,&cond);
    double mean_ltau=total.n_drop?total.sum_ltau/(double)total.n_drop:0.0;
    double mean_h=total.sum_h/(double)N;
    double mean_ltc=total.n_hit?total.sum_ltc/(double)total.n_hit:0.0;
    u64 med_tau=median_from_bins(total.tau_bin,NBIN,total.n_drop);
    u64 med_tc =median_from_bins(total.tc_bin,NBIN,total.n_hit);

    printf("%s,%d,%.6f,%.6f,%.4f,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%.4f,%llu,%.4f,%.4f,%llu,%.5f,%.5f\n",
           label,D,vdrift,edrift,cdrift,cdrift_meas,p_odd,
           (double)total.n_drop/N,(double)total.n_escape/N,(double)total.n_cap/N,
           (double)total.n_hit/N,(double)total.n_nohit/N,
           mean_ltau,(unsigned long long)med_tau,mean_h,
           mean_ltc,(unsigned long long)med_tc,hK,cond);
    return 0;
}
