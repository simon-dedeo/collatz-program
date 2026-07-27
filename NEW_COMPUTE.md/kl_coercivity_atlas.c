#define _POSIX_C_SOURCE 200809L
#include <float.h>
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "npy.h"

enum { NB = 11, MAX_LEVEL = 32 };
static const double betas[NB] = {64,128,256,512,1024,2048,4096,8192,16384,32768,65536};

static void fail(const char *s) { fprintf(stderr,"kl_coercivity_atlas: %s\n",s); exit(2); }
static inline double min3(double a,double b,double c){return fmin(a,fmin(b,c));}
static inline double second3(double a,double b,double c){double lo=min3(a,b,c),hi=fmax(a,fmax(b,c));return a+b+c-lo-hi;}
static inline unsigned argmin3(double a,double b,double c){return a<=b&&a<=c?0U:(b<=c?1U:2U);}
static inline double smooth_excess(double a,double b,double c,double beta){
    double m=min3(a,b,c);
    if(!(m>0)||!isfinite(a)||!isfinite(b)||!isfinite(c))return NAN;
    double lm=log(m);
    double da=fmax(0.0,log(a)-lm),db=fmax(0.0,log(b)-lm),dc=fmax(0.0,log(c)-lm);
    double s=exp(-beta*da)+exp(-beta*db)+exp(-beta*dc);
    return m*expm1(-log(s/3.0)/beta);
}
static int power3_level(uint64_t n){int e=0;if(!n)return-1;while(n%3==0){n/=3;++e;}return n==1?e+1:-1;}
static inline uint64_t transport(uint64_t i,uint64_t n){return(4*i+2)%n;}
static inline uint64_t branch(uint64_t i,uint64_t n){uint64_t p=n/3;unsigned k=(unsigned)(i%3);return k==0?(4*(i/3))%p:(2*((i-2)/3)+1)%p;}

static void block_stats(FILE*out,unsigned depth,const char*kind,const double*reward,
                        uint64_t n,long double total,double*seq,double*prefix){
    uint64_t r=0,first=0,last=0,run=0,maxrun=0;
    for(uint64_t t=0;t<n;++t){
        double z=reward[r];seq[t]=z;
        if(z==0){++run;if(run>maxrun)maxrun=run;}else run=0;
        r=transport(r,n);
    }
    if(r!=0)fail("transport orbit does not close");
    while(first<n&&seq[first]==0)++first;
    while(last<n&&seq[n-1-last]==0)++last;
    if(first<n&&first+last>maxrun)maxrun=first+last;
    prefix[0]=0;
    for(uint64_t t=0;t<n;++t)prefix[t+1]=prefix[t]+seq[t];
    fprintf(out,"RUN\tdepth=%u\tkind=%s\tcycle=%llu\tmax_zero_run=%llu\n",depth,kind,
            (unsigned long long)n,(unsigned long long)maxrun);
    for(uint64_t L=1;;){
        double mn=DBL_MAX,mx=0,sq=0;unsigned long long zero=0,quarter=0,half=0,below=0;
        double expected=(double)(total*(long double)L/(long double)n);
        if(L==n){mn=mx=(double)total;sq=0;}
        else{
#pragma omp parallel for schedule(static) reduction(min:mn) reduction(max:mx) reduction(+:sq,zero,quarter,half,below)
            for(uint64_t t=0;t<n;++t){
                uint64_t e=t+L;double s=e<=n?prefix[e]-prefix[t]:prefix[n]-prefix[t]+prefix[e-n];
                if(s<mn)mn=s;
                if(s>mx)mx=s;
                if(s==0)++zero;
                if(expected>0){double q=s/expected,d=q-1;sq+=d*d;if(q<.25)++quarter;if(q<.5)++half;if(q<1)++below;}
            }
        }
        fprintf(out,"BLOCK\tdepth=%u\tkind=%s\tlength=%llu\tmin_over_mean=%.17g\tmax_over_mean=%.17g\tcv=%.17g\tzero_fraction=%.17g\tbelow_quarter=%.17g\tbelow_half=%.17g\tbelow_mean=%.17g\n",
                depth,kind,(unsigned long long)L,expected>0?mn/expected:0,expected>0?mx/expected:0,
                expected>0?sqrt(sq/(double)n):0,(double)zero/(double)n,(double)quarter/(double)n,
                (double)half/(double)n,(double)below/(double)n);
        if(L==n)break;
        if(L>n/3)L=n;else L*=3;
    }
}

static void analyze(FILE*out,unsigned depth,const double*x,const double*g,const double*gg,
                    uint64_t n,double lambda,double*hardv,double*frv,double*seq,double*prefix){
    uint64_t c=n/3,b=c/3;long double total=0,G=0;
#pragma omp parallel for reduction(+:total)
    for(uint64_t i=0;i<n;++i)total+=(long double)x[i];
#pragma omp parallel for reduction(+:G)
    for(uint64_t i=0;i<c;++i)G+=(long double)g[i];
    const double alpha=log(3.0)/log(2.0),tau=pow(lambda,-2),w2=pow(lambda,alpha-2),w8=pow(lambda,alpha-1);
    long double hard=0,fr=0,hb[NB]={0},ae[NB]={0},safe[NB]={0};
    unsigned long long edges=0,mismatch=0;
#pragma omp parallel for schedule(static) reduction(+:hard,fr,edges,mismatch) reduction(+:hb[:NB],ae[:NB],safe[:NB])
    for(uint64_t r=0;r<c;++r){
        hardv[r]=0;frv[r]=0;unsigned kind=(unsigned)(r%3);if(kind==1)continue;++edges;
        double w=kind==0?w2:w8;uint64_t tf=transport(r,c),bf=branch(r,c);unsigned sig[3]={9,9,9};
        for(unsigned d=0;d<3;++d){uint64_t rr=r+(uint64_t)d*c,ft=transport(rr,n),fb=branch(rr,n);sig[ft/c]=(unsigned)(fb/b);}
        double a[3],z[3],A[3],Z[3],xx[3],yy[3],sum[3];
        for(unsigned d=0;d<3;++d){a[d]=x[tf+(uint64_t)d*c];A[d]=a[d]-g[tf];z[d]=g[bf+(uint64_t)d*b];Z[d]=z[d]-gg[bf];xx[d]=tau*a[d];yy[d]=w*z[sig[d]];sum[d]=xx[d]+yy[d];}
        double h=DBL_MAX;for(unsigned d=0;d<3;++d)h=fmin(h,tau*A[d]+w*Z[sig[d]]);hardv[r]=h;hard+=h;
        unsigned ia=argmin3(A[0],A[1],A[2]),iz=argmin3(Z[0],Z[1],Z[2]);
        if(sig[ia]!=iz){double q=fmin(tau*second3(A[0],A[1],A[2]),w*second3(Z[0],Z[1],Z[2]));frv[r]=q;fr+=q;++mismatch;}
        for(unsigned q=0;q<NB;++q){
            double be=betas[q],ex=tau*smooth_excess(a[0],a[1],a[2],be),ey=w*smooth_excess(z[sig[0]],z[sig[1]],z[sig[2]],be),es=smooth_excess(sum[0],sum[1],sum[2],be);
            double delta=es-ex-ey;
            hb[q]+=h+delta;ae[q]+=fabs(delta);safe[q]+=ex+ey+es;
        }
    }
    long double eps=(total-3*G)/total,target=((long double)(w2+w8)*G/2)*eps*eps;
    fprintf(out,"STAGE\tdepth=%u\tlevel=%d\tstates=%llu\tepsilon=%.18Lg\tedges=%llu\tmismatch=%llu\thard=%.18Lg\tfr=%.18Lg\ttarget=%.18Lg\thard_ratio=%.18Lg\tfr_ratio=%.18Lg\n",
            depth,power3_level(n),(unsigned long long)n,eps,edges,mismatch,hard,fr,target,hard/target,fr/target);
    for(unsigned q=0;q<NB;++q)fprintf(out,"COLD\tdepth=%u\tbeta=%.0f\th=%.18Lg\tactual_abs_error=%.18Lg\trowwise_safe_error=%.18Lg\th_minus_safe_over_target=%.18Lg\th_minus_actual_abs_over_target=%.18Lg\n",
            depth,betas[q],hb[q],ae[q],safe[q],(hb[q]-safe[q])/target,(hb[q]-ae[q])/target);
    fflush(out);
    block_stats(out,depth,"hard",hardv,c,hard,seq,prefix);fflush(out);
    block_stats(out,depth,"frustration",frv,c,fr,seq,prefix);fflush(out);
}

int main(int argc,char**argv){
    if(argc!=5)fail("usage: VECTOR.npy LAMBDA MAX_PROJECTION OUTPUT.tsv");
    double lambda=strtod(argv[2],0);unsigned maxp=(unsigned)strtoul(argv[3],0,10);if(!(lambda>1&&lambda<2))fail("bad lambda");
    npy_view v;v.fd=-1;int rc=npy_open_1d(argv[1],&v);if(rc){fprintf(stderr,"NPY error %d\n",rc);return 2;}
    int level=power3_level(v.count);if(level<4||level>MAX_LEVEL)fail("unsupported level");uint64_t n0=v.count;
    double*x0=NULL;if(posix_memalign((void**)&x0,64,(size_t)n0*sizeof(double)))fail("input allocation");int bad=0;
#pragma omp parallel for schedule(static) reduction(|:bad)
    for(uint64_t i=0;i<n0;++i){x0[i]=npy_get(&v,i);if(!(x0[i]>0)||!isfinite(x0[i]))bad=1;}
    if(bad)fail("input is not finite and strictly positive");
    npy_close(&v);
    uint64_t lens[MAX_LEVEL]={0},off[MAX_LEVEL]={0},total_hier=0;lens[0]=n0;
    for(int d=1;d<level-1;++d){lens[d]=lens[d-1]/3;off[d]=total_hier;total_hier+=lens[d];}
    double*hier=NULL;if(posix_memalign((void**)&hier,64,(size_t)total_hier*sizeof(double)))fail("hierarchy allocation");
    double*prev=x0;
    for(int d=1;d<level-1;++d){double*dst=hier+off[d];uint64_t len=lens[d];
#pragma omp parallel for schedule(static)
        for(uint64_t i=0;i<len;++i)dst[i]=min3(prev[i],prev[i+len],prev[i+2*len]);prev=dst;
    }
    uint64_t maxc=n0/3;double *hardv=NULL,*frv=NULL,*seq=NULL,*prefix=NULL;
    if(posix_memalign((void**)&hardv,64,(size_t)maxc*sizeof(double))||posix_memalign((void**)&frv,64,(size_t)maxc*sizeof(double))||posix_memalign((void**)&seq,64,(size_t)maxc*sizeof(double))||posix_memalign((void**)&prefix,64,(size_t)(maxc+1)*sizeof(double)))fail("work allocation");
    FILE*out=fopen(argv[4],"w");if(!out)fail("cannot open output");setvbuf(out,NULL,_IOLBF,0);
    fprintf(out,"# multiscale floating coercivity atlas file=%s k=%d states=%llu lambda=%.17g max_projection=%u threads=%d\n",argv[1],level,(unsigned long long)n0,lambda,maxp,omp_get_max_threads());
    unsigned last=(unsigned)(level-4);if(maxp<last)last=maxp;
    for(unsigned d=0;d<=last;++d){const double*x=d==0?x0:hier+off[d];const double*g=hier+off[d+1];const double*gg=hier+off[d+2];analyze(out,d,x,g,gg,lens[d],lambda,hardv,frv,seq,prefix);}
    fclose(out);free(prefix);free(seq);free(frv);free(hardv);free(hier);free(x0);return 0;
}
