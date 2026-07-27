#define _POSIX_C_SOURCE 200809L
#include <gmp.h>
#include <omp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { DIM=25, MAX_WORDS=4096 };
typedef __int128 i128;
typedef struct { uint64_t r,b,p3o; unsigned S,O; } word_t;
typedef struct { mpz_t target,pow3; uint64_t Q; } state_t;
typedef struct { uint64_t q; int64_t delta[DIM]; } edge_t;
typedef struct { edge_t *edge; } row_t;
typedef struct { int64_t a[DIM]; uint64_t feasible,max_scale; uint64_t tested; } candidate_t;
static word_t words[MAX_WORDS]; static unsigned nw; static volatile sig_atomic_t stop_requested;
static void request_stop(int sig){(void)sig;stop_requested=1;}
static void fail(const char*s){fprintf(stderr,"carry_policy_cegis: %s\n",s);exit(2);}
static uint64_t rng(uint64_t*x){*x^=*x<<13;*x^=*x>>7;*x^=*x<<17;return *x;}
static uint64_t powu(uint64_t a,unsigned e){uint64_t x=1;while(e--){if(x>UINT64_MAX/a)fail("small power overflow");x*=a;}return x;}
static int crossing(unsigned S,unsigned O){i128 a=1,b=1;for(unsigned i=0;i<O;++i)a*=3;for(unsigned i=0;i<S;++i)b*=2;return a>b;}
static uint64_t invodd(uint64_t a){uint64_t x=a;for(int i=0;i<6;++i)x*=2-a*x;return x;}

static void build_words(unsigned bound){
    nw=0;
    for(unsigned source=1;source<=bound;++source){uint64_t x=source;unsigned S=0,O=0;int complete=0;
        while(1){if(x==2)break;if(x==1){if(crossing(S+1,O+1)){++S;++O;x=2;complete=1;}break;}unsigned odd=x&1U;++S;if(odd){++O;x=(3*x+1)/2;}else x/=2;if(crossing(S,O)){complete=1;break;}if(S>=62)fail("word exceeds 61 bits");}
        if(!complete)continue;uint64_t mask=((uint64_t)1<<S)-1,r=source&mask,p3=powu(3,O),constant=(x*((uint64_t)1<<S))-p3*source,b=(p3*r+constant)>>S;
        int seen=0;for(unsigned j=0;j<nw;++j)if(words[j].S==S&&words[j].r==r){seen=1;break;}if(!seen){if(nw==MAX_WORDS)fail("word table full");words[nw++]=(word_t){r,b,p3,S,O};}
    }
    for(unsigned i=0;i<nw;++i)for(unsigned j=i+1;j<nw;++j)if(words[j].r<words[i].r){word_t t=words[i];words[i]=words[j];words[j]=t;}
}
static void state_init(state_t*s){mpz_inits(s->target,s->pow3,NULL);s->Q=0;}
static void state_clear(state_t*s){mpz_clears(s->target,s->pow3,NULL);}
static void state_root(state_t*s){mpz_set_ui(s->target,0);mpz_set_ui(s->pow3,1);s->Q=0;}
static void state_set(state_t*d,const state_t*s){mpz_set(d->target,s->target);mpz_set(d->pow3,s->pow3);d->Q=s->Q;}
static uint64_t extend(const state_t*p,state_t*c,const word_t*w){
    uint64_t mod=(uint64_t)1<<w->S,mask=mod-1,t=mpz_fdiv_ui(p->target,mod),pm=mpz_fdiv_ui(p->pow3,mod),q=((w->r-t)*invodd(pm))&mask;
    mpz_mul_ui(c->target,p->pow3,q);mpz_add(c->target,c->target,p->target);mpz_sub_ui(c->target,c->target,w->r);if(!mpz_divisible_2exp_p(c->target,w->S))fail("nonintegral extension");mpz_fdiv_q_2exp(c->target,c->target,w->S);mpz_mul_ui(c->target,c->target,w->p3o);mpz_add_ui(c->target,c->target,w->b);mpz_mul_ui(c->pow3,p->pow3,w->p3o);c->Q=p->Q+w->O;return q;
}
static unsigned v2cap(const mpz_t x){if(mpz_sgn(x)==0)return 127;mp_bitcnt_t v=mpz_scan1(x,0);return v>127?127:(unsigned)v;}
static void features(const state_t*s,int64_t f[DIM]){
    if(mpz_cmp_ui(s->target,0)<=0)fail("features require positive boundary");mpz_t H,z,t;mpz_inits(H,z,t,NULL);mpz_add_ui(H,s->target,1);if(!mpz_divisible_ui_p(H,3))fail("boundary is not 2 mod 3");mpz_divexact_ui(H,H,3);mpz_set(z,H);uint64_t c=0;while(mpz_divisible_ui_p(z,3)){mpz_divexact_ui(z,z,3);++c;}if(c>s->Q)fail("negative D");uint64_t D=s->Q-c;
    f[0]=(int64_t)D;f[1]=(int64_t)c;f[2]=(int64_t)mpz_sizeinbase(z,2);mpz_sub_ui(t,z,1);f[3]=v2cap(t);mpz_add_ui(t,z,1);f[4]=v2cap(t);f[5]=v2cap(H);f[6]=(int64_t)(D*D);f[7]=(int64_t)(c*c);f[8]=(int64_t)(D*c);for(int i=9;i<DIM;++i)f[i]=0;f[9+(int)mpz_fdiv_ui(z,16)]=1;mpz_clears(H,z,t,NULL);
}
static unsigned choose_edge(const uint64_t*q,uint64_t*x){uint64_t r=rng(x);if(r%10<7){unsigned best=0;for(unsigned j=1;j<nw;++j)if(q[j]<q[best])best=j;return best;}return (unsigned)(rng(x)%nw);}
static row_t*build_corpus(unsigned walks,unsigned steps,uint64_t seed){
    uint64_t n=(uint64_t)walks*steps;row_t*rows=calloc((size_t)n,sizeof(*rows));if(!rows)fail("row allocation");edge_t*all=calloc((size_t)n*nw,sizeof(*all));if(!all)fail("edge allocation");for(uint64_t i=0;i<n;++i)rows[i].edge=&all[i*nw];
    state_t cur,child,next;state_init(&cur);state_init(&child);state_init(&next);uint64_t index=0,*qs=calloc(nw,sizeof(*qs));if(!qs)fail("q allocation");
    for(unsigned w=0;w<walks;++w){uint64_t x=seed^((uint64_t)(w+1)*UINT64_C(0x9e3779b97f4a7c15));if(!x)x=1;state_root(&cur);for(unsigned j=0;j<nw;++j)qs[j]=extend(&cur,&child,&words[j]);unsigned pick=choose_edge(qs,&x);extend(&cur,&next,&words[pick]);state_set(&cur,&next);
        for(unsigned d=0;d<steps;++d){int64_t pf[DIM];features(&cur,pf);for(unsigned j=0;j<nw;++j){uint64_t q=extend(&cur,&child,&words[j]);int64_t cf[DIM];features(&child,cf);rows[index].edge[j].q=q;for(int k=0;k<DIM;++k)rows[index].edge[j].delta[k]=pf[k]-cf[k];qs[j]=q;}pick=choose_edge(qs,&x);extend(&cur,&next,&words[pick]);state_set(&cur,&next);++index;}
    }
    free(qs);state_clear(&cur);state_clear(&child);state_clear(&next);return rows;
}
static int admissible(const int64_t*a,int strict){if(!strict)return 1;if(a[2]<0||a[3]<0||a[4]<0||a[5]<0||a[6]<=0||a[7]<=0)return 0;i128 lhs=(i128)4*a[6]*a[7],rhs=(i128)a[8]*a[8];return lhs>rhs;}
static void score(candidate_t*c,const row_t*rows,uint64_t nrows){c->feasible=0;c->max_scale=0;for(uint64_t i=0;i<nrows;++i){int ok=0;uint64_t need_best=UINT64_MAX;for(unsigned j=0;j<nw;++j){i128 delta=0;for(int k=0;k<DIM;++k)delta+=(i128)c->a[k]*rows[i].edge[j].delta[k];uint64_t q=rows[i].edge[j].q;if((q==0&&delta>=0)||(q>0&&delta>0)){uint64_t need=0;if(q){if(delta>(i128)UINT64_MAX)need=1;else{uint64_t d=(uint64_t)delta;need=q/d+(q%d!=0);}}if(need<need_best)need_best=need;ok=1;}}if(ok){++c->feasible;if(need_best>c->max_scale)c->max_scale=need_best;}}
}
static int better(const candidate_t*a,const candidate_t*b){return a->feasible>b->feasible||(a->feasible==b->feasible&&a->max_scale<b->max_scale);}
static void random_candidate(candidate_t*c,uint64_t*x,int strict){for(int k=0;k<DIM;++k)c->a[k]=(int64_t)(rng(x)%65)-32;if(strict){for(int k=2;k<=5;++k)c->a[k]=(int64_t)(rng(x)%33);do{c->a[6]=1+(int64_t)(rng(x)%16);c->a[7]=1+(int64_t)(rng(x)%16);c->a[8]=(int64_t)(rng(x)%33)-16;}while(!admissible(c->a,1));}c->feasible=0;c->max_scale=UINT64_MAX;}
static void mutate(candidate_t*c,uint64_t*x,int strict){int k=(int)(rng(x)%DIM);int64_t old=c->a[k],step=1+(int64_t)(rng(x)%5);c->a[k]+=(rng(x)&1)?step:-step;if(c->a[k]>64)c->a[k]=64;if(c->a[k]<-64)c->a[k]=-64;if(!admissible(c->a,strict))c->a[k]=old;}
static void print_candidate(FILE*f,const char*tag,const candidate_t*c,uint64_t held_feasible,uint64_t held_scale,uint64_t nrows,double seconds){fprintf(f,"%s\tseconds=%.6f\tevaluated=%llu\ttrain_feasible=%llu\ttrain_rows=%llu\ttrain_max_scale=%llu\theld_feasible=%llu\theld_rows=%llu\theld_max_scale=%llu\tcoeff=",tag,seconds,(unsigned long long)c->tested,(unsigned long long)c->feasible,(unsigned long long)nrows,(unsigned long long)c->max_scale,(unsigned long long)held_feasible,(unsigned long long)nrows,(unsigned long long)held_scale);for(int k=0;k<DIM;++k)fprintf(f,"%s%lld",k?",":"",(long long)c->a[k]);fputc('\n',f);}

int main(int argc,char**argv){if(argc!=9)fail("usage: WORD_BOUND WALKS STEPS STRICT SECONDS SEED OUTPUT.tsv LABEL");unsigned bound=(unsigned)strtoul(argv[1],0,10),walks=(unsigned)strtoul(argv[2],0,10),steps=(unsigned)strtoul(argv[3],0,10);int strict=atoi(argv[4]);double seconds=strtod(argv[5],0);uint64_t seed=strtoull(argv[6],0,10);if(!bound||!walks||!steps||(strict!=0&&strict!=1)||seconds<=0)fail("invalid arguments");if(signal(SIGUSR1,request_stop)==SIG_ERR)fail("signal handler");build_words(bound);uint64_t nrows=(uint64_t)walks*steps;row_t*train=build_corpus(walks,steps,seed),*held=build_corpus(walks,steps,seed^UINT64_C(0xd1b54a32d192ed03));int nt=omp_get_max_threads();candidate_t*best=calloc((size_t)nt,sizeof(*best));if(!best)fail("best allocation");for(int t=0;t<nt;++t){uint64_t x=seed^((uint64_t)(t+1)*UINT64_C(0x94d049bb133111eb));random_candidate(&best[t],&x,strict);score(&best[t],train,nrows);best[t].tested=1;}
    FILE*out=fopen(argv[7],"w");if(!out)fail("output open");setvbuf(out,NULL,_IOLBF,0);fprintf(out,"# exact finite carry-policy CEGIS word_bound=%u words=%u walks=%u steps=%u rows=%llu strict=%d seconds_cap=%.0f seed=%llu threads=%d dim=%d label=%s\n",bound,nw,walks,steps,(unsigned long long)nrows,strict,seconds,(unsigned long long)seed,nt,DIM,argv[8]);fprintf(out,"FEATURES\tD,c,bitlen_z,v2_z_minus_1_cap127,v2_z_plus_1_cap127,v2_H_cap127,D2,c2,Dc,z_mod16_lookup_0..15\n");for(unsigned j=0;j<nw;++j)fprintf(out,"WORD\tindex=%u\tr=%llu\tb=%llu\tS=%u\tO=%u\n",j,(unsigned long long)words[j].r,(unsigned long long)words[j].b,words[j].S,words[j].O);
    double started=omp_get_wtime(),last=started;candidate_t global=best[0];uint64_t heldf=0,helds=0;
    while(!stop_requested&&omp_get_wtime()-started<seconds){
#pragma omp parallel
        {int t=omp_get_thread_num();uint64_t x=seed^((uint64_t)(t+1)*UINT64_C(0x2545f4914f6cdd1d))^best[t].tested;for(int it=0;it<64;++it){candidate_t c=best[t];if((rng(&x)%10)<2)random_candidate(&c,&x,strict);else mutate(&c,&x,strict);score(&c,train,nrows);++best[t].tested;if(better(&c,&best[t])){uint64_t tested=best[t].tested;best[t]=c;best[t].tested=tested;}}}
        for(int t=0;t<nt;++t)if(better(&best[t],&global))global=best[t];double now=omp_get_wtime();if(now-last>=10.0){candidate_t hc=global;score(&hc,held,nrows);heldf=hc.feasible;helds=hc.max_scale;print_candidate(out,"CHECKPOINT",&global,heldf,helds,nrows,now-started);last=now;}
    }
    candidate_t hc=global;score(&hc,held,nrows);heldf=hc.feasible;helds=hc.max_scale;print_candidate(out,"BEST",&global,heldf,helds,nrows,omp_get_wtime()-started);fprintf(out,"RESULT\tstatus=%s\tfinite_sample_certificate=%s\tsymbolic_all_state_certificate=null\tcounterexample=null\n",stop_requested?"partial":"complete",global.feasible==nrows&&heldf==nrows?"yes":"no");fclose(out);free(train[0].edge);free(train);free(held[0].edge);free(held);free(best);return 0;}
