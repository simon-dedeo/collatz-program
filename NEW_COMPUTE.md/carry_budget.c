#define _POSIX_C_SOURCE 200809L
#include <gmp.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __uint128_t u128;
typedef struct { uint64_t r,b,p3o; unsigned S,O; } word_t;
typedef struct { mpz_t rho,target,pow2,pow3; uint64_t carry; } state_t;
typedef struct { u128 *count; uint64_t *mincarry; state_t *stack; } context_t;
static word_t words[4096]; static unsigned nw,depth_cap; static uint64_t budget;

static void fail(const char*s){fprintf(stderr,"carry_budget: %s\n",s);exit(2);}
static void print128(FILE*f,u128 x){char b[64];unsigned n=0;do{b[n++]=(char)('0'+x%10);x/=10;}while(x);while(n)fputc(b[--n],f);}
static uint64_t powu(uint64_t a,unsigned e){uint64_t x=1;while(e--){if(x>UINT64_MAX/a)fail("small power overflow");x*=a;}return x;}
static int crossing(unsigned S,unsigned O){ __uint128_t a=1,b=1;for(unsigned i=0;i<O;++i)a*=3;for(unsigned i=0;i<S;++i)b*=2;return a>b; }
static uint64_t invodd(uint64_t a){uint64_t x=a;for(int i=0;i<6;++i)x*=2-a*x;return x;}

static void build_words(unsigned bound){
    for(unsigned source=1;source<=bound;++source){uint64_t x=source,bits=0;unsigned S=0,O=0;int complete=0;while(1){if(x==2)break;if(x==1){if(crossing(S+1,O+1)){bits|=(uint64_t)1<<S;++S;++O;x=2;complete=1;}break;}unsigned odd=x&1U;bits|=(uint64_t)odd<<S;++S;if(odd){++O;x=(3*x+1)/2;}else x/=2;if(crossing(S,O)){complete=1;break;}if(S>=62)fail("word exceeds 61 bits");}if(!complete)continue;
        uint64_t mask=((uint64_t)1<<S)-1,r=source&mask,p3=powu(3,O),constant=(x*((uint64_t)1<<S))-p3*source,b=(p3*r+constant)>>S;
        int seen=0;for(unsigned j=0;j<nw;++j)if(words[j].S==S&&words[j].r==r){seen=1;break;}if(!seen){if(nw==4096)fail("word table full");words[nw++]=(word_t){r,b,p3,S,O};}
    }
    for(unsigned i=0;i<nw;++i)for(unsigned j=i+1;j<nw;++j)if(words[j].r<words[i].r){word_t t=words[i];words[i]=words[j];words[j]=t;}
}
static void init_state(state_t*s){mpz_inits(s->rho,s->target,s->pow2,s->pow3,NULL);s->carry=0;}
static void clear_state(state_t*s){mpz_clears(s->rho,s->target,s->pow2,s->pow3,NULL);}
static void root(state_t*s){mpz_set_ui(s->rho,0);mpz_set_ui(s->target,0);mpz_set_ui(s->pow2,1);mpz_set_ui(s->pow3,1);s->carry=0;}
static int extend(const state_t*p,state_t*c,const word_t*w){
    uint64_t mod=(uint64_t)1<<w->S,mask=mod-1,t=mpz_fdiv_ui(p->target,mod),pm=mpz_fdiv_ui(p->pow3,mod);
    uint64_t q=((w->r-t)*invodd(pm))&mask;if(q>budget-p->carry)return 0;
    mpz_mul_ui(c->target,p->pow3,q);mpz_add(c->target,c->target,p->target);mpz_sub_ui(c->target,c->target,w->r);if(!mpz_divisible_2exp_p(c->target,w->S))fail("nonintegral parameter");mpz_fdiv_q_2exp(c->target,c->target,w->S);mpz_mul_ui(c->target,c->target,w->p3o);mpz_add_ui(c->target,c->target,w->b);
    mpz_mul_ui(c->rho,p->pow2,q);mpz_add(c->rho,c->rho,p->rho);mpz_mul_2exp(c->pow2,p->pow2,w->S);mpz_mul_ui(c->pow3,p->pow3,w->p3o);c->carry=p->carry+q;return 1;
}
static void record(context_t*ctx,unsigned d,const state_t*s){ctx->count[d]++;if(s->carry<ctx->mincarry[d])ctx->mincarry[d]=s->carry;}
static void dfs(context_t*ctx,unsigned d){if(d>=depth_cap)return;state_t*p=&ctx->stack[d],*c=&ctx->stack[d+1];for(unsigned j=0;j<nw;++j)if(extend(p,c,&words[j])){record(ctx,d+1,c);dfs(ctx,d+1);}}
static uint64_t ipow_cap(uint64_t a,unsigned e){uint64_t x=1;while(e--){if(x>1000000/a)return 1000001;x*=a;}return x;}
static int decode_prefix(uint64_t code,unsigned pd,context_t*ctx,int do_record){root(&ctx->stack[0]);for(unsigned d=0;d<pd;++d){unsigned j=(unsigned)(code%nw);code/=nw;if(!extend(&ctx->stack[d],&ctx->stack[d+1],&words[j]))return 0;if(do_record)record(ctx,d+1,&ctx->stack[d+1]);}return 1;}

int main(int argc,char**argv){if(argc!=5)fail("usage: SOURCE_RESIDUE_BOUND CARRY_BUDGET DEPTH_CAP OUTPUT.tsv");unsigned bound=(unsigned)strtoul(argv[1],0,10);budget=strtoull(argv[2],0,10);depth_cap=(unsigned)strtoul(argv[3],0,10);if(!bound||!depth_cap)fail("invalid bounds");build_words(bound);if(!nw)fail("empty code");
    unsigned pd=1;while(ipow_cap(nw,pd)<100000&&pd<depth_cap)++pd;uint64_t prefixes=ipow_cap(nw,pd);if(prefixes>1000000)fail("prefix fanout too large");int nt=omp_get_max_threads();context_t*ctx=calloc((size_t)nt,sizeof(*ctx));if(!ctx)fail("allocation");for(int t=0;t<nt;++t){ctx[t].count=calloc(depth_cap+1,sizeof(u128));ctx[t].mincarry=malloc((depth_cap+1)*sizeof(uint64_t));ctx[t].stack=malloc((depth_cap+1)*sizeof(state_t));if(!ctx[t].count||!ctx[t].mincarry||!ctx[t].stack)fail("allocation");for(unsigned d=0;d<=depth_cap;++d){ctx[t].mincarry[d]=UINT64_MAX;init_state(&ctx[t].stack[d]);}}
    double start=omp_get_wtime();context_t early={calloc(depth_cap+1,sizeof(u128)),malloc((depth_cap+1)*sizeof(uint64_t)),malloc((depth_cap+1)*sizeof(state_t))};for(unsigned d=0;d<=depth_cap;++d){early.mincarry[d]=UINT64_MAX;init_state(&early.stack[d]);}early.count[0]=1;early.mincarry[0]=0;for(unsigned d=1;d<pd;++d){uint64_t m=ipow_cap(nw,d);for(uint64_t code=0;code<m;++code)if(decode_prefix(code,d,&early,0))record(&early,d,&early.stack[d]);}
#pragma omp parallel for schedule(dynamic,1)
    for(uint64_t code=0;code<prefixes;++code){context_t*c=&ctx[omp_get_thread_num()];if(decode_prefix(code,pd,c,0)){record(c,pd,&c->stack[pd]);dfs(c,pd);}}
    FILE*out=fopen(argv[4],"w");if(!out)fail("cannot open output");fprintf(out,"# exact finite-subcode carry DP source_bound=%u words=%u budget=%llu depth_cap=%u prefix_depth=%u prefixes=%llu threads=%d seconds=%.6f\n",bound,nw,(unsigned long long)budget,depth_cap,pd,(unsigned long long)prefixes,nt,omp_get_wtime()-start);for(unsigned j=0;j<nw;++j)fprintf(out,"WORD\t%u\tS=%u\tO=%u\tr=%llu\tb=%llu\n",j,words[j].S,words[j].O,(unsigned long long)words[j].r,(unsigned long long)words[j].b);
    unsigned last=0;for(unsigned d=0;d<=depth_cap;++d){u128 count=early.count[d];uint64_t mc=early.mincarry[d];for(int t=0;t<nt;++t){count+=ctx[t].count[d];if(ctx[t].mincarry[d]<mc)mc=ctx[t].mincarry[d];}if(count)last=d;fprintf(out,"DEPTH\t%u\t",d);print128(out,count);fprintf(out,"\t%s",mc==UINT64_MAX?"null":"");if(mc!=UINT64_MAX)fprintf(out,"%llu",(unsigned long long)mc);fputc('\n',out);}fprintf(out,"RESULT\tdeepest_nonempty=%u\tfirst_empty=%u\tstatus=%s\tcounterexample=null\n",last,last<depth_cap?last+1:0,last<depth_cap?"exhausted":"depth_cap");fclose(out);
    for(int t=0;t<nt;++t){for(unsigned d=0;d<=depth_cap;++d)clear_state(&ctx[t].stack[d]);free(ctx[t].stack);free(ctx[t].count);free(ctx[t].mincarry);}for(unsigned d=0;d<=depth_cap;++d)clear_state(&early.stack[d]);free(early.stack);free(early.count);free(early.mincarry);free(ctx);return 0;}
