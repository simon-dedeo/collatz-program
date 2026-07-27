#define _POSIX_C_SOURCE 200809L
#include <gmp.h>
#include <omp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

enum { MAX_DEPTH=8, SCRATCH=12 };
typedef struct { mpz_t ib,is,ob,os; unsigned m,h,next; } edge_t;
typedef struct { mpz_t ib,is,ob,os; } relation_t;
typedef struct {
    unsigned long long paths,failed,stable,decreased,nonoutward;
    int have_root,have_delta; mpz_t min_root,min_delta; uint64_t root_code,delta_code;
} stat_t;
typedef struct { relation_t stack[MAX_DEPTH+1]; mpz_t z[SCRATCH]; stat_t stat[MAX_DEPTH+1]; } context_t;
static unsigned MB,HB,DEPTH; static edge_t *edges;
static volatile sig_atomic_t stop_requested=0;
static void request_stop(int signal_number){(void)signal_number;stop_requested=1;}

static void fail(const char*s){fprintf(stderr,"bouncer_atlas: %s\n",s);exit(2);}
static void relation_init(relation_t*r){mpz_inits(r->ib,r->is,r->ob,r->os,NULL);}
static void relation_clear(relation_t*r){mpz_clears(r->ib,r->is,r->ob,r->os,NULL);}
static void relation_edge(relation_t*r,const edge_t*e){mpz_set(r->ib,e->ib);mpz_set(r->is,e->is);mpz_set(r->ob,e->ob);mpz_set(r->os,e->os);}
static void stat_init(stat_t*s){s->paths=s->failed=s->stable=s->decreased=s->nonoutward=0;s->have_root=s->have_delta=0;mpz_inits(s->min_root,s->min_delta,NULL);}
static void stat_clear(stat_t*s){mpz_clears(s->min_root,s->min_delta,NULL);}
static edge_t*edge(unsigned m,unsigned h,unsigned n){return &edges[((size_t)(m-1)*HB+(h-1))*MB+(n-1)];}

static int crt(mpz_t out,mpz_t mod,const mpz_t a,const mpz_t am,const mpz_t b,const mpz_t bm){
    mpz_t g,d,aa,bb,k,inv;mpz_inits(g,d,aa,bb,k,inv,NULL);mpz_gcd(g,am,bm);mpz_sub(d,b,a);
    if(!mpz_divisible_p(d,g)){mpz_clears(g,d,aa,bb,k,inv,NULL);return 0;}
    mpz_divexact(aa,am,g);mpz_divexact(bb,bm,g);mpz_divexact(d,d,g);
    if(mpz_cmp_ui(bb,1)==0)mpz_set_ui(k,0);else{if(!mpz_invert(inv,aa,bb))fail("CRT inverse");mpz_mul(k,d,inv);mpz_mod(k,k,bb);}
    mpz_mul(out,am,k);mpz_add(out,out,a);mpz_mul(mod,am,bb);mpz_mod(out,out,mod);mpz_clears(g,d,aa,bb,k,inv,NULL);return 1;
}

static void make_edge(edge_t*e,unsigned m,unsigned h,unsigned next,const mpz_t A,const mpz_t B,const mpz_t C,const mpz_t D,const mpz_t F,const mpz_t M){
    e->m=m;e->h=h;e->next=next;mpz_inits(e->ib,e->is,e->ob,e->os,NULL);
    mpz_t Ah,Bh,Cm,Dm,r1,a1,r2,a2,qodd,mododd,p2,r3,q,qstep,t,u,inv;
    mpz_inits(Ah,Bh,Cm,Dm,r1,a1,r2,a2,qodd,mododd,p2,r3,q,qstep,t,u,inv,NULL);
    mpz_pow_ui(Ah,A,h);mpz_pow_ui(Bh,B,h);mpz_pow_ui(Cm,C,m);mpz_pow_ui(Dm,D,m);
    mpz_mul(r1,F,Cm);if(!mpz_invert(inv,Bh,r1))fail("B inverse mod FC^m");mpz_neg(a1,inv);mpz_mod(a1,a1,r1);
    /* Division by C^m is not invertible modulo M because both contain
       powers of three.  Enforce the pre-division congruence modulo C^m M. */
    mpz_mul(r2,Cm,M);if(!mpz_invert(inv,Dm,r2))fail("D inverse mod CM");mpz_mul(a2,Cm,inv);mpz_sub_ui(a2,a2,1);
    if(!mpz_invert(inv,Bh,r2))fail("B inverse mod CM");mpz_mul(a2,a2,inv);mpz_mod(a2,a2,r2);
    if(!crt(qodd,mododd,a1,r1,a2,r2))fail("odd-register CRT incompatible");
    mpz_set_ui(p2,1);mpz_mul_2exp(p2,p2,23U*next+1U);mpz_set_ui(r3,1);mpz_mul_2exp(r3,r3,23U*next);mpz_sub_ui(r3,r3,1);if(!mpz_invert(inv,Ah,p2))fail("A inverse mod power of two");mpz_mul(r3,r3,inv);mpz_mod(r3,r3,p2);
    if(!crt(q,qstep,qodd,mododd,r3,p2))fail("dyadic CRT incompatible");
    mpz_mul(t,Bh,q);mpz_add_ui(t,t,1);if(!mpz_divisible_p(t,Cm))fail("edge input quotient nonintegral");mpz_divexact(u,t,Cm);mpz_mul(e->ib,Dm,u);mpz_sub_ui(e->ib,e->ib,1);
    mpz_mul(t,Bh,qstep);if(!mpz_divisible_p(t,Cm))fail("edge stride nonintegral");mpz_divexact(t,t,Cm);mpz_mul(e->is,Dm,t);
    mpz_mul(e->ob,Ah,q);mpz_mul(e->os,Ah,qstep);
    /* Independently replay two members of the affine family.  This checks
       the CRT construction against the literal bouncer formula rather than
       merely rechecking the congruences from which it was derived. */
    for(unsigned long r=0;r<2;++r){
        mpz_mul_ui(a1,e->is,r);mpz_add(a1,a1,e->ib);if(mpz_sgn(a1)<=0||mpz_even_p(a1))fail("edge input is not positive odd");
        if(!mpz_divisible_p(a1,M))fail("edge input lost M register");mpz_add_ui(a2,a1,1);if(!mpz_divisible_p(a2,F))fail("edge input lost F register");
        if(mpz_scan1(a2,0)!=23U*m)fail("edge input valuation");
        mpz_mul(r1,Cm,a2);mpz_sub(r1,r1,Dm);if(mpz_sgn(r1)<=0||mpz_scan1(r1,0)!=23U*m+154U*h)fail("edge collision valuation");
        mpz_tdiv_q_2exp(r1,r1,23U*m+154U*h);mpz_mul(r1,r1,Ah);
        mpz_mul_ui(r2,e->os,r);mpz_add(r2,r2,e->ob);if(mpz_cmp(r1,r2))fail("edge literal replay mismatch");
        if(!mpz_divisible_p(r2,M))fail("edge output lost M register");mpz_add_ui(r3,r2,1);if(!mpz_divisible_p(r3,F))fail("edge output lost F register");
        if(mpz_scan1(r3,0)!=23U*next)fail("edge output valuation");
    }
    mpz_clears(Ah,Bh,Cm,Dm,r1,a1,r2,a2,qodd,mododd,p2,r3,q,qstep,t,u,inv,NULL);
}

static int compose(const relation_t*a,const edge_t*b,relation_t*out,context_t*c){
    mpz_ptr d=c->z[0],g=c->z[1],aa=c->z[2],bb=c->z[3],dg=c->z[4],inv=c->z[5],t=c->z[6],u=c->z[7],k=c->z[8],tmp=c->z[9],left=c->z[10],right=c->z[11];
    mpz_sub(d,b->ib,a->ob);mpz_gcd(g,a->os,b->is);if(!mpz_divisible_p(d,g))return 0;
    mpz_divexact(aa,a->os,g);mpz_divexact(bb,b->is,g);mpz_divexact(dg,d,g);
    if(mpz_cmp_ui(bb,1)==0)mpz_set_ui(t,0);else{if(!mpz_invert(inv,aa,bb))fail("link inverse");mpz_mul(t,dg,inv);mpz_mod(t,t,bb);}
    mpz_mul(tmp,a->os,t);mpz_sub(tmp,tmp,d);mpz_divexact(u,tmp,b->is);
    if(mpz_sgn(u)<0){mpz_neg(tmp,u);mpz_add(tmp,tmp,aa);mpz_sub_ui(tmp,tmp,1);mpz_fdiv_q(k,tmp,aa);mpz_addmul(t,bb,k);mpz_addmul(u,aa,k);}
    mpz_mul(out->ib,a->is,t);mpz_add(out->ib,out->ib,a->ib);mpz_mul(out->is,a->is,bb);
    mpz_mul(out->ob,b->os,u);mpz_add(out->ob,out->ob,b->ob);mpz_mul(out->os,b->os,aa);
    mpz_mul(left,a->os,t);mpz_add(left,left,a->ob);mpz_mul(right,b->is,u);mpz_add(right,right,b->ib);if(mpz_cmp(left,right))fail("link equality");return 1;
}

static void record(stat_t*s,const relation_t*parent,const relation_t*child,uint64_t code,mpz_t tmp){
    ++s->paths;if(mpz_cmp(child->ob,child->ib)<=0)++s->nonoutward;mpz_sub(tmp,child->ib,parent->ib);int sg=mpz_sgn(tmp);if(!sg)++s->stable;if(sg<0){++s->decreased;mpz_neg(tmp,tmp);}
    int root_cmp=s->have_root?mpz_cmp(child->ib,s->min_root):-1,delta_cmp=s->have_delta?mpz_cmp(tmp,s->min_delta):-1;
    if(!s->have_root||root_cmp<0||(root_cmp==0&&code<s->root_code)){s->have_root=1;mpz_set(s->min_root,child->ib);s->root_code=code;}
    if(!s->have_delta||delta_cmp<0||(delta_cmp==0&&code<s->delta_code)){s->have_delta=1;mpz_set(s->min_delta,tmp);s->delta_code=code;}
}
static void merge_stat(stat_t*d,const stat_t*s){d->paths+=s->paths;d->failed+=s->failed;d->stable+=s->stable;d->decreased+=s->decreased;d->nonoutward+=s->nonoutward;if(s->have_root&&(!d->have_root||mpz_cmp(s->min_root,d->min_root)<0||(mpz_cmp(s->min_root,d->min_root)==0&&s->root_code<d->root_code))){d->have_root=1;mpz_set(d->min_root,s->min_root);d->root_code=s->root_code;}if(s->have_delta&&(!d->have_delta||mpz_cmp(s->min_delta,d->min_delta)<0||(mpz_cmp(s->min_delta,d->min_delta)==0&&s->delta_code<d->delta_code))){d->have_delta=1;mpz_set(d->min_delta,s->min_delta);d->delta_code=s->delta_code;}}
static void reset_stat(stat_t*s){s->paths=s->failed=s->stable=s->decreased=s->nonoutward=0;s->have_root=s->have_delta=0;}

static __attribute__((noinline)) void dfs(context_t*c,unsigned depth,unsigned current_m,uint64_t code){
    if(depth>=DEPTH||depth>=MAX_DEPTH)return;uint64_t base=(uint64_t)HB*MB;unsigned next_depth=depth+1;
    for(unsigned h=1;h<=HB;++h)for(unsigned n=1;n<=MB;++n){uint64_t sym=(uint64_t)(h-1)*MB+(n-1);if(code>(UINT64_MAX-sym)/base)fail("path code overflow");uint64_t nc=code*base+sym;relation_t*out=&c->stack[next_depth];if(!compose(&c->stack[depth],edge(current_m,h,n),out,c)){++c->stat[next_depth].failed;continue;}record(&c->stat[next_depth],&c->stack[depth],out,nc,c->z[9]);dfs(c,next_depth,n,nc);}
}
static uint64_t mulcap(uint64_t a,uint64_t b){if(a&&b>UINT64_MAX/a)fail("task count overflow");return a*b;}
static void print_stat(FILE*f,unsigned d,const stat_t*s,uint64_t done,uint64_t total){fprintf(f,"DEPTH\tdepth=%u\tprocessed_prefix_tasks=%llu\ttotal_prefix_tasks=%llu\tpaths=%llu\tlink_failures=%llu\tstabilizations=%llu\tdecreases=%llu\tnonoutward=%llu\tmin_root_bits=%zu\tmin_root=",d,(unsigned long long)done,(unsigned long long)total,s->paths,s->failed,s->stable,s->decreased,s->nonoutward,s->have_root?mpz_sizeinbase(s->min_root,2):0);if(s->have_root)mpz_out_str(f,10,s->min_root);else fputs("null",f);fprintf(f,"\tmin_root_code=%llu\tmin_increment_bits=%zu\tmin_increment=",(unsigned long long)(s->have_root?s->root_code:0),s->have_delta?mpz_sizeinbase(s->min_delta,2):0);if(s->have_delta)mpz_out_str(f,10,s->min_delta);else fputs("null",f);fprintf(f,"\tmin_increment_code=%llu\n",(unsigned long long)(s->have_delta?s->delta_code:0));}

int main(int argc,char**argv){
    if(argc!=9)fail("usage: M_BOUND H_BOUND DEPTH SHARD SHARDS BATCH_PREFIXES OUTPUT.tsv RUN_LABEL");MB=(unsigned)strtoul(argv[1],0,10);HB=(unsigned)strtoul(argv[2],0,10);DEPTH=(unsigned)strtoul(argv[3],0,10);uint64_t shard=strtoull(argv[4],0,10),shards=strtoull(argv[5],0,10),batch=strtoull(argv[6],0,10);const char*outpath=argv[7];
    /* argv[8] is a required run label, retained verbatim in the header. */
    if(!MB||!HB||DEPTH<2||DEPTH>MAX_DEPTH||!shards||shard>=shards||!batch)fail("invalid bounds");
    if(signal(SIGUSR1,request_stop)==SIG_ERR)fail("cannot install stop handler");
    mpz_t A,B,C,D,F,M,t;mpz_inits(A,B,C,D,F,M,t,NULL);mpz_ui_pow_ui(A,3,114);mpz_ui_pow_ui(B,2,154);mpz_ui_pow_ui(C,3,17);mpz_ui_pow_ui(D,2,23);mpz_sub(F,A,B);mpz_divexact_ui(F,F,5);mpz_ui_pow_ui(M,3,33);mpz_sub(t,C,D);mpz_mul(M,M,t);
    size_t ne=(size_t)MB*HB*MB;edges=calloc(ne,sizeof(*edges));if(!edges)fail("edge allocation");for(unsigned m=1;m<=MB;++m)for(unsigned h=1;h<=HB;++h)for(unsigned n=1;n<=MB;++n)make_edge(edge(m,h,n),m,h,n,A,B,C,D,F,M);
    uint64_t alphabet=(uint64_t)HB*MB,total=mulcap(MB,mulcap(alphabet,alphabet)),mine=(total-shard+shards-1)/shards;int nt=omp_get_max_threads();context_t*ctx=calloc((size_t)nt,sizeof(*ctx));stat_t global[MAX_DEPTH+1];for(unsigned d=0;d<=DEPTH;++d)stat_init(&global[d]);
    for(int q=0;q<nt;++q){for(unsigned d=0;d<=DEPTH;++d){relation_init(&ctx[q].stack[d]);stat_init(&ctx[q].stat[d]);}mpz_inits(ctx[q].z[0],ctx[q].z[1],ctx[q].z[2],ctx[q].z[3],ctx[q].z[4],ctx[q].z[5],ctx[q].z[6],ctx[q].z[7],ctx[q].z[8],ctx[q].z[9],ctx[q].z[10],ctx[q].z[11],NULL);}
    FILE*out=fopen(outpath,"w");if(!out)fail("cannot open output");setvbuf(out,NULL,_IOLBF,0);fprintf(out,"# exact bouncer backward-cylinder atlas m_bound=%u h_bound=%u depth=%u total_prefix_tasks=%llu shard=%llu shards=%llu shard_tasks=%llu batch=%llu threads=%d label=%s\n",MB,HB,DEPTH,(unsigned long long)total,(unsigned long long)shard,(unsigned long long)shards,(unsigned long long)mine,(unsigned long long)batch,nt,argv[8]);
    for(size_t i=0;i<ne;++i){edge_t*e=&edges[i];fprintf(out,"EDGE\tm=%u\th=%u\tnext_m=%u\tinput_base=",e->m,e->h,e->next);mpz_out_str(out,10,e->ib);fputs("\tinput_stride=",out);mpz_out_str(out,10,e->is);fputs("\toutput_base=",out);mpz_out_str(out,10,e->ob);fputs("\toutput_stride=",out);mpz_out_str(out,10,e->os);fputc('\n',out);}
    double started=omp_get_wtime();uint64_t done=0;
    while(done<mine&&!stop_requested){uint64_t take=mine-done<batch?mine-done:batch;
        for(int q=0;q<nt;++q)for(unsigned d=2;d<=DEPTH;++d)reset_stat(&ctx[q].stat[d]);
#pragma omp parallel for schedule(dynamic,1)
        for(uint64_t p=0;p<take;++p){uint64_t code=shard+(done+p)*shards,q=code;unsigned m0=(unsigned)(q%MB)+1;q/=MB;uint64_t s0=q%alphabet;q/=alphabet;uint64_t s1=q%alphabet;unsigned h0=(unsigned)(s0/MB)+1,m1=(unsigned)(s0%MB)+1,h1=(unsigned)(s1/MB)+1,m2=(unsigned)(s1%MB)+1;context_t*c=&ctx[omp_get_thread_num()];relation_edge(&c->stack[1],edge(m0,h0,m1));if(!compose(&c->stack[1],edge(m1,h1,m2),&c->stack[2],c)){++c->stat[2].failed;continue;}record(&c->stat[2],&c->stack[1],&c->stack[2],code,c->z[9]);dfs(c,2,m2,code);}
        for(int q=0;q<nt;++q)for(unsigned d=2;d<=DEPTH;++d)merge_stat(&global[d],&ctx[q].stat[d]);done+=take;fprintf(out,"CHECKPOINT\tprocessed_prefix_tasks=%llu\tshard_tasks=%llu\tseconds=%.6f\n",(unsigned long long)done,(unsigned long long)mine,omp_get_wtime()-started);for(unsigned d=2;d<=DEPTH;++d)print_stat(out,d,&global[d],done,mine);fflush(out);
    }
    fprintf(out,"RESULT\tstatus=%s\tprocessed_prefix_tasks=%llu\tshard_tasks=%llu\tfinite_stabilizations=%llu\tinvariant=null\tcounterexample=null\n",done==mine?"complete":"partial",(unsigned long long)done,(unsigned long long)mine,global[DEPTH].stable);fclose(out);
    for(int q=0;q<nt;++q){for(unsigned d=0;d<=DEPTH;++d){relation_clear(&ctx[q].stack[d]);stat_clear(&ctx[q].stat[d]);}mpz_clears(ctx[q].z[0],ctx[q].z[1],ctx[q].z[2],ctx[q].z[3],ctx[q].z[4],ctx[q].z[5],ctx[q].z[6],ctx[q].z[7],ctx[q].z[8],ctx[q].z[9],ctx[q].z[10],ctx[q].z[11],NULL);}for(unsigned d=0;d<=DEPTH;++d)stat_clear(&global[d]);free(ctx);for(size_t i=0;i<ne;++i)mpz_clears(edges[i].ib,edges[i].is,edges[i].ob,edges[i].os,NULL);free(edges);mpz_clears(A,B,C,D,F,M,t,NULL);return 0;
}
