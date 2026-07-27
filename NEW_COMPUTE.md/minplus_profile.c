#define _POSIX_C_SOURCE 200809L
#include <gmp.h>
#include <omp.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef __uint128_t u128;
static void fail(const char*s){fprintf(stderr,"minplus_profile: %s\n",s);exit(2);}
static void atomic_min_u64(_Atomic uint64_t *p,uint64_t x){uint64_t old=atomic_load_explicit(p,memory_order_relaxed);while(x<old&&!atomic_compare_exchange_weak_explicit(p,&old,x,memory_order_relaxed,memory_order_relaxed));}
static unsigned *need_odds;

static void build_crossing_table(unsigned step_cap){mpz_t p2,p3;mpz_inits(p2,p3,NULL);mpz_set_ui(p2,1);mpz_set_ui(p3,1);need_odds=malloc((size_t)(step_cap+2)*sizeof(*need_odds));if(!need_odds)fail("crossing-table allocation failed");need_odds[0]=1;unsigned odds=0;for(unsigned s=1;s<=step_cap+1;++s){mpz_mul_ui(p2,p2,2);while(mpz_cmp(p3,p2)<=0){mpz_mul_ui(p3,p3,3);++odds;}need_odds[s]=odds;}mpz_clears(p2,p3,NULL);}

typedef struct{unsigned blocks,steps;u128 terminal_max;} profile_t;
static profile_t profile(uint64_t source,unsigned step_cap,unsigned depth_cap){u128 v=source,maxv=v;unsigned S=0,O=0,blocks=0,steps=0;while(steps<step_cap){if(v==1){if(O+1>=need_odds[S+1]){++blocks;v=2;}return(profile_t){blocks,steps,maxv};}if(v==2)return(profile_t){blocks,steps,maxv};unsigned odd=(unsigned)(v&1);if(odd){if(v>(~(u128)0-1)/3)fail("orbit overflow");v=(3*v+1)/2;++O;}else v/=2;++S;++steps;if(v>maxv)maxv=v;if(O>=need_odds[S]){++blocks;if(blocks>=depth_cap)return(profile_t){blocks,steps,maxv};S=O=0;}}
    fail("shortcut step cap exhausted");return(profile_t){0,0,0};}

int main(int argc,char**argv){if(argc!=6)fail("usage: MAX_SOURCE DEPTH_CAP PHASE_EXPONENT STEP_CAP OUTPUT.tsv");uint64_t B=strtoull(argv[1],0,10);unsigned D=(unsigned)strtoul(argv[2],0,10),K=(unsigned)strtoul(argv[3],0,10),step=(unsigned)strtoul(argv[4],0,10);if(!B||!D||!step)fail("invalid bounds");build_crossing_table(step);
    uint64_t phases=0,p=1;for(unsigned e=0;e<=K;++e){if(UINT64_MAX-phases<p)fail("phase count overflow");phases+=p;if(e<K)p*=3;}if(phases>SIZE_MAX/(D+1)/sizeof(_Atomic uint64_t))fail("profile allocation overflow");size_t cells=(size_t)(D+1)*(size_t)phases;_Atomic uint64_t*mins=malloc(cells*sizeof(*mins));if(!mins)fail("profile allocation failed");
#pragma omp parallel for schedule(static)
    for(size_t i=0;i<cells;++i)atomic_init(&mins[i],UINT64_MAX);
    _Atomic uint64_t overflow_max;atomic_init(&overflow_max,0);double started=omp_get_wtime();
#pragma omp parallel for schedule(dynamic,4096)
    for(uint64_t x=1;x<=B;++x){profile_t q=profile(x,step,D);uint64_t old=atomic_load(&overflow_max),mx=(uint64_t)(q.terminal_max>UINT64_MAX?UINT64_MAX:q.terminal_max);while(mx>old&&!atomic_compare_exchange_weak(&overflow_max,&old,mx));unsigned upto=q.blocks<D?q.blocks:D;uint64_t mod=1,offset=0;for(unsigned e=0;e<=K;++e){uint64_t r=e?x%mod:0;for(unsigned d=1;d<=upto;++d)atomic_min_u64(&mins[(size_t)d*phases+offset+r],x);offset+=mod;if(e<K)mod*=3;}}
    FILE*out=fopen(argv[5],"w");if(!out)fail("cannot open output");fprintf(out,"# exact exhaustive triadic minimum profile B=%llu depth=%u K=%u cells=%zu step_cap=%u threads=%d seconds=%.6f maximum_orbit_value_capped_u64=%llu\n",(unsigned long long)B,D,K,cells,step,omp_get_max_threads(),omp_get_wtime()-started,(unsigned long long)atomic_load(&overflow_max));
    uint64_t off1=1;for(unsigned d=1;d<=D;++d){uint64_t h=atomic_load(&mins[(size_t)d*phases]);uint64_t m=K>=1?atomic_load(&mins[(size_t)d*phases+off1+2]):UINT64_MAX;fprintf(out,"SLICE\tdepth=%u\th=",d);if(h==UINT64_MAX)fprintf(out,"null");else fprintf(out,"%llu",(unsigned long long)h);fprintf(out,"\tm_residue2=");if(m==UINT64_MAX)fprintf(out,"null");else fprintf(out,"%llu",(unsigned long long)m);if(h!=UINT64_MAX&&m!=UINT64_MAX&&d<D){uint64_t next=atomic_load(&mins[(size_t)(d+1)*phases]);if(next!=UINT64_MAX)fprintf(out,"\tsigma=%lld",(long long)((next-h)/2));}fputc('\n',out);}
    uint64_t offset=0,mod=1;for(unsigned e=0;e<=K;++e){uint64_t nonempty=0,maxmin=0;for(unsigned d=1;d<=D;++d)for(uint64_t r=0;r<mod;++r){uint64_t z=atomic_load(&mins[(size_t)d*phases+offset+r]);if(z!=UINT64_MAX){++nonempty;if(z>maxmin)maxmin=z;}}fprintf(out,"PHASE\texponent=%u\tmodulus=%llu\tnonempty_cells=%llu\tmax_finite_minimum=%llu\n",e,(unsigned long long)mod,(unsigned long long)nonempty,(unsigned long long)maxmin);offset+=mod;mod*=3;}
    fprintf(out,"RESULT\tclaim=exhaustive_sources_1_through_B\tcounterexample=null\n");fclose(out);free(mins);free(need_odds);return 0;}
