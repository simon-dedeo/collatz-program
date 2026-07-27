#define _POSIX_C_SOURCE 200809L
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef __uint128_t u128;
typedef struct { uint64_t x[4]; } u256;
typedef struct { unsigned max_extra; u256 seed,endpoint; unsigned long long hist[257],positive,overflow; } stats_t;
static void fail(const char*s){fprintf(stderr,"zero_carry_champions: %s\n",s);exit(2);}
static u256 zero256(void){return(u256){{0,0,0,0}};} static u256 one256(void){return(u256){{1,0,0,0}};}
static int iszero(u256 a){return!(a.x[0]|a.x[1]|a.x[2]|a.x[3]);}
static int cmp256(u256 a,u256 b){for(int i=3;i>=0;--i)if(a.x[i]!=b.x[i])return a.x[i]<b.x[i]?-1:1;return 0;}
static int muladd(u256 a,uint64_t m,uint64_t add,u256*out){u128 carry=add;for(int i=0;i<4;++i){u128 z=(u128)a.x[i]*m+carry;out->x[i]=(uint64_t)z;carry=z>>64;}return carry!=0;}
static int addmul(u256 base,u256 a,uint64_t m,u256*out){u128 carry=0;for(int i=0;i<4;++i){u128 z=(u128)a.x[i]*m+base.x[i]+carry;out->x[i]=(uint64_t)z;carry=z>>64;}return carry!=0;}
static int add_shift(u256*a,uint64_t v,unsigned sh){unsigned q=sh/64,r=sh%64;if(q>=4)return v!=0;u128 z=(u128)a->x[q]+((u128)v<<r);a->x[q]=(uint64_t)z;u128 carry=z>>64;if(r&&q+1<4){z=(u128)a->x[q+1]+(v>>(64-r))+carry;a->x[q+1]=(uint64_t)z;carry=z>>64;++q;}while(carry&&++q<4){z=(u128)a->x[q]+carry;a->x[q]=(uint64_t)z;carry=z>>64;}return carry!=0;}
static u256 shr(u256 a,unsigned s){u256 z=zero256();unsigned q=s/64,r=s%64;for(unsigned i=q;i<4;++i){z.x[i-q]|=a.x[i]>>r;if(r&&i+1<4)z.x[i-q]|=a.x[i+1]<<(64-r);}return z;}
static uint32_t div10(u256*a){u128 rem=0;for(int i=3;i>=0;--i){u128 z=(rem<<64)|a->x[i];a->x[i]=(uint64_t)(z/10);rem=z%10;}return(uint32_t)rem;}
static void print256(FILE*f,u256 a){char b[100];unsigned n=0;do{b[n++]=(char)('0'+div10(&a));}while(!iszero(a));while(n)fputc(b[--n],f);}
static uint64_t invodd(uint64_t a){uint64_t x=a;for(int i=0;i<6;++i)x*=2-a*x;return x;}
static uint64_t pow3(unsigned d){uint64_t x=1;while(d--){if(x>UINT64_MAX/3)fail("depth too large for schedule counter");x*=3;}return x;}
static int extend(unsigned sym,u256*r,u256*K,u256*A,unsigned*L){static const unsigned ell[3]={1,3,6};static const uint64_t src[3]={0,5,49},mul[3]={3,9,81},add[3]={0,3,63};unsigned e=ell[sym];uint64_t mask=((uint64_t)1<<e)-1,t=((src[sym]-(K->x[0]&mask))*invodd(A->x[0]))&mask;if(add_shift(r,t,*L))return 0;u256 pre,num,nextA;if(addmul(*K,*A,t,&pre)||muladd(pre,mul[sym],add[sym],&num))return 0;if(num.x[0]&mask)fail("cylinder extension lost integrality");*K=shr(num,e);if(muladd(*A,mul[sym],0,&nextA))return 0;*A=nextA;*L+=e;return *L<256;}
static unsigned continue_seed(u256 h,unsigned cap,int*overflow){unsigned d=0;while(d<cap){uint64_t lo=h.x[0],m,a;unsigned sh;if(!(lo&1)){m=3;a=0;sh=1;}else if((lo&7)==5){m=9;a=3;sh=3;}else if((lo&63)==49){m=81;a=63;sh=6;}else break;u256 num;if(muladd(h,m,a,&num)){*overflow=1;break;}h=shr(num,sh);++d;}return d;}
int main(int argc,char**argv){if(argc!=4)fail("usage: PREFIX_DEPTH EXTRA_CAP OUTPUT.tsv");unsigned depth=(unsigned)strtoul(argv[1],0,10),cap=(unsigned)strtoul(argv[2],0,10);if(depth<1||depth>40||cap>256)fail("depth must be 1..40 and cap <=256");uint64_t count=pow3(depth);int nt=omp_get_max_threads();stats_t*s=calloc((size_t)nt,sizeof(*s));if(!s)fail("allocation");for(int t=0;t<nt;++t)for(int i=0;i<4;++i)s[t].seed.x[i]=UINT64_MAX;double start=omp_get_wtime();
#pragma omp parallel for schedule(static)
    for(uint64_t code=0;code<count;++code){u256 r=zero256(),K=zero256(),A=one256();unsigned L=0;uint64_t q=code;int ok=1;for(unsigned d=0;d<depth;++d){unsigned sym=(unsigned)(q%3);q/=3;if(!extend(sym,&r,&K,&A,&L)){ok=0;break;}}if(!ok||iszero(r))continue;stats_t*t=&s[omp_get_thread_num()];++t->positive;int ov=0;unsigned extra=continue_seed(r,cap,&ov);if(ov)++t->overflow;++t->hist[extra];if(extra>t->max_extra||(extra==t->max_extra&&cmp256(r,t->seed)<0)){t->max_extra=extra;t->seed=r;t->endpoint=K;}}
    stats_t z={0};for(int i=0;i<4;++i)z.seed.x[i]=UINT64_MAX;for(int t=0;t<nt;++t){z.positive+=s[t].positive;z.overflow+=s[t].overflow;for(unsigned d=0;d<=256;++d)z.hist[d]+=s[t].hist[d];if(s[t].max_extra>z.max_extra||(s[t].max_extra==z.max_extra&&cmp256(s[t].seed,z.seed)<0)){z.max_extra=s[t].max_extra;z.seed=s[t].seed;z.endpoint=s[t].endpoint;}}
    FILE*out=fopen(argv[3],"w");if(!out)fail("cannot open output");fprintf(out,"# exact exhaustive zero-carry canonical-cylinder census prefix_depth=%u schedules=%llu positive_representatives=%llu replay_cap=%u threads=%d seconds=%.6f overflowed_replays=%llu arithmetic_bits=256\n",depth,(unsigned long long)count,z.positive,cap,nt,omp_get_wtime()-start,z.overflow);for(unsigned d=0;d<=cap;++d)if(z.hist[d])fprintf(out,"HIST\ttotal_survival=%u\tbeyond_prefix=%u\tcount=%llu\n",d,d>=depth?d-depth:0,z.hist[d]);fprintf(out,"CHAMPION\ttotal_survival=%u\tbeyond_prefix=%u\tseed=",z.max_extra,z.max_extra>=depth?z.max_extra-depth:0);print256(out,z.seed);fprintf(out,"\tprefix_endpoint=");print256(out,z.endpoint);fprintf(out,"\tcounterexample=null\n");fclose(out);free(s);return 0;}
