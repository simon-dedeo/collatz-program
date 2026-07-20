/* u128_probe.cu — verify unsigned __int128 arithmetic on device (RTX 4090, CUDA 12.8)
 * Tests +, -, *, >>, <<, compares against host-computed references.
 * Also (guarded by TRY_DIV128) probes whether device 128-bit / and % compile.
 */
#include <cstdio>
#include <cstdint>

typedef unsigned __int128 u128;
typedef __int128 i128;
typedef uint64_t u64;

#define CK(call) do { cudaError_t e = (call); if (e != cudaSuccess) { \
    fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e), __FILE__, __LINE__); return 2; } } while (0)

struct Pair { u64 hi, lo; };
__host__ __device__ static inline u128 mk(Pair p) { return ((u128)p.hi << 64) | p.lo; }
__host__ __device__ static inline Pair un(u128 v) { Pair p; p.hi = (u64)(v >> 64); p.lo = (u64)v; return p; }

__global__ void probe(const Pair *a, const Pair *b, Pair *out, int n)
{
    int t = blockIdx.x * blockDim.x + threadIdx.x;
    if (t >= n) return;
    u128 x = mk(a[t]), y = mk(b[t]);
    u128 add = x + y;
    u128 sub = x - y;
    u128 mul = x * y;                      /* low 128 bits */
    u128 shr = x >> (int)(y & 127);
    u128 shl = x << (int)(y & 127);
    u128 cmp = (x < y) ? (u128)1 : (x == y) ? (u128)2 : (u128)3;
    i128 sx = (i128)(x >> 2), sy = -(i128)(y >> 3);
    i128 smul = sx * sy;
    u128 h = add ^ sub ^ mul ^ shr ^ shl ^ cmp ^ (u128)smul;
#ifdef TRY_DIV128
    u128 dv = (y != 0) ? x / y : (u128)0;
    u128 md = (y != 0) ? x % y : (u128)0;
    h ^= dv ^ md;
#endif
    out[t] = un(h);
}

static u64 rng(u64 *s) { u64 x = *s; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return *s = x; }

int main(void)
{
    const int n = 4096;
    Pair *ha = new Pair[n], *hb = new Pair[n], *ho = new Pair[n];
    u64 s = 0x123456789abcdefULL;
    for (int i = 0; i < n; i++) {
        ha[i].hi = rng(&s); ha[i].lo = rng(&s);
        hb[i].hi = rng(&s) >> (i % 64); hb[i].lo = rng(&s) | 1;
    }
    Pair *da, *db, *dz;
    CK(cudaMalloc(&da, n * sizeof(Pair))); CK(cudaMalloc(&db, n * sizeof(Pair)));
    CK(cudaMalloc(&dz, n * sizeof(Pair)));
    CK(cudaMemcpy(da, ha, n * sizeof(Pair), cudaMemcpyHostToDevice));
    CK(cudaMemcpy(db, hb, n * sizeof(Pair), cudaMemcpyHostToDevice));
    probe<<<(n + 127) / 128, 128>>>(da, db, dz, n);
    CK(cudaGetLastError());
    CK(cudaMemcpy(ho, dz, n * sizeof(Pair), cudaMemcpyDeviceToHost));

    int bad = 0;
    for (int i = 0; i < n; i++) {
        u128 x = mk(ha[i]), y = mk(hb[i]);
        u128 add = x + y, sub = x - y, mul = x * y;
        u128 shr = x >> (int)(y & 127), shl = x << (int)(y & 127);
        u128 cmp = (x < y) ? (u128)1 : (x == y) ? (u128)2 : (u128)3;
        i128 sx = (i128)(x >> 2), sy = -(i128)(y >> 3);
        i128 smul = sx * sy;
        u128 h = add ^ sub ^ mul ^ shr ^ shl ^ cmp ^ (u128)smul;
#ifdef TRY_DIV128
        u128 dv = (y != 0) ? x / y : (u128)0;
        u128 md = (y != 0) ? x % y : (u128)0;
        h ^= dv ^ md;
#endif
        Pair e = un(h);
        if (e.hi != ho[i].hi || e.lo != ho[i].lo) bad++;
    }
    printf("u128 probe: %d/%d mismatches%s\n", bad, n,
#ifdef TRY_DIV128
           " (with /,%)"
#else
           " (+,-,*,>>,<<,cmp,i128*)"
#endif
    );
    return bad != 0;
}
