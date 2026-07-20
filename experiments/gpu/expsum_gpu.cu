/* expsum_gpu.cu — CUDA port of expsum.c EXHAUSTIVE mode: exponential sums
 * S_{K,L}(xi) at the Collatz cycle modulus M = 2^K - 3^L, ALL xi mod M.
 * (Tested: RTX 4090, sm_89, CUDA 12.8.)
 *
 * WHAT RUNS WHERE
 *   GPU  : one thread per xi.  Each thread runs the O(K*L) transfer-matrix DP
 *          entirely in registers/local memory with double-precision complex
 *          accumulators and EXACT integer phase residues, then contributes to
 *          block-level reductions (sum Re S, sum |S|, sum log|S|, counts,
 *          max|S| + argmax).
 *   HOST : per-block partials are merged sequentially in long double
 *          (deterministic), the divisible count (1/M) sum_xi S is formed, and
 *          divisible words are brute-classified exactly as in expsum.c
 *          (verbatim host port).  TSV rows use the same format strings.
 *
 * NUMERICS / SEMANTIC NOTES vs the CPU tool
 *   - Exhaustive mode caps M < 2^62, so phase residues fit in u64 on device;
 *     they are maintained exactly (doubling mod M per position), just as the
 *     CPU maintains them in u128.  No u128 arithmetic is needed in this
 *     kernel at all.
 *   - Phases: CPU computes cosl/sinl(2*pi*R/M) in long double (80-bit on
 *     Linux/x86); the GPU uses sincospi(2*R/M) in double.  |S| therefore
 *     agrees to ~1e-12 relative (measured), comfortably inside the 1e-9
 *     validation gate; div_count is integral to ~1e-9 and matches exactly.
 *   - argmax_xi: |S(M-xi)| = |S(xi)| exactly (conjugation), so the argmax is
 *     always a near-tie between xi* and M-xi*; which one wins depends on
 *     last-bit rounding and may differ from the CPU run.  Ties inside the
 *     GPU reduction are broken toward the SMALLER xi (the CPU's ascending
 *     scan does the same for exact ties).
 *   - n_zeroS uses the same |S| < 1e-12 threshold (no signature K <= 26 has
 *     any such xi on either CPU or GPU).
 *
 * CLI:
 *   expsum_gpu selftest                  GPU DP vs host brute force + counts
 *   expsum_gpu exhaustive KMIN KMAX      K <= 40, skips M >= 2^62 (as CPU)
 *
 * Build: nvcc -O3 -arch=sm_89 -o expsum_gpu expsum_gpu.cu   (see Makefile.gpu)
 */
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <ctime>
#include <cuda_runtime.h>

typedef unsigned __int128 u128;
typedef __int128          i128;
typedef uint64_t          u64;

#define LMAX_G       26          /* max L on device: K <= 40 admissible band */
#define K_CAP_EXH    40          /* exhaustive mode cap (same as CPU)        */
#define CLASSIFY_CAP 50000000ULL /* classify words when C(K,L) <= this       */

#define NBLK 4096                /* reduction grid: fixed, deterministic     */
#define BS   128                 /* threads per block                        */

#define CK(call) do { cudaError_t e_ = (call); if (e_ != cudaSuccess) { \
    fprintf(stderr, "CUDA error: %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); \
    exit(2); } } while (0)

/* ------------------------------------------------------------------ utils -- */

static void u128_str(u128 v, char *buf)
{
    char t[48]; int i = 0, j = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) buf[j++] = t[--i];
    buf[j] = 0;
}

static u128 p2_128(int k) { return (u128)1 << k; }
static u128 p3_128(int l) { u128 r = 1; while (l-- > 0) r *= 3; return r; }

static inline u128 addmod128(u128 a, u128 b, u128 m) { a += b; if (a >= m) a -= m; return a; }
static inline u128 dblmod128(u128 a, u128 m)         { a <<= 1; if (a >= m) a -= m; return a; }

static u128 mulmod128(u128 a, u128 b, u128 m)
{
    u128 r = 0;
    a %= m;
    while (b) {
        if (b & 1) r = addmod128(r, a, m);
        a = dblmod128(a, m);
        b >>= 1;
    }
    return r;
}

static u128 binom_u128(int K, int L)
{
    if (L < 0 || L > K) return 0;
    if (L > K - L) L = K - L;
    u128 c = 1;
    for (int i = 1; i <= L; i++) { c = c * (u128)(K - L + i) / (u128)i; }
    return c;
}

static long double logbinom(int K, int L)
{ return lgammal((long double)K + 1) - lgammal((long double)L + 1) - lgammal((long double)(K - L) + 1); }

/* splitmix64 (selftest xi sampling, same as CPU) */
static u64 sm64(u64 *s)
{
    u64 z = (*s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static u128 rand_mod(u64 *s, u128 m)
{
    u128 r = ((u128)sm64(s) << 64) | (u128)sm64(s);
    return r % m;
}

static double now_sec(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* --------------------------------------------------------------- device ---- */

typedef struct {
    double sumRe, sumAbs, sumLog;
    long long nAlpha, nZero;
    double maxMag;
    unsigned long long argmax;
} Partial;

/* full-ensemble S_{K,L}(xi); residues exact in u64 (M < 2^62) */
__device__ static double2 dp_S_dev(int K, int L, u64 M, u64 xi)
{
    u64 R[LMAX_G];
    double2 A[LMAX_G + 1];

    R[L - 1] = xi % M;                              /* xi * 3^0 */
    for (int i = L - 2; i >= 0; i--) {              /* R[i] = 3*R[i+1] mod M */
        u64 t = R[i + 1] << 1; if (t >= M) t -= M;
        t += R[i + 1]; if (t >= M) t -= M;
        R[i] = t;
    }
    A[0] = make_double2(1.0, 0.0);
    for (int i = 1; i <= L; i++) A[i] = make_double2(0.0, 0.0);

    for (int j = 0; j < K; j++) {
        int hi = (j < L - 1) ? j : L - 1;
        for (int i = hi; i >= 0; i--) {
            double sn, cn;
            sincospi(2.0 * ((double)R[i] / (double)M), &sn, &cn);
            double ax = A[i].x, ay = A[i].y;
            A[i + 1].x += ax * cn - ay * sn;
            A[i + 1].y += ax * sn + ay * cn;
        }
        for (int i = 0; i < L; i++) { u64 t = R[i] << 1; if (t >= M) t -= M; R[i] = t; }
    }
    return A[L];
}

__global__ static void skernel(int K, int L, u64 M, Partial *pb)
{
    double lRe = 0.0, lAbs = 0.0, lLog = 0.0, lMax = -1.0;
    long long lnA = 0, lnZ = 0;
    u64 lArg = 0;
    u64 stride = (u64)gridDim.x * blockDim.x;
    for (u64 xi = 1 + (u64)blockIdx.x * blockDim.x + threadIdx.x; xi < M; xi += stride) {
        double2 s = dp_S_dev(K, L, M, xi);
        double mag = sqrt(s.x * s.x + s.y * s.y);
        lRe += s.x;
        lAbs += mag;
        if (mag > 1e-12) {
            lLog += log(mag); lnA++;
            if (mag > lMax || (mag == lMax && xi < lArg)) { lMax = mag; lArg = xi; }
        } else lnZ++;
    }

    __shared__ double sRe[BS], sAbs[BS], sLog[BS], sMax[BS];
    __shared__ long long sA[BS], sZ[BS];
    __shared__ unsigned long long sArg[BS];
    int tid = threadIdx.x;
    sRe[tid] = lRe; sAbs[tid] = lAbs; sLog[tid] = lLog;
    sA[tid] = lnA; sZ[tid] = lnZ; sMax[tid] = lMax; sArg[tid] = lArg;
    __syncthreads();
    for (int w = BS / 2; w > 0; w >>= 1) {
        if (tid < w) {
            sRe[tid] += sRe[tid + w]; sAbs[tid] += sAbs[tid + w]; sLog[tid] += sLog[tid + w];
            sA[tid] += sA[tid + w]; sZ[tid] += sZ[tid + w];
            if (sMax[tid + w] > sMax[tid] ||
                (sMax[tid + w] == sMax[tid] && sArg[tid + w] < sArg[tid])) {
                sMax[tid] = sMax[tid + w]; sArg[tid] = sArg[tid + w];
            }
        }
        __syncthreads();
    }
    if (tid == 0) {
        Partial p;
        p.sumRe = sRe[0]; p.sumAbs = sAbs[0]; p.sumLog = sLog[0];
        p.nAlpha = sA[0]; p.nZero = sZ[0]; p.maxMag = sMax[0]; p.argmax = sArg[0];
        pb[blockIdx.x] = p;
    }
}

/* debug/selftest kernel: S at an explicit xi list */
__global__ static void skernel_list(int K, int L, u64 M, const u64 *xs, int nx, double2 *out)
{
    int t = blockIdx.x * blockDim.x + threadIdx.x;
    if (t < nx) out[t] = dp_S_dev(K, L, M, xs[t]);
}

/* ------------------------------------- host: brute force (verbatim port) --- */

static u64 gosper_next(u64 mask)
{
    u64 c = mask & (~mask + 1ULL);
    u64 r = mask + c;
    return (((r ^ mask) >> 2) / c) | r;
}

/* brute S (host, long double, all-words ensemble) for the selftest */
static void brute_S(int K, int L, u128 M, u128 xi, long double *re, long double *im)
{
    const long double TWOPI = 6.283185307179586476925286766559005768L;
    long double sr = 0, si = 0;
    u128 pw3[LMAX_G], pw2[64];
    u64 top = 1ULL << K;

    *re = 0; *im = 0;
    if (L < 1 || L > K || K > 24) return;
    pw3[0] = 1 % M;
    for (int t = 1; t < L; t++) pw3[t] = mulmod128(pw3[t - 1], 3, M);
    pw2[0] = 1 % M;
    for (int j = 1; j < K; j++) pw2[j] = dblmod128(pw2[j - 1], M);
    xi %= M;

    for (u64 mask = (1ULL << L) - 1; mask < top; ) {
        u128 w = 0; int i = 0;
        for (int j = 0; j < K; j++)
            if ((mask >> j) & 1ULL) { w = addmod128(w, mulmod128(pw3[L - 1 - i], pw2[j], M), M); i++; }
        u128 r = mulmod128(xi, w, M);
        long double a = TWOPI * (long double)r / (long double)M;
        sr += cosl(a); si += sinl(a);
        u64 nx = gosper_next(mask);
        if (nx <= mask || nx >= top) break;
        mask = nx;
    }
    *re = sr; *im = si;
}

/* enumerate words; count M|W, W/M >= 1, and realizable parity words (q=+1) */
static int brute_classify(int K, int L, u128 M,
                          long long *n_div, long long *n_pos, long long *n_real)
{
    if (K > 62 || L < 1 || L > K) return 0;
    if (binom_u128(K, L) > (u128)CLASSIFY_CAP) return 0;

    u128 pw3[LMAX_G + 40];
    pw3[0] = 1;
    for (int t = 1; t < L; t++) pw3[t] = pw3[t - 1] * 3;

    long long nd = 0, np = 0, nr = 0;
    u64 top = 1ULL << K;
    for (u64 mask = (1ULL << L) - 1; mask < top; ) {
        u128 w = 0; int i = 0;
        for (int j = 0; j < K; j++)
            if ((mask >> j) & 1ULL) { w += pw3[L - 1 - i] << j; i++; }
        if (w % M == 0) {
            nd++;
            u128 n0 = w / M;
            if (n0 >= 1) {
                np++;
                u128 n = n0; int ok = 1;
                for (int j = 0; j < K; j++) {
                    int v = (int)(n & 1);
                    if (v != (int)((mask >> j) & 1ULL)) { ok = 0; break; }
                    n = v ? (3 * n + 1) >> 1 : n >> 1;
                }
                if (ok && n == n0) nr++;
            }
        }
        u64 nx = gosper_next(mask);
        if (nx <= mask || nx >= top) break;
        mask = nx;
    }
    *n_div = nd; *n_pos = np; *n_real = nr;
    return 1;
}

/* ------------------------------------------------------- admissible band --- */

static int admissible_band(int K, int *Ls)
{
    int L0 = (int)floorl((long double)K * logl(2.0L) / logl(3.0L));
    int n = 0;
    for (int d = -2; d <= 2; d++) {
        int L = L0 + d;
        if (L < 1 || L >= K || L > LMAX_G) continue;
        if ((long double)L * logl(3.0L) >= (long double)K * logl(2.0L)) continue;
        if (p3_128(L) >= p2_128(K)) continue;
        Ls[n++] = L;
    }
    return n;
}

/* --------------------------------------------------------------- output ---- */

static void tsv_header(void)
{
    printf("mode\tK\tL\tM\tC\tn_xi\tdiv_count\tresid\tn_pos\tn_real\t"
           "max_ratio\targmax_xi\tmean_ratio\tmax_alpha\tmean_alpha\tn_zeroS\torbit_dev\ttop5_xi\n");
}

/* ------------------------------------------------------------ exhaustive --- */

static Partial *d_pb = NULL;
static Partial h_pb[NBLK];

/* reduce all xi in [1, M-1] on the GPU; returns merged partial */
static Partial gpu_sweep(int K, int L, u64 M)
{
    Partial tot;
    tot.sumRe = tot.sumAbs = tot.sumLog = 0.0;
    tot.nAlpha = tot.nZero = 0; tot.maxMag = -1.0; tot.argmax = 0;
    if (M <= 1) return tot;

    u64 need = M - 1;
    u64 nblk = (need + BS - 1) / BS;
    if (nblk > NBLK) nblk = NBLK;
    skernel<<<(unsigned)nblk, BS>>>(K, L, M, d_pb);
    CK(cudaGetLastError());
    CK(cudaMemcpy(h_pb, d_pb, nblk * sizeof(Partial), cudaMemcpyDeviceToHost));

    long double sRe = 0, sAbs = 0, sLog = 0;
    for (u64 b = 0; b < nblk; b++) {
        sRe += h_pb[b].sumRe; sAbs += h_pb[b].sumAbs; sLog += h_pb[b].sumLog;
        tot.nAlpha += h_pb[b].nAlpha; tot.nZero += h_pb[b].nZero;
        if (h_pb[b].maxMag > tot.maxMag ||
            (h_pb[b].maxMag == tot.maxMag && h_pb[b].argmax < tot.argmax)) {
            tot.maxMag = h_pb[b].maxMag; tot.argmax = h_pb[b].argmax;
        }
    }
    tot.sumRe = (double)sRe; tot.sumAbs = (double)sAbs; tot.sumLog = (double)sLog;
    return tot;
}

static void run_exhaustive(int K0, int K1)
{
    tsv_header();
    for (int K = K0; K <= K1 && K <= K_CAP_EXH; K++) {
        int Ls[8], nL = admissible_band(K, Ls);
        for (int li = 0; li < nL; li++) {
            int L = Ls[li];
            u128 Mw = p2_128(K) - p3_128(L);
            if (Mw >> 62) { fprintf(stderr, "# (K=%d,L=%d): M >= 2^62, skipping exhaustive\n", K, L); continue; }
            u64 M = (u64)Mw;
            long long Mll = (long long)M;
            u128 Cu = binom_u128(K, L);
            long double C = (long double)Cu, logC = logbinom(K, L);
            double t0 = now_sec();

            Partial p = gpu_sweep(K, L, M);
            long double sumRe = p.sumRe, sumAbs = p.sumAbs, sumLog = p.sumLog;
            long double maxMag = p.maxMag;
            long long nAlpha = p.nAlpha, nZero = p.nZero;
            u128 argmax = (u128)p.argmax;

            long double cnt = (sumRe + C) / (long double)M;   /* xi = 0 contributes C */
            long long   div = (long long)llroundl(cnt);
            long double resid = fabsl(cnt - (long double)div);

            long long npos = -1, nreal = -1, ndiv2 = -1;
            if (Cu <= (u128)CLASSIFY_CAP && K <= 62) {
                brute_classify(K, L, Mw, &ndiv2, &npos, &nreal);
                if (ndiv2 != div)
                    fprintf(stderr, "# WARNING (K=%d,L=%d): DP count %lld != brute count %lld\n",
                            K, L, div, ndiv2);
            }

            char mb[48], cb[48], ab[48];
            u128_str(Mw, mb); u128_str(Cu, cb); u128_str(argmax, ab);
            char posb[24] = "-", realb[24] = "-";
            if (npos  >= 0) snprintf(posb,  sizeof posb,  "%lld", npos);
            if (nreal >= 0) snprintf(realb, sizeof realb, "%lld", nreal);

            long double maxRatio  = (Mll > 1 && maxMag >= 0) ? maxMag / C : -1;
            long double meanRatio = (Mll > 1) ? sumAbs / (long double)(Mll - 1) / C : -1;
            long double maxAlpha  = (maxMag > 0 && logC > 0) ? logl((long double)maxMag) / logC : 0;
            long double meanAlpha = (nAlpha > 0 && logC > 0) ? (sumLog / (long double)nAlpha) / logC : 0;

            printf("exhaustive\t%d\t%d\t%s\t%s\t%lld\t%lld\t%.3Lg\t%s\t%s\t"
                   "%.6Lg\t%s\t%.6Lg\t%.6Lf\t%.6Lf\t%lld\t-\t-\n",
                   K, L, mb, cb, Mll, div, resid, posb, realb,
                   maxRatio, ab, meanRatio, maxAlpha, meanAlpha, nZero);
            fflush(stdout);
            fprintf(stderr, "# exhaustive (K=%d,L=%d) M=%s: %.1fs\n", K, L, mb, now_sec() - t0);
        }
    }
}

/* ------------------------------------------------------------- selftest ---- */

static int st_fail = 0;
static void check(int ok, const char *what)
{
    printf("  [%s] %s\n", ok ? "PASS" : "FAIL", what);
    if (!ok) st_fail = 1;
}

static void selftest_dp_vs_brute(void)
{
    struct { int K, L; } cases[] = {{8,3},{10,6},{12,7},{14,8},{15,9},{16,10}};
    u64 seed = 12345;
    long double worst = 0;
    printf("(a) GPU DP vs host brute-force enumeration of S (all-words ensemble)\n");
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        int K = cases[c].K, L = cases[c].L;
        u128 Mw = p2_128(K) - p3_128(L);
        u64 M = (u64)Mw;
        long double C = (long double)binom_u128(K, L);

        u64 xs_h[9]; int nx = 0;
        xs_h[nx++] = 0;                          /* S(0) = C sanity */
        for (int t = 0; t < 8; t++) xs_h[nx++] = (u64)rand_mod(&seed, Mw);

        u64 *d_xs; double2 *d_out; double2 out[9];
        CK(cudaMalloc(&d_xs, nx * sizeof(u64)));
        CK(cudaMalloc(&d_out, nx * sizeof(double2)));
        CK(cudaMemcpy(d_xs, xs_h, nx * sizeof(u64), cudaMemcpyHostToDevice));
        skernel_list<<<1, nx>>>(K, L, M, d_xs, nx, d_out);
        CK(cudaGetLastError());
        CK(cudaMemcpy(out, d_out, nx * sizeof(double2), cudaMemcpyDeviceToHost));
        cudaFree(d_xs); cudaFree(d_out);

        if (fabsl((long double)out[0].x - C) > 1e-9L * (C + 1) || fabsl((long double)out[0].y) > 1e-9L * C)
            { check(0, "S(0) = C(K,L)"); return; }
        for (int t = 1; t < nx; t++) {
            long double br, bi;
            brute_S(K, L, Mw, (u128)xs_h[t], &br, &bi);
            long double dr = (long double)out[t].x - br, di = (long double)out[t].y - bi;
            long double diff = sqrtl(dr * dr + di * di);
            if (diff > worst) worst = diff;
            if (diff > 1e-9L * (C + 1)) {
                printf("    mismatch K=%d L=%d xi=%llu |diff|=%Lg\n", K, L,
                       (unsigned long long)xs_h[t], diff);
                check(0, "GPU DP == brute force"); return;
            }
        }
    }
    printf("    max |S_gpu - S_brute| over all cases: %Lg\n", worst);
    check(1, "GPU DP == host brute force at random xi (tol 1e-9 * C(K,L))");
}

static void selftest_counts(void)
{
    struct { int K, L; } cases[] = {{6,3},{8,5},{13,8},{16,10},{18,11}};
    printf("(b) count check: (1/M) sum_xi S(xi) == #divisible words (brute)\n");
    int allok = 1;
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        int K = cases[c].K, L = cases[c].L;
        u128 Mw = p2_128(K) - p3_128(L);
        u64 M = (u64)Mw;
        long long nd, np, nr;
        brute_classify(K, L, Mw, &nd, &np, &nr);
        Partial p = gpu_sweep(K, L, M);
        long double C = (long double)binom_u128(K, L);
        long double cnt = ((long double)p.sumRe + C) / (long double)M;
        long long cint = (long long)llroundl(cnt);
        char mb[48]; u128_str(Mw, mb);
        printf("    (K=%2d,L=%2d) M=%-8s  gpu_count=%.6Lf  brute=%lld (pos=%lld real=%lld)\n",
               K, L, mb, cnt, nd, np, nr);
        if (cint != nd || fabsl(cnt - (long double)cint) > 1e-6L) allok = 0;
        if (K == 6 && L == 3 && !(nd == 2 && np == 2 && nr == 2 && cint == 2)) allok = 0;
    }
    check(allok, "counts agree and are integral (incl. exact (6,3) = 2)");
}

static int run_selftest(void)
{
    printf("expsum_gpu selftest\n===================\n");
    selftest_dp_vs_brute();
    selftest_counts();
    printf(st_fail ? "SELFTEST: FAIL\n" : "SELFTEST: ALL PASS\n");
    return st_fail;
}

/* ------------------------------------------------------------------ main --- */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "usage: %s selftest\n"
        "       %s exhaustive KMIN KMAX     (K <= %d; loops ALL xi mod M on the GPU)\n",
        argv0, argv0, K_CAP_EXH);
}

int main(int argc, char **argv)
{
    if (argc < 2) { usage(argv[0]); return 2; }
    cudaDeviceProp prop;
    CK(cudaGetDeviceProperties(&prop, 0));
    fprintf(stderr, "# GPU: %s, %d SMs\n", prop.name, prop.multiProcessorCount);
    CK(cudaMalloc(&d_pb, NBLK * sizeof(Partial)));

    if (!strcmp(argv[1], "selftest")) {
        return run_selftest();
    } else if (!strcmp(argv[1], "exhaustive") && argc >= 4) {
        int K0 = atoi(argv[2]), K1 = atoi(argv[3]);
        if (K0 < 2) K0 = 2;
        if (K1 > K_CAP_EXH) { fprintf(stderr, "# capping KMAX at %d\n", K_CAP_EXH); K1 = K_CAP_EXH; }
        run_exhaustive(K0, K1);
        return 0;
    }
    usage(argv[0]);
    return 2;
}
