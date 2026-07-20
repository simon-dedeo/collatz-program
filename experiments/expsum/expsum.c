/* expsum.c — exponential sums S_{K,L}(xi) at the Collatz cycle modulus M = 2^K - 3^L
 *
 * Implements Crack 3 of docs/CRACKS.md ("Exponential sums at the cycle modulus").
 *
 * CONVENTION (derived in README.md, verified numerically by `expsum selftest`):
 *   Accelerated map  T(n) = n/2 (n even),  (3n+q)/2 (n odd);  q=+1 Collatz, q=-1 the 3x-1 map.
 *   For a cycle n_0 -> n_1 -> ... -> n_K = n_0 with parity word v (v_j = n_j mod 2),
 *   L = #ones, and b_0 < ... < b_{L-1} the 0-based positions of the ones:
 *
 *       n_0 * (2^K - 3^L) = q * W(v),      W(v) = sum_{i=0}^{L-1} 3^{L-1-i} * 2^{b_i}.
 *
 *   Note b_i = i + c_i where c_i = #even steps strictly before the (i+1)-th odd step.
 *   The "2^{c_i}" variant of the formula is the PLAIN-map (n -> 3n+q / n/2) convention,
 *   whose modulus is 2^{#halvings} - 3^L; with M = 2^K - 3^L fixed (K = total T-steps)
 *   the exponent must be the position b_i, otherwise even the trivial-cycle words fail
 *   the divisibility test.  Both conventions are verified in the selftest (trivial cycle;
 *   3x-1 cycles {1}, {5,7,10}, the 17-cycle; plain-map {5,14,7,20,10}).
 *
 * OBJECT:
 *   S_{K,L}(xi) = sum over all C(K,L) length-K words v with L ones of e(xi*W(v)/M),
 *   e(x) = exp(2 pi i x), M = 2^K - 3^L > 0.  Orthogonality gives
 *       #{v : M | W(v)} = (1/M) * sum_{xi mod M} S_{K,L}(xi),      S(0) = C(K,L).
 *   Divisible words are only NECESSARY for integer cycles (need also W/M >= 1 and the
 *   word to be the actual parity word of n = W/M); count = 0 excludes the signature.
 *
 * DP: process positions j = 0..K-1, state i = #ones placed so far (0..L).
 *   Placing the (i+1)-th one at position j contributes phase r(i,j) = xi*3^{L-1-i}*2^j mod M.
 *   Maintained incrementally: R[i] <- xi*3^{L-1-i} mod M at j=0, doubled mod M each j.
 *   O(K*L) complex ops per xi; exact integer phases as u128 (needs M < 2^126).
 *
 * ROTATION COVARIANCE (proved in README, verified here):
 *   left rotation rho:  v_0 = 0  =>  W(v) = 2 W(rho v)          (exact integers)
 *                       v_0 = 1  =>  3 W(v) + M = 2 W(rho v)    (exact integers)
 *   Corollary: S(2 xi) = S_0(xi) + S_1(3 xi)  (S_b = sum restricted to words with v_0=b).
 *   The naive symmetry |S(2 xi)| = |S(xi)| is NOT a consequence and is FALSE in general
 *   (counterexample K=3, L=1, M=5); the selftest measures its violation and verifies the
 *   intertwining relation to machine precision.  Consequently sampled mode treats
 *   <2>-orbit constancy of |S| as a hypothesis to be measured (orbit_dev column),
 *   not as a dedup rule.
 *
 * MODES:
 *   expsum selftest
 *       (a) DP vs brute-force enumeration of S at random xi (K <= 16, all ensembles);
 *       (b) count check: (1/M) sum_xi S == brute count of divisible words (M <= 1e5),
 *           plus exact known values for (6,3);
 *       (c) cycle-equation verification (convention checks listed above);
 *       (d) symmetry: naive |S(2xi)|=|S(xi)| (measured), intertwining (must pass),
 *           conjugation |S(-xi)|=|S(xi)| (must pass).
 *   expsum exhaustive KMIN KMAX
 *       For admissible signatures (L in floor(K*log2/log3)-2 .. +2, M > 0), loop ALL
 *       xi mod M (OpenMP), record max_{xi!=0}|S|/C, argmax, mean, log|S|/log C stats,
 *       and divisible count (1/M) sum_xi S; when C(K,L) <= 5e7 also brute-classify
 *       divisible words: n_pos = those with W/M >= 1, n_real = realizable parity words
 *       (actual integer cycles; expect only trivial-cycle words).  Cap K <= 40.
 *   expsum sampled KMIN KMAX [NRAND] [SEED] [NORBITS]
 *       xi in {1..1000} + NRAND randoms (default 100000, fixed seed) + NORBITS
 *       <2>-orbit sweeps (diagnostic).  Cap K <= 118 (u128 phases; K > 118 needs
 *       big-int — out of scope for v1).
 *
 * OUTPUT: one TSV row per (K,L) on stdout; progress on stderr.  Columns:
 *   mode K L M C n_xi div_count resid n_pos n_real max_ratio argmax_xi mean_ratio
 *   max_alpha mean_alpha n_zeroS orbit_dev top5_xi
 *   where ratio = |S|/C(K,L), alpha = ln|S|/ln C  (sqrt cancellation <=> alpha ~ 0.5),
 *   resid = |(1/M) sum S - nearest integer| (accumulation sanity), n_zeroS = #xi with
 *   |S| < 1e-12 (excluded from alpha stats), orbit_dev = max over sampled <2>-orbits of
 *   (max|S| - min|S|)/C along the orbit.
 *
 * Build:  cc -O2 -Wall -Wextra -o expsum expsum.c -lm          (sequential)
 *         gcc -O2 -Wall -Wextra -fopenmp -o expsum expsum.c -lm (OpenMP)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <complex.h>
#include <time.h>

#ifdef _OPENMP
#  include <omp.h>
#  define OMP(x) _Pragma(x)
#else
#  define OMP(x)
#endif

typedef unsigned __int128 u128;
typedef __int128          i128;
typedef uint64_t          u64;
typedef long double complex lcplx;

#define LMAX        100          /* max L handled by the DP                      */
#define K_CAP_EXH    40          /* exhaustive mode cap                          */
#define K_CAP_SAMP  118          /* sampled mode cap (M < 2^126 for u128 phases) */
#define CLASSIFY_CAP 50000000ULL /* classify words when C(K,L) <= this           */

static const long double TWOPI = 6.283185307179586476925286766559005768L;

/* ------------------------------------------------------------------ utils -- */

static void u128_str(u128 v, char *buf)
{
    char t[48]; int i = 0, j = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) buf[j++] = t[--i];
    buf[j] = 0;
}

static void i128_str(i128 v, char *buf)
{
    if (v < 0) { *buf++ = '-'; u128_str((u128)(-v), buf); }
    else u128_str((u128)v, buf);
}

static u128 p2_128(int k) { return (u128)1 << k; }              /* k <= 126 */
static u128 p3_128(int l) { u128 r = 1; while (l-- > 0) r *= 3; return r; } /* l <= 80 */

static inline u128 addmod128(u128 a, u128 b, u128 m)  /* a,b < m < 2^127 */
{ a += b; if (a >= m) a -= m; return a; }

static inline u128 dblmod128(u128 a, u128 m)          /* a < m < 2^127 */
{ a <<= 1; if (a >= m) a -= m; return a; }

static u128 mulmod128(u128 a, u128 b, u128 m)          /* peasant; m < 2^126 */
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

static u128 binom_u128(int K, int L)                   /* exact; caller keeps it small */
{
    if (L < 0 || L > K) return 0;
    if (L > K - L) L = K - L;
    u128 c = 1;
    for (int i = 1; i <= L; i++) { c = c * (u128)(K - L + i) / (u128)i; }
    return c;
}

static long double logbinom(int K, int L)              /* natural log of C(K,L) */
{ return lgammal((long double)K + 1) - lgammal((long double)L + 1) - lgammal((long double)(K - L) + 1); }

/* splitmix64 */
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

/* ------------------------------------------------------- core DP for S ----- */
/* first_bit: -1 = all words; 0 = words with v_0 = 0; 1 = words with v_0 = 1.  */
static lcplx dp_S(int K, int L, u128 M, u128 xi, int first_bit)
{
    u128  R[LMAX];
    lcplx A[LMAX + 1];

    if (L < 1 || L > K || L > LMAX) return 0;
    xi %= M;

    R[L - 1] = xi;                                  /* xi * 3^0 */
    for (int i = L - 2; i >= 0; i--)                /* R[i] = 3*R[i+1] mod M   */
        R[i] = addmod128(dblmod128(R[i + 1], M), R[i + 1], M);

    for (int i = 0; i <= L; i++) A[i] = 0;
    A[0] = 1;

    for (int j = 0; j < K; j++) {
        if (!(j == 0 && first_bit == 0)) {          /* option: place a '1' here */
            int hi = (j < L - 1) ? j : L - 1;
            for (int i = hi; i >= 0; i--) {
                long double a = TWOPI * (long double)R[i] / (long double)M;
                A[i + 1] += A[i] * (cosl(a) + sinl(a) * I);
            }
        }
        if (j == 0 && first_bit == 1) A[0] = 0;     /* '1' at position 0 forced */
        for (int i = 0; i < L; i++) R[i] = dblmod128(R[i], M);
    }
    return A[L];
}

/* -------------------------------------------- brute force (selftest only) -- */

static u64 gosper_next(u64 mask)
{
    u64 c = mask & (~mask + 1ULL);
    u64 r = mask + c;
    return (((r ^ mask) >> 2) / c) | r;
}

static lcplx brute_S(int K, int L, u128 M, u128 xi, int first_bit)
{
    lcplx s = 0;
    u128 pw3[LMAX], pw2[64];
    u64 top = 1ULL << K;

    if (L < 1 || L > K || K > 24) return 0;
    pw3[0] = 1 % M;
    for (int t = 1; t < L; t++) pw3[t] = mulmod128(pw3[t - 1], 3, M);
    pw2[0] = 1 % M;
    for (int j = 1; j < K; j++) pw2[j] = dblmod128(pw2[j - 1], M);
    xi %= M;

    for (u64 mask = (1ULL << L) - 1; mask < top; ) {
        int keep = (first_bit < 0) || ((int)(mask & 1ULL) == first_bit);
        if (keep) {
            u128 w = 0; int i = 0;
            for (int j = 0; j < K; j++)
                if ((mask >> j) & 1ULL) { w = addmod128(w, mulmod128(pw3[L - 1 - i], pw2[j], M), M); i++; }
            u128 r = mulmod128(xi, w, M);
            long double a = TWOPI * (long double)r / (long double)M;
            s += cosl(a) + sinl(a) * I;
        }
        u64 nx = gosper_next(mask);
        if (nx <= mask || nx >= top) break;
        mask = nx;
    }
    return s;
}

/* enumerate words; count M|W, W/M >= 1, and realizable parity words (q=+1) */
static int brute_classify(int K, int L, u128 M,
                          long long *n_div, long long *n_pos, long long *n_real)
{
    if (K > 62 || L < 1 || L > K) return 0;
    if (binom_u128(K, L) > (u128)CLASSIFY_CAP) return 0;

    u128 pw3[LMAX];
    pw3[0] = 1;
    for (int t = 1; t < L; t++) pw3[t] = pw3[t - 1] * 3;   /* exact: W < 2^126 for K<=40 */

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

/* (1/M) sum_xi S(xi) via the DP (parallel over xi) */
static long double count_by_dp(int K, int L, u128 M)
{
    long long Mll = (long long)M;
    long double sum = 0;
    OMP("omp parallel")
    {
        long double loc = 0;
        OMP("omp for schedule(dynamic,256) nowait")
        for (long long x = 0; x < Mll; x++)
            loc += creall(dp_S(K, L, M, (u128)x, -1));
        OMP("omp critical")
        { sum += loc; }
    }
    return sum / (long double)M;
}

/* --------------------------------------------- cycle-equation verification -- */
/* accelerated map T(n) = n/2 | (3n+q)/2; returns 1 iff n0*M == q*W around the cycle */
static int verify_cycle_acc(u64 n0, int q, int *Kout, int *Lout, i128 *Mout, i128 *Wout)
{
    int bits[200], K = 0, L = 0;
    i128 n = (i128)n0;
    do {
        if (K >= 200) return 0;
        int v = (int)(n & 1);
        bits[K++] = v; L += v;
        n = v ? (3 * n + q) / 2 : n / 2;
        if (n <= 0) return 0;
    } while (n != (i128)n0);

    i128 M = (i128)p2_128(K) - (i128)p3_128(L);
    i128 W = 0; int i = 0;
    for (int j = 0; j < K; j++)
        if (bits[j]) { W += (i128)p3_128(L - 1 - i) * (i128)p2_128(j); i++; }
    *Kout = K; *Lout = L; *Mout = M; *Wout = W;
    return (i128)n0 * M == (i128)q * W;
}

/* plain map U(n) = n/2 | 3n+q; modulus 2^E - 3^L, exponents c_i = #halvings before */
static int verify_cycle_plain(u64 n0, int q, int *Eout, int *Lout, i128 *Mout, i128 *Wout)
{
    int codd[200], L = 0, E = 0, steps = 0;
    i128 n = (i128)n0;
    do {
        if (steps++ >= 400) return 0;
        if (n & 1) { if (L >= 200) return 0; codd[L++] = E; n = 3 * n + q; }
        else       { E++; n /= 2; }
        if (n <= 0) return 0;
    } while (n != (i128)n0);

    i128 M = (i128)p2_128(E) - (i128)p3_128(L);
    i128 W = 0;
    for (int i = 0; i < L; i++)
        W += (i128)p3_128(L - 1 - i) * (i128)p2_128(codd[i]);
    *Eout = E; *Lout = L; *Mout = M; *Wout = W;
    return (i128)n0 * M == (i128)q * W;
}

/* ------------------------------------------------------- admissible band --- */
/* L in floor(K*log2/log3) - 2 .. + 2, clamped to [1, K-1], M = 2^K - 3^L > 0  */
static int admissible_band(int K, int *Ls)
{
    int L0 = (int)floorl((long double)K * logl(2.0L) / logl(3.0L));
    int n = 0;
    for (int d = -2; d <= 2; d++) {
        int L = L0 + d;
        if (L < 1 || L >= K || L > LMAX) continue;
        if ((long double)L * logl(3.0L) >= (long double)K * logl(2.0L)) continue; /* M <= 0 */
        if (p3_128(L) >= p2_128(K)) continue;                                     /* exact  */
        Ls[n++] = L;
    }
    return n;
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
    printf("(a) DP vs brute-force enumeration of S (all/first0/first1 ensembles)\n");
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        int K = cases[c].K, L = cases[c].L;
        u128 M = p2_128(K) - p3_128(L);
        long double C = (long double)binom_u128(K, L);
        for (int fb = -1; fb <= 1; fb++) {
            /* xi = 0 sanity: S(0) counts the ensemble */
            lcplx s0 = dp_S(K, L, M, 0, fb);
            long double expect = (fb < 0) ? C
                               : (fb == 0) ? (long double)binom_u128(K - 1, L)
                                           : (long double)binom_u128(K - 1, L - 1);
            if (fabsl(creall(s0) - expect) > 1e-9L * (expect + 1) || fabsl(cimagl(s0)) > 1e-9L)
                { check(0, "S(0) = ensemble size"); return; }
            for (int t = 0; t < 4; t++) {
                u128 xi = rand_mod(&seed, M);
                lcplx d = dp_S(K, L, M, xi, fb), b = brute_S(K, L, M, xi, fb);
                long double diff = cabsl(d - b);
                if (diff > worst) worst = diff;
                if (diff > 1e-12L * (C + 1)) {
                    char mb[48]; u128_str(xi, mb);
                    printf("    mismatch K=%d L=%d fb=%d xi=%s |diff|=%Lg\n", K, L, fb, mb, diff);
                    check(0, "DP == brute force"); return;
                }
            }
        }
    }
    printf("    max |S_dp - S_brute| over all cases: %Lg\n", worst);
    check(1, "DP == brute force at random xi (tol 1e-12 * C(K,L))");
}

static void selftest_counts(void)
{
    struct { int K, L; } cases[] = {{8,5},{13,8},{16,10},{18,11}};
    printf("(b) count check: (1/M) sum_xi S(xi) == #divisible words (brute)\n");
    int allok = 1;
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        int K = cases[c].K, L = cases[c].L;
        u128 M = p2_128(K) - p3_128(L);
        long long nd, np, nr;
        brute_classify(K, L, M, &nd, &np, &nr);
        long double cnt = count_by_dp(K, L, M);
        long long cint = (long long)llroundl(cnt);
        char mb[48]; u128_str(M, mb);
        printf("    (K=%2d,L=%2d) M=%-8s  dp_count=%.6Lf  brute=%lld (pos=%lld real=%lld)\n",
               K, L, mb, cnt, nd, np, nr);
        if (cint != nd || fabsl(cnt - (long double)cint) > 1e-6L) allok = 0;
    }
    check(allok, "counts agree and are integral");

    /* exact known value: (6,3), M=37 — exactly the 2 rotations of (10)^3, n = 1 */
    {
        u128 M = p2_128(6) - p3_128(3);
        long long nd, np, nr;
        brute_classify(6, 3, M, &nd, &np, &nr);
        long double cnt = count_by_dp(6, 3, M);
        printf("    (K= 6,L= 3) M=37       dp_count=%.6Lf  brute=%lld (pos=%lld real=%lld)\n",
               cnt, nd, np, nr);
        check(nd == 2 && np == 2 && nr == 2 && llroundl(cnt) == 2,
              "(6,3): exactly 2 divisible words, both = trivial cycle (n=1)");
    }
}

static void selftest_cycles(void)
{
    printf("(c) cycle-equation verification: n * (2^K - 3^L) = q * W(v)\n");
    struct { u64 n; int q, K, L; long long M, W; const char *what; } acc[] = {
        { 1, +1,  2, 1,    1,    1, "3x+1 trivial cycle {1,2}, word 10"            },
        { 1, -1,  1, 1,   -1,    1, "3x-1 fixed point {1}, word 1"                 },
        { 5, -1,  3, 2,   -1,    5, "3x-1 cycle {5,7,10} (= plain {5,14,7,20,10})" },
        {17, -1, 11, 7, -139, 2363, "3x-1 17-cycle (K=11, L=7)"                    },
    };
    for (size_t c = 0; c < sizeof acc / sizeof acc[0]; c++) {
        int K, L; i128 M, W;
        int ok = verify_cycle_acc(acc[c].n, acc[c].q, &K, &L, &M, &W);
        char mb[48], wb[48]; i128_str(M, mb); i128_str(W, wb);
        printf("    accel n=%-2llu q=%+d: K=%d L=%d M=%s W=%s  (%s)\n",
               (unsigned long long)acc[c].n, acc[c].q, K, L, mb, wb, acc[c].what);
        ok = ok && K == acc[c].K && L == acc[c].L
                && M == (i128)acc[c].M && W == (i128)acc[c].W;
        check(ok, acc[c].what);
    }
    /* plain-map convention: modulus 2^E - 3^L, exponents c_i = #halvings before */
    struct { u64 n; int q, E, L; long long M, W; const char *what; } pl[] = {
        { 1, +1, 2, 1,  1, 1, "plain 3x+1 trivial {1,4,2}: 1*(2^2-3^1) = W = 1"      },
        { 5, -1, 3, 2, -1, 5, "plain 3x-1 {5,14,7,20,10}: 5*(2^3-3^2) = -W, W = 5"   },
    };
    for (size_t c = 0; c < sizeof pl / sizeof pl[0]; c++) {
        int E, L; i128 M, W;
        int ok = verify_cycle_plain(pl[c].n, pl[c].q, &E, &L, &M, &W);
        char mb[48], wb[48]; i128_str(M, mb); i128_str(W, wb);
        printf("    plain n=%-2llu q=%+d: E=%d L=%d M=%s W=%s  (%s)\n",
               (unsigned long long)pl[c].n, pl[c].q, E, L, mb, wb, pl[c].what);
        ok = ok && E == pl[c].E && L == pl[c].L
                && M == (i128)pl[c].M && W == (i128)pl[c].W;
        check(ok, pl[c].what);
    }
}

static void selftest_symmetry(void)
{
    struct { int K, L; } cases[] = {{14,8},{16,10},{18,11}};
    u64 seed = 987654321;
    long double worst_naive = 0, worst_naive1 = 0, worst_inter = 0, worst_conj = 0;
    printf("(d) symmetry checks over 100 random xi per signature\n");
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        int K = cases[c].K, L = cases[c].L;
        u128 M = p2_128(K) - p3_128(L);
        long double C  = (long double)binom_u128(K, L);
        long double C1 = (long double)binom_u128(K - 1, L - 1);
        for (int t = 0; t < 100; t++) {
            u128 xi  = 1 + rand_mod(&seed, M - 1);
            u128 xi2 = dblmod128(xi, M);
            u128 xi3 = addmod128(xi2, xi, M);
            lcplx S    = dp_S(K, L, M, xi,  -1);
            lcplx S2   = dp_S(K, L, M, xi2, -1);
            lcplx S0   = dp_S(K, L, M, xi,   0);
            lcplx S13  = dp_S(K, L, M, xi3,  1);
            lcplx S1   = dp_S(K, L, M, xi,   1);
            lcplx S12  = dp_S(K, L, M, xi2,  1);
            lcplx Sm   = dp_S(K, L, M, M - xi, -1);
            long double dn  = fabsl(cabsl(S2) - cabsl(S)) / C;
            long double dn1 = fabsl(cabsl(S12) - cabsl(S1)) / C1;
            long double di  = cabsl(S2 - (S0 + S13)) / C;
            long double dc  = fabsl(cabsl(Sm) - cabsl(S)) / C;
            if (dn  > worst_naive)  worst_naive  = dn;
            if (dn1 > worst_naive1) worst_naive1 = dn1;
            if (di  > worst_inter)  worst_inter  = di;
            if (dc  > worst_conj)   worst_conj   = dc;
        }
    }
    printf("    naive |S(2xi)|=|S(xi)| (all words):      max dev/C  = %Lg  -> %s\n",
           worst_naive, worst_naive < 1e-9L ? "HOLDS" : "FAILS");
    printf("    naive |S1(2xi)|=|S1(xi)| (v_0=1 words):  max dev/C1 = %Lg  -> %s\n",
           worst_naive1, worst_naive1 < 1e-9L ? "HOLDS" : "FAILS");
    printf("    intertwining S(2xi) = S0(xi) + S1(3xi):  max dev/C  = %Lg\n", worst_inter);
    printf("    conjugation |S(M-xi)| = |S(xi)|:         max dev/C  = %Lg\n", worst_conj);
    check(worst_inter < 1e-9L, "exact intertwining S(2xi) = S0(xi) + S1(3xi)");
    check(worst_conj  < 1e-9L, "conjugation symmetry |S(-xi)| = |S(xi)|");
    printf("    NOTE: the naive <2>-orbit symmetry is expected to FAIL; the rotation\n"
           "    covariance yields the intertwining above instead (see README).\n");
}

static int run_selftest(void)
{
    printf("expsum selftest\n===============\n");
    selftest_cycles();
    selftest_dp_vs_brute();
    selftest_counts();
    selftest_symmetry();
    printf(st_fail ? "SELFTEST: FAIL\n" : "SELFTEST: ALL PASS\n");
    return st_fail;
}

/* --------------------------------------------------------------- output ---- */

static void tsv_header(void)
{
    printf("mode\tK\tL\tM\tC\tn_xi\tdiv_count\tresid\tn_pos\tn_real\t"
           "max_ratio\targmax_xi\tmean_ratio\tmax_alpha\tmean_alpha\tn_zeroS\torbit_dev\ttop5_xi\n");
}

/* ------------------------------------------------------------ exhaustive --- */

static void run_exhaustive(int K0, int K1)
{
    tsv_header();
    for (int K = K0; K <= K1 && K <= K_CAP_EXH; K++) {
        int Ls[8], nL = admissible_band(K, Ls);
        for (int li = 0; li < nL; li++) {
            int L = Ls[li];
            u128 M = p2_128(K) - p3_128(L);
            if (M >> 62) { fprintf(stderr, "# (K=%d,L=%d): M >= 2^62, skipping exhaustive\n", K, L); continue; }
            long long Mll = (long long)M;
            u128 Cu = binom_u128(K, L);
            long double C = (long double)Cu, logC = logbinom(K, L);
            double t0 = now_sec();

            long double sumRe = 0, sumAbs = 0, sumLog = 0, maxMag = -1;
            long long nAlpha = 0, nZero = 0;
            u128 argmax = 0;

            OMP("omp parallel")
            {
                long double lRe = 0, lAbs = 0, lLog = 0, lMax = -1;
                long long lnA = 0, lnZ = 0; u128 lArg = 0;
                OMP("omp for schedule(dynamic,256) nowait")
                for (long long x = 1; x < Mll; x++) {
                    lcplx s = dp_S(K, L, M, (u128)x, -1);
                    long double mag = cabsl(s);
                    lRe += creall(s);
                    lAbs += mag;
                    if (mag > 1e-12L) {
                        lLog += logl(mag); lnA++;
                        if (mag > lMax) { lMax = mag; lArg = (u128)x; }
                    } else lnZ++;
                }
                OMP("omp critical")
                {
                    sumRe += lRe; sumAbs += lAbs; sumLog += lLog;
                    nAlpha += lnA; nZero += lnZ;
                    if (lMax > maxMag) { maxMag = lMax; argmax = lArg; }
                }
            }

            long double cnt = (sumRe + C) / (long double)M;   /* xi = 0 contributes C */
            long long   div = (long long)llroundl(cnt);
            long double resid = fabsl(cnt - (long double)div);

            long long npos = -1, nreal = -1, ndiv2 = -1;
            if (Cu <= (u128)CLASSIFY_CAP && K <= 62) {
                brute_classify(K, L, M, &ndiv2, &npos, &nreal);
                if (ndiv2 != div)
                    fprintf(stderr, "# WARNING (K=%d,L=%d): DP count %lld != brute count %lld\n",
                            K, L, div, ndiv2);
            }

            char mb[48], cb[48], ab[48];
            u128_str(M, mb); u128_str(Cu, cb); u128_str(argmax, ab);
            char posb[24] = "-", realb[24] = "-";
            if (npos  >= 0) snprintf(posb,  sizeof posb,  "%lld", npos);
            if (nreal >= 0) snprintf(realb, sizeof realb, "%lld", nreal);

            long double maxRatio  = (Mll > 1 && maxMag >= 0) ? maxMag / C : -1;
            long double meanRatio = (Mll > 1) ? sumAbs / (long double)(Mll - 1) / C : -1;
            long double maxAlpha  = (maxMag > 0 && logC > 0) ? logl(maxMag) / logC : 0;
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

/* --------------------------------------------------------------- sampled --- */

typedef struct { long double mag; u128 xi; } Top;

static void top5_insert(Top *t, long double mag, u128 xi)
{
    if (mag <= t[4].mag) return;
    t[4].mag = mag; t[4].xi = xi;
    for (int i = 4; i > 0 && t[i].mag > t[i - 1].mag; i--) {
        Top tmp = t[i]; t[i] = t[i - 1]; t[i - 1] = tmp;
    }
}

static void run_sampled(int K0, int K1, long long nrand, u64 seed0, int norbits)
{
    tsv_header();
    for (int K = K0; K <= K1 && K <= K_CAP_SAMP; K++) {
        int Ls[8], nL = admissible_band(K, Ls);
        for (int li = 0; li < nL; li++) {
            int L = Ls[li];
            u128 M = p2_128(K) - p3_128(L);
            u128 Cu = binom_u128(K, L);
            long double C = expl(logbinom(K, L)), logC = logbinom(K, L);
            double t0 = now_sec();

            /* xi list: 1..1000, then nrand randoms (fixed seed per signature) */
            long long nseq = (M - 1 < (u128)1000) ? (long long)(M - 1) : 1000;
            long long nxi = nseq + nrand;
            u128 *xs = (u128 *)malloc((size_t)nxi * sizeof(u128));
            if (!xs) { fprintf(stderr, "malloc failed\n"); exit(2); }
            for (long long t = 0; t < nseq; t++) xs[t] = (u128)(t + 1);
            u64 seed = seed0 ^ (u64)(K * 1000003 + L);
            for (long long t = 0; t < nrand; t++) xs[nseq + t] = 1 + rand_mod(&seed, M - 1);

            long double sumAbs = 0, sumLog = 0, maxMag = -1;
            long long nAlpha = 0, nZero = 0;
            u128 argmax = 0;
            Top top[5]; for (int i = 0; i < 5; i++) { top[i].mag = -1; top[i].xi = 0; }

            OMP("omp parallel")
            {
                long double lAbs = 0, lLog = 0, lMax = -1;
                long long lnA = 0, lnZ = 0; u128 lArg = 0;
                Top ltop[5]; for (int i = 0; i < 5; i++) { ltop[i].mag = -1; ltop[i].xi = 0; }
                OMP("omp for schedule(dynamic,64) nowait")
                for (long long t = 0; t < nxi; t++) {
                    lcplx s = dp_S(K, L, M, xs[t], -1);
                    long double mag = cabsl(s);
                    lAbs += mag;
                    if (mag > 1e-12L) {
                        lLog += logl(mag); lnA++;
                        if (mag > lMax) { lMax = mag; lArg = xs[t]; }
                        top5_insert(ltop, mag, xs[t]);
                    } else lnZ++;
                }
                OMP("omp critical")
                {
                    sumAbs += lAbs; sumLog += lLog; nAlpha += lnA; nZero += lnZ;
                    if (lMax > maxMag) { maxMag = lMax; argmax = lArg; }
                    for (int i = 0; i < 5; i++)
                        if (ltop[i].mag > 0) top5_insert(top, ltop[i].mag, ltop[i].xi);
                }
            }

            /* <2>-orbit sweeps: measure |S| variation along xi, 2xi, 4xi, ... */
            long double orbitDev = 0;
            for (int o = 0; o < norbits; o++) {
                u128 xi0 = 1 + rand_mod(&seed, M - 1), xi = xi0;
                long double mn = -1, mx = -1;
                for (int t = 0; t < 192; t++) {
                    long double mag = cabsl(dp_S(K, L, M, xi, -1));
                    if (mn < 0 || mag < mn) mn = mag;
                    if (mag > mx) mx = mag;
                    xi = dblmod128(xi, M);
                    if (xi == xi0) break;
                }
                long double dev = (mx - mn) / C;
                if (dev > orbitDev) orbitDev = dev;
            }

            char mb[48], cb[48], ab[48];
            u128_str(M, mb); u128_str(Cu, cb); u128_str(argmax, ab);
            char topbuf[512]; topbuf[0] = 0;
            for (int i = 0; i < 5 && top[i].mag > 0; i++) {
                char xb[48]; u128_str(top[i].xi, xb);
                char item[96];
                snprintf(item, sizeof item, "%s%s:%.4Lg", i ? "," : "", xb, top[i].mag / C);
                strncat(topbuf, item, sizeof topbuf - strlen(topbuf) - 1);
            }

            long double maxRatio  = (maxMag >= 0) ? maxMag / C : -1;
            long double meanRatio = (nxi > 0) ? sumAbs / (long double)nxi / C : -1;
            long double maxAlpha  = (maxMag > 0 && logC > 0) ? logl(maxMag) / logC : 0;
            long double meanAlpha = (nAlpha > 0 && logC > 0) ? (sumLog / (long double)nAlpha) / logC : 0;

            printf("sampled\t%d\t%d\t%s\t%s\t%lld\t-\t-\t-\t-\t"
                   "%.6Lg\t%s\t%.6Lg\t%.6Lf\t%.6Lf\t%lld\t%.3Lg\t%s\n",
                   K, L, mb, cb, nxi, maxRatio, ab, meanRatio, maxAlpha, meanAlpha,
                   nZero, orbitDev, topbuf);
            fflush(stdout);
            fprintf(stderr, "# sampled (K=%d,L=%d) M=%s n_xi=%lld: %.1fs\n",
                    K, L, mb, nxi, now_sec() - t0);
            free(xs);
        }
    }
}

/* ------------------------------------------------------------------ main --- */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "usage: %s selftest\n"
        "       %s exhaustive KMIN KMAX              (K <= %d; loops ALL xi mod M)\n"
        "       %s sampled KMIN KMAX [NRAND] [SEED] [NORBITS]\n"
        "                                             (K <= %d; default NRAND=100000,\n"
        "                                              SEED=20260720, NORBITS=3)\n",
        argv0, argv0, K_CAP_EXH, argv0, K_CAP_SAMP);
}

int main(int argc, char **argv)
{
    if (argc < 2) { usage(argv[0]); return 2; }
#ifdef _OPENMP
    fprintf(stderr, "# OpenMP enabled, max threads = %d\n", omp_get_max_threads());
#else
    fprintf(stderr, "# sequential build (no OpenMP)\n");
#endif
    if (!strcmp(argv[1], "selftest")) {
        return run_selftest();
    } else if (!strcmp(argv[1], "exhaustive") && argc >= 4) {
        int K0 = atoi(argv[2]), K1 = atoi(argv[3]);
        if (K0 < 2) K0 = 2;
        if (K1 > K_CAP_EXH) { fprintf(stderr, "# capping KMAX at %d\n", K_CAP_EXH); K1 = K_CAP_EXH; }
        run_exhaustive(K0, K1);
        return 0;
    } else if (!strcmp(argv[1], "sampled") && argc >= 4) {
        int K0 = atoi(argv[2]), K1 = atoi(argv[3]);
        long long nrand = (argc > 4) ? atoll(argv[4]) : 100000;
        u64 seed = (argc > 5) ? (u64)strtoull(argv[5], NULL, 10) : 20260720ULL;
        int norbits = (argc > 6) ? atoi(argv[6]) : 3;
        if (K0 < 2) K0 = 2;
        if (K1 > K_CAP_SAMP) { fprintf(stderr, "# capping KMAX at %d (u128 phase limit; K > %d needs big-int)\n", K_CAP_SAMP, K_CAP_SAMP); K1 = K_CAP_SAMP; }
        run_sampled(K0, K1, nrand, seed, norbits);
        return 0;
    }
    usage(argv[0]);
    return 2;
}
