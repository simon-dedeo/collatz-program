/* fate.c — orbit-fate census for Collatz-like maps
 *
 *   f(x) = x/2        if x even
 *   f(x) = A*x + B    if x odd        (A, B from command line; B may be negative)
 *
 * For every n in [1, N] (sequential blocks, parallel within a block) we classify
 * the orbit of n:
 *   - it drops below the current block base  -> inherit the recorded fate
 *   - it enters a cycle (Brent detection)    -> cycle registered by its minimum
 *   - it exceeds 2^120                       -> "overflow" (presumed divergent)
 *   - it runs STEPCAP steps without any of the above -> "cap" (investigate!)
 *
 * Any cycle is discovered exactly when n = (cycle minimum), because that orbit
 * never drops below its start. Discoveries are appended to a log immediately.
 * For (A,B) = (3,1) any registered cycle with min > 1, or any overflow/cap,
 * would be a disproof-grade event.
 *
 * Output: one TSV row per block with fate counts and the block's max excursion.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o fate fate.c   (Linux)
 *         cc -O3 -o fate fate.c                            (macOS, sequential)
 * Usage:  ./fate A B N [BLK] [OUTDIR]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#else
static int omp_get_thread_num(void) { return 0; }
static int omp_get_max_threads(void) { return 1; }
#endif

typedef unsigned __int128 u128;
typedef uint64_t u64;

static u64 A = 3;
static int64_t B = 1;

#define MAXCYC 64
#define F_OVER 201
#define F_CAP  202
static const u64 STEPCAP = 200000;
#define MAXV (((u128)1) << 120)

static u128 cyc_min[MAXCYC];
static u64 cyc_len[MAXCYC];
static int ncyc = 0;
static FILE *disc = NULL;

static inline u128 stepf(u128 x) {
    if ((x & 1) == 0) return x >> 1;
    return (u128)A * x + (u128)(__int128)B; /* wraparound add == subtraction for B<0; safe since A*x > |B| and x <= 2^120 */
}

static void u128str(u128 v, char *buf) {
    char t[48]; int i = 0, j = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) buf[j++] = t[--i];
    buf[j] = 0;
}

/* must be called inside a critical section */
static int register_cycle(u128 mn, u64 len) {
    for (int i = 0; i < ncyc; i++)
        if (cyc_min[i] == mn) return i + 1;
    if (ncyc == MAXCYC) { fprintf(stderr, "cycle registry full!\n"); exit(3); }
    cyc_min[ncyc] = mn; cyc_len[ncyc] = len; ncyc++;
    char b[48]; u128str(mn, b);
    fprintf(disc, "CYCLE map=%llu*x%+lld min=%s len=%llu\n",
            (unsigned long long)A, (long long)B, b, (unsigned long long)len);
    fflush(disc);
    return ncyc;
}

typedef struct { int code; u128 exc; } Res;

/* Classify orbit of n. Fates of all m < base are already final in fate[]. */
static Res classify(u64 n, u64 base, const uint8_t *fate) {
    u128 x = n, exc = n, tortoise = n;
    u64 power = 1, lam = 0, steps = 0;
    for (;;) {
        if (x > MAXV) return (Res){F_OVER, exc};
        x = stepf(x);
        steps++; lam++;
        if (x > exc) exc = x;
        if (x < (u128)base) return (Res){fate[(u64)x], exc};
        if (x == tortoise) break;                 /* cycle of length lam */
        if (lam == power) { tortoise = x; power <<= 1; lam = 0; }
        if (steps > STEPCAP) return (Res){F_CAP, exc};
    }
    u128 mn = x, y = stepf(x);
    while (y != x) { if (y < mn) mn = y; y = stepf(y); }
    int code;
#ifdef _OPENMP
#pragma omp critical(registry)
#endif
    code = register_cycle(mn, lam);
    return (Res){code, exc};
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s A B N [BLK] [OUTDIR]\n", argv[0]); return 1; }
    A = (u64)atoll(argv[1]);
    B = (int64_t)atoll(argv[2]);
    u64 N = (u64)atoll(argv[3]);
    u64 BLK = argc > 4 ? (u64)atoll(argv[4]) : 10000000ULL;
    const char *outdir = argc > 5 ? argv[5] : "results";

    uint8_t *fate = (uint8_t *)malloc(N + 1);
    if (!fate) { fprintf(stderr, "cannot allocate %llu bytes\n", (unsigned long long)(N + 1)); return 2; }
    memset(fate, 0, N + 1);

    char path[512];
    snprintf(path, sizeof path, "%s/fate_A%llu_B%lld_N%llu.tsv",
             outdir, (unsigned long long)A, (long long)B, (unsigned long long)N);
    FILE *out = fopen(path, "w");
    snprintf(path, sizeof path, "%s/discoveries_A%llu_B%lld.log",
             outdir, (unsigned long long)A, (long long)B);
    disc = fopen(path, "a");
    if (!out || !disc) { fprintf(stderr, "cannot open output files in %s\n", outdir); return 2; }

    fprintf(out, "base\thi\tc1\tc2\tc3\tc4\tc5\tc6\tc7\tc8\toverflow\tcap\texc_log2\texc_argn\n");
    time_t t0 = time(NULL);

    for (u64 base = 1; base <= N; base += BLK) {
        u64 hi = base + BLK - 1; if (hi > N) hi = N;
        u64 cnt[256]; memset(cnt, 0, sizeof cnt);
        u128 bexc = 0; u64 bargn = 0;
#ifdef _OPENMP
#pragma omp parallel
#endif
        {
            u64 lcnt[256]; memset(lcnt, 0, sizeof lcnt);
            u128 lexc = 0; u64 largn = 0;
#ifdef _OPENMP
#pragma omp for schedule(dynamic, 4096)
#endif
            for (u64 n = base; n <= hi; n++) {
                Res r = classify(n, base, fate);
                fate[n] = (uint8_t)r.code;
                lcnt[r.code]++;
                if (r.exc > lexc) { lexc = r.exc; largn = n; }
            }
#ifdef _OPENMP
#pragma omp critical(merge)
#endif
            {
                for (int i = 0; i < 256; i++) cnt[i] += lcnt[i];
                if (lexc > bexc) { bexc = lexc; bargn = largn; }
            }
        }
        fprintf(out, "%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%.4Lf\t%llu\n",
                (unsigned long long)base, (unsigned long long)hi,
                (unsigned long long)cnt[1], (unsigned long long)cnt[2], (unsigned long long)cnt[3],
                (unsigned long long)cnt[4], (unsigned long long)cnt[5], (unsigned long long)cnt[6],
                (unsigned long long)cnt[7], (unsigned long long)cnt[8],
                (unsigned long long)cnt[F_OVER], (unsigned long long)cnt[F_CAP],
                log2l((long double)bexc), (unsigned long long)bargn);
        fflush(out);
        if (cnt[F_CAP]) {
            fprintf(disc, "STEPCAP hit for %llu n in block base=%llu — investigate\n",
                    (unsigned long long)cnt[F_CAP], (unsigned long long)base);
            fflush(disc);
        }
        fprintf(stderr, "[%llus] block %llu..%llu done (%.2f%%)\n",
                (unsigned long long)(time(NULL) - t0), (unsigned long long)base,
                (unsigned long long)hi, 100.0 * (double)hi / (double)N);
    }

    fprintf(stderr, "cycle registry (%d cycles):\n", ncyc);
    for (int i = 0; i < ncyc; i++) {
        char b[48]; u128str(cyc_min[i], b);
        fprintf(stderr, "  class c%d: min=%s len=%llu\n", i + 1, b, (unsigned long long)cyc_len[i]);
    }
    fclose(out); fclose(disc); free(fate);
    return 0;
}
