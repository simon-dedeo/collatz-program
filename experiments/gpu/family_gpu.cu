/* family_gpu.cu — CUDA port of family.c (orbit-fate census across generalized
 * Collatz map families) for a single GPU (tested: RTX 4090, sm_89, CUDA 12.8).
 *
 * WHAT RUNS WHERE
 *   GPU  : the per-seed inner loop.  One thread per seed n (blocked by map);
 *          each thread resolves the TERMINAL fate of its seed by direct
 *          simulation and writes a compact record (kind, cycle_min, cycle_len,
 *          steps, excursion).
 *   HOST : everything else, ported VERBATIM from family.c — cycle registry,
 *          fate counts, rigidity probe, drift, row formatting.  The registry
 *          is resolved on the host by replaying the per-seed records in
 *          ascending-n order, which reproduces the CPU registration order
 *          (and therefore registry indices, basin-size tie-breaks, and the
 *          F_XCYC saturation behaviour) exactly.
 *
 * SEMANTIC EQUIVALENCE WITH THE CPU MEMO (drop-below-start inheritance)
 *   The CPU classifies seeds in ascending order; classify(n) stops at the
 *   first orbit value x < n and inherits fate[x], recording steps/excursion
 *   UP TO THAT DROP.  fate[x] itself was resolved the same way, so the CPU
 *   fate of n is determined by a CHAIN of segments, each segment being a
 *   fresh classify(seg_start) with its own Brent state and its own STEPCAP
 *   budget (the step cap is per-segment, NOT per-orbit).
 *   The GPU thread emulates that chain directly: it simulates the orbit,
 *   and every time the value drops below the current segment start it opens
 *   a new segment (resetting Brent state and the step budget, exactly like
 *   the CPU's classify() restart at the inherited seed).  The recorded
 *   steps / excursion for n are frozen at the FIRST drop below n — identical
 *   truncation semantics to the CPU.  The translation-trap fast path is
 *   ported verbatim and applied per segment (its "inherit at fate[vdrop]"
 *   exit becomes "open a new segment at vdrop").  Overflow (> 2^100) and the
 *   per-segment step cap use the same constants and the same check order as
 *   family.c, so every per-seed record — fate class, steps, excursion,
 *   cycle minimum, cycle length — is bit-identical to the CPU's.
 *   There is NO remaining semantic difference: validated TSV-byte-identical
 *   against family.c on anchors and grid2 sweeps.
 *
 * u128 ON DEVICE
 *   nvcc/sm_89 supports unsigned/signed __int128 (+, -, *, shifts, compares,
 *   and even /, %) in device code; verified bit-exact against host on random
 *   cases (u128_probe.cu).  The hot-path division x -> (x/d, x%d) for d = 3
 *   avoids the (slow) generic 128-bit divide via a 4x32-bit long division by
 *   the small d; d = 2 uses shifts, as on the CPU.
 *
 * CLI (same as family.c):
 *   family_gpu --selftest
 *   family_gpu anchors  [N]
 *   family_gpu grid2    [A] [B] [N]     (defaults 9 9 1000000)
 *   family_gpu critical [Bmax] [N]      (defaults 63 1000000)
 *   family_gpu grid3    [NSAMP] [N]     (defaults 20000 1000000)
 *   env: FAMILY_STEPCAP (default 50000), FAMILY_NOTRAP=1, FAMILY_GPU_MEM
 *        (record-buffer budget in MiB, default 3072)
 *
 * Build: nvcc -O3 -arch=sm_89 -o family_gpu family_gpu.cu   (see Makefile.gpu)
 */
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <cmath>
#include <cuda_runtime.h>

typedef unsigned __int128 u128;
typedef __int128 i128;
typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned long long ull;

#define DMAX   4          /* max modulus supported (modes use d = 2, 3) */
#define MAXCYC 32         /* per-map cycle registry cap */
#define F_XCYC 33         /* fate: cycle beyond registry cap */
#define F_OVER 201        /* fate: exceeded 2^100, presumed divergent */
#define F_CAP  202        /* fate: unresolved after STEPCAP steps */
#define NFATE  35         /* compact fate classes: 32 cycles + xcyc + over + cap */
#define ROWLEN 640

static u64 STEPCAP = 50000;              /* override: env FAMILY_STEPCAP */
static int TRAP_OFF = 0;                 /* env FAMILY_NOTRAP */
#define MAXV (((u128)1) << 100)

#define CK(call) do { cudaError_t e_ = (call); if (e_ != cudaSuccess) { \
    fprintf(stderr, "CUDA error: %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); \
    exit(2); } } while (0)

typedef struct { int d; u64 a[DMAX], b[DMAX]; const char *name; } Map;
typedef struct { int d; u64 a[DMAX], b[DMAX]; } DevMap;

typedef struct {
    int    ncyc;                /* cycles registered (<= MAXCYC) */
    int    xcyc;                /* 1 if registry saturated */
    u128   cyc_min[MAXCYC];
    u64    cyc_len[MAXCYC];
    u64    cnt[256];            /* counts per fate code */
    u64    sum_steps;
    u128   max_exc;
    double fate_H, rig_H;       /* marginal / min conditional fate entropy (bits) */
    int    rig_m;               /* argmin modulus */
} Census;

/* ================================================================ device == */

enum { K_CYC = 0, K_OVER = 1, K_CAP = 2 };

#define DEV_MAXV (((u128)1) << 100)

/* x -> (q, r) for small d (2..4): 4x32-bit long division, no 128-bit divide */
__device__ static inline void divmod_small(u128 x, u32 d, u128 *q, u64 *r)
{
    u64 hi = (u64)(x >> 64), lo = (u64)x;
    u64 qhi = hi / d, rem = hi % d;
    u64 t1 = (rem << 32) | (lo >> 32);
    u64 q1 = t1 / d, r1 = t1 % d;
    u64 t2 = (r1 << 32) | (lo & 0xffffffffull);
    u64 q2 = t2 / d, r2 = t2 % d;
    *q = ((u128)qhi << 64) | (u128)((q1 << 32) | q2);
    *r = r2;
}

__device__ static inline void step_split(const DevMap &mp, u128 x, u64 *i, u128 *q)
{
    if (mp.d == 2) { *i = (u64)x & 1; *q = x >> 1; }
    else            divmod_small(x, (u32)mp.d, q, i);
}

__device__ static inline u128 stepf_dev(const DevMap &mp, u128 x)
{
    u64 i; u128 q;
    step_split(mp, x, &i, &q);
    return (u128)mp.a[i] * q + (u128)mp.b[i];
}

typedef struct { int is_drop; u128 vdrop; u64 steps; u128 exc; } TrapOut;

/* Verbatim port of family.c trap_shortcut(); the CPU's "inherit fate[vdrop]"
 * exit is reported as is_drop=1 + vdrop (caller opens a new segment there).
 * nseg plays the role of the CPU's `n` (the current segment start). */
__device__ static int trap_shortcut_dev(const DevMap &mp, u128 nseg,
                                        u128 x, int res0, u64 steps, u128 exc,
                                        u64 stepcap, TrapOut *out)
{
    const int d = mp.d;
    int pos[DMAX], seq[DMAX];
    i128 C[DMAX + 1];
    int len = 0, t = -1, cur = res0;
    for (int i = 0; i < d; i++) pos[i] = -1;
    while (mp.a[cur] == (u64)d) {
        if (pos[cur] >= 0) { t = pos[cur]; break; }
        pos[cur] = len; seq[len] = cur; len++;
        cur = (int)(mp.b[cur] % (u64)d);
    }
    if (t < 0) return 0;
    const int p = len - t;
    C[0] = 0;
    for (int k = 0; k < len; k++)
        C[k + 1] = C[k] + ((i128)mp.b[seq[k]] - seq[k]);
    const i128 S = C[len] - C[t];
    if (S == 0) return 0;

    const u64 R = stepcap - steps;
    const i128 W = (i128)nseg - (i128)x;
    i128 loopMin = C[t + 1], loopMax = C[t + 1];
    for (int k = t + 2; k <= len; k++) {
        if (C[k] < loopMin) loopMin = C[k];
        if (C[k] > loopMax) loopMax = C[k];
    }

    if (S > 0) {
        for (int k = 1; k <= t; k++) if (C[k] < W) return 0;
        if (loopMin < W) return 0;
        i128 maxD = 0;
        if (R <= (u64)t) {
            for (u64 k = 1; k <= R; k++) if (C[k] > maxD) maxD = C[k];
        } else {
            const u64 kp = R - (u64)t, full = kp / (u64)p, rem = kp % (u64)p;
            for (int k = 1; k <= t; k++) if (C[k] > maxD) maxD = C[k];
            if (full > 0) {
                i128 v = (i128)(full - 1) * S + loopMax;
                if (v > maxD) maxD = v;
            }
            for (u64 j = 1; j <= rem; j++) {
                i128 v = (i128)full * S + C[t + (int)j];
                if (v > maxD) maxD = v;
            }
        }
        const i128 vmax = (i128)x + maxD;
        if (vmax > (i128)DEV_MAXV) return 0;
        u128 e = (u128)vmax > exc ? (u128)vmax : exc;
        out->is_drop = 0; out->vdrop = 0; out->steps = stepcap; out->exc = e;
        return 1;
    }

    /* S < 0: descending staircase */
    i128 firstMax = 0;
    for (int k = 1; k <= len; k++) if (C[k] > firstMax) firstMax = C[k];
    if ((i128)x + firstMax > (i128)DEV_MAXV) return 0;
    i128 kstar = 0, vdrop = 0; int found = 0;
    for (int k = 1; k <= t && !found; k++)
        if (C[k] < W) { kstar = k; vdrop = (i128)x + C[k]; found = 1; }
    if (!found) {
        i128 f = 0;
        const i128 need = W - loopMin;
        if (need <= 0) f = (-need) / (-S);            /* device i128 divide (probed OK) */
        while (f * S + loopMin >= W) f++;
        while (f > 0 && (f - 1) * S + loopMin < W) f--;
        for (int j = 1; j <= p; j++) {
            i128 v = f * S + C[t + j];
            if (v < W) {
                kstar = (i128)t + f * p + j;
                vdrop = (i128)x + v;
                found = 1;
                break;
            }
        }
    }
    const u64 K = (found && kstar <= (i128)R) ? (u64)kstar : R;
    i128 maxD = 0;
    if (K >= (u64)len) maxD = firstMax;
    else for (u64 k = 1; k <= K; k++) if (C[k] > maxD) maxD = C[k];
    const i128 vm = (i128)x + maxD;
    u128 e = (u128)vm > exc ? (u128)vm : exc;
    if (!found || kstar > (i128)R) {
        out->is_drop = 0; out->vdrop = 0; out->steps = stepcap; out->exc = e;
        return 1;
    }
    out->is_drop = 1; out->vdrop = (u128)vdrop; out->steps = steps + (u64)kstar; out->exc = e;
    return 1;
}

typedef struct { u128 cyc_min, exc; u64 steps, cyc_len; uint8_t kind; } SeedOut;

/* Segmented direct simulation == CPU classify() + fate inheritance chain.
 * Check order inside the loop matches family.c classify() exactly:
 *   loop top: overflow -> trap;  after step: drop -> cycle -> Brent -> cap. */
__device__ static void classify_seed(const DevMap &mp, u64 seed,
                                     u64 stepcap, int trapoff, SeedOut &o)
{
    u128 seg = seed;                    /* current segment start (CPU's `n`) */
    u128 x = seg, exc = seg, tortoise = seg;
    u64 power = 1, lam = 0, steps = 0;
    bool frozen = false;                /* n's steps/exc frozen at first drop */
    o.cyc_min = 0; o.cyc_len = 0; o.steps = 0; o.exc = seed;

    for (;;) {
        if (x > DEV_MAXV) {
            if (!frozen) { o.steps = steps; o.exc = exc; }
            o.kind = K_OVER; return;
        }
        u64 i; u128 q;
        step_split(mp, x, &i, &q);
        if (mp.a[i] == (u64)mp.d && !trapoff) {
            TrapOut t;
            if (trap_shortcut_dev(mp, seg, x, (int)i, steps, exc, stepcap, &t)) {
                if (!t.is_drop) {                     /* per-segment step cap */
                    if (!frozen) { o.steps = stepcap; o.exc = t.exc; }
                    o.kind = K_CAP; return;
                }
                if (!frozen) { o.steps = t.steps; o.exc = t.exc; frozen = true; }
                seg = t.vdrop; x = seg; exc = t.exc;  /* new segment */
                tortoise = x; power = 1; lam = 0; steps = 0;
                continue;
            }
        }
        x = (u128)mp.a[i] * q + (u128)mp.b[i];
        steps++; lam++;
        if (x > exc) exc = x;
        if (x < seg) {                                /* drop below segment start */
            if (!frozen) { o.steps = steps; o.exc = exc; frozen = true; }
            seg = x; tortoise = x; power = 1; lam = 0; steps = 0;
            continue;
        }
        if (x == tortoise) break;                     /* cycle of length lam */
        if (lam == power) { tortoise = x; power <<= 1; lam = 0; }
        if (steps >= stepcap) {
            if (!frozen) { o.steps = steps; o.exc = exc; }
            o.kind = K_CAP; return;
        }
    }
    u128 mn = x, y = stepf_dev(mp, x);
    while (y != x) { if (y < mn) mn = y; y = stepf_dev(mp, y); }
    if (!frozen) { o.steps = steps; o.exc = exc; }
    o.kind = K_CYC; o.cyc_min = mn; o.cyc_len = lam;
}

__global__ static void census_kernel(const DevMap *maps, int nmaps_b, u64 N,
                                     u64 stepcap, int trapoff,
                                     u128 *o_min, u128 *o_exc,
                                     u64 *o_steps, u64 *o_len, uint8_t *o_kind)
{
    u64 total = (u64)nmaps_b * N;
    u64 stride = (u64)gridDim.x * blockDim.x;
    for (u64 t = (u64)blockIdx.x * blockDim.x + threadIdx.x; t < total; t += stride) {
        int mi = (int)(t / N);
        u64 n = (t % N) + 1;
        DevMap mp = maps[mi];
        SeedOut o;
        classify_seed(mp, n, stepcap, trapoff, o);
        o_min[t] = o.cyc_min; o_exc[t] = o.exc;
        o_steps[t] = o.steps; o_len[t] = o.cyc_len; o_kind[t] = o.kind;
    }
}

/* ======================================== host: verbatim family.c logic == */

static void u128str(u128 v, char *buf) {
    char t[48]; int i = 0, j = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) buf[j++] = t[--i];
    buf[j] = 0;
}

static int row_valid(int i, u64 a, u64 b) {
    if (i == 0) return a + b >= 1;
    return b >= 1;
}

static int map_valid(const Map *mp) {
    for (int i = 0; i < mp->d; i++)
        if (!row_valid(i, mp->a[i], mp->b[i])) return 0;
    return 1;
}

static double map_drift(const Map *mp, int *flag) {
    double s = 0.0;
    *flag = 0;
    for (int i = 0; i < mp->d; i++) {
        u64 a = mp->a[i];
        if (a == 0) { *flag = 1; a = 1; }
        s += log((double)a / (double)mp->d);
    }
    return s / (double)mp->d;
}

static int register_cycle(Census *cs, u128 mn, u64 len) {
    for (int i = 0; i < cs->ncyc; i++)
        if (cs->cyc_min[i] == mn) return i + 1;
    if (cs->ncyc == MAXCYC) { cs->xcyc = 1; return F_XCYC; }
    cs->cyc_min[cs->ncyc] = mn;
    cs->cyc_len[cs->ncyc] = len;
    cs->ncyc++;
    return cs->ncyc;
}

/* -------------------------------------------------------- rigidity probe */

#define NMODS 12
#define RSUM  165
static const int RMODS[NMODS] = {2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 36};

static int fidx(int code) {
    if (code >= 1 && code <= MAXCYC) return code - 1;
    if (code == F_XCYC) return MAXCYC;
    if (code == F_OVER) return MAXCYC + 1;
    return MAXCYC + 2;
}

static double cond_entropy(const u32 *tab, int m, u64 total) {
    double H = 0.0;
    for (int r = 0; r < m; r++) {
        const u32 *row = tab + (size_t)r * NFATE;
        u64 cr = 0;
        for (int f = 0; f < NFATE; f++) cr += row[f];
        if (!cr) continue;
        for (int f = 0; f < NFATE; f++)
            if (row[f]) H += (double)row[f] * log2((double)cr / (double)row[f]);
    }
    return H / (double)total;
}

static void rigidity_probe(u64 N, const uint8_t *fate, Census *cs) {
    u64 lo = N / 2 + 1;
    u64 total = N - lo + 1;
    u32 tab[RSUM * NFATE];
    u64 marg[NFATE];
    int off[NMODS];
    memset(tab, 0, sizeof tab);
    memset(marg, 0, sizeof marg);
    { int o = 0; for (int k = 0; k < NMODS; k++) { off[k] = o; o += RMODS[k]; } }
    for (u64 n = lo; n <= N; n++) {
        int f = fidx(fate[n]);
        marg[f]++;
        for (int k = 0; k < NMODS; k++) {
            int r = (int)(n % (u64)RMODS[k]);
            tab[((size_t)off[k] + (size_t)r) * NFATE + (size_t)f]++;
        }
    }
    double Hm = 0.0;
    for (int f = 0; f < NFATE; f++)
        if (marg[f]) Hm += (double)marg[f] * log2((double)total / (double)marg[f]);
    cs->fate_H = Hm / (double)total;
    double best = 1e300; int bestm = 0;
    for (int k = 0; k < NMODS; k++) {
        double H = cond_entropy(tab + (size_t)off[k] * NFATE, RMODS[k], total);
        if (H < best - 1e-12) { best = H; bestm = RMODS[k]; }
    }
    cs->rig_H = best;
    cs->rig_m = bestm;
}

/* ---------------------------------------------------------------- output */

static void tsv_header(FILE *f) {
    fprintf(f, "d\ta0\tb0\ta1\tb1\ta2\tb2\tdrift\tdrift_flag\tn_cycles\tcycle_mins\t"
               "frac_c1\tfrac_c2\tfrac_c3\tfrac_c4\tfrac_overflow\tfrac_cap\t"
               "fate_H\trigidity_min_H\trigidity_argmin_m\tmax_exc_log2\tmean_steps\tname\n");
}

static void format_row(const Map *mp, u64 N, const Census *cs, char *row) {
    int flag = 0;
    double drift = map_drift(mp, &flag);

    int ord[MAXCYC];
    for (int i = 0; i < cs->ncyc; i++) ord[i] = i;
    for (int i = 0; i < cs->ncyc; i++) {
        int best = i;
        for (int j = i + 1; j < cs->ncyc; j++)
            if (cs->cnt[ord[j] + 1] > cs->cnt[ord[best] + 1]) best = j;
        int t = ord[i]; ord[i] = ord[best]; ord[best] = t;
    }
    int top = cs->ncyc < 4 ? cs->ncyc : 4;

    char mins[192];
    if (top == 0) strcpy(mins, "-");
    else {
        size_t pos = 0;
        for (int t = 0; t < top && pos < sizeof mins - 1; t++) {
            char b[48]; u128str(cs->cyc_min[ord[t]], b);
            pos += (size_t)snprintf(mins + pos, sizeof mins - pos, "%s%s",
                                    t ? ";" : "", b);
        }
    }
    double fr[4] = {0.0, 0.0, 0.0, 0.0};
    for (int t = 0; t < top; t++) fr[t] = (double)cs->cnt[ord[t] + 1] / (double)N;

    char coef[160];
    { size_t pos = 0;
      for (int i = 0; i < 3 && pos < sizeof coef - 1; i++) {
          if (i < mp->d)
              pos += (size_t)snprintf(coef + pos, sizeof coef - pos, "%s%llu\t%llu",
                                      i ? "\t" : "", (ull)mp->a[i], (ull)mp->b[i]);
          else
              pos += (size_t)snprintf(coef + pos, sizeof coef - pos, "%s-\t-",
                                      i ? "\t" : "");
      }
    }

    snprintf(row, ROWLEN,
             "%d\t%s\t%.6f\t%d\t%d\t%s\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t"
             "%.6f\t%.6f\t%d\t%.3f\t%.2f\t%s\n",
             mp->d, coef, drift, flag, cs->ncyc, mins,
             fr[0], fr[1], fr[2], fr[3],
             (double)cs->cnt[F_OVER] / (double)N,
             (double)cs->cnt[F_CAP] / (double)N,
             cs->fate_H, cs->rig_H, cs->rig_m,
             (double)log2l((long double)cs->max_exc),
             (double)cs->sum_steps / (double)N,
             mp->name ? mp->name : "-");
}

/* ------------------------------------------------------- family builders */

static Map *maps = NULL;
static int nmaps = 0, capmaps = 0;

static void add_map(Map m) {
    if (nmaps == capmaps) {
        capmaps = capmaps ? capmaps * 2 : 1024;
        maps = (Map *)realloc(maps, (size_t)capmaps * sizeof(Map));
        if (!maps) { fprintf(stderr, "out of memory\n"); exit(2); }
    }
    maps[nmaps++] = m;
}

static Map mk2(const char *name, u64 a0, u64 b0, u64 a1, u64 b1) {
    Map m; memset(&m, 0, sizeof m);
    m.d = 2; m.name = name;
    m.a[0] = a0; m.b[0] = b0; m.a[1] = a1; m.b[1] = b1;
    return m;
}

static void build_anchors(void) {
    add_map(mk2("COLLATZ", 1, 0, 6, 4));
    add_map(mk2("NEG3X",   1, 0, 6, 2));
    add_map(mk2("FIVEX",   1, 0, 10, 6));
    add_map(mk2("HYDRA",   3, 0, 3, 1));
    add_map(mk2("RIGID",   1, 0, 1, 1));
}

static void build_grid2(u64 A, u64 B) {
    for (u64 a0 = 0; a0 <= A; a0++)
        for (u64 b0 = 0; b0 <= B; b0++) {
            if (!row_valid(0, a0, b0)) continue;
            for (u64 a1 = 0; a1 <= A; a1++)
                for (u64 b1 = 0; b1 <= B; b1++) {
                    if (!row_valid(1, a1, b1)) continue;
                    add_map(mk2(NULL, a0, b0, a1, b1));
                }
        }
}

static void build_critical(u64 Bmax) {
    static const u64 pairs[3][2] = {{1, 4}, {2, 2}, {4, 1}};
    for (int p = 0; p < 3; p++)
        for (u64 b0 = 0; b0 <= Bmax; b0++)
            for (u64 b1 = 0; b1 <= Bmax; b1++) {
                if (!row_valid(0, pairs[p][0], b0)) continue;
                if (!row_valid(1, pairs[p][1], b1)) continue;
                add_map(mk2(NULL, pairs[p][0], b0, pairs[p][1], b1));
            }
}

static u64 rngstate = 88172645463325252ULL;
static u64 xorshift64(void) {
    u64 x = rngstate;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return rngstate = x;
}

static void build_grid3(u64 nsamp) {
    const u64 C = 6;
    u64 npool = 0;
    u64 total = (C + 1) * (C + 1) * (C + 1) * (C + 1) * (C + 1) * (C + 1);
    Map *pool = (Map *)malloc((size_t)total * sizeof(Map));
    if (!pool) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (u64 a0 = 0; a0 <= C; a0++) for (u64 b0 = 0; b0 <= C; b0++)
    for (u64 a1 = 0; a1 <= C; a1++) for (u64 b1 = 0; b1 <= C; b1++)
    for (u64 a2 = 0; a2 <= C; a2++) for (u64 b2 = 0; b2 <= C; b2++) {
        Map m; memset(&m, 0, sizeof m);
        m.d = 3; m.name = NULL;
        m.a[0] = a0; m.b[0] = b0;
        m.a[1] = a1; m.b[1] = b1;
        m.a[2] = a2; m.b[2] = b2;
        if (!map_valid(&m)) continue;
        pool[npool++] = m;
    }
    fprintf(stderr, "grid3: %llu valid maps in pool, sampling %llu (seed fixed)\n",
            (ull)npool, (ull)(nsamp < npool ? nsamp : npool));
    if (nsamp > npool) nsamp = npool;
    for (u64 k = 0; k < nsamp; k++) {
        u64 j = k + xorshift64() % (npool - k);
        Map t = pool[k]; pool[k] = pool[j]; pool[j] = t;
        add_map(pool[k]);
    }
    free(pool);
}

/* --------------------------------------------- GPU batch runner + replay */

typedef struct {
    u128 *d_min, *d_exc;
    u64  *d_steps, *d_len;
    uint8_t *d_kind;
    DevMap *d_maps;
    u128 *h_min, *h_exc;
    u64  *h_steps, *h_len;
    uint8_t *h_kind;
    u64 cap_seeds;              /* batch capacity in seeds */
    int cap_maps;
} GpuBuf;

static void gpubuf_alloc(GpuBuf *g, u64 cap_seeds, int cap_maps) {
    g->cap_seeds = cap_seeds; g->cap_maps = cap_maps;
    CK(cudaMalloc(&g->d_min,   cap_seeds * sizeof(u128)));
    CK(cudaMalloc(&g->d_exc,   cap_seeds * sizeof(u128)));
    CK(cudaMalloc(&g->d_steps, cap_seeds * sizeof(u64)));
    CK(cudaMalloc(&g->d_len,   cap_seeds * sizeof(u64)));
    CK(cudaMalloc(&g->d_kind,  cap_seeds * sizeof(uint8_t)));
    CK(cudaMalloc(&g->d_maps,  (size_t)cap_maps * sizeof(DevMap)));
    g->h_min   = (u128 *)malloc(cap_seeds * sizeof(u128));
    g->h_exc   = (u128 *)malloc(cap_seeds * sizeof(u128));
    g->h_steps = (u64 *)malloc(cap_seeds * sizeof(u64));
    g->h_len   = (u64 *)malloc(cap_seeds * sizeof(u64));
    g->h_kind  = (uint8_t *)malloc(cap_seeds * sizeof(uint8_t));
    if (!g->h_min || !g->h_exc || !g->h_steps || !g->h_len || !g->h_kind) {
        fprintf(stderr, "host record buffer alloc failed\n"); exit(2);
    }
}

static void gpubuf_free(GpuBuf *g) {
    cudaFree(g->d_min); cudaFree(g->d_exc); cudaFree(g->d_steps);
    cudaFree(g->d_len); cudaFree(g->d_kind); cudaFree(g->d_maps);
    free(g->h_min); free(g->h_exc); free(g->h_steps); free(g->h_len); free(g->h_kind);
}

/* run a batch of nb maps (records for map k land at offset k*N) */
static void gpu_run_batch(GpuBuf *g, const Map *batch, int nb, u64 N) {
    DevMap dm[1024];
    if (nb > 1024) { fprintf(stderr, "batch too large\n"); exit(2); }
    for (int k = 0; k < nb; k++) {
        dm[k].d = batch[k].d;
        for (int i = 0; i < DMAX; i++) { dm[k].a[i] = batch[k].a[i]; dm[k].b[i] = batch[k].b[i]; }
    }
    CK(cudaMemcpy(g->d_maps, dm, (size_t)nb * sizeof(DevMap), cudaMemcpyHostToDevice));
    u64 total = (u64)nb * N;
    int bs = 128;
    u64 nblk = (total + (u64)bs - 1) / (u64)bs;
    if (nblk > 2147483647ULL) nblk = 2147483647ULL;
    census_kernel<<<(unsigned)nblk, bs>>>(g->d_maps, nb, N, STEPCAP, TRAP_OFF,
                                          g->d_min, g->d_exc, g->d_steps, g->d_len, g->d_kind);
    CK(cudaGetLastError());
    CK(cudaDeviceSynchronize());
    CK(cudaMemcpy(g->h_min,   g->d_min,   total * sizeof(u128), cudaMemcpyDeviceToHost));
    CK(cudaMemcpy(g->h_exc,   g->d_exc,   total * sizeof(u128), cudaMemcpyDeviceToHost));
    CK(cudaMemcpy(g->h_steps, g->d_steps, total * sizeof(u64),  cudaMemcpyDeviceToHost));
    CK(cudaMemcpy(g->h_len,   g->d_len,   total * sizeof(u64),  cudaMemcpyDeviceToHost));
    CK(cudaMemcpy(g->h_kind,  g->d_kind,  total * sizeof(uint8_t), cudaMemcpyDeviceToHost));
}

/* ascending-n replay of one map's records == CPU run_census() aggregation */
static void replay_census(const GpuBuf *g, u64 off, u64 N, uint8_t *fate, Census *cs) {
    memset(cs, 0, sizeof *cs);
    for (u64 n = 1; n <= N; n++) {
        u64 idx = off + n - 1;
        int code;
        switch (g->h_kind[idx]) {
        case K_CYC:  code = register_cycle(cs, g->h_min[idx], g->h_len[idx]); break;
        case K_OVER: code = F_OVER; break;
        default:     code = F_CAP;  break;
        }
        fate[n] = (uint8_t)code;
        cs->cnt[code]++;
        cs->sum_steps += g->h_steps[idx];
        if (g->h_exc[idx] > cs->max_exc) cs->max_exc = g->h_exc[idx];
    }
    rigidity_probe(N, fate, cs);
}

/* single-map census through the GPU (selftest helper) */
static void gpu_census_single(const Map *mp, u64 N, uint8_t *fate, Census *cs) {
    GpuBuf g;
    gpubuf_alloc(&g, N, 1);
    gpu_run_batch(&g, mp, 1, N);
    replay_census(&g, 0, N, fate, cs);
    gpubuf_free(&g);
}

/* ------------------------------------------------------------ sweep loop */

static void run_all(u64 N) {
    u64 mem_mb = 3072;
    const char *mv = getenv("FAMILY_GPU_MEM");
    if (mv && atoll(mv) > 0) mem_mb = (u64)atoll(mv);
    const size_t per_seed = 2 * sizeof(u128) + 2 * sizeof(u64) + 1;   /* 49 B */
    u64 budget_seeds = mem_mb * 1024ULL * 1024ULL / per_seed;
    int mbatch = (int)(budget_seeds / N);
    if (mbatch < 1) mbatch = 1;
    if (mbatch > nmaps) mbatch = nmaps;
    if (mbatch > 1024) mbatch = 1024;

    cudaDeviceProp prop;
    CK(cudaGetDeviceProperties(&prop, 0));
    fprintf(stderr, "family_gpu: %d maps, N=%llu, stepcap=%llu, device=%s, batch=%d maps\n",
            nmaps, (ull)N, (ull)STEPCAP, prop.name, mbatch);
    if (nmaps == 0) { fprintf(stderr, "no maps to run\n"); exit(1); }

    char *rows = (char *)malloc((size_t)nmaps * ROWLEN);
    uint8_t *fate = (uint8_t *)malloc(N + 1);
    if (!rows || !fate) { fprintf(stderr, "out of memory\n"); exit(2); }

    GpuBuf g;
    gpubuf_alloc(&g, (u64)mbatch * N, mbatch);

    time_t t0 = time(NULL);
    int done = 0;
    for (int m0 = 0; m0 < nmaps; m0 += mbatch) {
        int nb = nmaps - m0 < mbatch ? nmaps - m0 : mbatch;
        gpu_run_batch(&g, maps + m0, nb, N);
        for (int k = 0; k < nb; k++) {
            Census cs;
            replay_census(&g, (u64)k * N, N, fate, &cs);
            format_row(&maps[m0 + k], N, &cs, rows + (size_t)(m0 + k) * ROWLEN);
            if (cs.xcyc)
                fprintf(stderr, "note: map #%d cycle registry saturated (>%d cycles)\n",
                        m0 + k, MAXCYC);
            done++;
            if (done == nmaps || done % 100 == 0 || nmaps <= 20)
                fprintf(stderr, "[%llus] %d/%d maps\n",
                        (ull)(time(NULL) - t0), done, nmaps);
        }
    }
    gpubuf_free(&g);

    tsv_header(stdout);
    for (int k = 0; k < nmaps; k++) fputs(rows + (size_t)k * ROWLEN, stdout);
    fflush(stdout);
    free(rows); free(fate);
    fprintf(stderr, "family_gpu: done in %llus\n", (ull)(time(NULL) - t0));
}

/* --------------------------------------------------------------- selftest */

static int st_fail = 0;

static void check(int cond, const char *what) {
    fprintf(stderr, "  [%s] %s\n", cond ? "PASS" : "FAIL", what);
    if (!cond) st_fail = 1;
}

static int has_cycle(const Census *cs, u64 mn, u64 len) {
    for (int i = 0; i < cs->ncyc; i++)
        if (cs->cyc_min[i] == (u128)mn && cs->cyc_len[i] == len) return 1;
    return 0;
}

static void st_row(const Map *mp, u64 N, const Census *cs) {
    char row[ROWLEN];
    format_row(mp, N, cs, row);
    fputs(row, stderr);
}

static int selftest(void) {
    const u64 N = 100000;
    fprintf(stderr, "family_gpu selftest, N=%llu\n", (ull)N);

    Map bad1 = mk2(NULL, 0, 0, 3, 1);
    Map bad2 = mk2(NULL, 1, 0, 1, 0);
    Map ok1  = mk2(NULL, 1, 0, 6, 4);
    check(!map_valid(&bad1), "validity: row0 (0,0) rejected");
    check(!map_valid(&bad2), "validity: row1 (a,0) rejected (f(1)=0)");
    check(map_valid(&ok1),   "validity: COLLATZ accepted");

    uint8_t *fate = (uint8_t *)malloc(N + 1);
    if (!fate) { fprintf(stderr, "alloc failed\n"); return 2; }
    Census cs;
    tsv_header(stderr);

    Map m = mk2("COLLATZ", 1, 0, 6, 4);
    gpu_census_single(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 1 && has_cycle(&cs, 1, 3), "COLLATZ: exactly 1 cycle, (min,len)=(1,3)");
    check(cs.cnt[1] == N,                        "COLLATZ: 100% absorbed into cycle 1");
    check(cs.cnt[F_OVER] == 0 && cs.cnt[F_CAP] == 0, "COLLATZ: no overflow, no step-cap");
    check(cs.rig_H < 1e-12,                      "COLLATZ: rigidity H = 0 (fate constant)");

    m = mk2("NEG3X", 1, 0, 6, 2);
    gpu_census_single(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 3, "NEG3X: exactly 3 cycles");
    check(has_cycle(&cs, 1, 2) && has_cycle(&cs, 5, 5) && has_cycle(&cs, 17, 18),
          "NEG3X: cycle (min,len) = (1,2),(5,5),(17,18)");
    check(cs.cnt[1] + cs.cnt[2] + cs.cnt[3] == N, "NEG3X: all n absorbed into a cycle");
    check(cs.cnt[F_OVER] == 0 && cs.cnt[F_CAP] == 0, "NEG3X: no overflow, no step-cap");
    check(cs.rig_H > 0.1, "NEG3X: rigidity H > 0.1 (fates mix across residues)");

    m = mk2("FIVEX", 1, 0, 10, 6);
    gpu_census_single(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 3, "FIVEX: exactly 3 cycles");
    check(has_cycle(&cs, 1, 7) && has_cycle(&cs, 13, 10) && has_cycle(&cs, 17, 10),
          "FIVEX: cycle (min,len) = (1,7),(13,10),(17,10)");
    check(cs.cnt[F_OVER] > N / 2, "FIVEX: majority overflow (presumed divergent)");

    m = mk2("HYDRA", 3, 0, 3, 1);
    gpu_census_single(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 1 && has_cycle(&cs, 1, 1), "HYDRA: single cycle = fixed point at 1");
    check(cs.cnt[1] == 1,                        "HYDRA: only n=1 is cyclic");
    check(cs.cnt[F_OVER] == N - 1,               "HYDRA: all n>1 overflow");

    m = mk2("RIGID", 1, 0, 1, 1);
    gpu_census_single(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 1 && has_cycle(&cs, 1, 1), "RIGID: single cycle = fixed point at 1");
    check(cs.cnt[1] == N,                        "RIGID: all n reach 1");
    check(cs.fate_H < 1e-12 && cs.rig_H < 1e-12, "RIGID: H(fate)=H(fate|residue)=0");
    { int flag; double dr = map_drift(&m, &flag);
      check(dr < 0.0 && flag == 0, "RIGID: negative drift, no zero-a flag"); }

    free(fate);
    fprintf(stderr, st_fail ? "SELFTEST: FAIL\n" : "SELFTEST: all checks passed\n");
    return st_fail;
}

/* ------------------------------------------------------------------ main */

static void usage(const char *prog) {
    fprintf(stderr,
        "usage: %s --selftest\n"
        "       %s anchors  [N]\n"
        "       %s grid2    [A] [B] [N]     (defaults 9 9 1000000)\n"
        "       %s critical [Bmax] [N]      (defaults 63 1000000)\n"
        "       %s grid3    [NSAMP] [N]     (defaults 20000 1000000)\n"
        "env: FAMILY_STEPCAP overrides the step cap (default 50000)\n"
        "     FAMILY_NOTRAP=1 disables the translation-trap fast path\n"
        "     FAMILY_GPU_MEM  record-buffer budget in MiB (default 3072)\n",
        prog, prog, prog, prog, prog);
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(argv[0]); return 1; }
    const char *sc = getenv("FAMILY_STEPCAP");
    if (sc && atoll(sc) > 0) {
        STEPCAP = (u64)atoll(sc);
        fprintf(stderr, "family_gpu: STEPCAP overridden to %llu\n", (ull)STEPCAP);
    }
    const char *nt = getenv("FAMILY_NOTRAP");
    if (nt && atoi(nt) != 0) {
        TRAP_OFF = 1;
        fprintf(stderr, "family_gpu: translation-trap fast path DISABLED\n");
    }
    const char *mode = argv[1];
    if (!strcmp(mode, "--selftest") || !strcmp(mode, "selftest"))
        return selftest();

    u64 N = 1000000ULL;
    if (!strcmp(mode, "anchors")) {
        if (argc > 2) N = (u64)atoll(argv[2]);
        build_anchors();
    } else if (!strcmp(mode, "grid2")) {
        u64 A = argc > 2 ? (u64)atoll(argv[2]) : 9;
        u64 B = argc > 3 ? (u64)atoll(argv[3]) : 9;
        if (argc > 4) N = (u64)atoll(argv[4]);
        build_grid2(A, B);
    } else if (!strcmp(mode, "critical")) {
        u64 Bmax = argc > 2 ? (u64)atoll(argv[2]) : 63;
        if (argc > 3) N = (u64)atoll(argv[3]);
        build_critical(Bmax);
    } else if (!strcmp(mode, "grid3")) {
        u64 ns = argc > 2 ? (u64)atoll(argv[2]) : 20000;
        if (argc > 3) N = (u64)atoll(argv[3]);
        build_grid3(ns);
    } else {
        usage(argv[0]);
        return 1;
    }
    if (N < 4) { fprintf(stderr, "N too small\n"); return 1; }
    run_all(N);
    free(maps);
    return 0;
}
