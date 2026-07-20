/* family.c — orbit-fate census across FAMILIES of generalized Collatz maps
 *
 * Map class (Michel's generalized Collatz mappings): fix a modulus d and
 * coefficient rows (a_i, b_i), i = 0..d-1, with a_i >= 0, b_i >= 0.  The map is
 *
 *     f(m) = a_i * q + b_i      where m = d*q + i   (i = m mod d)
 *
 * Validity (v1, nonnegative maps): f(m) >= 1 for all m >= 1, i.e.
 *     row 0     : a_0 + b_0 >= 1      (smallest argument is q = 1)
 *     row i > 0 : b_i >= 1            (smallest argument is q = 0, f(i) = b_i)
 * All rows are total functions, so orbits are defined forever.
 *
 * Named sanity anchors (d = 2):
 *     COLLATZ  (1,0),(6,4)    f(2q+1) = 6q+4 = 3m+1
 *     NEG3X    (1,0),(6,2)    f(2q+1) = 6q+2 = 3m-1
 *     FIVEX    (1,0),(10,6)   f(2q+1) = 10q+6 = 5m+1
 *     HYDRA    (3,0),(3,1)    f(m) = floor(3m/2)
 *     RIGID    (1,0),(1,1)    f(2q)=q, f(2q+1)=q+1 (all m -> 1; rigidity control)
 *
 * Per-map measurement over n in [1, N] (default N = 10^6), architecture
 * inherited from ../fate.c (validated): per-n Brent cycle detection with
 * drop-below-start fate inheritance (n processed in ascending order, so
 * fate[x] is final for every x < n), u128 values, overflow cap 2^100,
 * step cap 50000 (override: env FAMILY_STEPCAP).
 *
 *   - naive log-drift  (1/d) * sum_i ln(a_i / d)   [a_i = 0 rows use ln(1/d),
 *     flagged in drift_flag; NOTE this uniform-residue heuristic ignores
 *     forced-residue correlations — e.g. COLLATZ in this representation has
 *     drift +0.203 yet converges, because 6q+4 is always even]
 *   - fate census: distinct cycles (registry of minima + lengths, cap 32;
 *     overflow of the registry is lumped into an "extra cycle" fate class),
 *     fraction absorbed into each of the top 4 cycles (by basin size),
 *     fraction overflow (> 2^100, presumed divergent), fraction step-capped
 *   - RIGIDITY PROBE: over n in the top half (N/2, N], the conditional
 *     entropy H(fate | n mod m) in bits for m in
 *     {2,3,4,6,8,9,12,16,18,24,27,36}; reports the minimum and the argmin m
 *     (smallest m achieving it), plus the marginal fate entropy H(fate) as a
 *     baseline.  Rigid / residue-determined maps give ~0; mixing maps give
 *     ~H(fate).
 *   - max excursion (log2) and mean steps, both measured up to fate
 *     RESOLUTION (drop below start / cycle closure / overflow / cap), same
 *     truncation semantics as fate.c blocks.
 *
 * Family sweep modes (one TSV row per map on stdout, progress on stderr):
 *     family --selftest                  ground-truth checks on the anchors
 *     family anchors  [N]                the 5 named maps above
 *     family grid2    [A] [B] [N]        all valid d=2 maps, a_i<=A, b_i<=B
 *                                        (defaults 9 9 -> 8910 maps)
 *     family critical [Bmax] [N]         d=2 zero-drift line a_0*a_1 = 4:
 *                                        (a_0,a_1) in {(1,4),(2,2),(4,1)},
 *                                        b_i <= Bmax (default 63 -> 12096)
 *     family grid3    [NSAMP] [N]        d=3, coefficients <= 6, fixed-seed
 *                                        xorshift subsample (default 20000)
 *
 * Parallelism: over MAPS (omp for schedule(dynamic)); each map's census is
 * sequential.  Per-thread scratch: one (N+1)-byte fate array.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o family family.c -lm   (Linux)
 *         cc -O2 -Wall -Wextra -o family family.c -lm             (macOS, sequential)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

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
#define MAXV (((u128)1) << 100)

typedef struct { int d; u64 a[DMAX], b[DMAX]; const char *name; } Map;

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

/* ---------------------------------------------------------------- basics */

static void u128str(u128 v, char *buf) {
    char t[48]; int i = 0, j = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i) buf[j++] = t[--i];
    buf[j] = 0;
}

/* Row i is valid iff f(m) >= 1 for every m >= 1 with m == i (mod d). */
static int row_valid(int i, u64 a, u64 b) {
    if (i == 0) return a + b >= 1;   /* smallest argument has q = 1 */
    return b >= 1;                   /* q = 0: f(i) = b_i */
}

static int map_valid(const Map *mp) {
    for (int i = 0; i < mp->d; i++)
        if (!row_valid(i, mp->a[i], mp->b[i])) return 0;
    return 1;
}

/* naive log-drift (1/d) sum_i ln(a_i/d); a_i = 0 handled as ln(1/d), flagged */
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

static inline u128 stepf(const Map *mp, u128 x) {
    u64 i; u128 q;
    if (mp->d == 2) { i = (u64)(x & 1); q = x >> 1; }
    else { u64 dd = (u64)mp->d; i = (u64)(x % dd); q = x / dd; }
    /* x <= 2^100 when stepping and a_i is small, so no u128 overflow */
    return (u128)mp->a[i] * q + (u128)mp->b[i];
}

/* per-map registry; census is sequential per map, so no locking needed */
static int register_cycle(Census *cs, u128 mn, u64 len) {
    for (int i = 0; i < cs->ncyc; i++)
        if (cs->cyc_min[i] == mn) return i + 1;
    if (cs->ncyc == MAXCYC) { cs->xcyc = 1; return F_XCYC; }
    cs->cyc_min[cs->ncyc] = mn;
    cs->cyc_len[cs->ncyc] = len;
    cs->ncyc++;
    return cs->ncyc;
}

/* -------------------------------------------------------------- classify */

typedef struct { int code; u64 steps; u128 exc; } Res;

/* --- translation-trap fast path ---------------------------------------
 * Rows with a_i == d are translations: f(dq+i) = m + (b_i - i), and the next
 * residue, b_i mod d, depends only on i.  If the orbit's current residue lies
 * on a residue loop made entirely of such rows, its increments are periodic
 * forever (period p <= d, period sum S).  When S != 0 no value can ever
 * repeat (a repeated value would make the orbit periodic, forcing S = 0), so
 * the generic loop would grind all the way to the step cap (S > 0, or S < 0
 * started far above n), inherit at the first value below n (S < 0), or
 * overflow.  This routine reproduces the generic loop's EXACT result — same
 * fate code, same step count, same max excursion — in O(d) work instead of
 * O(STEPCAP).  S == 0 (a genuine value cycle) is left to Brent, which closes
 * it in O(p) steps.  Near-2^100 corner cases fall back to the generic loop.
 * Set FAMILY_NOTRAP=1 to disable, for A/B verification against the slow path.
 * Returns 1 iff the fate was resolved analytically. */
static int TRAP_OFF = 0;

static int trap_shortcut(const Map *mp, u64 n, const uint8_t *fate,
                         u128 x, int res0, u64 steps, u128 exc, Res *out) {
    const int d = mp->d;
    int pos[DMAX], seq[DMAX];
    i128 C[DMAX + 1];                     /* C[k] = D(k): offset after k steps */
    int len = 0, t = -1, cur = res0;
    for (int i = 0; i < d; i++) pos[i] = -1;
    while (mp->a[cur] == (u64)d) {
        if (pos[cur] >= 0) { t = pos[cur]; break; }
        pos[cur] = len; seq[len] = cur; len++;
        cur = (int)(mp->b[cur] % (u64)d);
    }
    if (t < 0) return 0;                  /* chain exits translation rows */
    const int p = len - t;                /* loop period; tail length t */
    C[0] = 0;
    for (int k = 0; k < len; k++)
        C[k + 1] = C[k] + ((i128)mp->b[seq[k]] - seq[k]);
    const i128 S = C[len] - C[t];         /* net shift per period */
    if (S == 0) return 0;                 /* value cycle: let Brent close it */

    const u64 R = STEPCAP - steps;        /* remaining budget (>= 1 here) */
    const i128 W = (i128)n - (i128)x;     /* drop condition: D(k) < W */
    i128 loopMin = C[t + 1], loopMax = C[t + 1];
    for (int k = t + 2; k <= len; k++) {
        if (C[k] < loopMin) loopMin = C[k];
        if (C[k] > loopMax) loopMax = C[k];
    }

    if (S > 0) {
        /* a drop, if any, happens within the tail or the first period:
           cheap for the generic loop, so just decline */
        for (int k = 1; k <= t; k++) if (C[k] < W) return 0;
        if (loopMin < W) return 0;
        /* no drop ever => step cap, unless 2^100 is crossed inside the
           budget (then the generic loop overflows first: decline, rare) */
        i128 maxD = 0;                    /* max D(k) over 0 <= k <= R */
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
        if (vmax > (i128)MAXV) return 0;
        u128 e = (u128)vmax > exc ? (u128)vmax : exc;
        *out = (Res){F_CAP, STEPCAP, e};
        return 1;
    }

    /* S < 0: descending staircase.  Values never exceed x + firstMax. */
    i128 firstMax = 0;
    for (int k = 1; k <= len; k++) if (C[k] > firstMax) firstMax = C[k];
    if ((i128)x + firstMax > (i128)MAXV) return 0;   /* decline near-2^100 band */
    /* first k with D(k) < W (exists: D -> -infinity).  f, kstar in i128:
       from far above n the drop index can approach 2^100. */
    i128 kstar = 0, vdrop = 0; int found = 0;
    for (int k = 1; k <= t && !found; k++)
        if (C[k] < W) { kstar = k; vdrop = (i128)x + C[k]; found = 1; }
    if (!found) {
        i128 f = 0;
        const i128 need = W - loopMin;    /* want smallest f with f*S < need */
        if (need <= 0) f = (-need) / (-S);
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
    /* exc over traversed steps: the max sits within tail + first period */
    const u64 K = (found && kstar <= (i128)R) ? (u64)kstar : R;
    i128 maxD = 0;
    if (K >= (u64)len) maxD = firstMax;
    else for (u64 k = 1; k <= K; k++) if (C[k] > maxD) maxD = C[k];
    const i128 vm = (i128)x + maxD;
    u128 e = (u128)vm > exc ? (u128)vm : exc;
    if (!found || kstar > (i128)R) { *out = (Res){F_CAP, STEPCAP, e}; return 1; }
    *out = (Res){fate[(u64)(u128)vdrop], steps + (u64)kstar, e};
    return 1;
}

/* Classify the orbit of n.  fate[x] is final for all x < n (ascending order).
 * Brent cycle detection, exactly as in fate.c, plus the translation-trap
 * fast path above. */
static Res classify(const Map *mp, u64 n, const uint8_t *fate, Census *cs) {
    u128 x = n, exc = n, tortoise = n;
    u64 power = 1, lam = 0, steps = 0;
    for (;;) {
        if (x > MAXV) return (Res){F_OVER, steps, exc};
        u64 i; u128 q;
        if (mp->d == 2) { i = (u64)(x & 1); q = x >> 1; }
        else { u64 dd = (u64)mp->d; i = (u64)(x % dd); q = x / dd; }
        if (mp->a[i] == (u64)mp->d && !TRAP_OFF) {
            Res out;
            if (trap_shortcut(mp, n, fate, x, (int)i, steps, exc, &out))
                return out;
        }
        x = (u128)mp->a[i] * q + (u128)mp->b[i];
        steps++; lam++;
        if (x > exc) exc = x;
        if (x < (u128)n) return (Res){fate[(u64)x], steps, exc};
        if (x == tortoise) break;                  /* cycle of length lam */
        if (lam == power) { tortoise = x; power <<= 1; lam = 0; }
        if (steps >= STEPCAP) return (Res){F_CAP, steps, exc};
    }
    u128 mn = x, y = stepf(mp, x);
    while (y != x) { if (y < mn) mn = y; y = stepf(mp, y); }
    return (Res){register_cycle(cs, mn, lam), steps, exc};
}

/* -------------------------------------------------------- rigidity probe */

#define NMODS 12
#define RSUM  165                       /* sum of RMODS */
static const int RMODS[NMODS] = {2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 36};

static int fidx(int code) {
    if (code >= 1 && code <= MAXCYC) return code - 1;
    if (code == F_XCYC) return MAXCYC;
    if (code == F_OVER) return MAXCYC + 1;
    return MAXCYC + 2;                  /* F_CAP */
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

/* H(fate | n mod m) in bits over n in (N/2, N]; min over RMODS + argmin.
 * Ascending RMODS with strict-improvement comparison => the SMALLEST modulus
 * achieving the minimum is reported. */
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

/* ----------------------------------------------------------- full census */

/* fate[] needs no clearing: n is processed in ascending order and classify
 * only reads fate[x] for 1 <= x < n, all of which were just written. */
static void run_census(const Map *mp, u64 N, uint8_t *fate, Census *cs) {
    memset(cs, 0, sizeof *cs);
    for (u64 n = 1; n <= N; n++) {
        Res r = classify(mp, n, fate, cs);
        fate[n] = (uint8_t)r.code;
        cs->cnt[r.code]++;
        cs->sum_steps += r.steps;
        if (r.exc > cs->max_exc) cs->max_exc = r.exc;
    }
    rigidity_probe(N, fate, cs);
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

    /* cycles ordered by basin size, descending (ties: discovery order) */
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

/* fixed-seed xorshift64 => deterministic grid3 subsample */
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
    for (u64 k = 0; k < nsamp; k++) {          /* partial Fisher-Yates */
        u64 j = k + xorshift64() % (npool - k);
        Map t = pool[k]; pool[k] = pool[j]; pool[j] = t;
        add_map(pool[k]);
    }
    free(pool);
}

/* ------------------------------------------------------------ sweep loop */

static void run_all(u64 N) {
    int nthreads = 1;
#ifdef _OPENMP
    nthreads = omp_get_max_threads();
#endif
    fprintf(stderr, "family: %d maps, N=%llu, stepcap=%llu, threads=%d\n",
            nmaps, (ull)N, (ull)STEPCAP, nthreads);
    if (nmaps == 0) { fprintf(stderr, "no maps to run\n"); exit(1); }
    char *rows = (char *)malloc((size_t)nmaps * ROWLEN);
    if (!rows) { fprintf(stderr, "out of memory for rows\n"); exit(2); }
    time_t t0 = time(NULL);
    int done = 0;
#ifdef _OPENMP
#pragma omp parallel
#endif
    {
        uint8_t *fate = (uint8_t *)malloc(N + 1);
        if (!fate) { fprintf(stderr, "cannot allocate fate array\n"); exit(2); }
#ifdef _OPENMP
#pragma omp for schedule(dynamic)
#endif
        for (int k = 0; k < nmaps; k++) {
            Census cs;
            run_census(&maps[k], N, fate, &cs);
            format_row(&maps[k], N, &cs, rows + (size_t)k * ROWLEN);
            if (cs.xcyc)
                fprintf(stderr, "note: map #%d cycle registry saturated (>%d cycles)\n",
                        k, MAXCYC);
            int dn;
#ifdef _OPENMP
#pragma omp critical(progress)
#endif
            { dn = ++done; }
            if (dn == nmaps || dn % 100 == 0 || nmaps <= 20)
                fprintf(stderr, "[%llus] %d/%d maps\n",
                        (ull)(time(NULL) - t0), dn, nmaps);
        }
        free(fate);
    }
    tsv_header(stdout);
    for (int k = 0; k < nmaps; k++) fputs(rows + (size_t)k * ROWLEN, stdout);
    fflush(stdout);
    free(rows);
    fprintf(stderr, "family: done in %llus\n", (ull)(time(NULL) - t0));
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
    fprintf(stderr, "family selftest, N=%llu\n", (ull)N);

    /* validity rules */
    Map bad1 = mk2(NULL, 0, 0, 3, 1);   /* row0 (0,0): f(2q) = 0        */
    Map bad2 = mk2(NULL, 1, 0, 1, 0);   /* row1 b=0:   f(1)  = 0        */
    Map ok1  = mk2(NULL, 1, 0, 6, 4);
    check(!map_valid(&bad1), "validity: row0 (0,0) rejected");
    check(!map_valid(&bad2), "validity: row1 (a,0) rejected (f(1)=0)");
    check(map_valid(&ok1),   "validity: COLLATZ accepted");

    uint8_t *fate = (uint8_t *)malloc(N + 1);
    if (!fate) { fprintf(stderr, "alloc failed\n"); return 2; }
    Census cs;
    tsv_header(stderr);

    Map m = mk2("COLLATZ", 1, 0, 6, 4);
    run_census(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 1 && has_cycle(&cs, 1, 3), "COLLATZ: exactly 1 cycle, (min,len)=(1,3)");
    check(cs.cnt[1] == N,                        "COLLATZ: 100% absorbed into cycle 1");
    check(cs.cnt[F_OVER] == 0 && cs.cnt[F_CAP] == 0, "COLLATZ: no overflow, no step-cap");
    check(cs.rig_H < 1e-12,                      "COLLATZ: rigidity H = 0 (fate constant)");

    m = mk2("NEG3X", 1, 0, 6, 2);
    run_census(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 3, "NEG3X: exactly 3 cycles");
    check(has_cycle(&cs, 1, 2) && has_cycle(&cs, 5, 5) && has_cycle(&cs, 17, 18),
          "NEG3X: cycle (min,len) = (1,2),(5,5),(17,18)");
    check(cs.cnt[1] + cs.cnt[2] + cs.cnt[3] == N, "NEG3X: all n absorbed into a cycle");
    check(cs.cnt[F_OVER] == 0 && cs.cnt[F_CAP] == 0, "NEG3X: no overflow, no step-cap");
    check(cs.rig_H > 0.1, "NEG3X: rigidity H > 0.1 (fates mix across residues)");

    m = mk2("FIVEX", 1, 0, 10, 6);
    run_census(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 3, "FIVEX: exactly 3 cycles");
    check(has_cycle(&cs, 1, 7) && has_cycle(&cs, 13, 10) && has_cycle(&cs, 17, 10),
          "FIVEX: cycle (min,len) = (1,7),(13,10),(17,10)");
    check(cs.cnt[F_OVER] > N / 2, "FIVEX: majority overflow (presumed divergent)");

    m = mk2("HYDRA", 3, 0, 3, 1);
    run_census(&m, N, fate, &cs); st_row(&m, N, &cs);
    check(cs.ncyc == 1 && has_cycle(&cs, 1, 1), "HYDRA: single cycle = fixed point at 1");
    check(cs.cnt[1] == 1,                        "HYDRA: only n=1 is cyclic");
    check(cs.cnt[F_OVER] == N - 1,               "HYDRA: all n>1 overflow");

    m = mk2("RIGID", 1, 0, 1, 1);
    run_census(&m, N, fate, &cs); st_row(&m, N, &cs);
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
        "env: FAMILY_STEPCAP overrides the step cap (default 50000)\n",
        prog, prog, prog, prog, prog);
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(argv[0]); return 1; }
    const char *sc = getenv("FAMILY_STEPCAP");
    if (sc && atoll(sc) > 0) {
        STEPCAP = (u64)atoll(sc);
        fprintf(stderr, "family: STEPCAP overridden to %llu\n", (ull)STEPCAP);
    }
    const char *nt = getenv("FAMILY_NOTRAP");
    if (nt && atoi(nt) != 0) {
        TRAP_OFF = 1;
        fprintf(stderr, "family: translation-trap fast path DISABLED\n");
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
