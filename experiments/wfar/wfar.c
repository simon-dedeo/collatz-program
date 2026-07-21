/*
 * wfar.c — Weighted (arctic / WFAR-style) divergence-exclusion certificates
 * for the Collatz map  T(n) = n/2 (n even),  3n+1 (n odd).
 *
 * A weighted certificate is (A, w, beta, delta; A', L0):
 *   A  : complete DFA over {0,1} (value automaton), weight w: states -> Q,
 *        beta >= 0, defining V(n) = w(state of A after enc(n)) + beta*len(n);
 *   A' : domain DFA, D = { n : A' accepts enc(n) };
 *   L0 : length cutoff, N0 = 2^(L0-1);
 *   condition (one-step drift): for all n in D with len(n) >= L0,
 *        V(T(n)) <= V(n) - delta.
 * Soundness (README Lemma 1): no orbit tail stays in D /\ [N0,oo); hence no
 * divergent orbit eventually remains in D.  Global D = N would prove Collatz
 * (Lemma 2) => any feasible global/cofinite domain is treated as a BUG.
 *
 * ENCODING (as dfacert.c): n >= 1 LSB-first binary; valid encodings end '1'.
 * Even step = drop first char (dlen = -1); odd step = 3n+1 carry transducer
 * (carry in {0,1,2}, starts 1, flush emits 1..2 bits, dlen in {+1,+2}).
 *
 * VERIFICATION: exact product BFS enumerates every realized end-triple
 * (p, q, dlen) = (A-state on enc(n), A-state on enc(T(n)), len change) over
 * all n in D, len >= L0.  Each triple is one linear constraint
 *        w[q] - w[p] + beta*dlen <= -delta.
 * SYNTHESIS: delta = 1 and w[0] = 0 WLOG (homogeneity / translation
 * invariance); feasibility of (w, beta) decided by an exact-rational
 * Fourier-Motzkin eliminator; witnesses re-checked against every original
 * constraint and validated by simulating up to 1e5 actual Collatz steps.
 *
 * v1 sweep: A' = A over all canonical initially-connected q-state tables
 * (dfacert enumerator) x all 2^q accepting sets, q <= 3.
 *
 * Build:  cc -O2 -Wall -Wextra -std=c11 -o wfar wfar.c            (mac)
 *         gcc -O2 -Wall -Wextra -std=c11 -fopenmp -o wfar wfar.c  (linux)
 * Usage:  ./wfar --selftest        property tests + mandatory controls
 *         ./wfar <q> [L0]          sweep canonical q-state tables (L0 >= 1)
 * Exit:   3 = simulation contradicts LP (bug); 4 = feasible global/cofinite
 *         certificate (bug per Lemma 2).
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <time.h>

#ifdef _OPENMP
#include <omp.h>
#else
static int omp_get_max_threads(void) { return 1; }
#endif

#define MAXQ    5           /* max DFA states (sweep uses <= 3)            */
#define NV      MAXQ        /* max LP vars: w[1..q-1], beta                */
#define MAXBITS 200
#define MAXL0   8
#define MAXROWS 200000      /* FM stage cap (never approached at q <= 3)   */

typedef struct {
    int q;                  /* number of states; start state is 0 */
    uint8_t d[MAXQ][2];     /* transition table */
    uint32_t F;             /* accepting set bitmask */
} DFA;

static void die(const char *msg)
{
    fprintf(stderr, "FATAL: %s\n", msg);
    exit(2);
}

/* ------------------------------------------------------------------ */
/* Encoding + transducer (ported from dfacert.c)                       */
/* ------------------------------------------------------------------ */

static int encode_bits(unsigned __int128 n, char *buf)
{
    int len = 0;
    while (n) { buf[len++] = (char)('0' + (int)(n & 1)); n >>= 1; }
    buf[len] = '\0';
    return len;
}

static unsigned __int128 decode_bits(const char *w, int len)
{
    unsigned __int128 n = 0;
    for (int i = len - 1; i >= 0; i--)
        n = (n << 1) | (unsigned)(w[i] - '0');
    return n;
}

static int transduce3np1(const char *in, int len, char *out)
{
    int c = 1, o = 0;
    for (int i = 0; i < len; i++) {
        int s = 3 * (in[i] - '0') + c;
        out[o++] = (char)('0' + (s & 1));
        c = s >> 1;                       /* c stays in {0,1,2} */
    }
    while (c) { out[o++] = (char)('0' + (c & 1)); c >>= 1; }
    out[o] = '\0';
    return o;
}

static int dfa_run(const DFA *A, const char *w, int len)
{
    int s = 0;
    for (int i = 0; i < len; i++) s = A->d[s][w[i] - '0'];
    return s;
}

/* membership of a VALID encoding (callers pass encode_bits output) */
static int dfa_accept_enc(const DFA *A, const char *w, int len)
{
    return (int)((A->F >> dfa_run(A, w, len)) & 1u);
}

static unsigned __int128 Tstep(unsigned __int128 n)
{
    return (n & 1) ? 3 * n + 1 : n >> 1;
}

/* ------------------------------------------------------------------ */
/* Exact rationals (long long num/den, __int128 intermediates)         */
/* ------------------------------------------------------------------ */

typedef struct { long long n, d; } Rat;   /* d > 0, gcd-reduced */

static __int128 gcd128(__int128 a, __int128 b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { __int128 t = a % b; a = b; b = t; }
    return a;
}

static Rat rmk128(__int128 n, __int128 d)
{
    if (d == 0) die("rat: zero denominator");
    if (d < 0) { n = -n; d = -d; }
    __int128 g = gcd128(n, d);
    if (g == 0) g = 1;
    n /= g; d /= g;
    if (n > (__int128)INT64_MAX || n < (__int128)INT64_MIN ||
        d > (__int128)INT64_MAX)
        die("rat: overflow after reduction");
    Rat r; r.n = (long long)n; r.d = (long long)d;
    return r;
}

static Rat rint_(long long v) { Rat r = { v, 1 }; return r; }
static Rat radd(Rat a, Rat b)
{ return rmk128((__int128)a.n * b.d + (__int128)b.n * a.d, (__int128)a.d * b.d); }
static Rat rsub(Rat a, Rat b)
{ return rmk128((__int128)a.n * b.d - (__int128)b.n * a.d, (__int128)a.d * b.d); }
static Rat rmul(Rat a, Rat b)
{ return rmk128((__int128)a.n * b.n, (__int128)a.d * b.d); }
static Rat rdiv(Rat a, Rat b)
{
    if (b.n == 0) die("rat: division by zero");
    return rmk128((__int128)a.n * b.d, (__int128)a.d * b.n);
}
static int rcmp(Rat a, Rat b)
{
    __int128 l = (__int128)a.n * b.d, r = (__int128)b.n * a.d;
    return (l < r) ? -1 : (l > r ? 1 : 0);
}
static int rsgn(Rat a) { return (a.n < 0) ? -1 : (a.n > 0 ? 1 : 0); }

/* ------------------------------------------------------------------ */
/* Linear inequality systems:  sum_j c[j]*u[j] <= rhs                  */
/* ------------------------------------------------------------------ */

typedef struct { Rat c[NV]; Rat rhs; } Row;
typedef struct { Row *r; int n, cap; } Sys;

static void sys_init(Sys *s) { s->r = NULL; s->n = 0; s->cap = 0; }
static void sys_free(Sys *s) { free(s->r); s->r = NULL; s->n = s->cap = 0; }

static void sys_push(Sys *s, const Row *row)
{
    if (s->n >= MAXROWS) die("FM: row cap exceeded (raise MAXROWS)");
    if (s->n == s->cap) {
        s->cap = s->cap ? 2 * s->cap : 64;
        if (s->cap > MAXROWS) s->cap = MAXROWS;
        s->r = (Row *)realloc(s->r, (size_t)s->cap * sizeof(Row));
        if (!s->r) die("out of memory");
    }
    s->r[s->n++] = *row;
}

static void sys_copy(Sys *dst, const Sys *src)
{
    sys_init(dst);
    for (int i = 0; i < src->n; i++) sys_push(dst, &src->r[i]);
}

static Row row_zero(void)
{
    Row r;
    for (int j = 0; j < NV; j++) r.c[j] = rint_(0);
    r.rhs = rint_(0);
    return r;
}

/* scale so the first nonzero coefficient has |.| = 1.
 * returns 1 keep, 0 drop (trivially true), -1 infeasible constant row. */
static int row_normalize(Row *r)
{
    int j0 = -1;
    for (int j = 0; j < NV; j++)
        if (r->c[j].n != 0) { j0 = j; break; }
    if (j0 < 0) return (rsgn(r->rhs) < 0) ? -1 : 0;
    Rat s = r->c[j0];
    if (s.n < 0) s.n = -s.n;               /* positive scale preserves <= */
    for (int j = j0; j < NV; j++) r->c[j] = rdiv(r->c[j], s);
    r->rhs = rdiv(r->rhs, s);
    return 1;
}

static int row_cmp_qsort(const void *pa, const void *pb)
{
    const Row *a = (const Row *)pa, *b = (const Row *)pb;
    for (int j = 0; j < NV; j++) {
        int s = rcmp(a->c[j], b->c[j]);
        if (s) return s;
    }
    return rcmp(a->rhs, b->rhs);
}

static int row_coeffs_eq(const Row *a, const Row *b)
{
    for (int j = 0; j < NV; j++)
        if (rcmp(a->c[j], b->c[j]) != 0) return 0;
    return 1;
}

/* normalize all rows, drop trivial, dedupe (same coeffs -> keep min rhs).
 * returns 1 if an infeasible constant row was found (0 <= rhs < 0).      */
static int sys_normalize(Sys *s)
{
    int w = 0;
    for (int i = 0; i < s->n; i++) {
        Row r = s->r[i];
        int k = row_normalize(&r);
        if (k < 0) return 1;
        if (k == 0) continue;
        s->r[w++] = r;
    }
    s->n = w;
    if (s->n > 1) {
        qsort(s->r, (size_t)s->n, sizeof(Row), row_cmp_qsort);
        w = 0;
        for (int i = 0; i < s->n; i++) {
            if (w > 0 && row_coeffs_eq(&s->r[w - 1], &s->r[i]))
                continue;                    /* sorted: earlier rhs is <= */
            s->r[w++] = s->r[i];
        }
        s->n = w;
    }
    return 0;
}

/* eliminate variable k: keep zero rows, combine every (pos, neg) pair.   */
static void fm_eliminate(const Sys *in, int k, Sys *out)
{
    sys_init(out);
    for (int i = 0; i < in->n; i++)
        if (in->r[i].c[k].n == 0) sys_push(out, &in->r[i]);
    for (int i = 0; i < in->n; i++) {
        if (rsgn(in->r[i].c[k]) <= 0) continue;          /* pos rows */
        for (int j = 0; j < in->n; j++) {
            if (rsgn(in->r[j].c[k]) >= 0) continue;      /* neg rows */
            Rat s1 = in->r[j].c[k]; s1.n = -s1.n;        /* -neg > 0  */
            Rat s2 = in->r[i].c[k];                      /*  pos > 0  */
            Row nr = row_zero();
            for (int t = 0; t < NV; t++)
                nr.c[t] = radd(rmul(s1, in->r[i].c[t]),
                               rmul(s2, in->r[j].c[t]));
            nr.c[k] = rint_(0);                          /* exact anyway */
            nr.rhs = radd(rmul(s1, in->r[i].rhs), rmul(s2, in->r[j].rhs));
            sys_push(out, &nr);
        }
    }
}

/* Fourier-Motzkin feasibility over variables 0..nv-1.
 * If wit != NULL and feasible: back-substitute a witness through the
 * stored stages and exact-check it against every row of `orig`.         */
static int fm_feasible(const Sys *orig, int nv, Rat *wit)
{
    Sys st[NV + 1];
    int built = 0, feas = 1;
    sys_copy(&st[0], orig);
    built = 1;
    if (sys_normalize(&st[0])) feas = 0;
    for (int k = 0; feas && k < nv; k++) {
        fm_eliminate(&st[k], k, &st[k + 1]);
        built = k + 2;
        if (sys_normalize(&st[k + 1])) feas = 0;
    }
    if (feas && wit) {
        for (int k = nv - 1; k >= 0; k--) {
            int haslo = 0, hashi = 0;
            Rat lo = rint_(0), hi = rint_(0);
            const Sys *S = &st[k];
            for (int i = 0; i < S->n; i++) {
                if (S->r[i].c[k].n == 0) continue;
                Rat rest = rint_(0);
                for (int t = k + 1; t < nv; t++)
                    rest = radd(rest, rmul(S->r[i].c[t], wit[t]));
                Rat bnd = rdiv(rsub(S->r[i].rhs, rest), S->r[i].c[k]);
                if (rsgn(S->r[i].c[k]) > 0) {
                    if (!hashi || rcmp(bnd, hi) < 0) hi = bnd;
                    hashi = 1;
                } else {
                    if (!haslo || rcmp(bnd, lo) > 0) lo = bnd;
                    haslo = 1;
                }
            }
            if (haslo && hashi && rcmp(lo, hi) > 0)
                die("FM back-substitution: empty interval (bug)");
            Rat zero = rint_(0);
            if ((!haslo || rcmp(lo, zero) <= 0) &&
                (!hashi || rcmp(zero, hi) <= 0))
                wit[k] = zero;
            else if (haslo && rsgn(lo) > 0 &&
                     (!hashi || rcmp(lo, hi) <= 0))
                wit[k] = lo;
            else if (hashi)
                wit[k] = hi;
            else
                wit[k] = lo;
        }
        /* exact re-check against the ORIGINAL system */
        for (int i = 0; i < orig->n; i++) {
            Rat lhs = rint_(0);
            for (int t = 0; t < nv; t++)
                lhs = radd(lhs, rmul(orig->r[i].c[t], wit[t]));
            if (rcmp(lhs, orig->r[i].rhs) > 0)
                die("FM witness violates an original constraint (bug)");
        }
    }
    for (int k = 0; k < built; k++) sys_free(&st[k]);
    return feas;
}

/* ------------------------------------------------------------------ */
/* Constraint generation: exact product BFS                            */
/* ------------------------------------------------------------------ */

/* One constraint per realized triple (p, q, dlen):
 *     w[q] - w[p] + beta*dlen <= -1        (delta = 1 normalized)
 * Variables (nv = qv): 0..qv-2 = w[1..qv-1] (w[0] = 0 fixed),
 * var qv-1 = beta.                                                     */
typedef struct {
    Sys sys;
    int qv;                      /* value-automaton state count */
    uint8_t trip[MAXQ][MAXQ][3]; /* dlen -1 -> 0, +1 -> 1, +2 -> 2 */
    int ntrip;
} CGen;

static void cgen_init(CGen *G, int qv)
{
    sys_init(&G->sys);
    memset(G->trip, 0, sizeof G->trip);
    G->ntrip = 0;
    G->qv = qv;
}

static void cgen_add(CGen *G, int p, int q, int dlen)
{
    int di = (dlen < 0) ? 0 : (dlen == 1 ? 1 : 2);
    if (G->trip[p][q][di]) return;
    G->trip[p][q][di] = 1;
    G->ntrip++;
    Row r = row_zero();
    if (q > 0) r.c[q - 1] = radd(r.c[q - 1], rint_(1));
    if (p > 0) r.c[p - 1] = radd(r.c[p - 1], rint_(-1));
    r.c[G->qv - 1] = radd(r.c[G->qv - 1], rint_(dlen));  /* beta slot */
    r.rhs = rint_(-1);
    sys_push(&G->sys, &r);
}

/* apply the end-of-word carry flush to the output-side value state.   */
static int flush_state(const DFA *Av, int y, int c, int *dlen)
{
    int k = 0;
    while (c) { y = Av->d[y][c & 1]; c >>= 1; k++; }
    *dlen = k;
    return y;
}

/* EVEN steps: enc(n) = 0 v, T(n) = v (drop first char), dlen = -1.
 * BFS state (x, y, z, l): x = Av on full input from d[0][0], y = Av on
 * the suffix v from 0, z = Ad on full input from its d[0][0], l = capped
 * length min(len, L0).  Completion at each '1'-transition.             */
static void gen_even(const DFA *Av, const DFA *Ad, int L0, CGen *G)
{
    uint8_t seen[MAXQ * MAXQ * MAXQ * MAXL0];
    int queue[MAXQ * MAXQ * MAXQ * MAXL0], qh = 0, qt = 0;
    memset(seen, 0, sizeof seen);
#define EIDX(x, y, z, l) ((((x) * MAXQ + (y)) * MAXQ + (z)) * MAXL0 + ((l) - 1))
    int x0 = Av->d[0][0], y0 = 0, z0 = Ad->d[0][0];
    int l0 = (1 < L0) ? 1 : L0;
    int st = EIDX(x0, y0, z0, l0);
    seen[st] = 1; queue[qt++] = st;
    while (qh < qt) {
        int pk = queue[qh++];
        int l = pk % MAXL0 + 1, z = (pk / MAXL0) % MAXQ,
            y = (pk / (MAXL0 * MAXQ)) % MAXQ, x = pk / (MAXL0 * MAXQ * MAXQ);
        for (int b = 0; b < 2; b++) {
            int nx = Av->d[x][b], ny = Av->d[y][b], nz = Ad->d[z][b];
            int nl = (l + 1 < L0) ? l + 1 : L0;
            if (b == 1 && ((Ad->F >> nz) & 1u) && nl >= L0)
                cgen_add(G, nx, ny, -1);
            int np = EIDX(nx, ny, nz, nl);
            if (!seen[np]) { seen[np] = 1; queue[qt++] = np; }
        }
    }
#undef EIDX
}

/* ODD steps: enc(n) starts (and ends) with '1'; output = 3n+1 transducer.
 * BFS state (x, y, z, c, l): x = Av on input, y = Av on output emitted so
 * far (one bit per input bit), z = Ad on input, c = carry, l capped len.
 * First bit forced '1' (s = 3+1 = 4: emit 0, carry 2); at each further
 * '1'-transition the word may end: flush carry (in {1,2}) into y giving
 * dlen = +1 or +2, output ends '1' (valid encoding).                    */
static void gen_odd(const DFA *Av, const DFA *Ad, int L0, CGen *G)
{
    uint8_t seen[MAXQ * MAXQ * MAXQ * 3 * MAXL0];
    int queue[MAXQ * MAXQ * MAXQ * 3 * MAXL0], qh = 0, qt = 0;
    memset(seen, 0, sizeof seen);
#define OIDX(x, y, z, c, l) \
    (((((x) * MAXQ + (y)) * MAXQ + (z)) * 3 + (c)) * MAXL0 + ((l) - 1))
    int x0 = Av->d[0][1], y0 = Av->d[0][0], z0 = Ad->d[0][1], c0 = 2;
    if (((Ad->F >> z0) & 1u) && 1 >= L0) {          /* word "1" (n = 1)  */
        int dl, yf = flush_state(Av, y0, c0, &dl);
        cgen_add(G, x0, yf, dl);
    }
    int l0 = (1 < L0) ? 1 : L0;
    int st = OIDX(x0, y0, z0, c0, l0);
    seen[st] = 1; queue[qt++] = st;
    while (qh < qt) {
        int pk = queue[qh++];
        int l = pk % MAXL0 + 1, c = (pk / MAXL0) % 3,
            z = (pk / (MAXL0 * 3)) % MAXQ,
            y = (pk / (MAXL0 * 3 * MAXQ)) % MAXQ,
            x = pk / (MAXL0 * 3 * MAXQ * MAXQ);
        for (int b = 0; b < 2; b++) {
            int s = 3 * b + c, e = s & 1, nc = s >> 1;
            int nx = Av->d[x][b], ny = Av->d[y][e], nz = Ad->d[z][b];
            int nl = (l + 1 < L0) ? l + 1 : L0;
            if (b == 1 && ((Ad->F >> nz) & 1u) && nl >= L0) {
                int dl, yf = flush_state(Av, ny, nc, &dl);
                cgen_add(G, nx, yf, dl);
            }
            int np = OIDX(nx, ny, nz, nc, nl);
            if (!seen[np]) { seen[np] = 1; queue[qt++] = np; }
        }
    }
#undef OIDX
}

/* Full constraint system for (Av, Ad, L0); rows are the drift constraints
 * only — callers append side rows (beta >= 0, optionally beta <= 0).    */
static void gen_constraints(const DFA *Av, const DFA *Ad, int L0, CGen *G)
{
    if (L0 < 1 || L0 > MAXL0) die("L0 out of range");
    cgen_init(G, Av->q);
    gen_even(Av, Ad, L0, G);
    gen_odd(Av, Ad, L0, G);
}

static Row row_beta_sign(int qv, int sign)   /* sign*beta <= 0 */
{
    Row r = row_zero();
    r.c[qv - 1] = rint_(sign);
    r.rhs = rint_(0);
    return r;
}

/* ------------------------------------------------------------------ */
/* Domain-language classification (exact)                              */
/* ------------------------------------------------------------------ */

/* Properties of L(T,F) /\ C, C = words ending in '1' (== enc images).
 * Reach_l = states reachable by words of length l; a member of length l
 * exists iff some s in Reach_{l-1} has d[s][1] in F.  The subset
 * trajectory Reach_0, Reach_1, ... is eventually periodic with
 * preperiod + period <= 2^q + 2^q, so scanning l = 1..(3*2^q + q + 4)
 * decides everything.  A member of length >= q pumps (its run visits
 * l+1 > q states; pumping an interior loop keeps the final '1'), so:
 *   infinite  <=>  a member of length >= q exists (first one appears
 *                  within the scan window by periodicity).             */
static void lang_props(const DFA *A, uint32_t F, int *nonempty, int *infinite)
{
    int q = A->q;
    int W = 3 * (1 << q) + q + 4;
    uint32_t reach = 1u;                     /* Reach_0 = {start} */
    *nonempty = 0; *infinite = 0;
    for (int l = 1; l <= W; l++) {
        for (int s = 0; s < q; s++)
            if (((reach >> s) & 1u) && ((F >> A->d[s][1]) & 1u)) {
                *nonempty = 1;
                if (l >= q) *infinite = 1;
                break;
            }
        uint32_t nr = 0;
        for (int s = 0; s < q; s++)
            if ((reach >> s) & 1u) {
                nr |= 1u << A->d[s][0];
                nr |= 1u << A->d[s][1];
            }
        reach = nr;
    }
}

/* D global (= all n) iff complement /\ C empty; D cofinite iff
 * complement /\ C finite.                                              */
static void domain_class(const DFA *Ad, int *nonempty, int *infinite,
                         int *global, int *cofinite)
{
    uint32_t mask = (1u << Ad->q) - 1u;
    int cne, cinf;
    lang_props(Ad, Ad->F, nonempty, infinite);
    lang_props(Ad, (~Ad->F) & mask, &cne, &cinf);
    *global = !cne;
    *cofinite = !cinf;
}

/* smallest members of D (by value) and a membership fingerprint mask   */
static int domain_samples(const DFA *Ad, int L0,
                          unsigned long long *out, int maxout,
                          uint64_t *fingerprint)
{
    char buf[MAXBITS];
    int cnt = 0;
    uint64_t fp = 0;
    for (unsigned long long n = 1; n <= (1ULL << 17); n++) {
        int len = encode_bits(n, buf);
        if (len < L0) continue;
        if (!dfa_accept_enc(Ad, buf, len)) continue;
        if (n <= 64) fp |= 1ULL << (n - 1);
        if (cnt < maxout) out[cnt] = n;
        cnt++;
        if (cnt >= maxout && n > 64) break;
    }
    *fingerprint = fp;
    return cnt < maxout ? cnt : maxout;
}

/* ------------------------------------------------------------------ */
/* Independent checks: brute-force coverage + orbit simulation          */
/* ------------------------------------------------------------------ */

/* every actual step n -> T(n), n <= nmax, n in D, len >= L0, must hit a
 * generated (p, q, dlen) triple.  (BFS configs are realized by real
 * words, so generated == actual; this checks the critical direction.)  */
static void brute_check_cgen(const DFA *Av, const DFA *Ad, int L0,
                             const CGen *G, unsigned long long nmax)
{
    char u[MAXBITS], v[MAXBITS];
    for (unsigned long long n = 1; n <= nmax; n++) {
        int lu = encode_bits(n, u);
        if (lu < L0) continue;
        if (!dfa_accept_enc(Ad, u, lu)) continue;
        int p = dfa_run(Av, u, lu);
        int lv = encode_bits(Tstep(n), v);
        int q = dfa_run(Av, v, lv);
        int dl = lv - lu;
        if (dl != -1 && dl != 1 && dl != 2)
            die("brute check: impossible dlen");
        int di = (dl < 0) ? 0 : (dl == 1 ? 1 : 2);
        if (!G->trip[p][q][di]) {
            fprintf(stderr, "brute check: n=%llu produced (p=%d,q=%d,dl=%d)"
                    " not in generated constraint set\n", n, p, q, dl);
            die("constraint generator missed a realized configuration");
        }
    }
}

/* Simulate real Collatz steps; every step taken at n in D (len >= L0)
 * must satisfy V(T(n)) - V(n) <= -1 for the given witness.  Returns the
 * number of checked steps; any violation aborts (exit 3).              */
static long long simulate_cert(const DFA *Av, const Rat *wfull, Rat beta,
                               const DFA *Ad, int L0, long long target)
{
    char u[MAXBITS], v[MAXBITS];
    long long checked = 0;
    Rat mone = rint_(-1);
    unsigned long long members[64];
    int nmem = 0;

    /* pass 1: scan small n */
    for (unsigned long long n = 1; n <= 2000000ULL && checked < target; n++) {
        int lu = encode_bits(n, u);
        if (lu < L0) continue;
        if (!dfa_accept_enc(Ad, u, lu)) continue;
        if (nmem < 64) members[nmem++] = n;
        int p = dfa_run(Av, u, lu);
        int lv = encode_bits(Tstep(n), v);
        int q = dfa_run(Av, v, lv);
        Rat dV = radd(rsub(wfull[q], wfull[p]), rmul(beta, rint_(lv - lu)));
        if (rcmp(dV, mone) > 0) {
            fprintf(stderr, "SIMULATION CONTRADICTS LP: n=%llu (p=%d,q=%d,"
                    "dlen=%d): dV=%lld/%lld > -1\n", n, p, q, lv - lu,
                    dV.n, dV.d);
            exit(3);
        }
        checked++;
    }
    /* pass 2: follow real orbits from the smallest members */
    for (int i = 0; i < nmem && checked < target; i++) {
        unsigned __int128 x = members[i];
        for (int s = 0; s < 5000 && checked < target; s++) {
            if (x > ((unsigned __int128)1 << 100)) break;
            int lu = encode_bits(x, u);
            if (lu >= L0 && dfa_accept_enc(Ad, u, lu)) {
                int p = dfa_run(Av, u, lu);
                int lv = encode_bits(Tstep(x), v);
                int q = dfa_run(Av, v, lv);
                Rat dV = radd(rsub(wfull[q], wfull[p]),
                              rmul(beta, rint_(lv - lu)));
                if (rcmp(dV, mone) > 0) {
                    fprintf(stderr, "SIMULATION CONTRADICTS LP (orbit): "
                            "n=%llu\n", (unsigned long long)x);
                    exit(3);
                }
                checked++;
            }
            x = Tstep(x);
        }
    }
    return checked;
}

/* ------------------------------------------------------------------ */
/* Printing                                                            */
/* ------------------------------------------------------------------ */

static void print_table_compact(FILE *f, const DFA *A)
{
    fprintf(f, "d=");
    for (int s = 0; s < A->q; s++)
        fprintf(f, "%s%d%d", s ? "." : "", A->d[s][0], A->d[s][1]);
    fprintf(f, " F={");
    int first = 1;
    for (int s = 0; s < A->q; s++)
        if ((A->F >> s) & 1u) { fprintf(f, "%s%d", first ? "" : ",", s); first = 0; }
    fprintf(f, "}");
}

static void print_witness(FILE *f, int qv, const Rat *wit)
{
    fprintf(f, "w=(0");
    for (int s = 1; s < qv; s++) {
        Rat r = wit[s - 1];
        if (r.d == 1) fprintf(f, ",%lld", r.n);
        else fprintf(f, ",%lld/%lld", r.n, r.d);
    }
    Rat b = wit[qv - 1];
    if (b.d == 1) fprintf(f, ") beta=%lld", b.n);
    else fprintf(f, ") beta=%lld/%lld", b.n, b.d);
    fprintf(f, " delta=1");
}

static void print_constraints(FILE *f, const CGen *G)
{
    fprintf(f, "constraints (%d realized triples):\n", G->ntrip);
    for (int p = 0; p < G->qv; p++)
        for (int q = 0; q < G->qv; q++)
            for (int di = 0; di < 3; di++)
                if (G->trip[p][q][di]) {
                    int dl = (di == 0) ? -1 : di;
                    fprintf(f, "  w[%d] - w[%d] %+d*beta <= -delta\n",
                            q, p, dl);
                }
}

/* ------------------------------------------------------------------ */
/* Canonical initially-connected DFA enumeration (ported from dfacert)  */
/* ------------------------------------------------------------------ */

typedef struct { uint8_t d[MAXQ][2]; } Table;

static int is_canonical_table(int q, const uint8_t d[][2])
{
    uint8_t seen[MAXQ] = {0};
    int order[MAXQ], nseen = 1;
    seen[0] = 1; order[0] = 0;
    for (int i = 0; i < nseen; i++) {
        int s = order[i];
        for (int b = 0; b < 2; b++) {
            int t = d[s][b];
            if (!seen[t]) {
                if (t != nseen) return 0;
                seen[t] = 1; order[nseen++] = t;
            }
        }
    }
    return nseen == q;
}

static void rec_tables(int q, int i, int m, uint8_t d[][2],
                       Table *out, int max, int *count)
{
    if (i == 2 * q) {
        if (*count >= max) die("table buffer too small");
        memcpy(out[*count].d, d, (size_t)MAXQ * 2);
        (*count)++;
        return;
    }
    if ((i & 1) == 0 && (i >> 1) > m) return;
    int hi = (m + 1 < q - 1) ? m + 1 : q - 1;
    for (int v = 0; v <= hi; v++) {
        d[i >> 1][i & 1] = (uint8_t)v;
        rec_tables(q, i + 1, v > m ? v : m, d, out, max, count);
    }
}

static int gen_canonical_tables(int q, Table *out, int max)
{
    uint8_t d[MAXQ][2];
    memset(d, 0, sizeof d);
    int count = 0;
    rec_tables(q, 0, 0, d, out, max, &count);
    for (int i = 0; i < count; i++)
        if (!is_canonical_table(q, out[i].d))
            die("enumerator produced a non-canonical table");
    return count;
}

static unsigned long long brute_count_canonical(int q)
{
    long long ntab = 1;
    for (int j = 0; j < 2 * q; j++) ntab *= q;
    unsigned long long count = 0;
    uint8_t d[MAXQ][2];
    for (long long idx = 0; idx < ntab; idx++) {
        long long t = idx;
        for (int j = 2 * q - 1; j >= 0; j--) {
            d[j >> 1][j & 1] = (uint8_t)(t % q);
            t /= q;
        }
        if (is_canonical_table(q, d)) count++;
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* Synthesis sweep: A' = A over canonical tables x accepting sets       */
/* ------------------------------------------------------------------ */

#define SIM_TARGET 100000LL
#define MAXFP 8192

typedef struct {
    long long pairs, empty, vacuous, infeasible, ginf, feasible;
    long long escape, drift, feas_finite;
    uint64_t fps[MAXFP];
    int nfp;
} Stats;

static void fp_add(Stats *S, uint64_t fp)
{
    for (int i = 0; i < S->nfp; i++)
        if (S->fps[i] == fp) return;
    if (S->nfp < MAXFP) S->fps[S->nfp++] = fp;
}

/* Feasible global/cofinite domain = would prove Collatz = bug (Lemma 2). */
static void bug_global(const DFA *Av, const DFA *Ad, int L0,
                       const CGen *G, const Rat *wit, int global)
{
    fprintf(stderr,
        "\n*** BUG: FEASIBLE %s-DOMAIN WEIGHTED CERTIFICATE ***\n"
        "A feasible certificate on a %s domain would prove the Collatz\n"
        "conjecture (README Lemma 2); at these sizes this is a checker bug\n"
        "with probability ~1.  Offending instance:\n",
        global ? "GLOBAL" : "COFINITE", global ? "global" : "cofinite");
    print_table_compact(stderr, Ad);
    fprintf(stderr, " L0=%d\n", L0);
    print_constraints(stderr, G);
    fprintf(stderr, "witness: ");
    print_witness(stderr, Av->q, wit);
    fprintf(stderr, "\nrunning independent orbit simulation "
            "(a violation would localize the bug as exit 3)...\n");
    Rat wfull[MAXQ];
    wfull[0] = rint_(0);
    for (int s = 1; s < Av->q; s++) wfull[s] = wit[s - 1];
    long long steps = simulate_cert(Av, wfull, wit[Av->q - 1], Ad, L0,
                                    SIM_TARGET);
    fprintf(stderr, "simulation checked %lld steps without violation — the\n"
            "bug is in constraint GENERATION (missing configuration), or\n"
            "the Collatz conjecture was just proven.  Investigate.\n", steps);
    exit(4);
}

static void sweep(int q, int L0)
{
    Table tabs[300];
    int nt = gen_canonical_tables(q, tabs, 300);
    Stats S;
    memset(&S, 0, sizeof S);
    fprintf(stderr, "q=%d L0=%d: %d canonical tables x %d accepting sets "
            "(threads=%d)\n", q, L0, nt, 1 << q, omp_get_max_threads());

#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic)
#endif
    for (int ti = 0; ti < nt; ti++) {
        for (uint32_t F = 0; F < (1u << q); F++) {
            DFA Ad, Av;
            Ad.q = Av.q = q;
            memcpy(Ad.d, tabs[ti].d, sizeof Ad.d);
            memcpy(Av.d, tabs[ti].d, sizeof Av.d);
            Ad.F = F;
            Av.F = 0;                       /* value automaton: F unused */

            int ne, inf, global, cofinite;
            domain_class(&Ad, &ne, &inf, &global, &cofinite);
            if (!ne) {
#ifdef _OPENMP
#pragma omp critical(stats)
#endif
                { S.pairs++; S.empty++; }
                continue;
            }
            CGen G;
            gen_constraints(&Av, &Ad, L0, &G);
            if (G.sys.n == 0) {             /* all members shorter than L0 */
#ifdef _OPENMP
#pragma omp critical(stats)
#endif
                { S.pairs++; S.vacuous++; }
                sys_free(&G.sys);
                continue;
            }
            Sys sys;
            sys_copy(&sys, &G.sys);
            Row bge0 = row_beta_sign(q, -1);        /* -beta <= 0 */
            sys_push(&sys, &bge0);
            Rat wit[NV];
            int feas = fm_feasible(&sys, q, wit);

            if (feas && (global || cofinite))
                bug_global(&Av, &Ad, L0, &G, wit, global);   /* exits */

            int escape = 0;
            long long steps = 0;
            unsigned long long smp[8];
            int nsmp = 0;
            uint64_t fp = 0;
            if (feas) {
                Sys sys0;
                sys_copy(&sys0, &sys);
                Row ble0 = row_beta_sign(q, +1);    /* +beta <= 0 */
                sys_push(&sys0, &ble0);
                escape = fm_feasible(&sys0, q, NULL);
                sys_free(&sys0);
                Rat wfull[MAXQ];
                wfull[0] = rint_(0);
                for (int s = 1; s < q; s++) wfull[s] = wit[s - 1];
                steps = simulate_cert(&Av, wfull, wit[q - 1], &Ad, L0,
                                      SIM_TARGET);
                nsmp = domain_samples(&Ad, L0, smp, 8, &fp);
            }
#ifdef _OPENMP
#pragma omp critical(stats)
#endif
            {
                S.pairs++;
                if (!feas) {
                    S.infeasible++;
                    if (global) S.ginf++;
                } else {
                    S.feasible++;
                    if (escape) S.escape++; else S.drift++;
                    if (!inf) S.feas_finite++;
                    fp_add(&S, fp);
                    printf("CERT q=%d L0=%d tab=%d ", q, L0, ti);
                    print_table_compact(stdout, &Ad);
                    printf(" type=%s D=%s members=",
                           escape ? "escape" : "drift",
                           inf ? "infinite" : "finite");
                    for (int i = 0; i < nsmp; i++)
                        printf("%s%llu", i ? "," : "", smp[i]);
                    printf(" ");
                    print_witness(stdout, q, wit);
                    printf(" sim=%lld\n", steps);
                }
            }
            sys_free(&sys);
            sys_free(&G.sys);
        }
    }
    printf("q=%d L0=%d: pairs=%lld emptyD=%lld vacuous=%lld "
           "infeasible=%lld (globalD=%lld) feasible=%lld [escape=%lld, "
           "drift=%lld] fingerprints=%d finiteD=%lld\n",
           q, L0, S.pairs, S.empty, S.vacuous, S.infeasible, S.ginf,
           S.feasible, S.escape, S.drift, S.nfp, S.feas_finite);
    fflush(stdout);
}

/* ------------------------------------------------------------------ */
/* Selftest: machinery ports, FM unit tests, mandatory controls        */
/* ------------------------------------------------------------------ */

static uint64_t xs_state;
static uint64_t xorshift64(void)
{
    uint64_t x = xs_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return xs_state = x;
}

#define CHECK(cond, msg) \
    do { if (!(cond)) { fprintf(stderr, "SELFTEST FAILED: %s\n", msg); \
         return 0; } } while (0)

/* hand DFAs used by the controls */
static const DFA A_all1   = { 1, {{0,0}}, 1u };                 /* D = N   */
static const DFA A_first0 = { 3, {{1,2},{1,1},{2,2}}, 1u<<1 };  /* evens   */
static const DFA A_first1 = { 3, {{1,2},{1,1},{2,2}}, 1u<<2 };  /* odds    */
static const DFA A_geq2   = { 3, {{1,1},{2,2},{2,2}}, 1u<<2 };  /* n >= 2  */
static const DFA A_only3  = { 4, {{3,1},{3,2},{3,3},{3,3}}, 1u<<2 }; /* {3} */

static Row mk_row(const int *co, int nv, int rhs)
{
    Row r = row_zero();
    for (int j = 0; j < nv; j++) r.c[j] = rint_(co[j]);
    r.rhs = rint_(rhs);
    return r;
}

static int selftest(void)
{
    char wa[MAXBITS], wb[MAXBITS], wc[MAXBITS];
    int la, lb, lc;

    /* --- transducer / encoding (ported from dfacert) ------------------ */
    la = transduce3np1("1", 1, wa);
    CHECK(la == 3 && strcmp(wa, "001") == 0, "T(1) != 001");
    la = transduce3np1("11", 2, wa);
    CHECK(la == 4 && strcmp(wa, "0101") == 0, "T(3) != 0101");
    la = transduce3np1("101", 3, wa);
    CHECK(la == 5 && strcmp(wa, "00001") == 0, "T(5) != 00001");
    xs_state = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 100000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 60) - 1)) | 1ULL;
        unsigned __int128 t = (unsigned __int128)3 * n + 1;
        la = encode_bits(n, wa);
        lb = encode_bits(t, wb);
        lc = transduce3np1(wa, la, wc);
        CHECK(lc == lb && memcmp(wb, wc, (size_t)lc) == 0,
              "transducer != arithmetic 3n+1");
        CHECK(lc == la + 1 || lc == la + 2 || lc == la,
              "odd dlen not in {0,+1,+2}");
        CHECK(wc[lc - 1] == '1', "transducer output not ending in 1");
    }
    for (int i = 0; i < 20000; i++) {
        uint64_t k = (xorshift64() & ((1ULL << 59) - 1)) + 1;
        la = encode_bits(2 * k, wa);
        lb = encode_bits(k, wb);
        CHECK(wa[0] == '0' && la == lb + 1 &&
              memcmp(wa + 1, wb, (size_t)lb) == 0,
              "even step != drop first char");
        uint64_t n = (xorshift64() & ((1ULL << 62) - 1)) + 1;
        la = encode_bits(n, wa);
        CHECK((uint64_t)decode_bits(wa, la) == n && wa[la - 1] == '1',
              "encode/decode roundtrip");
    }
    fprintf(stderr, "selftest: transducer/encoding ok (1e5 random odd)\n");

    /* --- canonical enumeration counts vs brute force ------------------ */
    {
        Table tabs[6000];
        const unsigned long long want[5] = { 0, 1, 12, 216, 5248 };
        for (int q = 1; q <= 4; q++) {
            int nt = gen_canonical_tables(q, tabs, 6000);
            CHECK((unsigned long long)nt == want[q],
                  "canonical table count != known value");
            CHECK(brute_count_canonical(q) == want[q],
                  "canonical table count != brute force");
        }
        fprintf(stderr, "selftest: canonical tables = 1,12,216,5248 ok\n");
    }

    /* --- FM unit tests ------------------------------------------------ */
    {
        Sys s; Rat wit[NV];
        int c1[1] = {1}, c2[1] = {-1};
        sys_init(&s);                       /* x <= 1, -x <= -2 : infeas */
        Row r = mk_row(c1, 1, 1);  sys_push(&s, &r);
        r = mk_row(c2, 1, -2);     sys_push(&s, &r);
        CHECK(!fm_feasible(&s, 1, NULL), "FM: should be infeasible");
        sys_free(&s);
        sys_init(&s);                       /* x <= 5, -x <= -3 : feas   */
        r = mk_row(c1, 1, 5);  sys_push(&s, &r);
        r = mk_row(c2, 1, -3); sys_push(&s, &r);
        CHECK(fm_feasible(&s, 1, wit), "FM: should be feasible");
        CHECK(rcmp(wit[0], rint_(3)) >= 0 && rcmp(wit[0], rint_(5)) <= 0,
              "FM: witness outside [3,5]");
        sys_free(&s);
        int a1[2] = {1,-1}, a2[2] = {-1,1};
        sys_init(&s);                       /* x-y<=-1, y-x<=-1 : infeas */
        r = mk_row(a1, 2, -1); sys_push(&s, &r);
        r = mk_row(a2, 2, -1); sys_push(&s, &r);
        CHECK(!fm_feasible(&s, 2, NULL), "FM: cycle should be infeasible");
        sys_free(&s);
        sys_init(&s);                       /* x-y<=-1 alone : feasible  */
        r = mk_row(a1, 2, -1); sys_push(&s, &r);
        CHECK(fm_feasible(&s, 2, wit), "FM: x-y<=-1 should be feasible");
        sys_free(&s);
        int b1[3] = {1,-1,2}, b2[3] = {-1,1,1}, b3[3] = {0,0,-1};
        sys_init(&s);   /* x-y+2z<=-1, y-x+z<=-1, -z<=0 : sum => 3z<=-2 */
        r = mk_row(b1, 3, -1); sys_push(&s, &r);
        r = mk_row(b2, 3, -1); sys_push(&s, &r);
        r = mk_row(b3, 3, 0);  sys_push(&s, &r);
        CHECK(!fm_feasible(&s, 3, NULL), "FM: 3-var should be infeasible");
        sys_free(&s);
        fprintf(stderr, "selftest: FM unit tests ok\n");
    }

    /* --- domain classification ---------------------------------------- */
    {
        int ne, inf, gl, cf;
        domain_class(&A_all1, &ne, &inf, &gl, &cf);
        CHECK(ne && inf && gl && cf, "class: D=N should be global");
        DFA A_none = A_all1; A_none.F = 0;
        domain_class(&A_none, &ne, &inf, &gl, &cf);
        CHECK(!ne, "class: empty D");
        domain_class(&A_first0, &ne, &inf, &gl, &cf);
        CHECK(ne && inf && !gl && !cf, "class: evens");
        domain_class(&A_first1, &ne, &inf, &gl, &cf);
        CHECK(ne && inf && !gl && !cf, "class: odds");
        domain_class(&A_geq2, &ne, &inf, &gl, &cf);
        CHECK(ne && inf && !gl && cf, "class: n>=2 should be cofinite");
        domain_class(&A_only3, &ne, &inf, &gl, &cf);
        CHECK(ne && !inf && !gl && !cf, "class: {3} should be finite");
        unsigned long long smp[8]; uint64_t fp;
        int ns = domain_samples(&A_first0, 1, smp, 8, &fp);
        CHECK(ns == 8 && smp[0] == 2 && smp[1] == 4 && smp[7] == 16,
              "samples: evens");
        fprintf(stderr, "selftest: domain classification ok\n");
    }

    /* --- CONTROL 1: global domain must be INFEASIBLE ------------------ */
    for (int L0 = 1; L0 <= 8; L0++) {
        CGen G;
        gen_constraints(&A_all1, &A_all1, L0, &G);
        CHECK(G.ntrip == 3 && G.trip[0][0][0] && G.trip[0][0][1] &&
              G.trip[0][0][2], "global q=1: wrong constraint set");
        Sys sys; sys_copy(&sys, &G.sys);
        Row b = row_beta_sign(1, -1); sys_push(&sys, &b);
        CHECK(!fm_feasible(&sys, 1, NULL),
              "CONTROL 1 FAILED: global q=1 domain came out FEASIBLE");
        sys_free(&sys); sys_free(&G.sys);
    }
    {
        Table tabs[300];
        for (int q = 2; q <= 3; q++) {
            int nt = gen_canonical_tables(q, tabs, 300);
            for (int ti = 0; ti < nt; ti++) {
                for (int L0 = 1; L0 <= 4; L0 += 3) {
                    DFA Ad; Ad.q = q; Ad.F = (1u << q) - 1u;
                    memcpy(Ad.d, tabs[ti].d, sizeof Ad.d);
                    DFA Av = Ad; Av.F = 0;
                    CGen G;
                    gen_constraints(&Av, &Ad, L0, &G);
                    Sys sys; sys_copy(&sys, &G.sys);
                    Row b = row_beta_sign(q, -1); sys_push(&sys, &b);
                    CHECK(!fm_feasible(&sys, q, NULL),
                          "CONTROL 1 FAILED: a global q<=3 domain is FEASIBLE");
                    sys_free(&sys); sys_free(&G.sys);
                }
            }
        }
        fprintf(stderr, "selftest: CONTROL 1 ok — global domain infeasible "
                "(q=1 L0=1..8; all q=2,3 tables, F=full, L0 in {1,4})\n");
    }

    /* --- CONTROL 2: even domain must be FOUND, with beta = 1 ---------- */
    {
        CGen G;
        gen_constraints(&A_all1, &A_first0, 1, &G);
        CHECK(G.ntrip == 1 && G.trip[0][0][0],
              "evens: constraint set != {(0,0,-1)}");
        brute_check_cgen(&A_all1, &A_first0, 1, &G, 1ULL << 16);
        Sys sys; sys_copy(&sys, &G.sys);
        Row b = row_beta_sign(1, -1); sys_push(&sys, &b);
        Rat wit[NV];
        CHECK(fm_feasible(&sys, 1, wit),
              "CONTROL 2 FAILED: even domain came out INFEASIBLE");
        CHECK(rcmp(wit[0], rint_(1)) == 0,
              "CONTROL 2: expected witness beta = 1");
        Sys sys0; sys_copy(&sys0, &sys);
        Row b0 = row_beta_sign(1, +1); sys_push(&sys0, &b0);
        CHECK(!fm_feasible(&sys0, 1, NULL),
              "CONTROL 2: evens should REQUIRE beta > 0 (drift type)");
        sys_free(&sys0);
        Rat wfull[MAXQ]; wfull[0] = rint_(0);
        long long steps = simulate_cert(&A_all1, wfull, wit[0], &A_first0,
                                        1, SIM_TARGET);
        CHECK(steps == SIM_TARGET, "CONTROL 2: simulation short");
        sys_free(&sys); sys_free(&G.sys);
        fprintf(stderr, "selftest: CONTROL 2 ok — D=evens certified "
                "(w=0, beta=1, delta=1), drift-type, 1e5 steps simulated\n");
    }

    /* --- CONTROL 3: odd domain infeasible; beta >= 0 is load-bearing -- */
    {
        CGen G;
        gen_constraints(&A_all1, &A_first1, 1, &G);
        CHECK(G.ntrip == 2 && G.trip[0][0][1] && G.trip[0][0][2],
              "odds: constraint set != {(0,0,+1),(0,0,+2)}");
        brute_check_cgen(&A_all1, &A_first1, 1, &G, 1ULL << 16);
        Sys sys; sys_copy(&sys, &G.sys);
        Row b = row_beta_sign(1, -1); sys_push(&sys, &b);
        CHECK(!fm_feasible(&sys, 1, NULL),
              "CONTROL 3 FAILED: odd domain FEASIBLE with beta >= 0");
        sys_free(&sys);
        Rat wit[NV];
        CHECK(fm_feasible(&G.sys, 1, wit),   /* without beta >= 0 */
              "CONTROL 3: odds should be feasible WITHOUT beta >= 0");
        CHECK(rsgn(wit[0]) < 0,
              "CONTROL 3: unsound witness should have beta < 0");
        sys_free(&G.sys);
        fprintf(stderr, "selftest: CONTROL 3 ok — D=odds infeasible with "
                "beta>=0; dropping beta>=0 admits the unsound beta=%lld/%lld "
                "certificate (V unbounded below)\n", wit[0].n, wit[0].d);
    }

    /* --- cofinite D = {n >= 2} must be infeasible (Lemma 2) ----------- */
    {
        DFA Av = A_geq2; Av.F = 0;
        CGen G;
        gen_constraints(&Av, &A_geq2, 1, &G);
        brute_check_cgen(&Av, &A_geq2, 1, &G, 1ULL << 16);
        Sys sys; sys_copy(&sys, &G.sys);
        Row b = row_beta_sign(3, -1); sys_push(&sys, &b);
        CHECK(!fm_feasible(&sys, 3, NULL),
              "cofinite D={n>=2} came out FEASIBLE (would prove Collatz)");
        sys_free(&sys); sys_free(&G.sys);
        fprintf(stderr, "selftest: cofinite D={n>=2} infeasible ok\n");
    }

    /* --- finite D = {3}: escape-type certificate ---------------------- */
    {
        DFA Av = A_only3; Av.F = 0;
        CGen G;
        gen_constraints(&Av, &A_only3, 1, &G);
        CHECK(G.ntrip == 1 && G.trip[2][3][2],
              "D={3}: constraint set != {(2,3,+2)}");
        brute_check_cgen(&Av, &A_only3, 1, &G, 1ULL << 16);
        Sys sys; sys_copy(&sys, &G.sys);
        Row b = row_beta_sign(4, -1); sys_push(&sys, &b);
        Rat wit[NV];
        CHECK(fm_feasible(&sys, 4, wit), "D={3} should be feasible");
        Sys sys0; sys_copy(&sys0, &sys);
        Row b0 = row_beta_sign(4, +1); sys_push(&sys0, &b0);
        CHECK(fm_feasible(&sys0, 4, NULL), "D={3} should be escape-type");
        sys_free(&sys0);
        Rat wfull[MAXQ]; wfull[0] = rint_(0);
        for (int s = 1; s < 4; s++) wfull[s] = wit[s - 1];
        simulate_cert(&Av, wfull, wit[3], &A_only3, 1, SIM_TARGET);
        sys_free(&sys); sys_free(&G.sys);
        fprintf(stderr, "selftest: finite D={3} escape-type ok\n");
    }

    /* --- generator completeness on a spread of q=3 tables x F --------- */
    {
        Table tabs[300];
        int nt = gen_canonical_tables(3, tabs, 300);
        for (int ti = 0; ti < nt; ti += 37) {
            for (uint32_t F = 0; F < 8; F++) {
                for (int L0 = 1; L0 <= 3; L0 += 2) {
                    DFA Ad; Ad.q = 3; Ad.F = F;
                    memcpy(Ad.d, tabs[ti].d, sizeof Ad.d);
                    DFA Av = Ad; Av.F = 0;
                    CGen G;
                    gen_constraints(&Av, &Ad, L0, &G);
                    brute_check_cgen(&Av, &Ad, L0, &G, 1ULL << 16);
                    sys_free(&G.sys);
                }
            }
        }
        fprintf(stderr, "selftest: generator covers all real steps "
                "n <= 2^16 (spread of q=3 tables x F x L0)\n");
    }

    fprintf(stderr, "SELFTEST PASSED\n");
    return 1;
}

/* ------------------------------------------------------------------ */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "usage: %s --selftest        property tests + mandatory controls\n"
        "       %s <q> [L0]          sweep canonical q-state tables "
        "(1 <= q <= 3, 1 <= L0 <= %d)\n", argv0, argv0, MAXL0);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest() ? 0 : 1;
    if (argc >= 2) {
        int q = atoi(argv[1]);
        int L0 = (argc >= 3) ? atoi(argv[2]) : 1;
        if (q < 1 || q > 3 || L0 < 1 || L0 > MAXL0) { usage(argv[0]); return 2; }
        if (!selftest()) return 1;   /* never search with a broken checker */
        sweep(q, L0);
        return 0;
    }
    usage(argv[0]);
    return 2;
}
