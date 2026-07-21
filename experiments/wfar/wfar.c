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

/* ===CHUNK4=== */
