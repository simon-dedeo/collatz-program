/*
 * dfacert3.c — Exhaustive search for "regular divergence certificates" for
 * the Collatz map  T(n) = n/2 (n even),  3n+1 (n odd)  —  BASE-3, MSD-FIRST.
 *
 * Sibling of dfacert.c (which searches in LSB-first base 2).  A regular
 * divergence certificate is a regular language L of base-3 encodings of
 * positive integers such that
 *     (1) L is nonempty,
 *     (2) the encoding of 1 is not in L,
 *     (3) T(L) subseteq L.
 * If such an L exists the Collatz conjecture is FALSE: every element's
 * forward orbit stays inside L forever and hence never reaches 1.
 *
 * ENCODING: n >= 1 is written in base 3, MOST significant digit first, with
 * no leading zeros.  Example: 12 = 110_3 -> "110".  The canonical language
 * is C = { w in {0,1,2}* : w nonempty and w[0] != '0' }, in bijection with
 * the positive integers.  For a candidate DFA A we work with
 * L_A := L(A) ∩ C.
 *
 * KEY FACTS (base 3, MSD-first):
 *   PARITY: 3 ≡ 1 (mod 2), so n mod 2 = (digit sum of w) mod 2.  All
 *     product constructions track digit-sum parity to know which words are
 *     even/odd.
 *   ODD STEP (n odd): string(3n+1) = string(n)·"1".  (Multiplying by 3
 *     appends a '0'; adding 1 turns it into '1' with no carry.)
 *   EVEN STEP (n even): string(n/2) by MSD-first long division:
 *     r := 0; for each digit d: emit (3r+d) div 2, set r := (3r+d) mod 2.
 *     The raw output has the same length as the input; its first digit is
 *     d0 div 2, which is 0 iff d0 = 1 (d0 in {1,2} for canonical input).
 *     Strip exactly that one possible leading zero: the next raw digit is
 *     (3·1+d1) div 2 >= 1, so a single strip always yields a canonical
 *     string.  Example: 12 = "110" -> raw "020" -> "20" = 6.
 *     THEOREM: the running remainder r always equals the digit-sum parity
 *     of the consumed prefix (both are the prefix value mod 2), so for
 *     even n the division ends with r = 0.  The even-closure checker
 *     tracks r and the parity independently and ASSERTS r == p.
 *
 * Closure conditions (2) and (3) are decided EXACTLY (not sampled) via
 * small product constructions — see check_even_closed / check_odd_closed.
 *
 * Enumeration: canonical initially-connected complete DFAs over {0,1,2}
 * with exactly q states, start state 0, states numbered in BFS discovery
 * order (symbol 0 before 1 before 2); all 2^q accepting subsets.  Every
 * regular language with a complete DFA of <= k states is covered by
 * running q = 1..k (take the minimal DFA, drop unreachable states,
 * renumber canonically).
 *
 * Build:  cc -O2 -Wall -Wextra -std=c11 -o dfacert3 dfacert3.c        (mac)
 *         gcc -O2 -Wall -Wextra -std=c11 -fopenmp -o dfacert3 dfacert3.c
 * Usage:  ./dfacert3 --selftest        run the property tests only
 *         ./dfacert3 <q>               search all canonical q-state DFAs
 *         ./dfacert3 --plain <q>       cross-check: plain q^(3q) enumeration
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
static int omp_get_thread_num(void){return 0;}
static int omp_get_max_threads(void){return 1;}
#endif

#define ALPHA 3             /* alphabet size (base-3 digits)          */
#define MAXQ 8              /* max number of DFA states supported     */
#define MAXQ_PLAIN 7        /* --plain: q^(3q) must fit in 64 bits    */
#define MAXDIGITS 160       /* string buffer size for encodings       */

typedef struct {
    int q;                  /* number of states; start state is 0     */
    uint8_t d[MAXQ][ALPHA]; /* transition table d[state][symbol]      */
    uint32_t F;             /* accepting set as bitmask               */
} DFA;

/* ------------------------------------------------------------------ */
/* Encoding helpers                                                    */
/* ------------------------------------------------------------------ */

/* MSD-first base-3 encoding of n >= 1; returns length; NUL-terminates. */
static int encode3(unsigned __int128 n, char *buf)
{
    char tmp[MAXDIGITS];
    int len = 0;
    while (n) { tmp[len++] = (char)('0' + (int)(n % 3)); n /= 3; }
    for (int i = 0; i < len; i++) buf[i] = tmp[len - 1 - i];
    buf[len] = '\0';
    return len;
}

static unsigned __int128 decode3(const char *w, int len)
{
    unsigned __int128 n = 0;
    for (int i = 0; i < len; i++)
        n = n * 3 + (unsigned)(w[i] - '0');
    return n;
}

/* Digit-sum parity of w == n mod 2 (since 3 ≡ 1 mod 2).  A digit flips
 * the parity iff it is odd, i.e. iff it is '1'.                        */
static int parity3(const char *w, int len)
{
    int p = 0;
    for (int i = 0; i < len; i++) p ^= (w[i] - '0') & 1;
    return p;
}

/* The 3n+1 map as a string operation: append '1'. */
static int append1(const char *in, int len, char *out)
{
    memcpy(out, in, (size_t)len);
    out[len] = '1';
    out[len + 1] = '\0';
    return len + 1;
}

/* The n/2 map as MSD-first long division by 2.  Writes the CANONICAL
 * quotient string: the raw output has one leading zero iff in[0] == '1',
 * and exactly that one zero is stripped (position 0 only).  Returns the
 * output length; stores the final remainder (= n mod 2) in *rem.       */
static int div2str(const char *in, int len, char *out, int *rem)
{
    int r = 0, o = 0;
    for (int i = 0; i < len; i++) {
        int t = 3 * r + (in[i] - '0');
        int e = t >> 1;                   /* quotient digit, in {0,1,2} */
        r = t & 1;
        if (i == 0 && e == 0) continue;   /* strip the one leading zero */
        out[o++] = (char)('0' + e);
    }
    out[o] = '\0';
    if (rem) *rem = r;
    return o;
}

/* Membership in L_A = L(A) ∩ C  (C = nonempty, not starting with '0'). */
static int dfa_member(const DFA *A, const char *w, int len)
{
    if (len <= 0 || w[0] == '0') return 0;
    int s = 0;
    for (int i = 0; i < len; i++) s = A->d[s][w[i] - '0'];
    return (int)((A->F >> s) & 1u);
}

/* ------------------------------------------------------------------ */
/* Certificate conditions                                              */
/* ------------------------------------------------------------------ */

/* (1) L_A nonempty: some accepting state is reachable from state 0 by a
 * canonical string, i.e. reachable from {d[0][1], d[0][2]} (inclusive)
 * by arbitrary further digits.                                          */
static int check_nonempty(const DFA *A)
{
    uint8_t seen[MAXQ] = {0};
    int queue[MAXQ], qh = 0, qt = 0;
    for (int b = 1; b <= 2; b++) {
        int t = A->d[0][b];
        if (!seen[t]) { seen[t] = 1; queue[qt++] = t; }
    }
    while (qh < qt) {
        int s = queue[qh++];
        if ((A->F >> s) & 1u) return 1;
        for (int b = 0; b < ALPHA; b++) {
            int t = A->d[s][b];
            if (!seen[t]) { seen[t] = 1; queue[qt++] = t; }
        }
    }
    return 0;
}

/* (2) "1" not in L_A.  encode3(1) = "1", canonical, so in L_A iff
 * d[0][1] in F.                                                         */
static int check_one_not_in(const DFA *A)
{
    return !((A->F >> A->d[0][1]) & 1u);
}

/* (3a) ODD closure: every w in L_A with odd digit sum (odd n) must have
 * w·"1" in L_A.  (w·"1" starts with the same nonzero digit: canonical.)
 *
 * BFS over pairs (x, p): x = A-state reached from 0 by some canonical
 * word, p = that word's digit-sum parity.  Start configurations are the
 * two possible first digits: (d[0][1], 1) and (d[0][2], 0).  A digit b
 * flips p iff b == 1.  Violation iff some reachable (x, 1) has x in F
 * (an odd member w) but d[x][1] not in F (w·"1" escapes).  The start
 * state (d[0][1], 1) is w = "1" itself: if "1" in L(A) the checker
 * includes it — mathematically that IS the closure condition at n = 1;
 * condition (2) is enforced separately.                                 */
static int check_odd_closed(const DFA *A)
{
    uint8_t seen[MAXQ * 2] = {0};
    int queue[MAXQ * 2], qh = 0, qt = 0;
    for (int b = 1; b <= 2; b++) {
        int st = A->d[0][b] * 2 + (b & 1);
        if (!seen[st]) { seen[st] = 1; queue[qt++] = st; }
    }
    while (qh < qt) {
        int st = queue[qh++], p = st & 1, x = st >> 1;
        if (p == 1 && ((A->F >> x) & 1u) && !((A->F >> A->d[x][1]) & 1u))
            return 0;                              /* violation found */
        for (int b = 0; b < ALPHA; b++) {
            int ns = A->d[x][b] * 2 + (p ^ (b & 1));
            if (!seen[ns]) { seen[ns] = 1; queue[qt++] = ns; }
        }
    }
    return 1;
}

/* (3b) EVEN closure: every w in L_A with even digit sum (even n) must
 * have div2str(w) in L_A.
 *
 * Product BFS over quadruples (x, y, r, p): x = A-state on the input
 * word read so far (from 0), y = A-state on the CANONICAL divided output
 * emitted so far (from 0), r = long-division remainder, p = digit-sum
 * parity of the input.  Exactly one output digit per input digit, except
 * that the raw output's leading zero (which occurs iff the first input
 * digit is 1) is skipped on the output side.  Hence two start
 * configurations, one per first digit d0 in {1,2}:
 *   d0 = 2: raw first output digit (3·0+2) div 2 = 1  ->  y consumes '1';
 *           (x,y,r,p) = (d[0][2], d[0][1], 0, 0).
 *   d0 = 1: raw first output digit (3·0+1) div 2 = 0, skipped  ->  y has
 *           consumed nothing; (x,y,r,p) = (d[0][1], 0, 1, 1).
 *           (The next raw digit is (3+d1) div 2 >= 1, so the string fed
 *           to y stays canonical.)
 * Every reachable product state corresponds to complete canonical input
 * words w; when the input is even (p == 0) the output is complete and
 * canonical, and membership of div2str(w) is exactly "y in F".
 * Violation iff some reachable state has p == 0, x in F, y not in F.
 * THEOREM (asserted, not assumed): r == p at every reachable state, both
 * being the consumed prefix's value mod 2; in particular even inputs end
 * with remainder 0.                                                     */
static int check_even_closed(const DFA *A)
{
    int q = A->q;
    uint8_t seen[MAXQ * MAXQ * 4] = {0};
    int queue[MAXQ * MAXQ * 4], qh = 0, qt = 0;
    /* d0 = 2 */
    int s2 = ((A->d[0][2] * q + A->d[0][1]) * 2 + 0) * 2 + 0;
    /* d0 = 1 (leading zero of the raw output skipped) */
    int s1 = ((A->d[0][1] * q + 0) * 2 + 1) * 2 + 1;
    seen[s2] = 1; queue[qt++] = s2;
    if (!seen[s1]) { seen[s1] = 1; queue[qt++] = s1; }
    while (qh < qt) {
        int st = queue[qh++];
        int p = st & 1, r = (st >> 1) & 1;
        int y = (st >> 2) % q, x = (st >> 2) / q;
        if (r != p) {
            fprintf(stderr, "FATAL: even-closure invariant r == parity "
                    "violated (internal bug)\n");
            exit(5);
        }
        if (p == 0 && ((A->F >> x) & 1u) && !((A->F >> y) & 1u))
            return 0;                              /* violation found */
        for (int b = 0; b < ALPHA; b++) {
            int t = 3 * r + b, e = t >> 1, nr = t & 1;
            int nx = A->d[x][b], ny = A->d[y][e], np = p ^ (b & 1);
            int ns = ((nx * q + ny) * 2 + nr) * 2 + np;
            if (!seen[ns]) { seen[ns] = 1; queue[qt++] = ns; }
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* Independent verification of a candidate (safety net, not the proof) */
/* ------------------------------------------------------------------ */

#define VERIF_MAXLEN   39   /* 3^39 < 2^62, and 3n+1 still fits in 64 bits */
#define VERIF_MEMBER_CAP 200000ULL
#define VERIF_NODE_CAP   50000000ULL
#define VERIF_NSAMPLE  20

typedef struct {
    const DFA *A;
    unsigned long long members, nodes;
    int fail;
    char buf[VERIF_MAXLEN + 8];
    unsigned long long sample[VERIF_NSAMPLE];
    int nsample;
} Verif;

static void verify_member(Verif *V, int len)
{
    V->members++;
    unsigned __int128 n = decode3(V->buf, len);
    unsigned long long nl = (unsigned long long)n;   /* len<=39 digits */
    if (V->nsample < VERIF_NSAMPLE) V->sample[V->nsample++] = nl;
    if (nl == 1ULL) {
        fprintf(stderr, "VERIFY BUG: 1 is a member of L\n");
        V->fail = 1; return;
    }
    if (parity3(V->buf, len) != (int)(nl & 1ULL)) {
        fprintf(stderr, "VERIFY BUG: digit-sum parity != n mod 2 at n=%llu\n", nl);
        V->fail = 1; return;
    }
    unsigned __int128 t = (nl & 1) ? ((unsigned __int128)3 * n + 1) : (n >> 1);
    char wt[MAXDIGITS];
    int lt = encode3(t, wt);
    if (!dfa_member(V->A, wt, lt)) {
        fprintf(stderr, "VERIFY BUG: member n=%llu but T(n)=%llu not in L\n",
                nl, (unsigned long long)t);
        V->fail = 1; return;
    }
    /* cross-check the string operations against arithmetic */
    char wo[MAXDIGITS];
    int lo, rem = -1;
    if (nl & 1) lo = append1(V->buf, len, wo);
    else        lo = div2str(V->buf, len, wo, &rem);
    if (!(nl & 1) && rem != 0) {
        fprintf(stderr, "VERIFY BUG: even n=%llu but division remainder %d\n",
                nl, rem);
        V->fail = 1; return;
    }
    if (lo != lt || memcmp(wo, wt, (size_t)lt) != 0) {
        fprintf(stderr, "VERIFY BUG: string-op mismatch at n=%llu\n", nl);
        V->fail = 1;
    }
}

static void verify_dfs(Verif *V, int state, int depth, int targetlen)
{
    if (V->fail || V->members >= VERIF_MEMBER_CAP || V->nodes >= VERIF_NODE_CAP)
        return;
    V->nodes++;
    if (depth == targetlen) {
        if ((V->A->F >> state) & 1u)
            verify_member(V, depth);
        return;
    }
    int lo = (depth == 0) ? 1 : 0;         /* canonical: no leading zero */
    for (int b = lo; b < ALPHA; b++) {
        V->buf[depth] = (char)('0' + b);
        verify_dfs(V, V->A->d[state][b], depth + 1, targetlen);
    }
}

static void run_verification(Verif *V, const DFA *A)
{
    memset(V, 0, sizeof *V);
    V->A = A;
    for (int len = 1; len <= VERIF_MAXLEN; len++) {
        if (V->fail || V->members >= VERIF_MEMBER_CAP ||
            V->nodes >= VERIF_NODE_CAP) break;
        verify_dfs(V, 0, 0, len);
    }
}

/* ------------------------------------------------------------------ */
/* Output of candidates                                                */
/* ------------------------------------------------------------------ */

static void print_dfa(FILE *f, const DFA *A)
{
    fprintf(f, "DFA (base-3 MSD-first): q=%d, start=0, F={", A->q);
    int first = 1;
    for (int s = 0; s < A->q; s++)
        if ((A->F >> s) & 1u) { fprintf(f, "%s%d", first ? "" : ",", s); first = 0; }
    fprintf(f, "}\n");
    for (int s = 0; s < A->q; s++)
        fprintf(f, "  state %d: on 0 -> %d, on 1 -> %d, on 2 -> %d%s\n",
                s, A->d[s][0], A->d[s][1], A->d[s][2],
                ((A->F >> s) & 1u) ? "   [accepting]" : "");
}

/* ------------------------------------------------------------------ */
/* Enumeration of canonical initially-connected DFAs                   */
/* ------------------------------------------------------------------ */

/* A transition table is canonical iff scanning slots in the order
 * (state 0, sym 0), (state 0, sym 1), (state 0, sym 2), (state 1, sym 0),
 * ... discovers the states exactly in the order 1, 2, ..., q-1 (start
 * state 0 is given), and all q states are discovered.                  */
static int is_canonical_table(int q, const uint8_t d[][ALPHA])
{
    uint8_t seen[MAXQ] = {0};
    int order[MAXQ], nseen = 1;
    seen[0] = 1; order[0] = 0;
    for (int i = 0; i < nseen; i++) {
        int s = order[i];
        for (int b = 0; b < ALPHA; b++) {
            int t = d[s][b];
            if (!seen[t]) {
                if (t != nseen) return 0;      /* discovered out of order */
                seen[t] = 1; order[nseen++] = t;
            }
        }
    }
    return nseen == q;                          /* initially connected */
}

typedef struct {
    int q;
    int plain;                       /* 1 = skip canonicity assertion */
    uint8_t d[MAXQ][ALPHA];
    unsigned long long tables, scanned, cands, verifs, flushed;
} Ctx;

static unsigned long long g_progress = 0;
static unsigned long long g_next_report = 10000000ULL;

static void flush_progress(Ctx *C)
{
#ifdef _OPENMP
#pragma omp critical(progress)
#endif
    {
        g_progress += C->scanned - C->flushed;
        C->flushed = C->scanned;
        while (g_progress >= g_next_report) {
            fprintf(stderr, "[progress] ~%llu DFAs scanned (thread %d)\n",
                    g_next_report, omp_get_thread_num());
            g_next_report += 10000000ULL;
        }
    }
}

static void handle_candidate(const DFA *A, Ctx *C)
{
#ifdef _OPENMP
#pragma omp critical(candidate)
#endif
    {
        printf("\n"
        "==================================================================\n"
        "=== CANDIDATE REGULAR DIVERGENCE CERTIFICATE FOUND ===============\n"
        "==================================================================\n");
        print_dfa(stdout, A);
        fflush(stdout);

        Verif V;
        run_verification(&V, A);
        if (V.fail || V.members == 0) {
            fprintf(stderr,
                "FATAL: candidate FAILED independent verification (members=%llu)."
                " This indicates a bug in the closure checker. Aborting.\n",
                V.members);
            print_dfa(stderr, A);
            exit(3);
        }
        printf("Independent verification PASSED: %llu members of L "
               "(length <= %d, capped) each satisfy T(n) in L and n != 1.\n",
               V.members, VERIF_MAXLEN);
        printf("Smallest members of L:");
        for (int i = 0; i < V.nsample; i++) printf(" %llu", V.sample[i]);
        printf("\n*** IF THIS IS NOT A BUG, THE COLLATZ CONJECTURE IS FALSE ***\n");
        fflush(stdout);

        FILE *f = fopen("discoveries.txt", "a");
        if (f) {
            time_t now = time(NULL);
            fprintf(f, "==== verified certificate, %s", ctime(&now));
            print_dfa(f, A);
            fprintf(f, "verified members (len<=%d): %llu\nsmallest:",
                    VERIF_MAXLEN, V.members);
            for (int i = 0; i < V.nsample; i++) fprintf(f, " %llu", V.sample[i]);
            fprintf(f, "\n\n");
            fclose(f);
        } else {
            fprintf(stderr, "warning: could not open discoveries.txt\n");
        }
        C->verifs++;
    }
}

/* Run all conditions for one transition table, over all accepting sets. */
static void process_table(Ctx *C)
{
    C->tables++;
    if (!C->plain && !is_canonical_table(C->q, C->d)) {
        fprintf(stderr, "FATAL: enumerator produced a non-canonical table\n");
        exit(4);
    }
    DFA A;
    A.q = C->q;
    memcpy(A.d, C->d, sizeof A.d);
    uint32_t nF = 1u << C->q;
    for (uint32_t F = 0; F < nF; F++) {
        A.F = F;
        C->scanned++;
        if (!check_one_not_in(&A)) continue;      /* (2): "1" in L        */
        if (!check_nonempty(&A))   continue;      /* (1): L empty         */
        if (!check_even_closed(&A)) continue;     /* (3b): even violation */
        if (!check_odd_closed(&A))  continue;     /* (3a): odd violation  */
        C->cands++;
        handle_candidate(&A, C);
    }
    if ((C->tables & 0x3FF) == 0) flush_progress(C);
}

/* Recursive canonical enumeration.  Slots are indexed i = 0..3q-1 with
 * slot i = (state i/3, symbol i%3); m = highest state index used so far.
 * Rules: (a) slot value v <= m+1 (a value of m+1 discovers a new state);
 * (b) when reaching the slots of state s (i % 3 == 0), s must already be
 * discovered (s <= m) — otherwise s is unreachable / out of order.
 * Rule (b) at s = q-1 forces all q states to be used.                  */
static void rec_slots(Ctx *C, int i, int m)
{
    int q = C->q;
    if (i == ALPHA * q) { process_table(C); return; }
    if (i % ALPHA == 0 && i / ALPHA > m) return;
    int hi = (m + 1 < q - 1) ? m + 1 : q - 1;
    for (int v = 0; v <= hi; v++) {
        C->d[i / ALPHA][i % ALPHA] = (uint8_t)v;
        rec_slots(C, i + 1, v > m ? v : m);
    }
}

/* Count canonical tables only (used by the selftest cross-check). */
static unsigned long long count_rec(int q, int i, int m)
{
    if (i == ALPHA * q) return 1;
    if (i % ALPHA == 0 && i / ALPHA > m) return 0;
    unsigned long long tot = 0;
    int hi = (m + 1 < q - 1) ? m + 1 : q - 1;
    for (int v = 0; v <= hi; v++) tot += count_rec(q, i + 1, v > m ? v : m);
    return tot;
}

static unsigned long long brute_count_canonical(int q)
{
    unsigned long long ntab = 1;
    for (int j = 0; j < ALPHA * q; j++) ntab *= (unsigned long long)q;
    unsigned long long count = 0;
    uint8_t d[MAXQ][ALPHA];
    for (unsigned long long idx = 0; idx < ntab; idx++) {
        unsigned long long t = idx;
        for (int j = ALPHA * q - 1; j >= 0; j--) {
            d[j / ALPHA][j % ALPHA] = (uint8_t)(t % (unsigned)q);
            t /= (unsigned)q;
        }
        if (is_canonical_table(q, d)) count++;
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* Search drivers                                                      */
/* ------------------------------------------------------------------ */

static double now_seconds(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void search_canonical(int q)
{
    double t0 = now_seconds();
    g_progress = 0;
    g_next_report = 10000000ULL;
    /* Parallel split: enumerate the first P slots as base-q prefixes. */
    int P = (ALPHA * q < 4) ? ALPHA * q : 4;
    long long npre = 1;
    for (int j = 0; j < P; j++) npre *= q;

    unsigned long long tot_tables = 0, tot_scanned = 0,
                       tot_cands = 0, tot_verifs = 0;

    fprintf(stderr, "q=%d: searching canonical initially-connected DFAs "
            "over {0,1,2} (threads=%d, prefix slots=%d)\n",
            q, omp_get_max_threads(), P);

#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic) \
        reduction(+:tot_tables,tot_scanned,tot_cands,tot_verifs)
#endif
    for (long long idx = 0; idx < npre; idx++) {
        Ctx C;
        memset(&C, 0, sizeof C);
        C.q = q;
        int digs[8];
        long long t = idx;
        for (int j = P - 1; j >= 0; j--) { digs[j] = (int)(t % q); t /= q; }
        int m = 0, ok = 1;
        for (int j = 0; j < P && ok; j++) {
            if (j % ALPHA == 0 && j / ALPHA > m) { ok = 0; break; }
            if (digs[j] > m + 1) { ok = 0; break; }
            C.d[j / ALPHA][j % ALPHA] = (uint8_t)digs[j];
            if (digs[j] > m) m = digs[j];
        }
        if (ok) rec_slots(&C, P, m);
        tot_tables += C.tables;
        tot_scanned += C.scanned;
        tot_cands += C.cands;
        tot_verifs += C.verifs;
    }

    double dt = now_seconds() - t0;
    fprintf(stderr, "q=%d: %llu canonical transition tables, %.2f s\n",
            q, tot_tables, dt);
    printf("q=%d: %llu canonical DFAs scanned, %llu candidates, "
           "%llu verified certificates\n",
           q, tot_scanned, tot_cands, tot_verifs);
    fflush(stdout);
}

/* Plain enumeration of ALL q^(3q) tables (isomorphic/unreachable dupes
 * included) — slower cross-check that canonical enumeration misses
 * nothing; candidate counts must be zero in both or nonzero in both.   */
static void search_plain(int q)
{
    double t0 = now_seconds();
    g_progress = 0;
    g_next_report = 10000000ULL;
    unsigned long long ntab = 1;
    for (int j = 0; j < ALPHA * q; j++) ntab *= (unsigned long long)q;

    Ctx C;
    memset(&C, 0, sizeof C);
    C.q = q;
    C.plain = 1;
    for (unsigned long long idx = 0; idx < ntab; idx++) {
        unsigned long long t = idx;
        for (int j = ALPHA * q - 1; j >= 0; j--) {
            C.d[j / ALPHA][j % ALPHA] = (uint8_t)(t % (unsigned)q);
            t /= (unsigned)q;
        }
        process_table(&C);
    }
    double dt = now_seconds() - t0;
    fprintf(stderr, "q=%d [plain]: %llu transition tables, %.2f s\n",
            q, C.tables, dt);
    printf("q=%d [plain]: %llu DFAs scanned, %llu candidates, "
           "%llu verified certificates\n", q, C.scanned, C.cands, C.verifs);
    fflush(stdout);
}

/* ------------------------------------------------------------------ */
/* Selftest                                                            */
/* ------------------------------------------------------------------ */

static uint64_t xs_state;
static uint64_t xorshift64(void)
{
    uint64_t x = xs_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return xs_state = x;
}

static int st_fail(const char *msg)
{
    fprintf(stderr, "SELFTEST FAILED: %s\n", msg);
    return 0;
}

static int selftest(void)
{
    char wa[MAXDIGITS], wb[MAXDIGITS], wc[MAXDIGITS];
    int la, lb, lc, rem;

    /* --- explicit string-operation cases ------------------------------ */
    /* odd step: append '1' */
    la = append1("1", 1, wa);                       /* T(1)  = 4  = "11"  */
    if (la != 2 || strcmp(wa, "11") != 0)  return st_fail("T(1) != 11");
    la = append1("10", 2, wa);                      /* T(3)  = 10 = "101" */
    if (la != 3 || strcmp(wa, "101") != 0) return st_fail("T(3) != 101");
    la = append1("12", 2, wa);                      /* T(5)  = 16 = "121" */
    if (la != 3 || strcmp(wa, "121") != 0) return st_fail("T(5) != 121");
    /* even step: long division, incl. the leading-zero case (in[0]=='1') */
    la = div2str("2", 1, wa, &rem);                 /* 2/2   = 1,  no LZ  */
    if (la != 1 || strcmp(wa, "1") != 0 || rem != 0)  return st_fail("2/2 != 1");
    la = div2str("11", 2, wa, &rem);                /* 4/2   = 2,  LZ     */
    if (la != 1 || strcmp(wa, "2") != 0 || rem != 0)  return st_fail("4/2 != 2");
    la = div2str("110", 3, wa, &rem);               /* 12/2  = 6,  LZ     */
    if (la != 2 || strcmp(wa, "20") != 0 || rem != 0) return st_fail("12/2 != 20");
    la = div2str("101", 3, wa, &rem);               /* 10/2  = 5,  LZ     */
    if (la != 2 || strcmp(wa, "12") != 0 || rem != 0) return st_fail("10/2 != 12");
    la = div2str("10", 2, wa, &rem);                /* 3 = 2*1 + 1        */
    if (la != 1 || strcmp(wa, "1") != 0 || rem != 1)  return st_fail("3 div 2 != 1 rem 1");

    /* --- property tests: 1e5 fixed-seed random n in [1, 2^60] --------- */
    xs_state = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 100000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 60) - 1)) + 1;
        la = encode3(n, wa);
        if (wa[0] == '0' || la == 0)
            return st_fail("encoding has a leading zero");
        if ((uint64_t)decode3(wa, la) != n)
            return st_fail("encode/decode roundtrip (random)");
        if (parity3(wa, la) != (int)(n & 1))
            return st_fail("digit-sum parity != n mod 2");
        if (n & 1) {                                   /* odd: 3n+1 */
            unsigned __int128 t = (unsigned __int128)3 * n + 1;
            lb = encode3(t, wb);
            lc = append1(wa, la, wc);
            if (lc != lb || memcmp(wb, wc, (size_t)lb) != 0)
                return st_fail("append-'1' output != arithmetic 3n+1");
        } else {                                       /* even: n/2 */
            lb = encode3(n / 2, wb);
            lc = div2str(wa, la, wc, &rem);
            if (rem != 0)
                return st_fail("even n but division remainder != 0");
            if (lc != lb || memcmp(wb, wc, (size_t)lb) != 0)
                return st_fail("string div2 output != arithmetic n/2");
        }
    }
    fprintf(stderr, "selftest: string ops == arithmetic (3n+1 odd, n/2 even), "
            "parity, roundtrip on 100000 random n <= 2^60\n");
    for (uint64_t n = 1; n <= 2000; n++) {
        la = encode3(n, wa);
        if ((uint64_t)decode3(wa, la) != n) return st_fail("roundtrip (small)");
        if (wa[0] == '0') return st_fail("leading zero (small)");
    }
    fprintf(stderr, "selftest: encode/decode roundtrip ok (n = 1..2000)\n");

    /* --- membership runner --------------------------------------------- */
    DFA A_all = { .q = 1, .d = {{0, 0, 0}}, .F = 1u };  /* L(A)=Sigma*, L_A=C */
    if (!dfa_member(&A_all, "1", 1))  return st_fail("membership: '1' in C");
    if (!dfa_member(&A_all, "2", 1))  return st_fail("membership: '2' in C");
    if (dfa_member(&A_all, "0", 1))   return st_fail("membership: '0' not in C");
    if (dfa_member(&A_all, "01", 2))  return st_fail("membership: '01' not in C");
    if (dfa_member(&A_all, "", 0))    return st_fail("membership: empty not in C");
    if (!dfa_member(&A_all, "10", 2)) return st_fail("membership: '10' in C");
    for (int i = 0; i < 1000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 40) - 1)) + 1;
        la = encode3(n, wa);
        if (!dfa_member(&A_all, wa, la)) return st_fail("membership: encode(n) in C");
    }

    /* --- positive/negative controls for the certificate checks -------- */

    /* Control 1: L = C (all n >= 1).  T-closed, but contains 1:
     * everything must pass EXCEPT the 1-not-in-L test.                  */
    if (!check_nonempty(&A_all))    return st_fail("A_all: should be nonempty");
    if (check_one_not_in(&A_all))   return st_fail("A_all: '1' should be in L");
    if (!check_even_closed(&A_all)) return st_fail("A_all: even closure should PASS");
    if (!check_odd_closed(&A_all))  return st_fail("A_all: odd closure should PASS");

    /* Control 2: L = all n >= 2 (C minus {"1"}).  T(2)=1 escapes, so the
     * EVEN closure must FAIL exactly (witness w="2" -> "1"); the odd
     * closure passes (odd n >= 3 has 3n+1 >= 10, still in L; and "1" is
     * not in L so it imposes nothing).
     * States: 0 start; 1 = read exactly "1"; 2 = accept sink; 3 = dead. */
    DFA A_ge2 = { .q = 4,
                  .d = {{3, 1, 2}, {2, 2, 2}, {2, 2, 2}, {3, 3, 3}},
                  .F = 1u << 2 };
    if (!check_nonempty(&A_ge2))   return st_fail("A_ge2: should be nonempty");
    if (!check_one_not_in(&A_ge2)) return st_fail("A_ge2: '1' should NOT be in L");
    if (check_even_closed(&A_ge2)) return st_fail("A_ge2: even closure should FAIL (w=2)");
    if (!check_odd_closed(&A_ge2)) return st_fail("A_ge2: odd closure should PASS");
    /* the exact base case w="2" -> "1": */
    if (!dfa_member(&A_ge2, "2", 1)) return st_fail("A_ge2: '2' (n=2) should be in L");
    if (dfa_member(&A_ge2, "1", 1))  return st_fail("A_ge2: '1' (n=1) should NOT be in L");

    /* Control 3: L = {"12"} = {5} (odd).  T(5) = 16 = "121" not in L:
     * odd closure must FAIL; even closure passes vacuously (no even
     * member: digit sum of "12" is odd).                                */
    DFA A_only5 = { .q = 4,
                    .d = {{3, 1, 3}, {3, 3, 2}, {3, 3, 3}, {3, 3, 3}},
                    .F = 1u << 2 };
    if (!check_nonempty(&A_only5))    return st_fail("A_only5: should be nonempty");
    if (!check_one_not_in(&A_only5))  return st_fail("A_only5: '1' should NOT be in L");
    if (!check_even_closed(&A_only5)) return st_fail("A_only5: even closure should PASS");
    if (check_odd_closed(&A_only5))   return st_fail("A_only5: odd closure should FAIL");

    /* Control 4: L = {"11"} = {4} (even).  T(4) = 2 = "2" not in L: the
     * EVEN closure must FAIL, and the violating word starts with digit 1
     * — this exercises the leading-zero-skip branch of the product
     * construction (raw output "02" -> canonical "2").                 */
    DFA A_only4 = { .q = 4,
                    .d = {{3, 1, 3}, {3, 2, 3}, {3, 3, 3}, {3, 3, 3}},
                    .F = 1u << 2 };
    if (!check_nonempty(&A_only4))   return st_fail("A_only4: should be nonempty");
    if (!check_one_not_in(&A_only4)) return st_fail("A_only4: '1' should NOT be in L");
    if (check_even_closed(&A_only4)) return st_fail("A_only4: even closure should FAIL (LZ branch)");
    if (!check_odd_closed(&A_only4)) return st_fail("A_only4: odd closure should PASS");

    /* Control 5: empty language — closures hold vacuously, nonempty fails. */
    DFA A_empty = { .q = 1, .d = {{0, 0, 0}}, .F = 0u };
    if (check_nonempty(&A_empty))     return st_fail("A_empty: should be empty");
    if (!check_one_not_in(&A_empty))  return st_fail("A_empty: '1' not in L");
    if (!check_even_closed(&A_empty)) return st_fail("A_empty: even closure vacuous");
    if (!check_odd_closed(&A_empty))  return st_fail("A_empty: odd closure vacuous");
    fprintf(stderr, "selftest: closure-checker controls ok "
            "(C, C-minus-{1}, {5}, {4} leading-zero case, empty)\n");

    /* --- canonical enumeration vs brute-force canonicity filter ------- */
    for (int q = 1; q <= 4; q++) {
        unsigned long long a = count_rec(q, 0, 0);
        unsigned long long b = brute_count_canonical(q);
        if (a != b) return st_fail("canonical enumeration count != brute-force count");
        fprintf(stderr, "selftest: q=%d canonical 3-symbol tables = %llu "
                "(brute-force agrees)\n", q, a);
    }
    if (count_rec(2, 0, 0) != 56)
        return st_fail("q=2 canonical table count != 56 (hand-verified value)");

    fprintf(stderr, "SELFTEST PASSED\n");
    return 1;
}

/* ------------------------------------------------------------------ */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "usage: %s --selftest        run property tests\n"
        "       %s <q>               search all canonical q-state DFAs (1..%d)\n"
        "       %s --plain <q>       cross-check via plain q^(3q) enumeration (1..%d)\n",
        argv0, argv0, MAXQ, argv0, MAXQ_PLAIN);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest() ? 0 : 1;

    if (argc >= 3 && strcmp(argv[1], "--plain") == 0) {
        int q = atoi(argv[2]);
        if (q < 1 || q > MAXQ_PLAIN) { usage(argv[0]); return 2; }
        if (!selftest()) return 1;
        search_plain(q);
        return 0;
    }

    if (argc >= 2) {
        int q = atoi(argv[1]);
        if (q < 1 || q > MAXQ) { usage(argv[0]); return 2; }
        if (!selftest()) return 1;      /* never search with a broken checker */
        search_canonical(q);
        return 0;
    }

    usage(argv[0]);
    return 2;
}
