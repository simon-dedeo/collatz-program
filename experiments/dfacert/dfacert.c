/*
 * dfacert.c — Exhaustive search for "regular divergence certificates" for
 * the Collatz map  T(n) = n/2 (n even),  3n+1 (n odd).
 *
 * A regular divergence certificate is a regular language L of binary
 * encodings of positive integers such that
 *     (1) L is nonempty,
 *     (2) the encoding of 1 is not in L,
 *     (3) T(L) subseteq L.
 * If such an L exists the Collatz conjecture is FALSE: every element's
 * forward orbit stays inside L forever and hence never reaches 1.
 *
 * ENCODING: n >= 1 is written in binary LSB-FIRST, so every valid encoding
 * ends in '1' (the MSB).  Example: 6 = 110b  ->  "011".
 * The canonical language is C = { w in {0,1}* : w ends in '1' }.
 * For a candidate DFA A we work with L_A := L(A) ∩ C.
 *
 * T AS STRING OPERATIONS (LSB-first):
 *   n even (w starts with '0'):  T(n) = n/2  =  drop the first character.
 *   n odd  (w starts with '1'):  T(n) = 3n+1 =  sequential transduction:
 *       carry c := 1;  for each input bit b: s = 3b + c; emit s&1; c = s>>1;
 *       after the input, flush: while c > 0 { emit c&1; c >>= 1; }.
 *     (carry stays in {0,1,2}; output length = input length +0, +1 or +2;
 *      output always ends in '1'.)
 *
 * Closure conditions (2) and (3) are decided EXACTLY (not sampled) via
 * small product constructions — see check_even_closed / check_odd_closed.
 *
 * Enumeration: canonical initially-connected complete DFAs over {0,1}
 * with exactly q states, start state 0, states numbered in BFS discovery
 * order (symbol 0 before symbol 1); all 2^q accepting subsets.  Every
 * regular language with a complete DFA of <= k states is covered by
 * running q = 1..k (take the minimal DFA, drop unreachable states,
 * renumber canonically).
 *
 * Build:  cc -O2 -Wall -Wextra -std=c11 -o dfacert dfacert.c        (mac)
 *         gcc -O2 -Wall -Wextra -std=c11 -fopenmp -o dfacert dfacert.c (linux)
 * Usage:  ./dfacert --selftest        run the property tests only
 *         ./dfacert <q>               search all canonical q-state DFAs
 *         ./dfacert --plain <q>       cross-check: plain q^(2q) enumeration
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

#define MAXQ 8              /* max number of DFA states supported */
#define MAXBITS 160         /* string buffer size for encodings */

typedef struct {
    int q;                  /* number of states; start state is 0 */
    uint8_t d[MAXQ][2];     /* transition table d[state][symbol] */
    uint32_t F;             /* accepting set as bitmask */
} DFA;

/* ------------------------------------------------------------------ */
/* Encoding helpers                                                    */
/* ------------------------------------------------------------------ */

/* LSB-first binary encoding of n >= 1; returns length; NUL-terminates. */
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

/* The 3n+1 map as an LSB-first string transduction (carry starts at 1). */
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

/* Membership in L_A = L(A) ∩ C  (C = nonempty strings ending in '1'). */
static int dfa_member(const DFA *A, const char *w, int len)
{
    if (len <= 0 || w[len - 1] != '1') return 0;
    int s = 0;
    for (int i = 0; i < len; i++) s = A->d[s][w[i] - '0'];
    return (int)((A->F >> s) & 1u);
}

/* ------------------------------------------------------------------ */
/* Certificate conditions                                              */
/* ------------------------------------------------------------------ */

/* (1) L_A nonempty: some state s reachable from 0 (by any string, incl.
 * the empty one) has d[s][1] accepting — then (path)·'1' is in L_A.    */
static int check_nonempty(const DFA *A)
{
    uint8_t seen[MAXQ] = {0};
    int queue[MAXQ], qh = 0, qt = 0;
    seen[0] = 1; queue[qt++] = 0;
    while (qh < qt) {
        int s = queue[qh++];
        for (int b = 0; b < 2; b++) {
            int t = A->d[s][b];
            if (!seen[t]) { seen[t] = 1; queue[qt++] = t; }
        }
    }
    for (int s = 0; s < A->q; s++)
        if (seen[s] && ((A->F >> A->d[s][1]) & 1u)) return 1;
    return 0;
}

/* (2) "1" not in L_A.  "1" ends in '1', so it is in L_A iff d[0][1] in F. */
static int check_one_not_in(const DFA *A)
{
    return !((A->F >> A->d[0][1]) & 1u);
}

/* (3a) EVEN closure: for every w = 0v in L_A we need v in L_A.
 * (w ends in '1' so v is nonempty and also ends in '1'; conversely w="0"
 * alone is not in C, so exactly the pairs (0v, v) with v in C matter.)
 *
 * Product BFS over pairs (x, y): x runs A from d[0][0] (simulating A on
 * w = 0·prefix), y runs A from 0 (simulating A on v = prefix), reading the
 * same symbols.  Every v ending in '1' is prefix·'1' for some reachable
 * pair (incl. the empty prefix: v = "1", w = "01" — the n=2 -> n=1 case).
 * Violation iff for some reachable (x,y): d[x][1] in F but d[y][1] not.  */
static int check_even_closed(const DFA *A)
{
    int q = A->q;
    uint8_t seen[MAXQ * MAXQ] = {0};
    int queue[MAXQ * MAXQ], qh = 0, qt = 0;
    int start = A->d[0][0] * q + 0;
    seen[start] = 1; queue[qt++] = start;
    while (qh < qt) {
        int p = queue[qh++], x = p / q, y = p % q;
        if (((A->F >> A->d[x][1]) & 1u) && !((A->F >> A->d[y][1]) & 1u))
            return 0;                              /* violation found */
        for (int b = 0; b < 2; b++) {
            int np = A->d[x][b] * q + A->d[y][b];
            if (!seen[np]) { seen[np] = 1; queue[qt++] = np; }
        }
    }
    return 1;
}

/* Feed the end-of-input carry flush into the output-side DFA state y. */
static int flush_accept(const DFA *A, int y, int c)
{
    while (c) { y = A->d[y][c & 1]; c >>= 1; }
    return (int)((A->F >> y) & 1u);
}

/* (3b) ODD closure: for every w in L_A starting with '1' (odd n; w also
 * ends in '1') we need transduce3np1(w) in L_A.  (If "1" itself is in
 * L(A) the checker includes it — mathematically that IS the closure
 * condition at n=1; condition (2) is enforced separately.)
 *
 * Product BFS over triples (x, y, c): x = A-state on the input read so
 * far (from state 0), y = A-state on the transducer output emitted so far
 * (from state 0; exactly one output bit per input bit), c = carry.
 * The first input bit is forced to '1'.  A word w = prefix·'1' is
 * complete; at every '1'-transition whose input-side target is accepting
 * we apply the carry flush to the output side and require acceptance.
 * After the final input bit '1' the carry is in {1,2}, so the flush emits
 * '1' last: the output always ends in '1', i.e. is a valid encoding, so
 * transduce(w) in L_A iff the flushed output state is accepting.        */
static int check_odd_closed(const DFA *A)
{
    int q = A->q;
    /* first bit b=1 from (x=0, y=0, c=1): s = 3+1 = 4, emit 0, carry 2 */
    int x0 = A->d[0][1], y0 = A->d[0][0], c0 = 2;
    /* the one-letter word w = "1" (n = 1) */
    if (((A->F >> x0) & 1u) && !flush_accept(A, y0, c0)) return 0;

    uint8_t seen[MAXQ * MAXQ * 3] = {0};
    int queue[MAXQ * MAXQ * 3], qh = 0, qt = 0;
    int st = (x0 * q + y0) * 3 + c0;
    seen[st] = 1; queue[qt++] = st;
    while (qh < qt) {
        int p = queue[qh++];
        int c = p % 3, y = (p / 3) % q, x = p / (3 * q);
        for (int b = 0; b < 2; b++) {
            int s = 3 * b + c, e = s & 1, nc = s >> 1;
            int nx = A->d[x][b], ny = A->d[y][e];
            if (b == 1 && ((A->F >> nx) & 1u) && !flush_accept(A, ny, nc))
                return 0;                          /* violation found */
            int np = (nx * q + ny) * 3 + nc;
            if (!seen[np]) { seen[np] = 1; queue[qt++] = np; }
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* Independent verification of a candidate (safety net, not the proof) */
/* ------------------------------------------------------------------ */

#define VERIF_MAXLEN   40
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
    unsigned __int128 n = decode_bits(V->buf, len);
    unsigned long long nl = (unsigned long long)n;   /* len<=40 bits */
    if (V->nsample < VERIF_NSAMPLE) V->sample[V->nsample++] = nl;
    if (nl == 1ULL) {
        fprintf(stderr, "VERIFY BUG: 1 is a member of L\n");
        V->fail = 1; return;
    }
    unsigned __int128 t = (nl & 1) ? ((unsigned __int128)3 * n + 1) : (n >> 1);
    char wt[MAXBITS];
    int lt = encode_bits(t, wt);
    if (!dfa_member(V->A, wt, lt)) {
        fprintf(stderr, "VERIFY BUG: member n=%llu but T(n)=%llu not in L\n",
                nl, (unsigned long long)t);
        V->fail = 1; return;
    }
    if (nl & 1) {   /* cross-check transducer against arithmetic */
        char wo[MAXBITS];
        int lo = transduce3np1(V->buf, len, wo);
        if (lo != lt || memcmp(wo, wt, (size_t)lt) != 0) {
            fprintf(stderr, "VERIFY BUG: transducer mismatch at n=%llu\n", nl);
            V->fail = 1;
        }
    }
}

static void verify_dfs(Verif *V, int state, int depth, int targetlen)
{
    if (V->fail || V->members >= VERIF_MEMBER_CAP || V->nodes >= VERIF_NODE_CAP)
        return;
    V->nodes++;
    if (depth == targetlen) {
        if (V->buf[depth - 1] == '1' && ((V->A->F >> state) & 1u))
            verify_member(V, depth);
        return;
    }
    for (int b = 0; b < 2; b++) {
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
    fprintf(f, "DFA: q=%d, start=0, F={", A->q);
    int first = 1;
    for (int s = 0; s < A->q; s++)
        if ((A->F >> s) & 1u) { fprintf(f, "%s%d", first ? "" : ",", s); first = 0; }
    fprintf(f, "}\n");
    for (int s = 0; s < A->q; s++)
        fprintf(f, "  state %d: on 0 -> %d, on 1 -> %d%s\n",
                s, A->d[s][0], A->d[s][1],
                ((A->F >> s) & 1u) ? "   [accepting]" : "");
}

/* ------------------------------------------------------------------ */
/* Enumeration of canonical initially-connected DFAs                   */
/* ------------------------------------------------------------------ */

/* A transition table is canonical iff scanning slots in the order
 * (state 0, sym 0), (state 0, sym 1), (state 1, sym 0), ... discovers the
 * states exactly in the order 1, 2, ..., q-1 (start state 0 is given),
 * and all q states are discovered.  Independent O(q) check:            */
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
    uint8_t d[MAXQ][2];
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
        if (!check_even_closed(&A)) continue;     /* (3a): even violation */
        if (!check_odd_closed(&A))  continue;     /* (3b): odd violation  */
        C->cands++;
        handle_candidate(&A, C);
    }
    if ((C->tables & 0x3FF) == 0) flush_progress(C);
}

/* Recursive canonical enumeration.  Slots are indexed i = 0..2q-1 with
 * slot i = (state i/2, symbol i%2); m = highest state index used so far.
 * Rules: (a) slot value v <= m+1 (a value of m+1 discovers a new state);
 * (b) when reaching the slots of state s (even i), s must already be
 * discovered (s <= m) — otherwise s is unreachable / out of order.
 * Rule (b) at s = q-1 forces all q states to be used.                  */
static void rec_slots(Ctx *C, int i, int m)
{
    int q = C->q;
    if (i == 2 * q) { process_table(C); return; }
    if ((i & 1) == 0 && (i >> 1) > m) return;
    int hi = (m + 1 < q - 1) ? m + 1 : q - 1;
    for (int v = 0; v <= hi; v++) {
        C->d[i >> 1][i & 1] = (uint8_t)v;
        rec_slots(C, i + 1, v > m ? v : m);
    }
}

/* Count canonical tables only (used by the selftest cross-check). */
static unsigned long long count_rec(int q, int i, int m)
{
    if (i == 2 * q) return 1;
    if ((i & 1) == 0 && (i >> 1) > m) return 0;
    unsigned long long tot = 0;
    int hi = (m + 1 < q - 1) ? m + 1 : q - 1;
    for (int v = 0; v <= hi; v++) tot += count_rec(q, i + 1, v > m ? v : m);
    return tot;
}

static unsigned long long brute_count_canonical(int q)
{
    long long ntab = 1;
    for (int j = 0; j < 2 * q; j++) ntab *= q;
    unsigned long long count = 0;
    uint8_t d[MAXQ][2];
    for (long long idx = 0; idx < ntab; idx++) {
        long long t = idx;
        for (int j = 2 * q - 1; j >= 0; j--) { d[j >> 1][j & 1] = (uint8_t)(t % q); t /= q; }
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
    int P = (2 * q < 4) ? 2 * q : 4;
    long long npre = 1;
    for (int j = 0; j < P; j++) npre *= q;

    unsigned long long tot_tables = 0, tot_scanned = 0,
                       tot_cands = 0, tot_verifs = 0;

    fprintf(stderr, "q=%d: searching canonical initially-connected DFAs "
            "(threads=%d, prefix slots=%d)\n", q, omp_get_max_threads(), P);

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
            if ((j & 1) == 0 && (j >> 1) > m) { ok = 0; break; }
            if (digs[j] > m + 1) { ok = 0; break; }
            C.d[j >> 1][j & 1] = (uint8_t)digs[j];
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

/* Plain enumeration of ALL q^(2q) tables (isomorphic/unreachable dupes
 * included) — slower cross-check that canonical enumeration misses
 * nothing; candidate counts must be zero in both or nonzero in both.   */
static void search_plain(int q)
{
    double t0 = now_seconds();
    g_progress = 0;
    g_next_report = 10000000ULL;
    long long ntab = 1;
    for (int j = 0; j < 2 * q; j++) ntab *= q;

    Ctx C;
    memset(&C, 0, sizeof C);
    C.q = q;
    C.plain = 1;
    for (long long idx = 0; idx < ntab; idx++) {
        long long t = idx;
        for (int j = 2 * q - 1; j >= 0; j--) { C.d[j >> 1][j & 1] = (uint8_t)(t % q); t /= q; }
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
    char wa[MAXBITS], wb[MAXBITS], wc[MAXBITS];
    int la, lb, lc;

    /* --- explicit transducer cases ------------------------------------ */
    la = transduce3np1("1", 1, wa);                       /* n=1 -> 4  */
    if (la != 3 || strcmp(wa, "001") != 0) return st_fail("T(1) != 001");
    la = transduce3np1("11", 2, wa);                      /* n=3 -> 10 */
    if (la != 4 || strcmp(wa, "0101") != 0) return st_fail("T(3) != 0101");
    la = transduce3np1("101", 3, wa);                     /* n=5 -> 16 */
    if (la != 5 || strcmp(wa, "00001") != 0) return st_fail("T(5) != 00001");

    /* --- transducer property test: 1e5 random odd n in [1, 2^60) ------ */
    xs_state = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 100000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 60) - 1)) | 1ULL;
        unsigned __int128 t = (unsigned __int128)3 * n + 1;
        la = encode_bits(n, wa);
        lb = encode_bits(t, wb);
        lc = transduce3np1(wa, la, wc);
        if (lc != lb || memcmp(wb, wc, (size_t)lc) != 0)
            return st_fail("transducer output != arithmetic 3n+1");
        if (wc[lc - 1] != '1') return st_fail("transducer output not ending in 1");
        if (!(lc == la || lc == la + 1 || lc == la + 2))
            return st_fail("transducer output length not in {len, len+1, len+2}");
    }
    fprintf(stderr, "selftest: transducer == 3n+1 on 100000 random odd n < 2^60\n");

    /* --- even step: drop first char == n/2 ---------------------------- */
    for (int i = 0; i < 100000; i++) {
        uint64_t k = (xorshift64() & ((1ULL << 59) - 1)) + 1;   /* k >= 1 */
        uint64_t n = 2 * k;
        la = encode_bits(n, wa);
        lb = encode_bits(k, wb);
        if (wa[0] != '0') return st_fail("even n encoding does not start with 0");
        if (la != lb + 1 || memcmp(wa + 1, wb, (size_t)lb) != 0)
            return st_fail("dropping first char != n/2");
    }
    fprintf(stderr, "selftest: even step (drop first char) == n/2 on 100000 random n\n");

    /* --- encode/decode roundtrip --------------------------------------- */
    for (int i = 0; i < 100000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 62) - 1)) + 1;
        la = encode_bits(n, wa);
        if ((uint64_t)decode_bits(wa, la) != n) return st_fail("roundtrip (random)");
        if (wa[la - 1] != '1') return st_fail("encoding does not end in 1");
    }
    for (uint64_t n = 1; n <= 2000; n++) {
        la = encode_bits(n, wa);
        if ((uint64_t)decode_bits(wa, la) != n) return st_fail("roundtrip (small)");
    }
    fprintf(stderr, "selftest: encode/decode roundtrip ok\n");

    /* --- membership runner --------------------------------------------- */
    DFA A_all = { .q = 1, .d = {{0, 0}}, .F = 1u };   /* L(A)=Sigma*, L_A=C */
    if (!dfa_member(&A_all, "1", 1))  return st_fail("membership: '1' in C");
    if (dfa_member(&A_all, "0", 1))   return st_fail("membership: '0' not in C");
    if (dfa_member(&A_all, "10", 2))  return st_fail("membership: '10' not in C");
    if (dfa_member(&A_all, "", 0))    return st_fail("membership: empty not in C");
    for (int i = 0; i < 1000; i++) {
        uint64_t n = (xorshift64() & ((1ULL << 40) - 1)) + 1;
        la = encode_bits(n, wa);
        if (!dfa_member(&A_all, wa, la)) return st_fail("membership: encode(n) in C");
    }

    /* --- positive/negative controls for the certificate checks -------- */

    /* Control 1: L = C (all n >= 1).  T-closed, but contains 1:
     * everything must pass EXCEPT the 1-not-in-L test.                  */
    if (!check_nonempty(&A_all))    return st_fail("A_all: should be nonempty");
    if (check_one_not_in(&A_all))   return st_fail("A_all: '1' should be in L");
    if (!check_even_closed(&A_all)) return st_fail("A_all: even closure should PASS");
    if (!check_odd_closed(&A_all))  return st_fail("A_all: odd closure should PASS");

    /* Control 2: L0 = all strings ending in 1 of length >= 2 (all n >= 2).
     * T(2)=1 escapes L0, so even closure must FAIL at w="01" (v="1").
     * Odd closure passes: odd n>=3 has 3n+1>=10, encoding length >= 2.   */
    DFA A_len2 = { .q = 3, .d = {{1, 1}, {2, 2}, {2, 2}}, .F = 1u << 2 };
    if (!check_nonempty(&A_len2))   return st_fail("A_len2: should be nonempty");
    if (!check_one_not_in(&A_len2)) return st_fail("A_len2: '1' should NOT be in L");
    if (check_even_closed(&A_len2)) return st_fail("A_len2: even closure should FAIL (w=01)");
    if (!check_odd_closed(&A_len2)) return st_fail("A_len2: odd closure should PASS");
    /* the exact quotient subtlety w="01" -> v="1": */
    if (!dfa_member(&A_len2, "01", 2)) return st_fail("A_len2: '01' (n=2) should be in L");
    if (dfa_member(&A_len2, "1", 1))   return st_fail("A_len2: '1' (n=1) should NOT be in L");

    /* Control 3: L = {"11"} = {3}.  T(3) = 10 = "0101" not in L:
     * odd closure must FAIL; even closure passes vacuously.             */
    DFA A_only3 = { .q = 4, .d = {{3, 1}, {3, 2}, {3, 3}, {3, 3}}, .F = 1u << 2 };
    if (!check_nonempty(&A_only3))    return st_fail("A_only3: should be nonempty");
    if (!check_one_not_in(&A_only3))  return st_fail("A_only3: '1' should NOT be in L");
    if (!check_even_closed(&A_only3)) return st_fail("A_only3: even closure should PASS");
    if (check_odd_closed(&A_only3))   return st_fail("A_only3: odd closure should FAIL");

    /* Control 4: empty language — closures hold vacuously, nonempty fails. */
    DFA A_empty = { .q = 1, .d = {{0, 0}}, .F = 0u };
    if (check_nonempty(&A_empty))     return st_fail("A_empty: should be empty");
    if (!check_one_not_in(&A_empty))  return st_fail("A_empty: '1' not in L");
    if (!check_even_closed(&A_empty)) return st_fail("A_empty: even closure vacuous");
    if (!check_odd_closed(&A_empty))  return st_fail("A_empty: odd closure vacuous");
    fprintf(stderr, "selftest: closure-checker controls ok "
            "(C, C-minus-{1}, {3}, empty)\n");

    /* --- canonical enumeration vs brute-force canonicity filter ------- */
    for (int q = 1; q <= 4; q++) {
        unsigned long long a = count_rec(q, 0, 0);
        unsigned long long b = brute_count_canonical(q);
        if (a != b) return st_fail("canonical enumeration count != brute-force count");
        fprintf(stderr, "selftest: q=%d canonical tables = %llu (brute-force agrees)\n",
                q, a);
    }
    if (count_rec(2, 0, 0) != 12)
        return st_fail("q=2 canonical table count != 12 (hand-verified value)");

    fprintf(stderr, "SELFTEST PASSED\n");
    return 1;
}

/* ------------------------------------------------------------------ */

static void usage(const char *argv0)
{
    fprintf(stderr,
        "usage: %s --selftest        run property tests\n"
        "       %s <q>               search all canonical q-state DFAs (1..%d)\n"
        "       %s --plain <q>       cross-check via plain q^(2q) enumeration\n",
        argv0, argv0, MAXQ, argv0);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest() ? 0 : 1;

    if (argc >= 3 && strcmp(argv[1], "--plain") == 0) {
        int q = atoi(argv[2]);
        if (q < 1 || q > MAXQ) { usage(argv[0]); return 2; }
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
