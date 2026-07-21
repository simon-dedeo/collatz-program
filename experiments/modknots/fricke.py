"""
The genuinely QUADRATIC / topological invariant: the Fricke trace polynomial
Tr(A_q) on the PSL(2,R)-character variety of PSL(2,Z), and the Alexander
polynomial of the modular (Lorenz) knot built from it.

Why this file exists.  Simon (arXiv:2211.05957) Prop. 0.2: the Alexander
polynomial of the modular knot sigma_A is
        Delta(sigma_A) = ( q^{Rad(A)} - Tr(A_q) + q^{-Rad(A)} ) / (q - q^{-1})^2 ,
a function ONLY of Rad(A)=#R-#L=K-L and the Fricke trace polynomial Tr(A_q),
where L_q=[[q,0],[1,1/q]], R_q=[[q,1],[0,1/q]] deform L,R (q->1 gives PSL2Z).
So the strongest topological invariant that is still a genuine CLASS FUNCTION
(coarser than the complete linking pairing of Thm 0.5) is Tr(A_q).

We compute Tr(A_q) exactly (Laurent polynomials over Z) for every necklace in a
fiber and ask the crack's Level-2 question: does Tr(A_q) -- equivalently the
Alexander polynomial -- SEPARATE the cycle locus {delta=0}=(M|W) inside the
(K,L) fiber?  Purity certificate: an invariant can certify cycles only if no
value-class mixes a delta=0 word with a delta!=0 word.

Also: the reversal witness.  In fiber (11,7) the actual cycle m17 a=(1,1,1,2,1,1,4)
and its necklace-reversal a=(1,1,2,1,1,1,4) have EQUAL ordinary trace (2855) but
delta 0 vs 60.  We test whether the finer Tr(A_q) (whole polynomial) tells them
apart -- and hence whether ANY function of (Rad, Tr) can see delta.
"""
import csv, itertools
from collections import defaultdict
from modknots import word_to_runvector, lam, bs_weight

# ---- Laurent polynomials over Z as dict {exponent: coeff}, exponent in Z -----
def lp_zero(): return {}
def lp_mono(c, e): return {e: c} if c else {}
def lp_add(a, b):
    r = dict(a)
    for e, c in b.items():
        r[e] = r.get(e, 0) + c
        if r[e] == 0: del r[e]
    return r
def lp_mul(a, b):
    r = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = e1 + e2
            r[e] = r.get(e, 0) + c1 * c2
    return {e: c for e, c in r.items() if c}
def lp_key(a):
    return tuple(sorted(a.items()))
def lp_str(a):
    if not a: return "0"
    return " + ".join(f"{c}q^{e}" for e, c in sorted(a.items()))

Q  = lp_mono(1, 1)      # q
Qi = lp_mono(1, -1)     # q^{-1}
ONE = lp_mono(1, 0)

# L_q = [[q,0],[1,1/q]], R_q = [[q,1],[0,1/q]] as 2x2 matrices of Laurent polys
Lq = ((Q, lp_zero()), (ONE, Qi))
Rq = ((Q, ONE), (lp_zero(), Qi))

def mmul(A, B):
    return (
        (lp_add(lp_mul(A[0][0], B[0][0]), lp_mul(A[0][1], B[1][0])),
         lp_add(lp_mul(A[0][0], B[0][1]), lp_mul(A[0][1], B[1][1]))),
        (lp_add(lp_mul(A[1][0], B[0][0]), lp_mul(A[1][1], B[1][0])),
         lp_add(lp_mul(A[1][0], B[0][1]), lp_mul(A[1][1], B[1][1]))),
    )

def Rq_pow(a):
    M = ((ONE, lp_zero()), (lp_zero(), ONE))
    for _ in range(a):
        M = mmul(M, Rq)
    return M

def fricke_trace(a):
    """Tr(A_q) for run vector a, A_q = prod R_q^{a_i} L_q. Laurent poly dict."""
    M = ((ONE, lp_zero()), (lp_zero(), ONE))
    for ai in a:
        M = mmul(mmul(M, Rq_pow(ai)), Lq)
    return lp_add(M[0][0], M[1][1])

def alexander(a, K, L):
    """Delta(sigma_A) = (q^{K-L} - Tr(A_q) + q^{-(K-L)}) / (q-1/q)^2, if it divides.
    Returns (poly_or_None, divides_bool)."""
    rad = K - L
    tr = fricke_trace(a)
    num = lp_add(lp_add(lp_mono(1, rad), lp_mono(1, -rad)),
                 {e: -c for e, c in tr.items()})
    # denominator (q - 1/q)^2 = q^2 - 2 + q^{-2}
    den = {2: 1, 0: -2, -2: 1}
    # Laurent long division from the top: max exponent strictly decreases each
    # step (leading term cancels, new terms only at re-2, re-4), so this halts.
    quo = {}
    rem = dict(num)
    den_lead_e = max(den); den_lead_c = den[den_lead_e]
    while rem:
        re = max(rem); rc = rem[re]
        if rc % den_lead_c != 0:
            return None, False
        qe = re - den_lead_e; qc = rc // den_lead_c
        quo[qe] = quo.get(qe, 0) + qc
        for de, dc in den.items():
            k = qe + de
            rem[k] = rem.get(k, 0) - qc * dc
            if rem[k] == 0: del rem[k]
    return ({e: c for e, c in quo.items() if c}, True) if not rem else (None, False)

def all_words(K, L):
    for pos in itertools.combinations(range(K), L):
        v = [0] * K
        for p in pos: v[p] = 1
        yield tuple(v)

def analyze_fiber(K, L, wcap=300000):
    import math
    if math.comb(K, L) > wcap:
        return None
    m = abs(lam(K, L))
    groups = defaultdict(set)     # Tr(A_q) polynomial -> set of {delta==0?}
    trace_groups = defaultdict(set)
    n0 = 0; nw = 0
    for v in all_words(K, L):
        a = tuple(word_to_runvector(v))
        delta0 = (bs_weight(v) % m == 0) if m > 1 else True
        tr = fricke_trace(a)
        groups[lp_key(tr)].add(delta0)
        # ordinary trace = Tr(A_q) at q=1 = sum of coeffs
        ordtr = sum(tr.values())
        trace_groups[ordtr].add(delta0)
        n0 += 1 if delta0 else 0
        nw += 1
    fricke_classes = len(groups)
    fricke_mixed = sum(1 for s in groups.values() if len(s) > 1)
    tr_classes = len(trace_groups)
    tr_mixed = sum(1 for s in trace_groups.values() if len(s) > 1)
    return {'K': K, 'L': L, 'Lambda': lam(K, L), 'nwords': nw, 'n_delta0': n0,
            'fricke_classes': fricke_classes, 'fricke_mixed': fricke_mixed,
            'ord_trace_classes': tr_classes, 'ord_trace_mixed': tr_mixed}

def reversal_witness():
    """Does the whole Fricke polynomial distinguish m17 from its reversal
    (which share ordinary trace 2855 but have delta 0 vs 60)?"""
    a_cyc = (1, 1, 1, 2, 1, 1, 4)      # m17, delta=0
    a_rev = (1, 1, 2, 1, 1, 1, 4)      # reversal necklace, delta=60
    tc = fricke_trace(a_cyc); tr = fricke_trace(a_rev)
    return a_cyc, a_rev, tc, tr, (lp_key(tc) == lp_key(tr))

def main():
    print("== reversal witness (11,7): does Tr(A_q) separate m17 from its reversal? ==")
    ac, ar, tc, tr, same = reversal_witness()
    print(f"  m17      a={ac}  Tr(A_q)={lp_str(tc)}")
    print(f"  reversal a={ar}  Tr(A_q)={lp_str(tr)}")
    print(f"  ordinary trace (q=1): {sum(tc.values())} vs {sum(tr.values())}")
    print(f"  Fricke polynomials identical? {same}  -> Tr(A_q) {'CANNOT' if same else 'can'} tell them apart")
    print()
    # Alexander of the known cycles
    print("== Alexander polynomials Delta(sigma_A) of known cycles (Simon Prop 0.2) ==")
    for name, a, K, L in [("m1", (1,), 1, 1), ("1_2", (2,), 2, 1),
                          ("m5", (1, 2), 3, 2), ("m17", (1,1,1,2,1,1,4), 11, 7)]:
        d, ok = alexander(a, K, L)
        print(f"  {name:4s} a={a}  Rad={K-L}  Delta={'divides: '+lp_str(d) if ok else 'NON-POLYNOMIAL (torus/degenerate)'}")
    print()
    print("== fiber purity: does Tr(A_q) / ordinary-trace separate {delta=0}? ==")
    fibers = [(3,2),(4,3),(6,4),(8,5),(9,6),(11,7),(12,8),(10,6),(9,5),(13,8),(14,9)]
    rows = []
    for K, L in fibers:
        r = analyze_fiber(K, L)
        if r:
            rows.append(r)
            print(f"  (K,L)=({K:2d},{L:2d}) Lam={r['Lambda']:>8d} nw={r['nwords']:>6d} "
                  f"n0={r['n_delta0']:>3d} | Fricke: {r['fricke_mixed']:>3d}/{r['fricke_classes']:<4d} mixed"
                  f"  | ord-trace: {r['ord_trace_mixed']:>3d}/{r['ord_trace_classes']:<4d} mixed")
    with open("fricke.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["K","L","Lambda","nwords","n_delta0","fricke_classes","fricke_mixed",
                    "ord_trace_classes","ord_trace_mixed"])
        for r in rows:
            w.writerow([r['K'],r['L'],r['Lambda'],r['nwords'],r['n_delta0'],
                        r['fricke_classes'],r['fricke_mixed'],
                        r['ord_trace_classes'],r['ord_trace_mixed']])
    print("wrote fricke.csv")

if __name__ == "__main__":
    main()
