"""Does any conjugation invariant SEPARATE the cycle (delta=0) locus within a
fixed (K,L) fiber? Enumerate all words; per fiber report:
  - Phi range (should be a single value K-L: zero within-fiber information),
  - whether the Dedekind sum s or trace mod |Lambda| separates {delta=0} from
    {delta!=0} (Spearman-free: we just check if the delta=0 set is an interval
    in the invariant's sorted order, and the point-biserial-ish gap),
  - a genuinely QUADRATIC conjugation-invariant word functional (a C.-L.-Simon-
    style interleaving/linking count against a fixed reference necklace) and
    whether IT separates.
Also: W(a) vs trace(M(a)) are BOTH continuant-type polynomials in the run vector
but different specialisations -> we show trace does not determine W (same-trace,
different-delta pairs), i.e. the classical (unimodular) continuant is blind to
the (3,2)-twisted continuant W.
"""
import csv, itertools
from statistics import mean, pstdev
from modknots import analyze_word, lam, word_to_runvector

def all_words(K, L):
    for pos in itertools.combinations(range(K), L):
        vv = [0]*K
        for p in pos:
            vv[p] = 1
        yield tuple(vv)

# --- quadratic proxy: interleaving/linking count vs a reference necklace ---
# Represent a necklace by its cyclic run vector a=(a_1,...,a_L). Map to the
# cyclic {R,L} word (a_i R's then one L). Linking-style count against reference:
# number of cyclic positions where the two words' "R/L exit patterns" cross,
# summed over relative rotations -- a bilinear (quadratic) necklace functional.
def rl_word(a):
    w = []
    for ai in a:
        w += [1]*ai + [0]   # 1=R, 0=L
    return w  # length K+L

def interleave_link(a, aref):
    """A symmetric, conjugation-invariant bilinear count in the spirit of the
    modular-knot linking pairing: over all relative cyclic offsets, count sign
    agreements of the R/L exit letters. O((K+L)(Kref+Lref))."""
    x = rl_word(a); y = rl_word(aref)
    nx, ny = len(x), len(y)
    tot = 0
    for off in range(ny):
        s = 0
        for i in range(nx):
            xi = x[i]
            yi = y[(i + off) % ny]
            s += 1 if xi == yi else -1
        tot += abs(s)
    return tot

REF = (2, 1)   # reference necklace R^2 L R^1 L  (a short primitive geodesic)

def separates(vals, labels):
    """labels: 1 if delta==0 else 0. Returns True if the delta==0 set is exactly
    the top or bottom block when sorted by val (a single-threshold separator),
    plus the normalised gap between the two groups' means over the spread."""
    pairs = sorted(zip(vals, labels))
    svals = [p[0] for p in pairs]
    slabs = [p[1] for p in pairs]
    n1 = sum(slabs)
    top_block = slabs[-n1:] == [1]*n1 if n1 else False
    bot_block = slabs[:n1] == [1]*n1 if n1 else False
    g1 = [v for v, l in zip(vals, labels) if l == 1]
    g0 = [v for v, l in zip(vals, labels) if l == 0]
    sd = pstdev(vals) or 1.0
    gap = abs((mean(g1) if g1 else 0) - (mean(g0) if g0 else 0)) / sd
    return (top_block or bot_block), gap

def analyze_fiber(K, L, wcap=400000):
    Lambda = lam(K, L)
    m = abs(Lambda)
    rows = []
    import math
    if math.comb(K, L) > wcap:
        return None
    for v in all_words(K, L):
        d = analyze_word(v)
        a = d['a']
        delta = d['W'] % m if m > 1 else 0
        rows.append({'v': v, 'a': a, 'W': d['W'], 'delta': delta,
                     'Phi': d['Phi'], 'ded': d['ded'], 'trace': d['trace'],
                     'trace_mod': d['trace'] % m if m > 1 else 0})
    labels = [1 if r['delta'] == 0 else 0 for r in rows]
    n0 = sum(labels)
    phis = set(r['Phi'] for r in rows)
    # separation tests
    sep_ded, gap_ded = separates([r['ded'] for r in rows], labels) if 0 < n0 < len(rows) else (None, 0)
    sep_tr, gap_tr = separates([r['trace_mod'] for r in rows], labels) if 0 < n0 < len(rows) else (None, 0)
    # quadratic proxy
    ql = [interleave_link(r['a'], REF) for r in rows]
    sep_q, gap_q = separates(ql, labels) if 0 < n0 < len(rows) else (None, 0)
    # PURITY CERTIFICATE (rigorous, non-statistical): group words by an invariant
    # value; the invariant can decide "delta==0" only if no value-class mixes a
    # delta==0 word with a delta!=0 word. Report #mixed classes / #classes.
    from collections import defaultdict
    def purity(keyfn):
        g = defaultdict(set)
        for r in rows:
            g[keyfn(r)].add(1 if r['delta'] == 0 else 0)
        classes = len(g)
        mixed = sum(1 for _, s in g.items() if len(s) > 1)
        return classes, mixed
    tr_classes, tr_mixed = purity(lambda r: r['trace'])
    ded_classes, ded_mixed = purity(lambda r: (r['ded']))
    q_classes, q_mixed = purity(lambda r: interleave_link(r['a'], REF))
    same_tr_diff_delta = tr_mixed
    return {
        'K': K, 'L': L, 'Lambda': Lambda, 'nwords': len(rows), 'n_delta0': n0,
        'Phi_values': sorted(phis), 'distinct_delta': len({r['delta'] for r in rows}),
        'ded_separates': sep_ded, 'ded_gap': round(gap_ded, 3),
        'trace_separates': sep_tr, 'trace_gap': round(gap_tr, 3),
        'quad_separates': sep_q, 'quad_gap': round(gap_q, 3),
        'trace_collisions_diff_delta': same_tr_diff_delta,
        'trace_mixed_frac': f"{tr_mixed}/{tr_classes}",
        'ded_mixed_frac': f"{ded_mixed}/{ded_classes}",
        'quad_mixed_frac': f"{q_mixed}/{q_classes}",
    }

def main():
    fibers = [(3,2),(4,3),(6,4),(8,5),(9,6),(11,7),(12,8),(10,6),(9,5)]
    out = []
    for K, L in fibers:
        r = analyze_fiber(K, L)
        if r:
            out.append(r)
            print(f"(K,L)=({K:2d},{L:2d}) Lam={r['Lambda']:>7d} nw={r['nwords']:>4d} n0={r['n_delta0']:>3d} "
                  f"Phi={r['Phi_values']} | delta-MIXED invariant-classes: "
                  f"trace={r['trace_mixed_frac']} ded={r['ded_mixed_frac']} quad={r['quad_mixed_frac']}")
    with open("separation.csv","w",newline="") as f:
        w = csv.writer(f)
        w.writerow(["K","L","Lambda","nwords","n_delta0","Phi_values","distinct_delta",
                    "trace_mixed_frac","ded_mixed_frac","quad_mixed_frac",
                    "ded_gap","trace_gap","quad_gap"])
        for r in out:
            w.writerow([r['K'],r['L'],r['Lambda'],r['nwords'],r['n_delta0'],
                        "|".join(map(str,r['Phi_values'])),r['distinct_delta'],
                        r['trace_mixed_frac'],r['ded_mixed_frac'],r['quad_mixed_frac'],
                        r['ded_gap'],r['trace_gap'],r['quad_gap']])
    print("wrote separation.csv")

if __name__ == "__main__":
    main()
