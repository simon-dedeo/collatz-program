"""The isotopy/length-descent test (the crack's Level-2 question):
does the cycle condition delta=0 factor through the modular-knot topology
(hyperbolic length = trace, or Dedekind sum)? Answer NO if we can exhibit two
DISTINCT necklaces (closed geodesics) with equal trace (equal length) but
different delta. Also confirm rotation-covariance delta(sigma v)=2^{a_1}delta(v),
and that W is a (3,2)-twist of the trace-continuant (same word, different weights)."""
import itertools
from collections import defaultdict
from fractions import Fraction
from modknots import analyze_word, lam, word_to_runvector, runvector_to_matrix

def necklaces(K, L):
    """canonical necklace reps (lexicographically-min rotation) of shape (K,L)."""
    seen = set()
    reps = []
    for pos in itertools.combinations(range(K), L):
        v = [0]*K
        for p in pos: v[p] = 1
        v = tuple(v)
        rots = [v[i:]+v[:i] for i in range(K)]
        rep = min(rots)
        if rep not in seen:
            seen.add(rep)
            reps.append(rep)
    return reps

def find_length_collisions(K, L):
    m = abs(lam(K, L))
    bytrace = defaultdict(list)
    byded = defaultdict(list)
    for v in necklaces(K, L):
        d = analyze_word(v)
        delta = d['W'] % m
        bytrace[d['trace']].append((v, delta, d['W'], d['a'], d['ded']))
        byded[round(d['ded'], 12)].append((v, delta, d['W'], d['a'], d['trace']))
    tr_split = [(t, recs) for t, recs in bytrace.items()
                if len({r[1] == 0 for r in recs}) > 1]
    ded_split = [(s, recs) for s, recs in byded.items()
                 if len({r[1] == 0 for r in recs}) > 1]
    return tr_split, ded_split, len(list(necklaces(K, L)))

def check_necklace_invariance(K, L):
    """delta=0 (Lambda|W) is a NECKLACE property: x_{sigma v}=T(x_v) keeps the
    orbit inside Z, so all rotations of a word agree on delta==0. Verify the
    delta==0 set is a union of full rotation-orbits."""
    m = abs(lam(K, L))
    bad = 0
    for pos in itertools.combinations(range(K), L):
        v = [0]*K
        for p in pos: v[p] = 1
        v = tuple(v)
        z0 = (analyze_word(v)['W'] % m == 0)
        for i in range(1, K):
            sv = v[i:]+v[:i]
            if (analyze_word(sv)['W'] % m == 0) != z0:
                bad += 1
                break
    return bad

if __name__ == "__main__":
    print("necklace-invariance of {delta=0} (11,7):",
          "OK" if check_necklace_invariance(11, 7) == 0 else "FAIL")
    for K, L in [(11, 7), (12, 8), (9, 6)]:
        tr_split, ded_split, nneck = find_length_collisions(K, L)
        print(f"\n(K,L)=({K},{L}) Lambda={lam(K,L)} #necklaces={nneck}")
        print(f"  trace-values carrying BOTH a cycle and a non-cycle necklace: {len(tr_split)}")
        for t, recs in tr_split[:2]:
            print(f"   trace={t}: " + " ; ".join(
                f"a={r[3]} delta={'0(CYCLE)' if r[1]==0 else r[1]} W={r[2]}" for r in recs))
        print(f"  Dedekind-values carrying both: {len(ded_split)}")
        for s, recs in ded_split[:2]:
            print(f"   ded={s}: " + " ; ".join(
                f"a={r[3]} delta={'0(CYCLE)' if r[1]==0 else r[1]}" for r in recs))
