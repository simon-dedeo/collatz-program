"""Sanity/verification: Phi = K-L on all short words; known cycles reproduce."""
import itertools
from modknots import analyze_word, bs_weight, lam, rademacher, word_to_matrix

def all_words(K, L):
    for pos in itertools.combinations(range(K), L):
        v = [0]*K
        for p in pos:
            v[p] = 1
        yield tuple(v)

def check_phi_collapse():
    # Verify the Rademacher/Dedekind-sum formula Psi(M(v)) equals K-L on ALL
    # words up to K=11 (c=M[1][0] stays small enough for exact Dedekind sums).
    bad = 0
    tot = 0
    for K in range(1, 12):
        for L in range(1, K+1):
            for v in all_words(K, L):
                d = analyze_word(v)
                tot += 1
                if d['Phi'] != K - L:
                    bad += 1
                    if bad < 5:
                        print("  MISMATCH", v, d['Phi'], K-L)
    print(f"Phi==K-L (Rademacher-Dedekind formula) check: {tot} words, {bad} mismatches")
    return bad == 0

def check_known_cycles():
    # (name, word, expected Lambda, expected W, expected x=W/Lambda)
    known = [
        ("{-1}", (1,), -1, 1, -1),
        ("{1,2}", (1,0), 1, 1, 1),
        ("{-5,-7,-10}", (1,1,0), -1, 5, -5),
        ("{-17..}", (1,1,1,1,0,1,1,1,0,0,0), -139, 2363, -17),
    ]
    ok = True
    for name, v, eLam, eW, ex in known:
        d = analyze_word(v)
        W = d['W']; Lam = d['Lambda']
        x = W // Lam if Lam != 0 else None
        good = (Lam == eLam and W == eW and x == ex)
        ok = ok and good
        print(f"  {name:14s} K={d['K']} L={d['L']} Lam={Lam} W={W} x={x} "
              f"Phi={d['Phi']} ded={d['ded']:.4f} tr={d['trace']}  {'OK' if good else 'FAIL'}")
    return ok

if __name__ == "__main__":
    a = check_phi_collapse()
    print()
    b = check_known_cycles()
    print()
    print("ALL PASS" if (a and b) else "SOME FAIL")
