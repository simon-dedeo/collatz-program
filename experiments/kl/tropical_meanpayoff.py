"""Quenched TROPICAL (mean-payoff / Gaubert-Sergeev) spectral function of the KL
min-max operator, vs the Archimedean KL exponent gamma_k.

B_trop(v)_m = max( v_{4m} - 2b ,   [chord] ),  chord = (a-2)b + min_j v(ref2)  [m=2 mod9]
                                                    or (a-1)b + min_j v(ref8)  [m=8 mod9]
class 5 mod9: only the s-move.  Two-player: counter=max over moves, adversary=min over digit j.

chi_k(b) = ergodic (mean-payoff) value; piecewise-affine convex in b.
Archimedean pressure P_k(b) = log2 rho_k(2^b).  Fact: sum >= max  =>  P >= chi  =>  b_trop <= gamma_k.
Gap P-chi is the predecessor-tree ENTROPY (log-sum-exp surplus over max).
"""
import numpy as np, math, sys
sys.path.insert(0, "/Users/simon/Desktop/COLLATZ")
from kl_perron_solver import build, eigval
A = math.log2(3)


def chi(b, S, T=200000, tol=1e-10):
    i4m, mask2, mask8, ref2, ref8, n = S
    v = np.zeros(n)
    lo = hi = 0.0
    for t in range(T):
        s = v[i4m] - 2 * b
        c2 = (A - 2) * b + np.minimum(np.minimum(v[ref2[:, 0]], v[ref2[:, 1]]), v[ref2[:, 2]])
        c8 = (A - 1) * b + np.minimum(np.minimum(v[ref8[:, 0]], v[ref8[:, 1]]), v[ref8[:, 2]])
        nv = s.copy()
        nv = np.where(mask2, np.maximum(nv, c2), nv)
        nv = np.where(mask8, np.maximum(nv, c8), nv)
        d = nv - v
        lo, hi = d.min(), d.max()          # Collatz-Wielandt bracket for topical maps
        if hi - lo < tol:
            return 0.5 * (lo + hi)
        v = nv - nv.mean()                 # renormalize to avoid overflow
    return 0.5 * (lo + hi)


def b_trop(S, blo=0.0, bhi=1.5):
    for _ in range(60):
        bm = 0.5 * (blo + bhi)
        if chi(bm, S) > 0:                 # chi decreasing in b on this range (checked)
            blo = bm
        else:
            bhi = bm
    return 0.5 * (blo + bhi)


if __name__ == "__main__":
    print(f"{'k':>2} {'states':>7} {'gamma_k':>9} {'b_trop':>9} {'gap(entropy)':>12} "
          f"{'chi(gamma_k)':>12} {'P(b_trop)':>10}")
    for k in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 8):
        S = build(k)
        n = S[5]
        # Archimedean threshold gamma_k
        lo, hi = 1.2, 2.0
        for _ in range(60):
            lam = math.sqrt(lo * hi)
            if eigval(lam, S)[0] >= 1.0:
                lo = lam
            else:
                hi = lam
        lam_k = 0.5 * (lo + hi)
        g = math.log2(lam_k)
        bt = b_trop(S)
        chg = chi(g, S)                    # tropical value at Archimedean threshold (<=0)
        Pbt = math.log2(eigval(2 ** bt, S)[0])   # Archimedean pressure at tropical threshold (>=0)
        print(f"{k:>2} {n:>7} {g:>9.5f} {bt:>9.5f} {g-bt:>12.5f} {chg:>12.5f} {Pbt:>10.5f}",
              flush=True)
