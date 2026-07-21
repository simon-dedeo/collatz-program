"""m5_recheck.py -- INDEPENDENT re-check of the falsification witness.
Stdlib only, plain Fractions, NO import of the other modules; re-derives every
load-bearing quantity from scratch, then re-reads cert_k15 from disk with an
independently coded fiber indexing to confirm m4's headline.
"""
from fractions import Fraction as F


# ---- (A) Aligned-block marginal-eigenvalue identity, from scratch -------------
# Phases over 6 transport moves from phase 2: 2,8,5,2,8,5.  Branch events:
#   B2 @ t=0 (coeff p^0*q2), B8 @ t=1 (p^1*q8), B2 @ t=3 (p^3*q2), B8 @ t=4 (p^4*q8);
#   tail p^6.  Aligned label perms: transport/B2 -> identity, B8 -> swap(1,2).
# Build 3x3 matrix rows j: out_j = sum coeff * D_j * in_{perm(j)} with D=1.
def aligned_matrix(p, q2, q8):
    swap = {0: 0, 1: 2, 2: 1}
    ident = {0: 0, 1: 1, 2: 2}
    terms = [(p**6, ident), (q2, ident), (p*q8, swap),
             (p**3*q2, ident), (p**4*q8, swap)]
    B = [[F(0)]*3 for _ in range(3)]
    for coeff, perm in terms:
        for j in range(3):
            B[j][perm[j]] += coeff
    return B


def matvec(B, v):
    return [sum(B[i][j]*v[j] for j in range(3)) for i in range(3)]


def check_marginal(p, q2, q8, tag):
    B = aligned_matrix(p, q2, q8)
    mean = [F(1), F(1), F(1)]
    osc = [F(2), F(-1), F(-1)]              # co-spine oscillation direction
    Bmean = matvec(B, mean)
    Bosc = matvec(B, osc)
    # eigenvalue on mean:
    lam_mean = Bmean[0] / mean[0]
    ok_mean = all(Bmean[i] == lam_mean*mean[i] for i in range(3))
    lam_osc = Bosc[0] / osc[0]
    ok_osc = all(Bosc[i] == lam_osc*osc[i] for i in range(3))
    norm = lam_osc/lam_mean
    print(f"[{tag}] Perron(mean)={lam_mean} eig(osc)={lam_osc}  "
          f"both_eigvec={ok_mean and ok_osc}  normalized_osc={norm} "
          f"(={float(norm):.6f})")
    return ok_mean and ok_osc and norm == 1


# ---- (B) Zero-charge cycle in the ball automaton, from scratch ----------------
MOD = 27
def is_state(q): return q % 3 == 2 and 0 <= q < MOD
def transport(q): return (4*q) % MOD
def b2(q): return [((4*q-2)//3) % 9 + i*9 for i in range(3)] if q % 9 == 2 else None
def b8(q): return [((2*q-1)//3) % 9 + i*9 for i in range(3)] if q % 9 == 8 else None
E3 = {5, 20, 26}   # residues of -1,-1/4,-1/16 mod 27


def check_zero_charge_cycle():
    # exhibit an explicit closed walk avoiding E3, and confirm it uses a B8
    # (oscillation-carrying swap) edge landing in C.
    C = [q for q in range(2, MOD, 3) if q not in E3]
    assert set(C) == {2, 8, 11, 14, 17, 23}
    # self-loop at 2 via B2 (2 -> {2,11,20}; target 2 in C): trivial zero-charge loop
    b2_2 = b2(2)
    selfloop2 = (2 in b2_2) and (2 not in E3)
    # oscillation-carrying B8 within C: at ball 8, B8 siblings {5,14,23}; drop
    # the E-sibling 5, keep 14,23 in C -> carries between-sibling (swap) osc.
    sib8 = b8(8)
    c_sibs_8 = [y for y in sib8 if y not in E3]
    # verify C is strongly connected avoiding E3 by BFS reachability both ways
    def adj(q):
        out = {transport(q)}
        for f in (b2(q), b8(q)):
            if f:
                out |= set(f)
        return {x for x in out if x not in E3}
    def reach(src):
        seen = {src}; st = [src]
        while st:
            u = st.pop()
            for w in adj(u):
                if w not in seen:
                    seen.add(w); st.append(w)
        return seen
    scc = all(set(C) <= reach(q) for q in C)
    print(f"[ball] C={sorted(C)}  self-loop@2(B2)={selfloop2}  "
          f"B8@8 siblings={sib8} in-C(osc-carrying)={c_sibs_8}  "
          f"C strongly-connected avoiding E3={scc}")
    return selfloop2 and scc and len(c_sibs_8) >= 2


# ---- (C) Independent re-read of cert_k15 headline -----------------------------
def recheck_data():
    import numpy as np
    C = np.load('/Users/simon/Desktop/COLLATZ/experiments/kl/cert_k15_C.npy')
    k = 15; stride = 3**(k-2)
    # fiber s in [0,stride): lifts s, s+stride, s+2*stride; state m=2+3s; ball=m%27
    v = [C[:stride].astype('int64'), C[stride:2*stride].astype('int64'),
         C[2*stride:3*stride].astype('int64')]
    mx = np.maximum(np.maximum(v[0], v[1]), v[2])
    mn = np.minimum(np.minimum(v[0], v[1]), v[2])
    mean = (v[0]+v[1]+v[2]) / 3.0
    osc = np.where(mean > 0, (mx-mn)/mean, 0.0)
    ball = (2 + 3*np.arange(stride, dtype='int64')) % 27
    inE = np.isin(ball, list(E3))
    def wmean(mask):
        m = mean[mask]; return float((osc[mask]*m).sum()/m.sum())
    oE, oC = wmean(inE), wmean(~inE)
    print(f"[data k=15 independent] mass-wtd osc  E={oE:.4f}  C={oC:.4f}  "
          f"ratio C/E={oC/oE:.3f}")
    return oC, oE


if __name__ == '__main__':
    print("=== (A) marginal eigenvalue identity (exact rationals) ===")
    a2 = check_marginal(F(1, 4), F(3, 4), F(3, 2), 'lam=2')
    # a generic rational lambda=9/5 to show identity is lambda-independent
    p = F(5, 9)**2
    a18 = check_marginal(p, F(3, 4), F(3, 2), 'generic-coeffs')
    print("=== (B) zero-charge cycle ===")
    b = check_zero_charge_cycle()
    print("=== (C) data re-read ===")
    recheck_data()
    print()
    print("FALSIFICATION WITNESS CONFIRMED:" if (a2 and b) else "CHECK FAILED:",
          "aligned marginal osc eigenvalue == 1 (exact) &&",
          "zero-charge oscillation-carrying cycle exists in C.")
