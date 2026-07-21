"""m2_profile.py -- exact L_w=6 block PROFILE map (sol-contraction Lemmas 1-3),
homogeneous, with affine source terms kept EXPLICIT (not collapsed).

A block over transport orbit r_t=4^t r, phases 2,8,5,2,8,5 (start phase 2):
events B2@t=0, B8@t=1, B2@t=3, B8@t=4; tail p^6.  Output fiber x=(x0,x1,x2):

  x_j = p^6 * x^tail_{P_tail(j)}
      + q2      * D * s0_{P0(j)}     (B2 @0)
      + p*q8    * D * s1_{P1(j)}     (B8 @1)
      + p^3*q2  * D * s3_{P3(j)}     (B2 @3)
      + p^4*q8  * D * s4_{P4(j)}     (B8 @4)

s_t = the branch-source fiber MEANS (3-vector over lift index) of event t; on the
ALIGNED class every permutation P is: tail/B2 -> identity, B8 -> j->2j (the swap).
D = min/mean policy factor in [3/(2K+1),1] (diagonal, per output index).

Self-referential (spine-like) closure: set every source s_t = x itself (the -1
spine references its own fiber, R8(-1)=-1; aligned class = spine face).  Then the
block is a single 3x3 nonnegative matrix B(D); its Perron root = mass growth, and
the eigenvalue on the mean-zero (oscillation) subspace / Perron = the NORMALIZED
oscillation multiplier.  We report both, exact where possible.
"""
from fractions import Fraction
import exact_weights as ew


def coeffs(lam=Fraction(2)):
    """Exact/enclosed (p,q2,q8) upper at lam. lam=2 exact via 2^(a-1) sandwich."""
    if lam == Fraction(2):
        p = Fraction(1, 4)
        # at lam=2: q2 = 2^(a-2) = 3/4 exactly (2^a=3), q8 = 2^(a-1)=3/2 exactly
        return p, Fraction(3, 4), Fraction(3, 2)
    enc = ew.weight_enclosures(lam, lam)
    return enc['p_hi'], enc['q2_hi'], enc['q8_hi']


# aligned permutations as index maps output_j -> source_index
P_ID = lambda j: j
P_SWAP = lambda j: (2 * j) % 3     # B8 aligned: j -> 2j


def block_matrix_selfref(D, lam=Fraction(2)):
    """3x3 exact matrix B with x^out = B x (self-referential aligned closure).
    D: tuple (D0,D1,D2) diagonal policy factors (Fractions in [3/(2K+1),1])."""
    p, q2, q8 = coeffs(lam)
    B = [[Fraction(0)] * 3 for _ in range(3)]
    # tail p^6, identity perm, no D
    for j in range(3):
        B[j][P_ID(j)] += p ** 6
    # B2 @0 : coeff q2, identity, D
    for j in range(3):
        B[j][P_ID(j)] += q2 * D[j]
    # B8 @1 : coeff p*q8, swap, D
    for j in range(3):
        B[j][P_SWAP(j)] += p * q8 * D[j]
    # B2 @3 : coeff p^3 q2, identity, D
    for j in range(3):
        B[j][P_ID(j)] += p ** 3 * q2 * D[j]
    # B8 @4 : coeff p^4 q8, swap, D
    for j in range(3):
        B[j][P_SWAP(j)] += p ** 4 * q8 * D[j]
    return B


def eig3(B):
    """Eigenvalues of 3x3 (float) + the mean-vector Perron and mean-zero action.
    Returns (perron, other_eigs, normalized_osc_radius)."""
    import numpy as np
    M = np.array([[float(x) for x in row] for row in B])
    ev = np.linalg.eigvals(M)
    ev = sorted(ev, key=lambda z: -abs(z))
    perron = abs(ev[0])
    others = [abs(z) for z in ev[1:]]
    norm_osc = max(others) / perron if perron > 0 else float('inf')
    return perron, others, norm_osc


if __name__ == '__main__':
    import csv, os
    outdir = os.path.dirname(os.path.abspath(__file__))
    rows = []
    for lam_name, lam in [('lam=2', Fraction(2)), ('lam18', ew.LAM18)]:
        for K in (1, 2, 4):
            dlo = Fraction(3, 2 * K + 1)
            # extreme D policies: all-1 (flat), and skew (one index at dlo)
            for Dname, D in [('D=1', (Fraction(1),) * 3),
                             ('D_skew0', (dlo, Fraction(1), Fraction(1))),
                             ('D_skew_all_lo', (dlo, dlo, dlo))]:
                B = block_matrix_selfref(D, lam)
                perron, others, nosc = eig3(B)
                rows.append({'lam': lam_name, 'K': K, 'D': Dname,
                             'perron': perron, 'eig2': others[0], 'eig3': others[1],
                             'norm_osc_radius': nosc})
    with open(os.path.join(outdir, 'csv', 'm2_aligned_spectrum.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader(); w.writerows(rows)
    for r in rows:
        print(f"{r['lam']:6} K={r['K']} {r['D']:14} perron={r['perron']:.6f} "
              f"|eig2|={r['eig2']:.6f} |eig3|={r['eig3']:.6f} "
              f"norm_osc={r['norm_osc_radius']:.6f}")
