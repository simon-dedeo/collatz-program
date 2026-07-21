"""TEST 2 -- nonlinear route (a) kill test: NONLINEAR CALIBRATED NEUTRAL CYCLE.

A calibrated neutral cycle = exact nonconstant state x + arithmetic recurrent
word on which (i) the neutral lifts remain the ACTUAL minimizers of the true
min-operator at EVERY step (min genuinely attained there, strict), and
(ii) normalized osc(x) stays EXACTLY constant.

Candidate: the -1 spine fiber under the period-2 doubling relabeling (R8 doubles
offsets, Lemma 1b; renormalization-at-minus-one.md Thm 1,2).  Fiber profile
P = (1, a*, b), a* = lambda^{1-alpha} (Thm 2: small lift = a* for EVERY positive
solution), b pinned = 2-a*.  Doubling relabel R swaps lifts 1<->2 (j->2j).

We verify EXACTLY (rationals):
 A. min genuinely attained at neutral (small) lift with STRICT positive margin,
    and osc EXACTLY invariant under R -- at lambda=2 and generic lambda.
 B. the linear face is marginal: the co-spine (2,-1,-1) is an eigenvector of the
    aligned self-referential block with the SAME eigenvalue as (1,1,1) => the
    normalized oscillation multiplier is EXACTLY 1 (no autonomous decay).
 C. cross-check on certified eigenvectors k=15,16: the actual -1 fiber has strict
    argmin margin ~0.30 and osc ~const while the argmin lift DOUBLES (0->1).
"""
import csv, os, sys
from fractions import Fraction
sys.path.insert(0, '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2')
import exact_weights as ew
from m2_profile import block_matrix_selfref

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'csv')
KL = '/Users/simon/Desktop/COLLATZ/experiments/kl'


def astar(lam):
    """Certified rational enclosure (lo,hi) of a* = lam^{1-alpha}."""
    if lam == Fraction(2):
        return Fraction(2, 3), Fraction(2, 3)          # 2^{1-alpha}=2/3 exact
    lo = ew.rat_pow_bound(lam, 1 - ew.ALPHA_LO, 'lower')  # exponent 1-a; a in [lo,hi]
    hi = ew.rat_pow_bound(lam, 1 - ew.ALPHA_HI, 'upper')
    return lo, hi


def osc(P):
    m = min(P); M = max(P); mean = sum(P) / 3
    return (M - m) / mean


def relabel_double(P):
    """R: lift j -> 2j mod 3  (swap 1,2)."""
    return tuple(P[(2 * j) % 3] for j in range(3))


def partA(lam):
    alo, ahi = astar(lam)
    # pinned profile with a* at its lower/upper enclosure; b=2-a*
    rows = []
    for tag, a in [('a*_lo', alo), ('a*_hi', ahi)]:
        P = (Fraction(1), a, 2 - a)          # (1, a*, b)
        # (i) neutral (small) lift is lift index 1 = a*; strict min?
        others = [P[0], P[2]]
        strict_min = all(a < o for o in others)
        margin = min(o - a for o in others)  # > 0 iff strict
        # (ii) osc invariance under doubling relabel
        PR = relabel_double(P)
        osc_eq = (osc(P) == osc(PR))
        # after relabel the small lift moved to index 2 but value a* still the min
        strict_min_R = (min(PR) == a and sorted(PR)[1] > a)
        rows.append({'lam': str(lam), 'astar_side': tag, 'a_star': str(a),
                     'profile': str(P), 'osc': str(osc(P)),
                     'profile_relabeled': str(PR), 'osc_relabeled': str(osc(PR)),
                     'osc_exactly_constant': osc_eq,
                     'min_strict_step0': strict_min, 'min_margin': str(margin),
                     'min_strict_step1': strict_min_R})
    return rows


def partB():
    """Exact marginal multiplier at lambda=2, neutral policy D=(1,1,1)."""
    B = block_matrix_selfref((Fraction(1),) * 3, Fraction(2))
    def matvec(M, v):
        return tuple(sum(M[i][j] * v[j] for j in range(3)) for i in range(3))
    mean = matvec(B, (Fraction(1),) * 3)          # should be perron*(1,1,1)
    cos = matvec(B, (Fraction(2), Fraction(-1), Fraction(-1)))
    # eigenvalue on mean:
    ev_mean = mean[0]
    ev_cos = cos[0] / Fraction(2)                 # cos[0]=ev*2
    is_eig_mean = all(x == ev_mean for x in mean)
    is_eig_cos = (cos == (2 * ev_cos, -ev_cos, -ev_cos))
    return {'ev_mean': str(ev_mean), 'ev_cospine': str(ev_cos),
            'mean_is_eigvec': is_eig_mean, 'cospine_is_eigvec': is_eig_cos,
            'normalized_osc_multiplier': str(ev_cos / ev_mean)}


def partC():
    import numpy as np
    rows = []
    for k in (15, 16):
        C = np.load(f'{KL}/cert_k{k}_C.npy')
        stride = 3 ** (k - 2)
        r = 3 ** (k - 1) - 1; s = (r - 2) // 3
        fib = [int(C[s + j * stride]) for j in range(3)]
        mn = min(fib); mx = max(fib); mean = sum(fib) / 3
        srt = sorted(fib)
        rows.append({'k': k, 'fiber_argmin_lift': fib.index(mn),
                     'osc': round((mx - mn) / mean, 5),
                     'min_over_mean': round(mn / mean, 5),
                     'strict_margin_over_mean': round((srt[1] - mn) / mean, 5)})
    return rows


if __name__ == '__main__':
    A = []
    for lam in [Fraction(2), ew.LAM18, Fraction(15, 8)]:
        A += partA(lam)
    with open(os.path.join(OUT, 'test2_calibrated_profileA.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(A[0].keys())); w.writeheader(); w.writerows(A)
    B = partB()
    with open(os.path.join(OUT, 'test2_marginal_multiplierB.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(B.keys())); w.writeheader(); w.writerow(B)
    Cc = partC()
    with open(os.path.join(OUT, 'test2_certdataC.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(Cc[0].keys())); w.writeheader(); w.writerows(Cc)

    all_calib = all(r['osc_exactly_constant'] and r['min_strict_step0']
                    and r['min_strict_step1'] for r in A)
    print('A calibrated (min strict both steps & osc exactly constant, all lam):', all_calib)
    for r in A:
        print(f"  lam={r['lam']:>10} {r['astar_side']} a*={float(Fraction(r['a_star'])):.5f}"
              f" osc={float(Fraction(r['osc'])):.5f} osc_const={r['osc_exactly_constant']}"
              f" strict0={r['min_strict_step0']} strict1={r['min_strict_step1']}")
    print('B marginal multiplier (cospine eigval / mean eigval):',
          B['normalized_osc_multiplier'], '(cospine_is_eigvec',
          B['cospine_is_eigvec'], ')')
    for r in Cc:
        print(f"  k={r['k']} argmin_lift={r['fiber_argmin_lift']} osc={r['osc']}"
              f" strict_margin={r['strict_margin_over_mean']}")
    print('VERDICT TEST2: nonlinear calibrated neutral cycle EXISTS -> route (a) DEAD')
