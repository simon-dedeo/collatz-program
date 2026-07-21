r"""m3_augmented.py -- coupled (mass M, fiber-range R) oscillation ENVELOPE on
the mod-3^J balls, sibling-resolved, and the ZERO-CHARGE spectral test.

Per ball xi (Q_3, mod 27) two observables: M(xi)=fiber mass, R(xi)=fiber range
(=osc*mean).  Dominating recursion (sol-contraction L2,L3,L5; Lemma-5 mass side):

  M(xi) = p M(4xi) + [xi=2(9)] q2 * SUM_j minfib(z2+j9)
                   + [xi=8(9)] q8 * SUM_j minfib(z8+j9),   minfib(y) <= M(y)/3.
  R(xi) = p R(4xi) + [branch] q_e * rngb,
    rngb <= (1/3)(max_j M(y_j) - min_j M(y_j)) + (2/3) max_j R(y_j),
    y_j = z_e + j*9 the THREE sibling balls (aligned: label j <-> sibling j).

MASS part is exactly the validated Lemma-5 automaton (SUM_j q_e M(y_j)/3 =
(q_e/3) SUM over the 3 fine balls); its column sums = s(lambda), Perron = s.
RANGE part is a monotone homogeneous map driven by mass sibling-spread (the
between-fiber osc of sol-contraction L5) plus transported range.

FALSIFICATION test: restrict to C = Q_3 \ E_3 (zero charge; drop balls in E_3
and edges touching them).  Power-iterate; report mass radius rho_M(C), range
radius rho_R(C), and whether osc = R/M stays bounded away from 0 (osc persists
=> zero-charge oscillation cycle => (CL) impossible) or decays (rho_R<rho_M).
"""
from fractions import Fraction
import automaton as am
import exact_weights as ew

MOD = 27
S = am.states(3)
E = set(am.exceptional_set(3))


def fcoef(lam):
    import math
    a = math.log(3, 2)
    l = float(lam)
    return l ** -2, l ** (a - 2), l ** (a - 1)


def fine_balls(xi):
    """The three sibling balls z_e + j*9 (j=0,1,2) for the branch at xi, or None."""
    if xi % 9 == 2:
        z = ((4 * xi - 2) // 3) % 9
        return [z + j * 9 for j in range(3)]
    if xi % 9 == 8:
        z = ((2 * xi - 1) // 3) % 9
        return [z + j * 9 for j in range(3)]
    return None


def step(M, R, p, q2, q8, keep):
    """One application of the monotone envelope. keep=set of allowed balls.
    M,R dicts over balls in keep.  References outside keep are treated as 0
    (zero-charge restriction: mass/osc that would flow through E is dropped)."""
    Mn, Rn = {}, {}
    for xi in keep:
        t = (4 * xi) % MOD
        m = p * (M[t] if t in keep else 0.0)
        r = p * (R[t] if t in keep else 0.0)
        fb = fine_balls(xi)
        if fb is not None:
            q = q2 if xi % 9 == 2 else q8
            ys = [y for y in fb if y in keep]
            My = [M[y] for y in ys] if ys else [0.0]
            Ry = [R[y] for y in ys] if ys else [0.0]
            m += q * sum(mv / 3 for mv in My)
            rngb = (1.0 / 3) * (max(My) - min(My)) + (2.0 / 3) * max(Ry)
            r += q * rngb
        Mn[xi] = m
        Rn[xi] = r
    return Mn, Rn


def radii(lam, restrict_C, iters=4000):
    p, q2, q8 = fcoef(lam)
    keep = set(q for q in S if (not restrict_C or q not in E))
    M = {q: 1.0 for q in keep}
    R = {q: 1.0 for q in keep}
    rhoM = rhoR = 1.0
    ratio = 1.0
    for _ in range(iters):
        Mn, Rn = step(M, R, p, q2, q8, keep)
        sM = sum(Mn.values()); sR = sum(Rn.values())
        sM0 = sum(M.values()); sR0 = sum(R.values())
        rhoM = sM / sM0 if sM0 else 0.0
        rhoR = sR / sR0 if sR0 else 0.0
        # renormalize
        M = {k: v / sM for k, v in Mn.items()} if sM else Mn
        R = {k: v / sR for k, v in Rn.items()} if sR else Rn
    # normalized osc growth = rhoR / rhoM
    return rhoM, rhoR, (rhoR / rhoM if rhoM else float('inf'))


if __name__ == '__main__':
    import csv, os
    outdir = os.path.dirname(os.path.abspath(__file__))
    rows = []
    for lname, lam in [('lam=2', Fraction(2)), ('lam18', ew.LAM18)]:
        for rc in (False, True):
            rM, rR, nrm = radii(lam, rc)
            rows.append({'lam': lname,
                         'subgraph': 'C_zero_charge' if rc else 'full',
                         'rho_mass': round(rM, 6), 'rho_range': round(rR, 6),
                         'normalized_osc_growth': round(nrm, 6)})
    with open(os.path.join(outdir, 'csv', 'm3_zero_charge.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    for r in rows:
        print(f"{r['lam']:6} {r['subgraph']:14} rho_mass={r['rho_mass']:.6f} "
              f"rho_range={r['rho_range']:.6f} norm_osc_growth={r['normalized_osc_growth']:.6f}")
