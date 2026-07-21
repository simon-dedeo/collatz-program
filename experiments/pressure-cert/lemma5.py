"""lemma5.py -- restricted-pressure gap search (sol-pressure Lemma 5, (2.9)-(2.10)).

Certificate object: positive rational h on Q_J, rational z > 1, rational R with

    sum_{e: q->q'} w_e * z^{b(e)} * h(q')  <=  R * h(q)      for every q,     (2.9)

where w_e are certified UPPER bounds on the normalized per-fiber-mass
multipliers valid for ALL lambda in [lam_lo, lam_hi] and every minimizing
policy (min <= mean domination; see automaton.py), and b(e) = 1_{target in E}.
Then for the mass unrolled n moves,  sum_r nu_k(r) z^{N_E(r,n)} <= C R^n, and
Markov gives (2.11):  nu_k{N_E >= theta n} <= C (R z^-theta)^n.  The certified
theta-region at (J,L) is  {theta : exists z with  R(z) z^-theta < 1}, i.e.
theta > theta* := min_z ln R(z)/ln z   (per MOVE of the level dynamics; the
L-blocked automaton is exactly the L-th power, b additive, so blocked results
are the L-th powers / L-multiples of the per-move ones).

Verification is exact: h is found by float Perron iteration, rounded to small
rationals, and (2.9) is then checked in Fraction arithmetic; R is returned as
the exact max row ratio.  The lambda-interval is covered by subdividing
[lam_lo, lam_hi] and taking per-subinterval certified upper weights; (2.9) is
required for every subinterval (per-weight monotonicity makes endpoint
evaluation valid on each piece).
"""

from fractions import Fraction
import math

import automaton as am
import exact_weights as ew


# ------------------------------------------------------------ float Perron tools

def _to_float(A):
    return [[float(x) for x in row] for row in A]


def perron(Af, iters=8000, tol=1e-14):
    """Power iteration; returns (rho, right eigenvector v with min 1)."""
    n = len(Af)
    v = [1.0] * n
    rho = 1.0
    for _ in range(iters):
        w = [sum(Af[i][j] * v[j] for j in range(n)) for i in range(n)]
        m = max(w)
        if m == 0:
            return 0.0, v
        w = [x / m for x in w]
        if max(abs(w[i] - v[i]) for i in range(n)) < tol:
            v = w
            rho = m
            break
        v, rho = w, m
    mn = min(x for x in v if x > 0) or 1.0
    v = [max(x, 1e-30) / mn for x in v]
    return rho, v


# ------------------------------------------------------------ exact certificate

def certify_h(J, subint_weights, E, z: Fraction, h_scale=10 ** 6):
    """Find (h, R) with exact verification of (2.9) for every weight subinterval.

    subint_weights: list of dicts {'p','q2','q8'} (Fractions, certified upper
    bounds on each subinterval of the lambda range).
    Returns (h list of Fractions, R Fraction, R_float).  R is the exact max of
    (W_z h)(q)/h(q) over q and subintervals -- so (2.9) holds with this R by
    construction; the 'search' part is only the quality of h.
    """
    n = len(am.states(J))
    # h from the float Perron eigenvector of the WORST (entrywise max) matrix
    Amax = [[Fraction(0)] * n for _ in range(n)]
    mats = []
    for w in subint_weights:
        A = am.weight_matrix(J, w, tilt=set(E), z=z)
        mats.append(A)
        for i in range(n):
            for j in range(n):
                if A[i][j] > Amax[i][j]:
                    Amax[i][j] = A[i][j]
    rho_f, v = perron(_to_float(Amax))
    h = [Fraction(round(x * h_scale), h_scale) for x in v]
    h = [x if x > 0 else Fraction(1, h_scale) for x in h]
    # exact R = max over subintervals and rows
    R = Fraction(0)
    for A in mats:
        for i in range(n):
            num = sum(A[i][j] * h[j] for j in range(n))
            r = num / h[i]
            if r > R:
                R = r
    return h, R, rho_f


def lambda_subintervals(lam_lo: Fraction, lam_hi: Fraction, pieces: int):
    """Certified upper weights on each of `pieces` equal subintervals."""
    out = []
    for i in range(pieces):
        a = lam_lo + (lam_hi - lam_lo) * i / pieces
        b = lam_lo + (lam_hi - lam_lo) * (i + 1) / pieces
        enc = ew.weight_enclosures(a, b)
        out.append({'p': enc['p_hi'], 'q2': enc['q2_hi'], 'q8': enc['q8_hi']})
    return out


def theta_star(J, E, lam_lo, lam_hi, pieces=8,
               zgrid=(Fraction(11, 10), Fraction(5, 4), Fraction(3, 2),
                      Fraction(2), Fraction(3), Fraction(5), Fraction(8),
                      Fraction(16), Fraction(64))):
    """Scan z-grid; for each z produce an exactly-verified (h,R); report
    theta_req(z) = ln R / ln z and the best (certified) theta*.
    Returns list of rows and the argmin row."""
    subw = lambda_subintervals(lam_lo, lam_hi, pieces)
    rows = []
    for z in zgrid:
        h, R, rho_f = certify_h(J, subw, E, z)
        th = math.log(float(R)) / math.log(float(z)) if R > 1 else 0.0
        rows.append({'J': J, 'z': z, 'R': R, 'R_float': float(R),
                     'theta_req': th, 'h': h})
    best = min(rows, key=lambda r: r['theta_req'])
    return rows, best


def exact_gap_check(R: Fraction, z: Fraction, theta: Fraction):
    """Exact check of (2.10): R * z^-theta < 1  <=>  R^den < z^num (theta=num/den)."""
    num, den = theta.numerator, theta.denominator
    return R.numerator ** den * z.denominator ** num < \
           R.denominator ** den * z.numerator ** num


# ------------------------------------------------------------ diagnostics

def spectral_radius(J, w, tilt=None, z=Fraction(1)):
    A = am.weight_matrix(J, w, tilt=set(tilt) if tilt else None, z=z)
    rho, _ = perron(_to_float(A))
    return rho


def offE_radius(J, w, E):
    """Perron radius of the automaton restricted to the complement of E."""
    S = am.states(J)
    keep = [i for i, q in enumerate(S) if q not in E]
    A = am.weight_matrix(J, w)
    sub = [[float(A[i][j]) for j in keep] for i in keep]
    rho, _ = perron(sub)
    return rho

def first_return_sum(J, w, E):
    """sum_n a_n: total weight of first-return loops E->E (renewal series,
    sol-pressure 4.4B).  = Perron radius of  W_EE + W_EC (I-W_CC)^-1 W_CE,
    valid when rho(W_CC) < 1.  Float diagnostic (decision support only)."""
    S = am.states(J)
    iE = [i for i, q in enumerate(S) if q in E]
    iC = [i for i, q in enumerate(S) if q not in E]
    import numpy as np
    A = np.array(_to_float(am.weight_matrix(J, w)))
    nC = len(iC)
    rho_cc = 0.0
    if nC:
        Acc = A[np.ix_(iC, iC)]
        rho_cc, _ = perron(Acc.tolist())
        if rho_cc >= 1:
            return None, rho_cc
        X = np.linalg.solve(np.eye(nC) - Acc, A[np.ix_(iC, iE)])
        ret = A[np.ix_(iE, iE)] + A[np.ix_(iE, iC)] @ X
    else:
        ret = A[np.ix_(iE, iE)]
    rho, _ = perron(ret.tolist())
    return rho, rho_cc


def weights_at(lam: Fraction):
    enc = ew.weight_enclosures(lam, lam)
    return {'p': enc['p_hi'], 'q2': enc['q2_hi'], 'q8': enc['q8_hi']}


if __name__ == '__main__':
    from exact_weights import LAM18
    for J in (2, 3):
        E = am.exceptional_set(J)
        w2 = weights_at(Fraction(2))
        w18 = weights_at(LAM18)
        print(f'J={J} E={E}')
        print('  rho(W) at lam=2   :', spectral_radius(J, w2),
              ' s(2)=', ew.s_annealed(2.0))
        print('  rho(W) at lam18   :', spectral_radius(J, w18),
              ' s(lam18)=', ew.s_annealed(float(LAM18)))
        print('  offE rho, lam=2   :', offE_radius(J, w2, E))
        print('  first-return sum lam=2:', first_return_sum(J, w2, E))
