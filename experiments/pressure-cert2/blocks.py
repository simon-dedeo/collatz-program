"""blocks.py -- per-(phase, window) block contraction data at (J=3, L_w=6).

For each covered window: exact interval 3x3 block matrix (single-profile
envelope; D-interval [3/(2K+1),1] from the HYPOTHESIS cone C_K), Birkhoff
X = sup cross-ratio (exact Fraction), tau <= (sqrt(X)-1)/(sqrt(X)+1) with a
certified rational upper bound via integer sqrt.  Also: C_row (envelope row
normalization), zero-row check (projective nonexpansiveness of every block).
Two weight regimes: lambda=2 exact; uniform [lam18, 2] enclosures.
K degradation curve: K in {2,4,8,16} quantifies the no-global-cone caveat.
"""
import csv
import math
from fractions import Fraction

import combined as cb


def sqrt_upper(X: Fraction, iters=40):
    """Rational s >= sqrt(X), certified: s*s >= X by exact comparison."""
    s = Fraction(math.isqrt(X.numerator // X.denominator + 1) + 1)
    for _ in range(iters):
        s2 = (s + X / s) / 2          # Newton from above stays above sqrt
        s2 = Fraction(s2.numerator, s2.denominator).limit_denominator(10 ** 12)
        if s2 * s2 >= X and s2 < s:
            s = s2
        else:
            break
    assert s * s >= X
    return s


def tau_upper(X: Fraction):
    s = sqrt_upper(X)
    return (s - 1) / (s + 1)


def scan(enc, K, tag):
    rows = []
    for phase in cb.PHASES:
        ncov = 0
        Xmax = Fraction(0)
        Cmax = Fraction(0)
        allnzr = True
        for D in cb.windows():
            cov, X, tau, C_row, nzr = cb.block_data(phase, D, enc, K)
            allnzr &= nzr
            Cmax = max(Cmax, C_row)
            if cov:
                ncov += 1
                Xmax = max(Xmax, X)
        tu = tau_upper(Xmax) if ncov else None
        rows.append({'tag': tag, 'phase': phase, 'K': K,
                     'covered': ncov, 'total': 4 ** cb.LW,
                     'cov_frac': ncov / 4 ** cb.LW,
                     'X_max': str(Xmax), 'tau_upper': str(tu) if tu else '',
                     'tau_float': float(tu) if tu else float('nan'),
                     'C_row_max': str(Cmax), 'C_row_float': float(Cmax),
                     'no_zero_rows': allnzr})
        print(rows[-1]['tag'], 'phase', phase, 'K', K,
              f"cov={ncov}/{4**cb.LW}", f"tau={rows[-1]['tau_float']:.9f}",
              f"C_row={float(Cmax):.6f}", 'nzr', allnzr)
    return rows


if __name__ == '__main__':
    rows = []
    encU = cb.enc_uniform()
    for K in (2, 4, 8, 16):
        rows += scan(cb.W2, K, 'lam2')
    rows += scan(encU, 2, 'uniform[lam18,2]')
    with open('/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2/blocks_tau.csv',
              'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        [w.writerow(r) for r in rows]
    print('wrote blocks_tau.csv')
