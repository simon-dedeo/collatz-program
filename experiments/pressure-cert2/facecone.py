"""facecone.py -- spine-face cone analysis of the aligned core (option (a)).

For strictly aligned windows (all digits in {0,3}; contains the -1 spine
u=.333333 and the +0 face u=.000000) the block support is diag(S={0}) union
affine classes A.  When |A|=1 the affine perm j->a+2j pins lift j0=-a and
couples the other two: the 2x2 face matrix is positive.  We compute, exactly:
  * how many aligned windows have |A|=1 (clean face) vs |A|=2 (7/8-support);
  * worst face Birkhoff ratio X_face and tau_face (2-dim cone) at lambda=2;
  * the pinned-scale multiplier interval [mu_lo, mu_hi] (marginality check:
    does it contain 1 -- the renormalization's chain-scale eigenvalue-1 mode).
Cone hypothesis K enters through the D-interval [3/(2K+1), 1].
"""
from fractions import Fraction
import csv

import combined as cb
from blocks import tau_upper


def face_data(phase, D, enc, K):
    terms = cb.block_terms(phase, D)
    A = sorted({add for (kind, t, (add, mul)) in terms if mul == 2})
    S = sorted({add for (kind, t, (add, mul)) in terms if mul == 1})
    if S != [0] or len(A) != 1:
        return None
    a = A[0]
    j0 = (-a) % 3                        # pinned lift
    face = [j for j in range(3) if j != j0]
    d_lo = Fraction(3, 2 * K + 1)
    lo = [[Fraction(0)] * 3 for _ in range(3)]
    hi = [[Fraction(0)] * 3 for _ in range(3)]
    for (kind, t, (add, mul)) in terms:
        if kind == 'tail':
            c_lo = c_hi = enc['p_lo'] ** t
            dl = dh = Fraction(1)
        else:
            q_lo, q_hi = (enc['q2_lo'], enc['q2_hi']) if kind == 'B2' \
                else (enc['q8_lo'], enc['q8_hi'])
            c_lo, c_hi = enc['p_lo'] ** t * q_lo, enc['p_hi'] ** t * q_hi
            dl, dh = d_lo, Fraction(1)
        for j in range(3):
            col = (add + mul * j) % 3
            lo[j][col] += c_lo * dl
            hi[j][col] += c_hi * dh
    i, j = face
    a11l, a12l, a21l, a22l = lo[i][i], lo[i][j], lo[j][i], lo[j][j]
    a11h, a12h, a21h, a22h = hi[i][i], hi[i][j], hi[j][i], hi[j][j]
    assert min(a11l, a12l, a21l, a22l) > 0
    X_face = max(a11h * a22h / (a12l * a21l), a12h * a21h / (a11l * a22l))
    # pinned-scale multiplier vs face mean
    row_p_lo, row_p_hi = sum(lo[j0]), sum(hi[j0])
    frow_lo = min(sum(lo[i]), sum(lo[j]))
    frow_hi = max(sum(hi[i]), sum(hi[j]))
    return X_face, row_p_lo / frow_hi, row_p_hi / frow_lo, j0


def main():
    K = 2
    rows = []
    for phase in cb.PHASES:
        n1 = n2 = 0
        Xmax = Fraction(0)
        mu_lo, mu_hi = Fraction(10 ** 9), Fraction(0)
        for D in cb.windows():
            if not all(d in (0, 3) for d in D):
                continue
            fd = face_data(phase, D, cb.W2, K)
            if fd is None:
                n2 += 1
                continue
            n1 += 1
            X, ml, mh, j0 = fd
            Xmax = max(Xmax, X)
            mu_lo, mu_hi = min(mu_lo, ml), max(mu_hi, mh)
        tf = tau_upper(Xmax) if n1 else None
        rows.append({'phase': phase, 'K': K, 'aligned_total': n1 + n2,
                     'clean_face': n1, 'mixed_A': n2,
                     'X_face_max': str(Xmax),
                     'tau_face': float(tf) if tf else float('nan'),
                     'mu_lo': float(mu_lo), 'mu_hi': float(mu_hi),
                     'marginal_1_in_mu': bool(mu_lo <= 1 <= mu_hi)})
        print(rows[-1])
    with open('/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2/facecone.csv',
              'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        [w.writerow(r) for r in rows]
    print('wrote facecone.csv')


if __name__ == '__main__':
    main()
