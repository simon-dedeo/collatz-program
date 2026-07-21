"""echarge.py -- tilted pressure on the combined automaton (J=3, L_w=6).

Charge field (depth-memory, not static residue): b(e) = 1 iff the TARGET
combined state's window is uncovered (dfa/combined coverage rule).
Model: annealed u-split (hypothesis U(sigma), measured in validate2.py).
Exact outputs:
  * ECH1: restricted certificate  sum_{e:q->q', q' unc} w_e h(q') <= R_unc h(q)
          over unc states only, R_unc < 1 exact  (pressure gap of the
          exceptional/aligned component; contains the -1 spine face).
  * ECH2: tilted certificate (h, z, R) on the full automaton with charge
          b(e), and rational theta = a/b with the exact integer gap R^b < z^a.
Everything load-bearing in Fractions; floats only propose h.
"""
import json
import math
from fractions import Fraction

import numpy as np

import combined as cb

HERE = '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2'


def build_states():
    S = []
    for q in cb.balls():
        for D in cb.windows():
            S.append((q, D))
    ix = {s: i for i, s in enumerate(S)}
    unc = np.array([not cb.covered(q % 9, D) for (q, D) in S])
    return S, ix, unc


def build_edges(S, ix, w):
    src, dst, wt = [], [], []
    for i, (q, D) in enumerate(S):
        for (q2, D2, weight, kind) in cb.transitions(q, D, w):
            src.append(i)
            dst.append(ix[(q2, D2)])
            wt.append(weight)
    return np.array(src), np.array(dst), wt


def perron(src, dst, wtf, n, mask=None, it=4000, tol=1e-12):
    keep = slice(None)
    if mask is not None:
        keepv = mask[src] & mask[dst]
        src, dst, wtf = src[keepv], dst[keepv], wtf[keepv]
    v = np.ones(n)
    rho = 1.0
    for _ in range(it):
        v2 = np.zeros(n)
        np.add.at(v2, src, wtf * v[dst])
        r2 = v2.max()
        if r2 == 0:
            return 0.0, v
        v2 /= r2
        if np.abs(v2 - v).max() < tol:
            return r2, v2
        v, rho = v2, r2
    return rho, v


def exact_R(S, ix, w, h, tilt_unc, z, restrict_unc, unc):
    """Exact max row ratio of the (tilted/restricted) operator against h."""
    R = Fraction(0)
    for i, (q, D) in enumerate(S):
        if restrict_unc and not unc[i]:
            continue
        num = Fraction(0)
        for (q2, D2, weight, kind) in cb.transitions(q, D, w):
            j = ix[(q2, D2)]
            if restrict_unc and not unc[j]:
                continue
            f = weight * h[j]
            if tilt_unc and unc[j]:
                f *= z
            num += f
        r = num / h[i]
        if r > R:
            R = r
    return R


def round_h(v, scale=10 ** 5):
    return [Fraction(max(round(x * scale), 1), scale) for x in v]


def main():
    w = {'p': Fraction(1, 4), 'q2': Fraction(3, 4), 'q8': Fraction(3, 2)}
    S, ix, unc = build_states()
    n = len(S)
    src, dst, wt = build_edges(S, ix, w)
    wtf = np.array([float(x) for x in wt])
    print(f'states={n} edges={len(src)} unc_frac={unc.mean():.6f}')

    # column sums (should be exactly 1 at lambda=2)
    col = np.zeros(n)
    np.add.at(col, dst, wtf)
    print(f'col sums: min={col.min():.12f} max={col.max():.12f}')

    rho, v = perron(src, dst, wtf, n)
    pi_unc = v[unc].sum() / v.sum()
    print(f'rho(full)={rho:.12f}  pi(unc)={pi_unc:.6f}')

    # ECH1: restricted radius on unc states
    rho_u, vu = perron(src, dst, wtf, n, mask=unc)
    print(f'rho(unc-restricted) float = {rho_u:.9f}')
    h_u = round_h(np.maximum(vu, 1e-8))
    R_unc = exact_R(S, ix, w, h_u, False, None, True, unc)
    print(f'R_unc exact = {R_unc} = {float(R_unc):.9f}  (<1: {R_unc < 1})')

    # ECH2: tilted full certificate
    out = {'ECH1': {'R_unc': str(R_unc), 'R_unc_float': float(R_unc),
                    'subcritical': bool(R_unc < 1),
                    'h_file': 'ech1_h.json'}}
    json.dump([[x.numerator, x.denominator] for x in h_u],
              open(f'{HERE}/ech1_h.json', 'w'))
    best = None
    for z in (Fraction(21, 20), Fraction(11, 10), Fraction(6, 5),
              Fraction(5, 4), Fraction(3, 2)):
        zf = float(z)
        wtz = wtf * np.where(unc[dst], zf, 1.0)
        rz, vz = perron(src, dst, wtz, n)
        th = math.log(rz) / math.log(zf)
        print(f'z={z}: rho_z(float)={rz:.9f} theta_req~{th:.6f}')
        if th < 1 and (best is None or th < best[1]):
            best = (z, th, vz)
    if best is None:
        print('NO tilt with theta_req < 1: mechanism fails at (3,6)')
        out['ECH2'] = {'feasible': False}
    else:
        z, th, vz = best
        h = round_h(np.maximum(vz, 1e-8))
        R = exact_R(S, ix, w, h, True, z, False, unc)
        thR = math.log(float(R)) / math.log(float(z))
        # rational theta = a/b in (thR, 1), close to thR + margin
        b = 64
        a = math.ceil(thR * b) + 1
        ok = (R.numerator ** b * z.denominator ** a <
              R.denominator ** b * z.numerator ** a) and a < b
        print(f'z={z} R={float(R):.9f} theta_req_exact~{thR:.6f} '
              f'theta={a}/{b} gap R^b<z^a: {ok}')
        json.dump([[x.numerator, x.denominator] for x in h],
                  open(f'{HERE}/ech2_h.json', 'w'))
        out['ECH2'] = {'feasible': True, 'z': str(z), 'R': str(R),
                       'R_float': float(R), 'theta_req_float': thR,
                       'a': a, 'b': b, 'gap_ok': bool(ok),
                       'h_file': 'ech2_h.json'}
    out['pi_unc_float'] = float(pi_unc)
    out['rho_full_float'] = float(rho)
    out['model'] = 'annealed u-split at lambda=2; exact weights 1/4,3/4,3/2'
    json.dump(out, open(f'{HERE}/echarge_results.json', 'w'), indent=1)
    print('wrote echarge_results.json')


if __name__ == '__main__':
    main()
