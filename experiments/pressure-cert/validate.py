"""validate.py -- cross-checks of the automaton against certified data.

V1  Brute-force verification of sol-contraction Lemma 1 index arithmetic at
    small k (pure integers): transport label shift, R2/R8 lift alignment,
    the exact facts floor((4r-2)/3^N)=floor(4r/3^N), floor((2r-1)/3^N)=
    floor(2r/3^N), and the u-cell shift rules used by lemma3.py.
V2  EXACT ball-mass domination on certified eigenvectors (int64 C arrays,
    k=15,16):  M(xi) <= p M(4xi) + q_e * S_e(xi)  and  S_e <= (1/3) sum M(fine)
    -- Fractions, no floats.  Failure would falsify the automaton.
V3  Empirical exceptional-neighborhood masses nu_k(E_J) for k=15..19 (float,
    memmapped), vs the annealed stationary pi(E_J): sol-pressure 4.4D.
V4  Cone parameter: empirical max over fibers of (fiber max/min) -> K.
"""

from fractions import Fraction
import numpy as np

import automaton as am
import exact_weights as ew

KL = '/Users/simon/Desktop/COLLATZ/experiments/kl'


# ------------------------------------------------------------------ V1

def v1_index_arithmetic(k=7, verbose=True):
    N = k - 1
    Q, Qp = 3 ** N, 3 ** (N - 1)
    ok = True
    for r in range(2, Q, 3):
        # transport: 4(r + jQ) mod 3^k = (4r mod Q) + (h+j)Q with h = floor(4r/Q)
        h = (4 * r) // Q
        for j in range(3):
            lhs = (4 * (r + j * Q)) % (3 * Q)
            rhs = (4 * r) % Q + ((h + j) % 3) * Q
            ok &= lhs == rhs
        if r % 9 == 2:
            z = (4 * r - 2) // 3
            hp = z // Qp
            assert hp == (4 * r) // Q  # floor((4r-2)/3^N) = floor(4r/3^N)
            for j in range(3):
                lhs = ((4 * (r + j * Q) - 2) // 3) % Q
                rhs = z % Qp + ((hp + j) % 3) * Qp
                ok &= lhs == rhs
        if r % 9 == 8:
            z = (2 * r - 1) // 3
            hp = z // Qp
            assert hp == (2 * r) // Q  # floor((2r-1)/3^N) = floor(2r/3^N)
            for j in range(3):
                lhs = ((2 * (r + j * Q) - 1) // 3) % Q
                rhs = z % Qp + ((hp + 2 * j) % 3) * Qp
                ok &= lhs == rhs
    if verbose:
        print(f'V1 k={k}: transport j->h+j, R2 j->h\'+j, R8 j->h\'+2j,'
              f' floor identities: {"PASS" if ok else "FAIL"}')
    return ok


# ------------------------------------------------------------------ V2

def _ball_masses(C, k, J):
    """Exact integer ball masses M(xi), xi in Q_J.  C int64 array, index
    i <-> m = 2+3i;  ball xi <-> i == (xi-2)/3 mod 3^(J-1)."""
    n = 3 ** (J - 1)
    M = {}
    idx = np.arange(C.shape[0], dtype=np.int64) % n
    for b in range(n):
        sel = C[idx == b]
        # chunked exact sum (avoid int64 overflow)
        tot = 0
        for c in range(0, sel.shape[0], 5000):
            tot += int(np.sum(sel[c:c + 5000], dtype=np.int64))
        M[2 + 3 * b] = tot
    return M


def _min_sums(C, k, J):
    """S_e per coarse ball: sum over level-(k-1) states r == rho mod 3^(J-1)
    of min_j C[r + j*3^(k-1)].  Exact ints."""
    nr = 3 ** (k - 2)              # number of level-(k-1) states
    third = 3 ** (k - 2)           # index stride of lifts: i = i_r + j*3^(k-2)
    mins = np.minimum(np.minimum(C[:third], C[third:2 * third]),
                      C[2 * third:])
    n = 3 ** (J - 2)               # coarse balls mod 3^(J-1): i_r mod 3^(J-2)
    idx = np.arange(third, dtype=np.int64) % n
    S = {}
    for b in range(n):
        sel = mins[idx == b]
        tot = 0
        for c in range(0, sel.shape[0], 5000):
            tot += int(np.sum(sel[c:c + 5000], dtype=np.int64))
        S[2 + 3 * b] = tot         # coarse ball residue mod 3^(J-1)
    return S


def v2_ball_domination(k, J, verbose=True):
    """Exact check on cert_k{k}_C.npy at lambda_k (from cert json)."""
    import json
    C = np.load(f'{KL}/cert_k{k}_C.npy')
    cert = json.load(open(f'{KL}/cert_k{k}.json'))
    lam = Fraction(cert['A'], cert['SC_L'])
    # exact upper bounds for the true weights at lambda_k
    p = lam ** -2
    q2 = ew.rat_pow_bound(lam, ew.ALPHA_HI - 2, 'upper')
    q8 = ew.rat_pow_bound(lam, ew.ALPHA_HI - 1, 'upper')
    M = _ball_masses(C, k, J)
    S = _min_sums(C, k, J)
    mod, modc = 3 ** J, 3 ** (J - 1)
    ok_sharp = ok_mean = True
    min_slack = None
    for xi in am.states(J):
        rhs = p * M[(4 * xi) % mod]
        kind, tg = am.branch_targets(xi, J)
        if kind:
            rho = ((4 * xi - 2) // 3) % modc if kind == 'B2' else \
                  ((2 * xi - 1) // 3) % modc
            q = q2 if kind == 'B2' else q8
            rhs_sharp = rhs + q * S[rho]
            rhs_mean = rhs + q * Fraction(sum(M[t] for t in tg), 3)
            ok_mean &= Fraction(M[xi]) <= rhs_mean
            # S_e <= (1/3) sum fine masses (min<=mean, exact)
            ok_mean &= 3 * S[rho] <= sum(M[t] for t in tg)
        else:
            rhs_sharp = rhs_mean = rhs
        ok_sharp &= Fraction(M[xi]) <= rhs_sharp
        sl = float(1 - Fraction(M[xi]) / rhs_sharp)
        min_slack = sl if min_slack is None else min(min_slack, sl)
    if verbose:
        print(f'V2 k={k} J={J}: sharp M<=pM4+qS: {"PASS" if ok_sharp else "FAIL"};'
              f' mean-dominated (automaton) : {"PASS" if ok_mean else "FAIL"};'
              f' min rel slack sharp = {min_slack:.3e}')
    return ok_sharp, ok_mean, min_slack


# ------------------------------------------------------------------ V3

def v3_empirical_E_mass(ks=(15, 16, 17, 18, 19), Js=(3, 4, 5, 6, 7, 8),
                        verbose=True):
    rows = []
    for k in ks:
        path = f'{KL}/eigvec_k{k}.npy'
        v = np.load(path, mmap_mode='r')
        nmax = 3 ** (max(Js) - 1)
        acc = np.zeros(nmax)
        tot = 0.0
        nstates = v.shape[0]
        for c in range(0, nstates, 10 ** 7):
            ch = np.asarray(v[c:c + 10 ** 7], dtype=np.float64)
            idx = (np.arange(c, c + ch.shape[0], dtype=np.int64)) % nmax
            acc += np.bincount(idx, weights=ch, minlength=nmax)
            tot += ch.sum()
        for J in Js:
            n = 3 ** (J - 1)
            # acc indexed by i mod nmax; ball index for J is i mod n: fold
            ballm = np.zeros(n)
            for b in range(0, nmax, n):
                ballm += acc[b:b + n]
            E = am.exceptional_set(J)
            nu = sum(ballm[(q - 2) // 3 % n] for q in E) / tot
            rows.append({'k': k, 'J': J, 'nu_E': nu})
            if verbose:
                print(f'V3 k={k} J={J}: nu_k(E_J) = {nu:.6f}')
    return rows


# ------------------------------------------------------------------ V4

def v4_cone_K(ks=(15, 16), verbose=True):
    out = {}
    for k in ks:
        v = np.load(f'{KL}/eigvec_k{k}.npy', mmap_mode='r')
        third = 3 ** (k - 2)
        a = np.asarray(v[:third]); b = np.asarray(v[third:2 * third])
        c = np.asarray(v[2 * third:])
        mx = np.maximum(np.maximum(a, b), c)
        mn = np.minimum(np.minimum(a, b), c)
        K = float((mx / mn).max())
        out[k] = K
        if verbose:
            print(f'V4 k={k}: max fiber max/min = {K:.4f}')
    return out


if __name__ == '__main__':
    v1_index_arithmetic(7)
    v1_index_arithmetic(8)
    for k in (15, 16):
        for J in (2, 3):
            v2_ball_domination(k, J)
    v4_cone_K()
    v3_empirical_E_mass(ks=(15, 16))
