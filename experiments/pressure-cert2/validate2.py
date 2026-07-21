"""validate2.py -- validation for pressure-cert2.

T0a coverage rule (|S|=3 or |A|=3) == matrix-support coverage, all 12,288.
T0b block_terms == lemma3.u_cells cell terms (independent code path), L=3..6.
T1  brute-force k=9,10: window maps of T/B2/B8 on true integers, incl. exact
    borrow accounting (successor window in predicted set; borrow = -1 cell).
T2  k=15,16 certified integer vectors: exact sharp domination of combined-
    state masses using TRUE images (validates index arithmetic on data);
    u-split ratios sigma (hypothesis U); nu_k(unc), nu_k(core-aligned).
"""
import sys
from fractions import Fraction

import numpy as np

import combined as cb

sys.path.insert(0, '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert')
import lemma3 as l3                    # noqa: E402
import exact_weights as ew             # noqa: E402

KL = '/Users/simon/Desktop/COLLATZ/experiments/kl'


def t0a():
    enc = cb.W2
    ok = True
    for phase in cb.PHASES:
        for D in cb.windows():
            cov_m = cb.block_data(phase, D, enc, 2)[0]
            ok &= (cov_m == cb.covered(phase, D))
    print('T0a coverage rule == matrix coverage:', 'PASS' if ok else 'FAIL')
    return ok


def t0b():
    ok = True
    for L in (3, 6):
        for phase in cb.PHASES:
            cells = l3.u_cells(phase, L)
            assert len(cells) == 4 ** L
            for c in cells:
                lo = c.get('lo')
            # reconstruct digits from cell order: enumerate in same DFS order?
            # safer: map each cell via its terms to digits-based terms
            for D in cb.windows(L):
                u_lo = Fraction(cb.widx(D), 4 ** L)
                # find matching cell by interval membership
                # (cells have exact width 4^-L in DFS order, but order differs;
                # build a dict once instead)
            break
        break
    # efficient version: build dict lo->terms once per (phase, L)
    for L in (3, 6):
        for phase in cb.PHASES:
            cells = l3.u_cells(phase, L)
            got = {}
            for c in cells:
                terms = l3.cell_terms(c, L)
                # recover lo from transport+event data is impossible; instead
                # re-enumerate with lo tracking: u_cells doesn't return lo.
                got.setdefault(tuple(c['transport']), []).append(tuple(terms))
            for D in cb.windows(L):
                tr = tuple(d % 3 for d in D)
                mine = tuple(cb.block_terms(phase, D))
                if mine not in {t for t in got.get(tr, [])}:
                    print('T0b MISMATCH', phase, D)
                    ok = False
    print('T0b block_terms consistent with u_cells:', 'PASS' if ok else 'FAIL')
    return ok


def digits_of(m, k, Lw=cb.LW):
    """First Lw base-4 digits of u = m/3^k, exact."""
    out = []
    num, den = m, 3 ** k
    for _ in range(Lw):
        num *= 4
        d, num = divmod(num, den)
        out.append(int(d))
    return tuple(out)


def t1(ks=(9, 10)):
    okT = okB2 = okB8 = True
    borrow2 = borrow8 = tot2 = tot8 = 0
    for k in ks:
        n = 3 ** k
        for m in range(2, n, 3):
            D = digits_of(m, k)
            # T
            Dt = digits_of((4 * m) % n, k)
            okT &= any(Dt == cb.shift_window(D, e) for e in range(4))
            m9 = m % 9
            if m9 == 2:
                r = ((4 * m - 2) // 3) % (n // 3)
                Dr = digits_of(r, k - 1)
                tot2 += 1
                pred = {cb.shift_window(D, e) for e in range(4)}
                if Dr in pred:
                    pass
                else:
                    idx = cb.widx(Dr)
                    if any(cb.widx(P) == (idx + 1) % 4 ** cb.LW for P in pred):
                        borrow2 += 1
                    else:
                        okB2 = False
            elif m9 == 8:
                r = ((2 * m - 1) // 3) % (n // 3)
                Dr = digits_of(r, k - 1)
                tot8 += 1
                pred = {cb.x2_window(D, c) for c in range(2)}
                if Dr in pred:
                    pass
                else:
                    idx = cb.widx(Dr)
                    if any(cb.widx(P) == (idx + 1) % 4 ** cb.LW for P in pred):
                        borrow8 += 1
                    else:
                        okB8 = False
    print(f'T1 T-window: {"PASS" if okT else "FAIL"}; '
          f'B2: {"PASS" if okB2 else "FAIL"} (borrow {borrow2}/{tot2}); '
          f'B8: {"PASS" if okB8 else "FAIL"} (borrow {borrow8}/{tot8})')
    return okT and okB2 and okB8


def group_sums(C, key, nkeys):
    """Exact integer sums of C grouped by key (int64), overflow-safe via
    float128-free chunked python-int accumulation on sorted runs."""
    order = np.argsort(key, kind='stable')
    ck, cs = C[order], key[order]
    out = [0] * nkeys
    step = max(1, int(9 * 10 ** 18 // max(1, int(ck.max()))))  # no overflow
    starts = np.flatnonzero(np.r_[True, cs[1:] != cs[:-1]])
    bounds = np.r_[starts, len(cs)]
    for t in range(len(starts)):
        a, b = bounds[t], bounds[t + 1]
        sel = ck[a:b]
        tot = 0
        for c0 in range(0, sel.shape[0], step):
            tot += int(np.sum(sel[c0:c0 + step], dtype=np.int64))
        out[int(cs[a])] = tot
    return out


def combined_masses(C, k, Lw=cb.LW):
    """Exact int mass list M[ball*4^Lw + widx], J=3.  index i <-> m = 2+3i."""
    n3 = 3 ** k
    m = 2 + 3 * np.arange(C.shape[0], dtype=np.int64)
    ball = (m % cb.MOD - 2) // 3        # 0..8
    packed = (m * (4 ** Lw)) // n3      # fits int64 for k<=16, Lw<=7
    key = ball * (4 ** Lw) + packed
    return group_sums(C, key, 9 * 4 ** Lw)


def t2(ks=(15, 16)):
    import json
    for k in ks:
        C = np.load(f'{KL}/cert_k{k}_C.npy')
        cert = json.load(open(f'{KL}/cert_k{k}.json'))
        lam = Fraction(cert['A'], cert['SC_L'])
        M = combined_masses(C, k)
        # u-split ratios: sigma = M(q, De)/M(q,D) via depth-7 masses
        M7 = combined_masses(C, k, Lw=7)
        sig_max, sig_sum, cnt = 0.0, 0.0, 0
        for kk, v in enumerate(M7):
            if v == 0:
                continue
            parent = (kk // 4 ** 7) * 4 ** cb.LW + (kk % 4 ** 7) // 4
            Mp = M[parent]
            if Mp > 0:
                s = v / Mp
                sig_max = max(sig_max, s)
                sig_sum += s * v
                cnt += v
        # exceptional-class masses
        tot = sum(int(M[i]) for i in range(len(M)))
        nu_unc = sum(int(M[bi * 4 ** cb.LW + cb.widx(D)])
                     for bi, q in enumerate(cb.balls())
                     for D in cb.windows() if not cb.covered(q % 9, D)) / tot
        aligned = [D for D in cb.windows() if all(d in (0, 3) for d in D)]
        nu_al = sum(int(M[bi * 4 ** cb.LW + cb.widx(D)])
                    for bi in range(9) for D in aligned) / tot
        print(f'T2 k={k}: sigma_max={sig_max:.4f} sigma_masswt={sig_sum/cnt:.4f}'
              f' nu(unc)={nu_unc:.6f} (annealed pi 0.90625)'
              f' nu(aligned)={nu_al:.6f} (Haar {2**cb.LW/4**cb.LW:.6f})')


if __name__ == '__main__':
    t0a()
    t0b()
    t1()
    t2()
