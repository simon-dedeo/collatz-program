"""scale_akdeniz.py -- obsolete scaled prototype (BLOCKED, NOT LAUNCHED).

Target: (J, L_w) with phase-8 coverage nonempty and worst-case u-split
closure: L_w >= 9.  Sizes: (3,9)=2.36M states (local overnight or 1 hr on
32 cores); (3,10)=9.4M; (6,10)=255M (akdeniz, sparse int-key edges, ~50 GB
if streamed by source-chunk; use L_w=10 only if (3,9) margins are thin).

The original launch estimate extrapolated a depth-6 split ratio to depth 9.
`split_ratio_audit.py` now checks the actual depth `9 -> 10` split on the
SHA-pinned feasible records.  Even on source-uncovered to T-successor-
uncovered transitions, k=19 has exact sigma_max = 0.5426010103..., above the
proposed 0.36--0.42 budget.  The pressure-closing scalar H1 premise therefore
lacks both proof and the claimed finite-scale evidence.  (A larger, non-closing
scalar bound is not at issue.)  H2 (the single-profile product-envelope
domination) also remains open.

Do not launch this pressure build as currently formulated.  A replacement
must retain the sibling mass vector or a state-dependent conditional cone;
otherwise another row certificate proves only the annealed surrogate.

Run (on akdeniz):  python3 scale_akdeniz.py J LW NPROC
Phases: 1) float Perron (numpy, sparse edge arrays, ~min)  2) h rounding
3) exact row verification, multiprocessing over source-state chunks, each
worker re-derives its rows from (J,LW) alone and returns max row ratio as a
Fraction; master takes exact max => R_unc / R tilted.  4) writes portable
JSON + h sidecar + sha256.  All load-bearing comparisons exact.
"""
import sys
from fractions import Fraction
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2')
import combined as cb


def configure(J, LW):
    cb.J, cb.LW = J, LW
    cb.MOD, cb.MODC = 3 ** J, 3 ** (J - 1)


def state_count(J, LW):
    return 3 ** (J - 1) * 4 ** LW


def worker(args):
    """Exact max row ratio over a chunk of unc source states."""
    J, LW, i0, i1, hpath, mode, zs = args
    configure(J, LW)
    h = np.load(hpath)                      # int64 numerators, common denom
    w = {'p': Fraction(1, 4), 'q2': Fraction(3, 4), 'q8': Fraction(3, 2)}
    z = Fraction(zs) if zs else None
    R = Fraction(0)
    nb = 3 ** (J - 1)
    for i in range(i0, i1):
        q = 2 + 3 * (i // 4 ** LW)
        Dx = i % 4 ** LW
        D = tuple((Dx >> (2 * (LW - 1 - t))) & 3 for t in range(LW))
        s_unc = not cb.covered(q % 9, D)
        if mode == 'restricted' and not s_unc:
            continue
        num = Fraction(0)
        for (q2, D2, weight, kind) in cb.transitions(q, D, w):
            j = ((q2 - 2) // 3) * 4 ** LW + cb.widx(D2)
            t_unc = not cb.covered(q2 % 9, D2)
            if mode == 'restricted':
                if t_unc:
                    num += weight * int(h[j])
            else:
                num += weight * int(h[j]) * (z if t_unc else 1)
        if num > 0:
            r = num / int(h[i])
            if r > R:
                R = r
    return (R.numerator, R.denominator)


def main(J, LW, nproc, mode='restricted', zs=None):
    configure(J, LW)
    n = state_count(J, LW)
    print(f'(J,LW)=({J},{LW}) states={n}')
    # --- float Perron on the (restricted) automaton, chunked matvec
    # (memory: edges regenerated per sweep; for n>1e7 use src-chunk streaming)
    raise SystemExit(
        'BLOCKED: required U(21/50) fails the exact depth-nine audit; '
        'replace the model'
    )


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]) if a else 3, int(a[1]) if len(a) > 1 else 9,
         int(a[2]) if len(a) > 2 else 32)
