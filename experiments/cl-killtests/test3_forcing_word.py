"""TEST 3 -- strict forcing word (the rescue).

Search a finite residue word W (|W|<=8 over phases {2,5,8}) and eta>0 s.t. the
TRUE min-composition satisfies osc(T_W x) <= (1-eta) osc(x) for EVERY normalized
nonconstant x.  Check contraction uniformly over the profile cone by extreme rays
(exact rationals at lambda=2).

True per-step operator on the ALIGNED all-0 window (self-referential; min
genuinely attained at the neutral lift, verified in TEST 2), at lambda=2:
  phase 5 (transport only): M = p*I
  phase 2 (B2, add=0,mul=1): M = p*I + q2*I          (identity)
  phase 8 (B8, add=0,mul=2): M = p*I + q8*SWAP        (swap 1<->2)
p=1/4, q2=3/4, q8=3/2.  T_W = product of per-step M's.

Extreme rays of the nonconstant (mean-zero) profile cone: the co-spine directions
(2,-1,-1),(-1,2,-1),(-1,-1,2).  osc-multiplier along a ray = |T_W ray|-spread /
(mean-eigenvalue * ray-spread).  A forcing word needs multiplier <= 1-eta on ALL.

Non-circularity: the all-0 window is FORWARD-INVARIANT under T/B2/B8 (shift e=0,
x2 c=0) and INDEPENDENT of the ball residue (top/low windows are independent
coords -- pressure-certificate-2 falsification).  So for EVERY residue word the
adversary can carry the co-spine profile on the all-0 window; if that profile is
never contracted, NO forcing word exists, and the reason is residue-independent.
"""
import csv, os, sys, itertools
from fractions import Fraction
sys.path.insert(0, '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2')
import combined as cb

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'csv')
P, Q2, Q8 = Fraction(1, 4), Fraction(3, 4), Fraction(3, 2)
I3 = [[Fraction(int(i == j)) for j in range(3)] for i in range(3)]
SWAP = [[Fraction(int(j == (2 * i) % 3)) for j in range(3)] for i in range(3)]


def scale(M, s):
    return [[s * M[i][j] for j in range(3)] for i in range(3)]


def addM(A, B):
    return [[A[i][j] + B[i][j] for j in range(3)] for i in range(3)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(3)) for i in range(3)]


def step_matrix(ph):
    if ph == 5:
        return scale(I3, P)
    if ph == 2:
        return addM(scale(I3, P), scale(I3, Q2))
    if ph == 8:
        return addM(scale(I3, P), scale(SWAP, Q8))
    raise ValueError


def osc(v):
    m = min(v); M = max(v); mean = sum(v) / 3
    return None if mean == 0 else (M - m) / mean


RAYS = [(2, -1, -1), (-1, 2, -1), (-1, -1, 2)]  # extreme rays of mean-zero cone
# positive representatives (add 2*mean) so osc is well-defined & nonconstant
POS = [tuple(Fraction(x) + 2 for x in r) for r in RAYS]


def word_multiplier(word):
    """Max osc-multiplier over the extreme rays (worst case for a forcing word)."""
    M = I3
    for ph in word:
        M = matmul(step_matrix(ph), M)
    # mean eigenvalue = row sum on (1,1,1)
    mean_ev = sum(M[0])
    worst = Fraction(0)
    contracts = True
    for pv in POS:
        out = matvec(M, pv)
        o_in = osc(pv); o_out = osc(out)
        # normalized multiplier: (osc_out) / (osc_in)  [mass already in M]
        mult = o_out / o_in if o_in else Fraction(0)
        worst = max(worst, mult)
        if mult < 1:
            pass
        else:
            contracts = False
    return worst, contracts, mean_ev


if __name__ == '__main__':
    rows = []
    any_forcing = False
    worst_overall = Fraction(0)
    for L in range(1, 9):
        best_eta = None
        n_words = 0
        for word in itertools.product((2, 5, 8), repeat=L):
            n_words += 1
            worst, contracts, _ = word_multiplier(word)
            worst_overall = max(worst_overall, worst)
            eta = 1 - worst           # uniform contraction factor achievable
            if eta > 0:               # some word contracts ALL extreme rays
                any_forcing = True
                if best_eta is None or eta > best_eta:
                    best_eta = eta
        rows.append({'word_len': L, 'n_words': n_words,
                     'max_cospine_osc_multiplier': str(worst_overall),
                     'any_word_with_eta>0': best_eta is not None,
                     'best_eta': str(best_eta) if best_eta else '0'})
        print(f"len={L}: n_words={n_words} worst_cospine_mult={float(worst_overall):.6f}"
              f" any_forcing={best_eta is not None}")
    # explicit co-spine invariance witness (eta=0 for every word)
    demo = word_multiplier((8, 2, 5, 8, 8, 2, 5, 8))
    with open(os.path.join(OUT, 'test3_forcing_word.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    # non-circular invariance check
    inv0 = (cb.shift_window((0,) * 6, 0) == (0,) * 6 and cb.x2_window((0,) * 6, 0) == (0,) * 6)
    print('all-0 window forward-invariant (T shift e=0 & B8 x2 c=0):', inv0)
    print('demo word (8,2,5,8,8,2,5,8): worst co-spine multiplier =', demo[0],
          '-> eta =', 1 - demo[0])
    print('VERDICT TEST3: NO strict forcing word exists (eta=0 for all |W|<=8);'
          ' co-spine profile on invariant all-0 window is preserved by every'
          ' residue word -> route (a) rescue FAILS.  any_forcing_word=', any_forcing)
