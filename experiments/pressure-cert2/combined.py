"""combined.py -- combined automaton: (ball mod 3^J) x (top u-window, L_w base-4 digits).

Exceptional set is DEPTH-MEMORY (window-defined), not static residue: the
<4>-orbit of -1 fills Q_J, so residue-based E_J is vacuous.  Here a combined
state is exceptional iff its L_w-digit top window is UNCOVERED (block support
< full), which is exactly the label-alignment obstruction class; it contains
the -1 spine (all digits 3) and the +0 face (all digits 0).

Window semantics: u = m/3^k in [0,1); digits d_1..d_Lw = first base-4 digits.
Shift data of an L-step transport block from phase = q mod 9 (in {2,5,8}):
  transport overflow at step t:  h_t = d_{t+1} mod 3
  B2 event (phase 2) at t:       add = (hsum_t + d_{t+1}) mod 3, mul 1
  B8 event (phase 8) at t:       add = ([d_{t+1}>=2] + 2*hsum_t) mod 3, mul 2
  tail: add = hsum_L, mul 1;  hsum_t = sum_{s<=t} d_s mod 3.
(floor identities floor((4r-2)/3^N)=floor(4r/3^N), floor((2r-1)/3^N)=
floor(2r/3^N) proved in pressure-cert; re-verified in validate2.py.)

Coverage rule (exact, verified against matrices in validate2.py):
support = union of shift-classes S (tail+B2 adds) and affine-classes A (B8
adds); |support| = 3|S|+3|A|-|S||A|; full (=9) iff |S|=3 or |A|=3.

Mass-automaton transitions (annealed u-split model; per-edge weights are
certified upper bounds; the u-split hypothesis U(sigma) is measured in
validate2.py and split_ratio_audit.py, NOT proved; its proposed universal
depth-nine `sigma <= 21/50` form is refuted by the exact k=19 feasible vector):
  T : (q,D) -> (4q, D[1:]+(e,))            e in 0..3, weight p/4
  B2: (q,D) -> (R2(q)+i*3^(J-1), D[1:]+(e,)) i,e -> weight (q2/3)/4
  B8: (q,D) -> (R8(q)+i*3^(J-1), x2(D,c))  i in 0..2, c in 0,1, w (q8/3)/2
x2 digit map: e_i = 2 d_i mod 4 + [d_{i+1}>=2] (i<Lw), e_Lw = 2 d_Lw mod 4 + c.
Borrow corrections (-2*3^-k, -3^-k) are k-boundary effects of Haar measure
O(3^-k 4^Lw): excluded from the annealed matrix, measured in validate2.py T1/T2.
"""
import sys
from fractions import Fraction
import math

sys.path.insert(0, '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert')
import exact_weights as ew                       # noqa: E402
from lemma3 import block_matrix, birkhoff        # noqa: E402

J, LW = 3, 6
MOD, MODC = 3 ** J, 3 ** (J - 1)
PHASES = (2, 5, 8)

# exact rational weights at lambda=2 (2^alpha = 3 exactly)
W2 = {'p_lo': Fraction(1, 4), 'p_hi': Fraction(1, 4),
      'q2_lo': Fraction(3, 4), 'q2_hi': Fraction(3, 4),
      'q8_lo': Fraction(3, 2), 'q8_hi': Fraction(3, 2)}


def enc_uniform(lam_lo=ew.LAM18, lam_hi=Fraction(2)):
    return ew.weight_enclosures(lam_lo, lam_hi)


def balls():
    return [q for q in range(2, MOD, 3)]


def windows(Lw=LW):
    if Lw == 0:
        yield ()
        return
    for d in range(4 ** Lw):
        yield tuple((d >> (2 * (Lw - 1 - i))) & 3 for i in range(Lw))


def widx(D):
    x = 0
    for d in D:
        x = 4 * x + d
    return x


def block_terms(phase, digits):
    """Exact term list (kind, t, (add, mul)) for a block of len(digits) moves."""
    terms, hsum, ph = [], 0, phase
    for t, d in enumerate(digits):
        if ph == 2:
            terms.append(('B2', t, ((hsum + d) % 3, 1)))
        elif ph == 8:
            terms.append(('B8', t, (((1 if d >= 2 else 0) + 2 * hsum) % 3, 2)))
        hsum = (hsum + d) % 3
        ph = (ph * 4) % 9
    terms.append(('tail', len(digits), (hsum, 1)))
    return terms


def sa_classes(phase, digits):
    """(S, A): shift-classes from tail+B2 adds, affine-classes from B8 adds."""
    S, A = set(), set()
    for (kind, t, (add, mul)) in block_terms(phase, digits):
        (A if mul == 2 else S).add(add)
    return S, A


def covered(phase, digits):
    S, A = sa_classes(phase, digits)
    return len(S) == 3 or len(A) == 3


def block_data(phase, digits, enc, K):
    """(covered, X_exact, tau_float, C_row_exact, no_zero_row)."""
    lo, hi = block_matrix(block_terms(phase, digits), enc, K)
    cov, delta, tau, X, C_row = birkhoff(lo, hi)
    nzr = all(any(lo[i][j] > 0 for j in range(3)) for i in range(3))
    return cov, X, tau, C_row, nzr


# ---------------------------------------------------------------- transitions

def x2_window(D, c):
    e = tuple((2 * D[i]) % 4 + (1 if D[i + 1] >= 2 else 0)
              for i in range(len(D) - 1))
    return e + ((2 * D[-1]) % 4 + c,)


def shift_window(D, e):
    return D[1:] + (e,)


def transitions(q, D, w):
    """[(q', D', weight, kind)] annealed model.  w: dict p,q2,q8 Fractions."""
    out = []
    for e in range(4):
        out.append(((4 * q) % MOD, shift_window(D, e), w['p'] / 4, 'T'))
    m9 = q % 9
    if m9 == 2:
        z = ((4 * q - 2) // 3) % MODC
        for i in range(3):
            for e in range(4):
                out.append((z + i * MODC, shift_window(D, e),
                            w['q2'] / 12, 'B2'))
    elif m9 == 8:
        z = ((2 * q - 1) // 3) % MODC
        for i in range(3):
            for c in range(2):
                out.append((z + i * MODC, x2_window(D, c),
                            w['q8'] / 6, 'B8'))
    return out
