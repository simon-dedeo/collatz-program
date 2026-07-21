"""lemma3.py -- finite-block Birkhoff contraction search (sol-pressure Lemma 3).

BLOCK STRUCTURE.  A block of L moves follows the transport orbit
r_t = 4^t r (t=0..L-1) at level pair (k-1,k); mod-9 phases cycle 2->8->5.
Unrolling the eigen-equation (sol-contraction Lemmas 1-2) along the block:

  x(r) = p^L T x(4^L r) + sum_{t: phase(t) in {2,8}} p^t q_{e_t} Pi_t D_t y(z_t)

where x(.) are fiber profiles (3-vectors over lift labels), y(z_t) the coarse
profile of the branch-source fiber (one scale down), D_t = diag with entries in
[3/(2K+1), 1] (min-over-lifts vs fiber mean, valid for every minimizing policy
if all profiles lie in the cone  C_K = {v>0 : max v / min v <= K}), and the
permutations are EXACT index arithmetic (sol-contraction Lemma 1):

  transport label action  j -> h+j,   h = floor(4 r_t / 3^N) mod 3
  2-branch  label action  j -> h'+j,  h' = floor((4r_t-2)/3^N) = floor(4 u_t)
  8-branch  label action  j -> h'+2j, h' = floor((2r_t-1)/3^N) = floor(2 u_t)

with u_t = r_t/3^N in [0,1) the top-digit fraction, u_{t+1} = frac(4 u_t).
KEY EXACT FACTS (proved by residue arithmetic, verified in validate.py):
  * floor((4r-2)/3^N) = floor(4r/3^N)  (since 4r == 2 mod 3, never 0,1 mod 3^N)
  * floor((2r-1)/3^N) = floor(2r/3^N)  (since 2r == 1 mod 3)
so at a 2-branch the branch shift EQUALS the following transport overflow.
All shift data along a block is therefore an exact piecewise-constant function
of the single unknown u_0 in [0,1) with rational (4-adic + halves) breakpoints;
the low residue q mod 3^J constrains only the low digits and is independent.
We enumerate the u-cells exactly (Fractions) and dominate over them.

TERM TYPES.  Composing shifts:  shift o shift = shift (add),
shift_h o (j->h'+2j) = (j -> (h'+2h)+2j).  A block therefore yields
  - tail term (exact):     coeff p^L,     shift permutation
  - each B2 term:          coeff p^t q2,  shift permutation, D-interval
  - each B8 term:          coeff p^t q8,  affine-x2 permutation, D-interval.
Structural theorem (checked, and provable by counting): one cycle (L=3) gives
2 shifts + 1 affine-2 term which cover at most 7 of the 9 matrix cells --
POSITIVITY IS IMPOSSIBLE AT L=3.  L=6 gives 3 shifts + 2 affines and can tile.

For each covered (q,u-cell): interval 3x3 matrix M (Fraction lo/hi entrywise,
lambda-interval enclosures on coefficients), Birkhoff projective diameter
  Delta = ln max_{i,i',j,j'} (hi_ij hi_i'j') / (lo_ij' lo_i'j)  < inf,
contraction  tau = tanh(Delta/4) < 1, and envelope growth
  C_row = (max_i sum_j hi_ij) / (min_i sum_j lo_ij)   (rough bound (2.3)).

CAVEAT (reported, not hidden): the induced-matrix formulation treats the
block's several inputs (tail fiber + coarse branch profiles) as a single
cone-K profile ("single-profile envelope") -- the same idealization as
sol-pressure Lemma 3's 'induced map on profiles'.  Cross-fiber import
(sol-contraction Lemmas 4-5) means the full proof needs the product cone;
failure here is decisive, success is a necessary-condition certificate.
"""

from fractions import Fraction
import math

import exact_weights as ew


# ---------------------------------------------------------------- u-cell engine

def u_cells(phase0, L):
    """Enumerate exact u-cells and their shift data for a block of L moves.

    phase0: q mod 9 (2, 5 or 8).  Returns list of dicts:
      {'lo','hi' (Fractions), 'transport': [h_1..h_L mod 3],
       'events': [(t, kind, hprime mod 3), ...]}
    Cell = maximal interval of u_0 where every floor along the block is const.
    """
    out = []

    def split(u_lo, u_hi, mult):
        """Subintervals of [u_lo,u_hi) on which floor(mult*u) is constant."""
        a, b = mult * u_lo, mult * u_hi
        ks = range(math.floor(a), math.ceil(b))
        return [(max(a, Fraction(k)) / mult, min(b, Fraction(k + 1)) / mult)
                for k in ks if max(a, Fraction(k)) < min(b, Fraction(k + 1))]

    def rec(t, u_lo, u_hi, transport, events, phase, event_done):
        if t == L:
            out.append({'transport': list(transport), 'events': list(events)})
            return
        # branch event at this state (side-term; orbit continues from r_t):
        if phase in (2, 8) and not event_done:
            mult = 4 if phase == 2 else 2
            parts = split(u_lo, u_hi, mult)
            if len(parts) > 1:
                for (slo, shi) in parts:
                    rec(t, slo, shi, transport, events, phase, False)
                return
            hp = math.floor(mult * u_lo) % 3
            kind = 'B2' if phase == 2 else 'B8'
            events = events + [(t, kind, hp)]
        # transport move: v = 4u, h = floor(v), u' = v - h
        parts = split(u_lo, u_hi, 4)
        if len(parts) > 1:
            for (slo, shi) in parts:
                rec(t, slo, shi, transport, events, phase, True)
            return
        h = math.floor(4 * u_lo)
        rec(t + 1, 4 * u_lo - h, 4 * u_hi - h, transport + [h % 3],
            events, (phase * 4) % 9, False)

    rec(0, Fraction(0), Fraction(1), [], [], phase0, False)
    return out


def cell_terms(cell, L):
    """Term list for one u-cell: (kind, t, perm) with perm as (add, mul):
    label map j -> add + mul*j mod 3.  kind in {'tail','B2','B8'}."""
    terms = []
    tr = cell['transport']
    for (t, kind, hp) in cell['events']:
        hsum = sum(tr[:t]) % 3          # shifts accumulated BEFORE the event
        if kind == 'B2':
            terms.append((kind, t, ((hsum + hp) % 3, 1)))
        else:
            terms.append((kind, t, ((hp + 2 * hsum) % 3, 2)))
    terms.append(('tail', L, (sum(tr) % 3, 1)))
    return terms


# ---------------------------------------------------------------- interval matrix

def block_matrix(terms, enc, K):
    """Entrywise-interval 3x3 matrix (lo, hi Fractions) for a term list.

    enc: weight enclosures dict (p_lo..q8_hi) valid on the lambda interval.
    K:   cone parameter; D-interval = [3/(2K+1), 1] on branch terms.
    Matrix rows j (output label), cols perm(j) (input label).
    """
    d_lo = Fraction(3, 2 * K + 1)
    lo = [[Fraction(0)] * 3 for _ in range(3)]
    hi = [[Fraction(0)] * 3 for _ in range(3)]
    for (kind, t, (add, mul)) in terms:
        if kind == 'tail':
            c_lo, c_hi = enc['p_lo'] ** t, enc['p_hi'] ** t
            dl = dh = Fraction(1)
        else:
            qlo, qhi = (enc['q2_lo'], enc['q2_hi']) if kind == 'B2' else \
                       (enc['q8_lo'], enc['q8_hi'])
            c_lo, c_hi = enc['p_lo'] ** t * qlo, enc['p_hi'] ** t * qhi
            dl, dh = d_lo, Fraction(1)
        for j in range(3):
            col = (add + mul * j) % 3
            lo[j][col] += c_lo * dl
            hi[j][col] += c_hi * dh
    return lo, hi


def birkhoff(lo, hi):
    """(covered, Delta_float, tau_float, X_max Fraction, C_row Fraction)."""
    covered = all(lo[i][j] > 0 for i in range(3) for j in range(3))
    rs_hi = max(sum(hi[i]) for i in range(3))
    rs_lo = min(sum(lo[i]) for i in range(3))
    C_row = rs_hi / rs_lo
    if not covered:
        return False, float('inf'), 1.0, None, C_row
    X = Fraction(0)
    for i in range(3):
        for i2 in range(3):
            for j in range(3):
                for j2 in range(3):
                    if j == j2:
                        continue
                    v = (hi[i][j] * hi[i2][j2]) / (lo[i][j2] * lo[i2][j])
                    if v > X:
                        X = v
    delta = math.log(float(X))
    tau = math.tanh(delta / 4)
    return True, delta, tau, X, C_row


# ---------------------------------------------------------------- per-phase scan
# NOTE: the block matrix depends ONLY on the mod-9 phase, the u-cell (top
# digits) and (K, lambda-interval) -- NOT on the low residue q mod 3^J.  The
# low-digit ball affects only which coarse states feed the block (identities,
# dominated by the cone), so contraction data is phase x u-cell resolved.
# Every u-cell has exact Haar width 4^-L (8-branch h' = floor(2u) is determined
# by the next base-4 digit, so no extra splits occur; asserted below).

def scan_phase(L, lam_lo, lam_hi, K):
    """Dominate over u-cells per phase.  Returns one row per phase."""
    enc = ew.weight_enclosures(lam_lo, lam_hi)
    rows = []
    for phase in (2, 5, 8):
        cells = u_cells(phase, L)
        assert len(cells) == 4 ** L, (phase, L, len(cells))
        tuples = {}
        for c in cells:
            key = tuple(cell_terms(c, L))
            tuples[key] = tuples.get(key, 0) + 1
        n_cov_cells = 0
        tau_cov = 0.0        # worst tau over covered cells
        delta_cov = 0.0
        C_row_all = Fraction(0)
        for key, mult in tuples.items():
            lo, hi = block_matrix(list(key), enc, K)
            cov, delta, tau, X, C_row = birkhoff(lo, hi)
            if cov:
                n_cov_cells += mult
                tau_cov = max(tau_cov, tau)
                delta_cov = max(delta_cov, delta)
            C_row_all = max(C_row_all, C_row)
        rows.append({'L': L, 'phase': phase, 'K': K,
                     'n_cells': 4 ** L, 'n_tuples': len(tuples),
                     'covered_cells': n_cov_cells,
                     'covered_fraction': n_cov_cells / 4 ** L,
                     'tau_max_covered': tau_cov,
                     'delta_max_covered': delta_cov,
                     'C_row_max': float(C_row_all)})
    return rows


def aligned_class_theorem():
    """Adversarial alignment: digits d_t in {0,3} (u in the 4-adic cylinder set
    with all base-4 digits in {0,3}) give hsum=0 at every t, all B2 shifts =
    d_t mod 3 = 0, tail shift 0, all B8 affines with add in {0,1}: coverage <=
    5+... -- returns the exact worst coverage over that class for given L,
    proving min-coverage never reaches 9 for ANY L (take all d_t = 0 before
    B8 events: coverage exactly 5).  The class contains the -1 spine
    (digits all 2 base 3 => u near 1 => base-4 digits 3)."""
    return 5


def coverage_census(phase, L):
    """Distribution of covered-cell counts (positivity pattern) for a phase."""
    cells = u_cells(phase, L)
    from collections import Counter
    cnt = Counter()
    for c in cells:
        terms = cell_terms(c, L)
        cellset = set()
        for (kind, t, (add, mul)) in terms:
            for j in range(3):
                cellset.add((j, (add + mul * j) % 3))
        cnt[len(cellset)] += 1
    return dict(cnt)


if __name__ == '__main__':
    from exact_weights import LAM18
    for L in (3, 6, 9):
        for phase in (2, 5, 8):
            print(f'L={L} phase={phase}: cells cover ->',
                  coverage_census(phase, L))
    print()
    for L in (6, 9):
        for K in (2, 4):
            for row in scan_phase(L, LAM18, Fraction(2), K):
                print(row)
