"""automaton.py -- the blocked ball automaton for the KL pressure certificate.

STATES.  Q_J = {q mod 3^J : q == 2 (mod 3)}  (|Q_J| = 3^(J-1)).  A state is the
3-adic ball B(q,3^-J) intersected with the level-k index set [3^k]; everything
below is uniform in k >= J+2.

LEVEL DYNAMICS on balls (exact, from the eigen-equation; see THEOREM.md sec.2):
for a level-k eigen/feasible vector c and M_k(xi) := sum_{m in [3^k], m==xi mod 3^J} c(m),

  M(xi) <= p*M(4xi mod 3^J)
         + 1[xi==2 (9)] * (q2/3) * sum_{i=0,1,2} M(R2(xi) + i*3^(J-1))
         + 1[xi==8 (9)] * (q8/3) * sum_{i=0,1,2} M(R8(xi) + i*3^(J-1))     (*)

with R2(xi) = (4xi-2)/3 mod 3^(J-1), R8(xi) = (2xi-1)/3 mod 3^(J-1).
Derivation (all steps exact):
 - transport m -> 4m is a bijection of [3^k] mapping ball xi onto ball 4xi;
 - m -> r_e(m) is a bijection {m in [3^k]: m==e mod 9} -> [3^(k-1)] mapping
   ball xi onto the coarser ball {r == R_e(xi) mod 3^(J-1)} (R_e is 3-adically
   3-expanding, so one low digit is lost);
 - min_j c(r + j*3^(k-1)) <= (1/3) * (fiber sum): "per-fiber-mass" domination --
   THIS is the essential normalization: the spine edge carries q8/3, not q8.
The three fine balls R_e(xi)+i*3^(J-1) partition the coarse target ball; the
top-of-tower lift index j is NOT the ball digit i (lifts of one r all lie in
one mod-3^J ball; the i-digit comes from r ranging over the coarse ball).

Policy domination: (*) dominates every minimizing policy since min <= mean is
policy-free.  Edge weights are certified UPPER bounds over lambda in
[lam_lo, lam_hi] (exact_weights).

The automaton is the weighted digraph W with edges
  T : q -> 4q mod 3^J                  weight p
  B2: q -> R2(q)+i*3^(J-1), i=0,1,2    weight q2/3 each   (q == 2 mod 9)
  B8: q -> R8(q)+i*3^(J-1), i=0,1,2    weight q8/3 each   (q == 8 mod 9)

Blocked (L-move) transitions are exactly the L-th matrix power; the tilt count
b(e) is additive along paths, so the blocked tilted automaton is (W_z)^L and
all pressure computations may be done on the 1-step matrix.
"""

from fractions import Fraction


def states(J):
    return [q for q in range(2, 3 ** J, 3)]


def idx_map(J):
    return {q: i for i, q in enumerate(states(J))}


def transport(q, J):
    return (4 * q) % 3 ** J


def branch_targets(q, J):
    """Return (kind, [3 targets mod 3^J]) or (None, []).  Exact index arithmetic."""
    m9 = q % 9
    if m9 == 2:
        z = ((4 * q - 2) // 3) % 3 ** (J - 1)
        return 'B2', [z + i * 3 ** (J - 1) for i in range(3)]
    if m9 == 8:
        z = ((2 * q - 1) // 3) % 3 ** (J - 1)
        return 'B8', [z + i * 3 ** (J - 1) for i in range(3)]
    return None, []


def edges(J):
    """List of (src, dst, kind) with kind in {'T','B2','B8'} (B-edges 3x)."""
    E = []
    for q in states(J):
        E.append((q, transport(q, J), 'T'))
        kind, tg = branch_targets(q, J)
        if kind:
            for t in tg:
                E.append((q, t, kind))
    return E


def backward_orbit(J, qcut):
    """Residues mod 3^J of -4^{-t}, t=0..qcut-1 (backward <4>-orbit of -1).

    Exact: inv4 = modular inverse of 4 mod 3^J.  Note the full orbit has period
    3^(J-1) and covers ALL of Q_J, so qcut is an essential truncation parameter;
    t=0,1,2 give -1=(2)^inf, -1/4=(20)^inf, -1/16=(2100)^inf (verbatim periodic
    addresses, cf. fiber-geometry.md M4).
    """
    mod = 3 ** J
    inv4 = pow(4, -1, mod)
    out, x = [], (-1) % mod
    for _ in range(qcut):
        out.append(x)
        x = (x * inv4) % mod
    return out


def exceptional_set(J, qcut=None):
    """Default exceptional set: J-digit balls of the first qcut orbit points."""
    if qcut is None:
        qcut = J          # -1, -1/4, ..., -4^{-(J-1)}
    return sorted(set(backward_orbit(J, qcut)))


def weight_matrix(J, w, tilt=None, z=Fraction(1)):
    """Row-form matrix A[i][j] (Fraction) of the automaton.

    w: dict with keys 'p','q2','q8' (Fractions -- e.g. certified upper bounds).
    tilt: set of exceptional states; edges INTO tilt-states get factor z
          (b(e) = 1_{target in E}; additive along paths).
    """
    S = states(J)
    ix = idx_map(J)
    n = len(S)
    A = [[Fraction(0)] * n for _ in range(n)]
    for (src, dst, kind) in edges(J):
        wt = w['p'] if kind == 'T' else (w['q2'] if kind == 'B2' else w['q8']) / 3
        if tilt is not None and dst in tilt:
            wt = wt * z
        A[ix[src]][ix[dst]] += wt
    return A


if __name__ == '__main__':
    for J in (2, 3):
        S = states(J)
        print(f'J={J}: {len(S)} states; orbit(qcut=J) =', exceptional_set(J))
        print('  edges:', edges(J))
