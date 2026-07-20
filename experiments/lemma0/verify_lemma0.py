#!/usr/bin/env python3
"""Symbolic verification of Lemma 0 (docs/notes/mahler-cartier-lemma0.md).

Checks, with sympy, that for h(z) = sum_{n>=0} a_n z^n (a_n symbolic) the
Berg-Meinardus residual

    R(z) := h(z^3) - h(z^6) - (1/(3z)) * sum_{j=0}^{2} w^j h(w^j z^2),
    w = exp(2*pi*i/3),

expanded through z^60, equals EXACTLY

    P(z) := sum_k (a_{2k} - a_k) z^{6k} + sum_k (a_{2k+1} - a_{3k+2}) z^{6k+3},

i.e. the BM equation <=> { a_{2k} = a_k, a_{2k+1} = a_{3k+2} }, and no other
relations appear (coefficients at m not divisible by 3 vanish identically).

Also checks:
  1. R(z) == (L h)(z^3) where L = 1 - M2 - z*M2*Lambda_{3,2}
     (M_k h(z) = h(z^k), Lambda_{3,2}(sum a_n z^n) = sum a_{3n+2} z^n).
  2. The relation set {a_{2k}-a_k} u {a_{2k+1}-a_{3k+2}} and the set
     {a_n - a_{T(n)}} span the same linear subspace (within the index window),
     T(n) = n/2 (n even), 3n+1 (n odd).
  3. A random coefficient assignment constant on the Collatz-graph components
     of {0,...,60} (computed by brute-force orbit merging) kills R.
  4. A random NON-component-constant assignment does NOT kill R.

Run: python3 verify_lemma0.py   (exits 0 and prints PASS lines iff all checks pass)
"""

import random
import sympy as sp

DEG = 60          # verify coefficients of z^m for 0 <= m <= DEG
NSYM = DEG + 1    # symbols a_0 ... a_60 (indices needed: <= 30 for the Cartier
                  # term, <= 20 for h(z^3), <= 29 for a_{3k+2}; 60 is ample)

z, w = sp.symbols('z w')
a = sp.symbols(f'a0:{NSYM}')
h = sum(a[n] * z**n for n in range(NSYM))


def trunc(expr, deg=DEG):
    """Expand and drop all z-powers above deg (exact for the terms kept)."""
    p = sp.Poly(sp.expand(expr), z)
    return sum(c * z**m for (m,), c in p.terms() if m <= deg)


def reduce_w(expr):
    """Reduce w-powers via w^3 = 1 and then w^2 = -1 - w (min poly w^2+w+1)."""
    p = sp.Poly(sp.expand(expr), w)
    out = 0
    for (e,), c in p.terms():
        out += c * w**(e % 3)
    out = sp.expand(out.subs(w**2, -1 - w))
    return sp.expand(out)


def T(n):
    return n // 2 if n % 2 == 0 else 3 * n + 1


# ---------------------------------------------------------------- residual R
lhs = trunc(h.subs(z, z**3))                     # h(z^3), exact through z^60
rhs1 = trunc(h.subs(z, z**6))                    # h(z^6)

S = sp.expand(sum(w**j * h.subs(z, w**j * z**2) for j in range(3)))
S = sp.Poly(S, z)
# keep z-degree <= DEG+1 (we divide by z next); exact: needs a_n for n <= 30
S = sum(c * z**m for (m,), c in S.terms() if m <= DEG + 1)
S = reduce_w(S)
assert sp.Poly(S, w).degree() <= 0, "root-of-unity average failed to be w-free"
cart = trunc(sp.expand(S / (3 * z)))             # no pole: z^0 coeff of S is 0
assert sp.Poly(sp.expand(S), z).coeff_monomial(1) == 0, "unexpected pole at z=0"

R = sp.expand(lhs - rhs1 - cart)

# ------------------------------------------------------- predicted relations
P = sum((a[2 * k] - a[k]) * z**(6 * k) for k in range(0, DEG // 6 + 1))
P += sum((a[2 * k + 1] - a[3 * k + 2]) * z**(6 * k + 3)
         for k in range(0, (DEG - 3) // 6 + 1))

diff = sp.expand(R - P)
assert diff == 0, f"Lemma 0 coefficient identity FAILED: residual {diff}"
print(f"PASS 1: BM residual == sum (a_2k - a_k) z^6k + (a_2k+1 - a_3k+2) z^6k+3"
      f"  (all m <= {DEG}, incl. vacuous m != 0 mod 3)")

# ------------------------------------------------ operator form L = 1 - M2 - z M2 Lam32
lam = sum(a[3 * n + 2] * z**n for n in range(NSYM) if 3 * n + 2 < NSYM)
Lh = sp.expand(h - h.subs(z, z**2) - z * lam.subs(z, z**2))
Lh3 = trunc(Lh.subs(z, z**3))
assert sp.expand(R - Lh3) == 0, "R != (Lh)(z^3): operator form FAILED"
print("PASS 2: R(z) == (Lh)(z^3) with L = 1 - M2 - z*M2*Lambda_{3,2}")

# --------------------------- relation sets generate each other (Lemma 0 step 3)
# Claim: {a_2k - a_k (k>=1)} u {a_2k+1 - a_3k+2 (k>=0)}  <=>  {a_n - a_T(n) (n>=1)}.
# Window-honest membership tests:
#   (i)  every T-relation a_n - a_{T(n)} lies in the span of BM relations,
#        whenever the generating BM pair fits in the window:
#        n even: it IS the BM even relation; n = 2k+1 odd: it is
#        (a_2k+1 - a_3k+2) + (a_2(3k+2) - a_3k+2 scaled): need 6k+4 <= DEG.
#   (ii) every BM relation lies in the span of T-relations: even ones are
#        T-edges; odd a_2k+1 - a_3k+2 = (a_2k+1 - a_6k+4) - (a_6k+4 - a_3k+2),
#        two T-edges (T(2k+1) = 6k+4, T(6k+4) = 3k+2): need 6k+4 <= DEG.
def vec(expr):
    return sp.Matrix([[sp.diff(expr, a[i]) for i in range(NSYM)]])

def in_rowspace(M, v):
    return sp.Matrix.vstack(M, v).rank() == M.rank()

bm_rel = [a[2 * k] - a[k] for k in range(1, NSYM) if 2 * k < NSYM]
bm_rel += [a[2 * k + 1] - a[3 * k + 2] for k in range(NSYM)
           if 2 * k + 1 < NSYM and 3 * k + 2 < NSYM]
t_rel = [a[n] - a[T(n)] for n in range(1, NSYM) if T(n) < NSYM]
M_bm = sp.Matrix([vec(r) for r in bm_rel])
M_t = sp.Matrix([vec(r) for r in t_rel])

n_i = 0
for n in range(1, NSYM):
    if n % 2 == 0 and n < NSYM:
        ok_window = True
    elif n % 2 == 1:
        ok_window = (3 * n + 1 <= DEG)
    if T(n) < NSYM and ok_window:
        assert in_rowspace(M_bm, vec(a[n] - a[T(n)])), f"T-edge {n} not in BM span"
        n_i += 1
n_ii = 0
for k in range(0, (DEG - 4) // 6 + 1):          # 6k+4 <= DEG
    r = a[2 * k + 1] - a[3 * k + 2]
    assert in_rowspace(M_t, vec(r)), f"BM odd relation k={k} not in T span"
    n_ii += 1
for k in range(1, DEG // 2 + 1):                 # even BM relations are T-edges
    assert in_rowspace(M_t, vec(a[2 * k] - a[k])), f"BM even relation k={k}"
    n_ii += 1
print(f"PASS 3: relation systems generate each other within the window "
      f"({n_i} T-edges in BM-span; {n_ii} BM relations in T-span)")

# ------------------------------------- brute-force components, solution test
random.seed(20260720)
parent = list(range(NSYM))

def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x

def union(x, y):
    parent[find(x)] = find(y)

# merge n with T(n): follow the full orbit until it re-enters {0..60} and
# reaches the cycle, merging every index that lies in the window
for n in range(1, NSYM):
    m = n
    seen = set()
    while m not in seen:
        seen.add(m)
        nxt = T(m)
        if m < NSYM and nxt < NSYM:
            union(m, nxt)
        m = nxt
        if m == 1:
            break
    # ensure connection of n to the window-representative of its orbit tail:
    # walk again, connecting successive window elements through excursions
    m, last_in = n, n
    for _ in range(200):
        m = T(m)
        if m < NSYM:
            union(last_in, m)
            last_in = m
        if m == 1:
            break

comps = {}
for n in range(NSYM):
    comps.setdefault(find(n), []).append(n)
print(f"   components of {{0..{DEG}}} by brute force: {len(comps)} "
      f"(expect 2: {{0}} and the rest)")
assert len(comps) == 2 and sorted(comps[find(0)]) == [0]

cvals = {root: sp.Rational(random.randint(-9, 9), random.randint(1, 7))
         for root in comps}
subs_sol = {a[n]: cvals[find(n)] for n in range(NSYM)}
assert sp.expand(R.subs(subs_sol)) == 0
print(f"PASS 4: random component-constant assignment (c0={cvals[find(0)]}, "
      f"c1={cvals[find(1)]}) satisfies BM through z^{DEG}")

# ------------------------------------------------------------ non-solution
subs_bad = {a[n]: random.choice([0, 1]) for n in range(NSYM)}
subs_bad[a[2]], subs_bad[a[1]] = 1, 0        # force a_2 != a_1  => z^6 coeff != 0
Rbad = sp.expand(R.subs(subs_bad))
assert Rbad != 0
print(f"PASS 5: random non-component-constant assignment violates BM "
      f"(residual has {len(sp.Poly(Rbad, z).terms())} nonzero coefficients)")

print("ALL CHECKS PASSED")
