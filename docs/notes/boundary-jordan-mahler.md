# Boundary-Jordan Mahler attack on the place-value counter

## Verdict

The most aggressive next step is not a larger counter-transducer search.  It
is a **boundary-Jordan lifting theorem** for one explicit two-variable Mahler
system.  Such a theorem would rule out all eight place-value ruler schedules
at once.

No such value theorem is proved here.  The reduction to it is exact; the
remaining transcendence input is explicitly isolated below.

## 1. The fixed value forced by a place-value orbit

For

```text
m_n = j + 8*17^v17(n+1),              1 <= j <= 8,
A_n = sum_(1<=t<=n) 17^v17(t),
```

put

```text
H(C,Z) = sum_(n>=0) C^A_n Z^n,
c      = 2^64/3^48,
z_j    = 2^(15+8j)/3^(11+6j).
```

The existing public-payload telescope and converse show that an ordinary
self-writing orbit with this schedule would force the 2-adic value

```text
H(c,z_j) = 1 - 2^20*Wbar(r)
```

for some natural `r`.  In particular, `H(c,z_j)` would be rational.  Thus it
is enough to prove that each of the eight 2-adic values is transcendental (or
merely irrational).

`KontoroC/RankTwoRulerMahler.lean` already kernel-checks the block law, the
convergent functional equation, all Jordan iterates, and the multiplicative
rank determinant used below.

## 2. The exact Mahler system

The block law gives

```text
H(C,Z) = P_17(CZ) H(C^17,C^16 Z^17),
P_17(X) = 1+X+...+X^16.
```

In the column convention of multivariate Mahler theory, the monomial map is

```text
T = [[17,16],
     [ 0,17]].
```

It is nonsingular, has no root-of-unity eigenvalue, and belongs to the
functional class `F` of Brechler.  The point `(c,z_j)` contracts to zero both
over the reals and in `Q_2`.  It is multiplicatively independent because its
prime-exponent vectors are

```text
(64,-48), (15+8j,-11-6j)
```

and their determinant is exactly `16` for every `j`.  Finally every regularity
factor is nonzero: at the real embedding,
`P_17(T^k(c,z_j)_1*T^k(c,z_j)_2)` is strictly positive.

## 3. Why the newest general theorem does not apply verbatim

Enzo Brechler's 27 July 2026 preprint, *Transcendence of multivariate Mahler
functions and algebraic relations between their values*, proves a functional
rational--transcendental dichotomy for transformations in class `F` and an
optimal lifting theorem for admissible transformations.  Its Definition 1.1
requires a Perron--Frobenius eigenvector with strictly positive coordinates
for value-transcendence applications; the paper explicitly separates this
value class from the weaker functional class `F` in the discussion preceding
Definition 1.5.

Our defective Jordan matrix lies exactly on that boundary.  Its eigenvectors
for eigenvalue `17` satisfy

```text
16*y=0,
```

so every eigenvector has second coordinate zero.  It has no strictly positive
Perron eigenvector.  Therefore citing the general value theorem here would be
invalid.  The functional dichotomy does apply, but functional transcendence
alone does not decide a 2-adic special value.

Source: <https://arxiv.org/abs/2607.24877>, especially Definition 1.1,
Corollary 1.4, and the class-`F` discussion around Definition 1.5.

## 4. Functional nonrationality is elementary

We do not need a natural-boundary theorem to show that `H` is not rational.
Treat `H` as a power series in `Z` over `Q(C)`.  If it were rational, its
coefficients `C^A_n` would satisfy a fixed linear recurrence

```text
sum_(0<=i<=d) R_i(C) C^A_(n+i) = 0
```

with polynomial coefficients after clearing denominators and with `R_d != 0`.
Choose `n=17^k-d`.  The final coefficient has exponent `A_(17^k)`, while all
earlier ones have exponent at most

```text
A_(17^k-1) = A_(17^k)-17^k.
```

For `17^k` larger than every `deg R_i`, the leading `C`-degree of the final
term is unique, a contradiction.  Hence `H` and `1` are linearly independent
over `Q(C,Z)`.

This elementary argument is a good Lean target because it uses only the
already formalized spike identity and degree comparison.

## 5. The explicit replacement for Perron positivity

The Perron hypothesis in general Mahler lifting theorems controls cancellation
along the transformed algebraic point.  For this one orbit, cancellation is
already controlled exactly.  At

```text
T^k(c,z_j) =
  (c^(17^k), c^(16*k*17^(k-1))*z_j^(17^k)),
```

a monomial with coefficient `a` has valuation

```text
v2(a C_k^p Z_k^q)
 = v2(a)
 + 64*p*17^k
 + q*((15+8j)*17^k + 1024*k*17^(k-1)).
```

For two support pairs the difference, apart from coefficient valuation, is

```text
17^(k-1) *
  (17*(64*dp+(15+8j)*dq) + 1024*k*dq).
```

If `dq != 0`, the bracket is affine in `k` and vanishes at most once.  If
`dq=0`, distinct monomials never collide.  Consequently every nonzero finite
polynomial has, for all sufficiently large `k`, a unique term of least
2-adic valuation.  It cannot vanish on the tail of the Jordan orbit.

This is stronger and more explicit than an abstract Zariski-density check.
The executable certificate is
`breakoff_ether_branch_pressure.py::jordan_monomial_separation_certificate`;
its formula and finite regressions are committed in
`breakoff_ether_branch_pressure_audit.json`.

## 6. The one theorem that would close the ruler lane

The desired theorem is deliberately narrow.

> **Boundary-Jordan 2-adic lifting theorem.**  Let
> `T(C,Z)=(C^17,C^16 Z^17)`.  Let `alpha=(c,z)` be a nonzero algebraic point
> whose coordinates are multiplicatively independent and have positive
> 2-adic valuation.  Let `f in Qbar[[C,Z]]` be analytic at zero, nonrational,
> and satisfy a regular first-order Mahler equation
> `f(C,Z)=P(C,Z)f(T(C,Z))`.  Then `f(alpha)` is transcendental over `Q`.

For the Collatz application it is enough to prove the linear lifting special
case: if `f(alpha)` is algebraic, then `f` is rational.  No algebraic
independence of several values is needed.

The standard auxiliary-function proof should be rebuilt with the anisotropic
weight

```text
w_k(p,q)=64*p*17^k
          +q*((15+8j)*17^k+1024*k*17^(k-1))
```

instead of a Perron eigenvector.  The unique-minimum formula above supplies
the zero estimate.  Functional nonrationality supplies the nonvanishing
auxiliary function.  Regularity transports its evaluations back to the
single alleged algebraic value.  A product-formula estimate is then the final
step.  The polynomial factor `k` is a feature, not a defect: an anisotropic
Newton rectangle can allocate fewer `Z` degrees as the Jordan shear grows.

## 7. Consequence if the theorem lands

For each `1<=j<=8`:

```text
ordinary self-writing orbit with branch m_n
  -> H(c,z_j) is rational                 (kernel-checked interface)
  -> H(c,z_j) is transcendental           (boundary-Jordan lifting)
  -> contradiction.
```

This would close the autonomous place-value counter before synthesis.  PSC
should therefore be secondary: use computation only to test and optimize the
anisotropic auxiliary-function inequalities, not to search millions of
transducers whose prescribed Mahler value is already the decisive gate.

## Claim boundary

- Machine-checked now: ruler block law, functional equation, Jordan iterates,
  determinant `16`, public-payload rational-value implication, and the exact
  finite-polynomial valuation formula used by the executable audit.
- Elementary but not yet formalized here: the coefficient-spike proof that
  `H` is nonrational.
- Open and load-bearing: the boundary-Jordan 2-adic lifting theorem and its
  final product-formula estimate.
- Therefore no Collatz theorem or counterexample is claimed.
