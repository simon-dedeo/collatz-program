# Boundary-Jordan Mahler attack on the place-value counter

## Verdict (30 July update)

The general boundary-Jordan lifting theorem is unnecessary for this Collatz
specialization.  The 17-block law contains a degree-one Padé cancellation

```text
E(C,Z) = (1-CZ)H(C,Z)-1
```

whose first nonzero `Z`-term occurs at degree **17**, not degree one.  At the
`k`th Jordan iterate this gives 17 times the available 2-adic precision while
paying only one additional rational-height factor.  An elementary product-
formula argument then proves that every specialized value `H(c,z_j)`,
`1 <= j <= 8`, is irrational in `Q_2`.

The Padé identity and the Collatz consumer are kernel-checked.  The exact
exponent/height identities have an independently replayable integer audit.
The final all-level rational-height contradiction is written out below and is
now the priority Lean target.  Until that last argument is kernel-checked, the
irrationality conclusion is a research theorem, not yet a project-certified
result.

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

## 6. The general theorem that is no longer needed

The initially desired theorem was deliberately narrow.

> **Boundary-Jordan 2-adic lifting theorem.**  Let
> `T(C,Z)=(C^17,C^16 Z^17)`.  Let `alpha=(c,z)` be a nonzero algebraic point
> whose coordinates are multiplicatively independent and have positive
> 2-adic valuation.  Let `f in Qbar[[C,Z]]` be analytic at zero, nonrational,
> and satisfy a regular first-order Mahler equation
> `f(C,Z)=P(C,Z)f(T(C,Z))`.  Then `f(alpha)` is transcendental over `Q`.

For a general first-order boundary-Jordan function this remains interesting,
but the place-value series has extra block cancellation which bypasses it.

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

## 7. The degree-17 Padé remainder

Since

```text
(1-X)P_17(X)=1-X^17,
```

the functional equation gives the exact identity

```text
(1-CZ)H(C,Z)-1
  = (1-(CZ)^17) H(C^17,C^16 Z^17)-1.
```

The first sixteen coefficients cancel because `A_n=n` for `0<=n<17`.
The coefficient of `Z^17` is

```text
C^33-C^17 = C^17(C^16-1).
```

Thus, when `C` and `Z` have positive 2-adic valuation, the remainder has
exact valuation

```text
v2(E(C,Z)) = 17(v2(C)+v2(Z)).
```

One quick way to see exactness is to write the right side as

```text
[H(T(C,Z))-1] - (CZ)^17 H(T(C,Z)).
```

Here `H(T(C,Z))` is a 2-adic unit.  The first bracket begins with
`C^33 Z^17`, whose norm is strictly smaller than that of `(CZ)^17`; the
ultrametric inequality therefore has unequal sides and gives equality.

`RankTwoRulerMahler.lean::one_sub_mul_P17` and
`valueAt_pade_remainder` kernel-check the finite-factor and convergent-series
identities.

## 8. Elementary irrationality proof

Fix `j` and write the `k`th iterate as `(C_k,Z_k)`, with

```text
u_k = C_k Z_k = 2^e_k / 3^f_k,
e_k = (79+8j)17^k + 1024 k 17^(k-1),
f_k = (59+6j)17^k +  768 k 17^(k-1).
```

The terms with `k=0` interpret the displayed shear terms as zero.  All
`u_k` lie strictly between zero and one in the real embedding.

Assume for contradiction that the 2-adic value is the reduced rational
`beta=A/B`.  Put

```text
Q_k = product_(0<=i<k) P_17(u_i).
```

The iterated functional equation gives `H(C_k,Z_k)=beta/Q_k`.  Hence

```text
R_k = (1-u_k) beta/Q_k - 1
```

is rational.  By the Padé calculation,

```text
v2(R_k)=17 e_k.                                      (P)
```

The value `H(c,z_j)` is a 2-adic unit, so `A` and `B` are odd.  Write

```text
P_17(u_i)=N_i/3^(16 f_i).
```

Every `N_i` is positive and odd.  Since `0<u_i<1`,

```text
N_i < 17 * 3^(16 f_i).
```

If `S_k=sum_(i<k)f_i`, clearing the odd denominator of `R_k` gives a
nonzero integer numerator bounded by

```text
abs(numerator(R_k))
  < (abs(A)+B*17^k) * 3^G_k,
G_k = f_k + 16 S_k.                                  (H)
```

Because the denominator is odd, (P) says `2^(17e_k)` divides this numerator.
The exact exponent simplification is

```text
17 e_k = 2 G_k + D_k,

17 D_k = 1904*j*17^k + 14336*k*17^k + 20451*17^k
         + 204*j + 374.
```

In particular `D_k >= 17^k`.  Combining (P) and (H), and using `4>3`, gives

```text
3^G_k 2^D_k
  < 4^G_k 2^D_k
  = 2^(17e_k)
  < (abs(A)+B*17^k)3^G_k,
```

so

```text
2^D_k < abs(A)+B*17^k.                                (*)
```

But `D_k>=17^k`, while for the fixed integers `A,B` the left side of (*)
eventually dominates `abs(A)+B*17^k`.  This is the contradiction.

The self-contained exact verifier
`experiments/kontorovich/boundary_jordan_pade_audit.py` checks the
coefficient cancellation, closed formulas, real-contraction gates, and
32,776 integer exponent rows through `k=4096`; the hash-pinned artifact is
`boundary_jordan_pade_audit.json`.  The bounded regression is not presented
as a proof of the universal final step.

## 9. Consequence after Lean closes the height argument

For each `1<=j<=8`:

```text
ordinary self-writing orbit with branch m_n
  -> H(c,z_j) is rational                 (kernel-checked interface)
  -> H(c,z_j) is irrational               (degree-17 Padé/height argument)
  -> contradiction.
```

This closes the autonomous place-value counter before synthesis once the
last height argument is kernel-checked.  It does not rule out other
aperiodic counters or prove Collatz.

## Claim boundary

- Machine-checked now: ruler block law, functional equation, Jordan iterates,
  determinant `16`, public-payload rational-value implication, the geometric
  factor identity, the degree-17 Padé remainder identity, and the conditional
  eight-rail Collatz consumer.
- Exactly audited: coefficient cancellation, all displayed exponent formulas,
  contraction inequalities, and 32,776 bounded regression rows.
- Research theorem awaiting full Lean: irrationality of each `H(c,z_j)` by
  the integer numerator/height contradiction in Section 8.
- No Collatz theorem or counterexample is claimed.  What is closed by the
  research proof is one proposed autonomous counter architecture.
