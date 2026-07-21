# Critical coding of the annealed endpoint

**Status (2026-07-21): independently audited research derivation with an exact
finite core. Lean commit `9cdcfaf` now checks the scalar slack identity,
terminal variation/Pearson bounds, and defect-plus-slack endpoint bridge. The
all-level coding/trace/Perron argument, local-limit estimate, and selected-family
Pearson estimate remain open.**

This note explains why the `lambda=2` annealed endpoint is neither a generic
smooth law nor evidence for a simple one-step contraction.  It has a derived
countable affine coding whose symbol law is Shannon-supercritical but
algebraically
critical at Renyi order two.  That coding exposes a plausible pair-carry
local-limit problem, but it does **not** prove the polynomial Pearson bound
suggested by the finite KL certificates.

Run the exact finite audit with

```bash
python3 experiments/kl/verify_annealed_critical_coding.py
```

The checker uses only the Python standard library.  It verifies induced-map
instances through forty transport steps and the geometric-series constants,
reconstructs the
first two annealed Perron marginals, verifies the induced marginals against the
original three-map IFS, checks the collision renewal and its stochastic
alignment kernel through depth four, and checks two exact no-go examples
described below: the sparse product law and the signed detail-shell witness.
It also checks the sharp terminal
Pearson/minimum-defect factorization and exhausts rational probability fibers
through denominator sixty. The all-level statements below are short research
proofs, independently audited but not yet formalized.

## 1. Resolving the isometric return

Let

```text
Y = 2 + 3 Z_3.
```

Reading the columns of the annealed KL operator at `lambda=2` gives the
stationary random IFS

```text
g_0(x) = x/4,          probability 1/4,
g_2(x) = (3x+2)/4,    probability 1/4,
g_8(x) = (3x+1)/2,    probability 1/2.
```

The map `g_0` is a 3-adic isometry.  The other two maps contract by exactly
one ternary digit.  Resolve the initial run of `g_0` maps in the stationary
distributional equation.  For every `l>=0`,

```text
g_0^l o g_8(x) = (3x+1)/2^(2l+1),   probability 2^-(2l+1),
g_0^l o g_2(x) = (3x+2)/2^(2l+2),   probability 2^-(2l+2).
```

Equivalently, one induced block is indexed by an integer `e>=1`:

```text
p_e = 2^-e,
H_e(x) = (3x+b_e)/2^e,
b_e = 1 if e is odd, 2 if e is even.
```

Thus, for iid block lengths `E_i` with this law and
`S_i=E_1+...+E_i`, the stationary 3-adic variable has the convergent series

```text
X = sum_(i>=1) 3^(i-1) b_(E_i) 2^(-S_i).
```

After `j` terms the remainder is divisible by `3^j`.  Since the tail lies in
`Y`, the first `j` blocks determine `X mod 3^(j+1)`.  This fixes the indexing:
depth `j` has `3^j` possible atoms in `Y/3^(j+1)`, and depth zero is the one
fixed residue modulo three.

The block entropy and power sums are elementary geometric series:

```text
E[E] = 2,
H(E) = 2 log(2) = log(4) > log(3),
sum_e p_e^q = 1/(2^q-1).
```

In particular,

```text
sum_e p_e^2 = 1/3.
```

So the code has more Shannon entropy than one ternary digit per block, but its
Renyi-2 entropy is exactly one ternary digit.  This distinction is the useful
signal: Shannon/Pearson conditional information may decay while global
collision energy remains critical.

## 2. Exact first digit and collision renewal

Modulo nine, the output class depends on `e mod 6`:

```text
e mod 6 in {2,3}  -> 2,
e mod 6 in {4,5}  -> 5,
e mod 6 in {0,1}  -> 8.
```

Summing the geometric weights in these classes gives

```text
(S_2,S_5,S_8) = (8,2,11)/21,
sum_d S_d^2 = 3/7.
```

This is exactly the level-two Perron law used in the annealed-floor argument.

Let `r_j` be the stationary depth-`j` law, and define

```text
C_j = sum_x r_j(x)^2
    = P[X = X' mod 3^(j+1)],
Q_j = 3^j C_j,
Q_0 = 1.
```

If the first blocks agree, then

```text
H_e(X)-H_e(X') = 3*2^-e (X-X'),
```

so a depth-`j` collision is exactly a depth-`j-1` collision of the tails.
The total equal-block weight is `1/3`.  Therefore

```text
C_j = (1/3) C_(j-1) + R_j,
Q_j = Q_(j-1) + 3^j R_j,
```

where `R_j` is the collision probability with unequal first blocks.

There is a useful exact normalization of `R_j`.  On the
`N=3^(j-1)` parent states put

```text
B_j(x,y) = sum_(e != f) p_e p_f
             1[H_e(x) = H_f(y) mod 3^(j+1)].
```

For fixed `x,e,f` whose output first digits agree, division by three leaves a
unique affine solution `y mod 3^j`; if the first digits differ there is no
solution.  Hence every row sum is

```text
sum_d S_d^2 - sum_e p_e^2 = 3/7 - 1/3 = 2/21.
```

Swapping `(x,e)` with `(y,f)` shows that `B_j` is symmetric, so its column
sums are the same.  Consequently

```text
P_j = (21/2) B_j
```

is symmetric and doubly stochastic, and the renewal becomes

```text
Q_j-Q_(j-1)
  = (2/7) N r_(j-1)^T P_j r_(j-1).                 (2.1)
```

The constant `2/7` is therefore exact: it is the increment obtained if the
parent law is Haar-uniform against the alignment kernel.  It is not yet a
proved limiting slope for the actual annealed law.

The checker obtains, in exact arithmetic,

```text
Q_1 = 9/7,
Q_2 = 106203/67963,
Q_2-Q_1 = 18822/67963.
```

It also reconstructs the depth-two law with common denominator `87381` and
numerators

```text
(9632,4316,5240,6392,2408,17246,17264,1598,23285).
```

Since a symmetric stochastic matrix has `l2` operator norm at most one,
(2.1) gives only

```text
0 <= Q_j-Q_(j-1) <= (2/7) Q_(j-1),
Q_j <= (9/7)^j.
```

The desired sharper statement is a local-limit theorem specific to these
affine kernels:

```text
N r_(j-1)^T P_j r_(j-1) -> 1.                     (2.2)
```

A summable error in (2.2) would give
`Q_j=(2/7)j+O(1)`.  In affine form the problem is to show that the weighted
off-diagonal differences

```text
x - 2^(e-f)y + (b_e-b_f*2^(e-f))/3
```

equidistribute at zero modulo growing powers of three.  Generic Doeblin
mixing does not supply this: distinct blocks have distinct rational slopes,
and their modular repetitions occur on a period growing like `2*3^j`.

Exploratory float recurrence through `j=18` gives an alignment multiplier
`0.992444...` and increment `0.283555556...`, compared with
`2/7=0.285714286...`.  These values motivate (2.2), but they are not part of
the exact checker and no asymptotic claim is made from them.

## 3. Why global collision growth is not the Pearson theorem

Even a proof of `Q_j=Theta(j)` would not imply decay of the local Pearson
increments.  An exact independent ternary product law demonstrates the gap.
Use the uniform digit at every depth except powers of two; at an active depth
use

```text
p = ((2-sqrt(2))/6, (2-sqrt(2))/6, (1+sqrt(2))/3).
```

This is a probability vector and

```text
3 sum_i p_i^2 - 1 = 1.
```

For a product law, global collision energy factors as

```text
Q_j = product_(i<=j) (1+chi_i).
```

There are `floor(log_2 j)+1` active depths up to `j`, so

```text
j <= Q_j <= 2j,
```

while `chi_j=1` at infinitely many depths.  The checker performs all
quadratic-field arithmetic exactly and verifies the finite core through depth
256; the all-level conclusion is the displayed product formula in the audited
research derivation. A local Pearson theorem therefore needs
an inverse-density or shell-correlation estimate; Renyi criticality by itself
is insufficient.

The same warning applies to numerical asymptotics.  The annealed values
through `j=18` do not distinguish a pure inverse-power law robustly.  Late
windows are also compatible with a mixed exponential/power fit near
`0.93^j j^-0.7`.  The finite calibration `chi_j<=6/j^2` remains a useful
candidate upper envelope, but `6/j^2` should not be described as the annealed
asymptotic.

## 4. Exact obstructions to a scalar energy contraction

There is already a direction whose normalized quadratic energy increases at
the first nontrivial annealed detail shell. Let `T` sum each three-lift fiber,
let `L` be the uniform lift, let `Pi=I-LT`, and let `U` be the level-three transport
permutation.  At `lambda=2`, the annealed operator restricted to `ker T` is
`U/4`.  Define

```text
K_detail = (I-U/4)^(-1) Pi A_2^(3) L.
```

For the trace-zero coarse vector `z=(1,1,-2)`, exact rational evaluation gives

```text
K_detail z = (504,-258,629,528,126,725,-1032,132,-1354)/1387,
3 ||K_detail z||_2^2 / ||z||_2^2 = 1605/1387 > 1.
```

The factor three normalizes coordinate `l2` energy between dimensions three
and nine.  The checker builds `A_2^(3)` columnwise from the three IFS maps and
verifies `(I-U/4)K_detail z=Pi A_2^(3)Lz`, `T(K_detail z)=0`, and the norm
identity. Thus a
uniform normalized unweighted one-step coordinate-`l2` contraction for this
linear shell-response operator is false before the nonlinear minimum defect is
introduced. The signed witness does not exclude weighted, multistep, or
selection-specific energy arguments. A successful estimate has to use such
additional structure.

The terminal Pearson energy does have a sharp elementary connection to the
minimum defect.  For a ternary conditional law `p`, define

```text
chi(p) = 3 sum_i (p_i-1/3)^2
```

and put

```text
u = 1/3 - min_i p_i.
```

After permuting coordinates its deviations from uniform are
`(-u,x,u-x)`, with `-u<=x<=2u`.  Direct factorization gives

```text
chi(p) - (9/2)u^2 = 6(x-u/2)^2,
18u^2 - chi(p) = 6(2u-x)(u+x),
```

and `u<=1/3`, hence

```text
(9/2)u^2 <= chi(p) <= 18u^2 <= 6u.                (4.1)
```

If parents are weighted by their normalized mass, define
`chi_terminal=E[chi(p)]` and `delta=E[u]`. Jensen and (4.1) give

```text
(9/2) delta^2 <= (9/2) E[u^2]
                    <= chi_terminal
                    <= 18 E[u^2] <= 6 delta.       (4.2)
```

Here parent expectation uses the normalized parent masses. Put

```text
alpha = log_2(3),
w_2 = lambda^(alpha-2),
w_8 = lambda^(alpha-1),
s(lambda) = lambda^-2+(w_2+w_8)/3.
```

For a normalized exact critical vector,

```text
delta = (s(lambda)-1)/(w_2+w_8).
```

Thus a terminal `chi<=C/k^2` theorem would force
`s(lambda_k)-1=O(1/k)` and, on the branch `1<lambda_k<=2`, force
`lambda_k->2`.  The converse is not automatic: obtaining
`chi=O(delta^2)` requires the level-uniform anti-concentration estimate

```text
E[u^2] <= K (E[u])^2,                              (4.3)
```

with `K` independent of the level. Even (4.3) gives the polynomial Pearson
rate only after a separate selected-family estimate `delta=O(1/k)` has been
proved.

For feasible vectors, the exact identity is

```text
s(lambda)-1 = (w_2+w_8)delta + Sigma.
```

In scale-free form the aggregate normalized slack is

```text
Sigma = sum_m(F_lambda(c)_m-c_m) / sum_m c_m.
```

Qualitative `Sigma->0` is enough for endpoint convergence once `delta->0`,
but it gives no `1/k` rate. The paired mean-defect rate and
anti-concentration problem (4.3), or a direct spatial-measure substitute, is
now the cleanest terminal form of the polynomial-energy lane.

Lean commit `9cdcfaf` kernel-checks the pointwise bounds (4.1), the weighted
Jensen lower/upper comparison needed here, the exact normalized
`2 delta <= Delta_terminal <= 4 delta` relation, the aggregate-slack identity,
and the sequential implication `delta_k,Sigma_k -> 0 => lambda_k -> 2` on
`1<=lambda_k<=2`. It does not prove either missing rate or anti-concentration
input. The public weighted theorem does not yet expose the intermediate
`(9/2)E[u^2] <= chi_terminal` inequality explicitly; the Lean-side handoff has
requested that small interface strengthening.

## 5. Audited nonlinear renewal interface for selected critical vectors

There is a second algebraic reduction which isolates what direct compactness
must use. It has been independently audited as a research proof; it is not
exercised by the finite checker above and is not yet Lean-formalized. Assume
`1<lambda`, `c>0`, `sum c=1`, and `F_lambda(c)=c`. Let

```text
tau = lambda^-2,
w_2 = lambda^(alpha-2),
w_8 = lambda^(alpha-1),
b = w_2+w_8,
alpha = log_2(3).
```

Let `S` be transport, and let `J_2,J_8` be the mass-preserving injections of
a coarse profile into the two branch classes.  Normalize their mixture by

```text
J_lambda = (w_2 J_2+w_8 J_8)/b.
```

Let `g` be the coarse fiber-minimum vector, `M=sum g`, and `q=g/M`.
Summing the critical equation gives `1=tau+bM`; therefore

```text
c = tau S c + (1-tau) J_lambda q,
c = R_lambda q,
R_lambda = (1-tau)(I-tau S)^(-1)J_lambda
         = (1-tau) sum_(n>=0) tau^n S^n J_lambda.  (5.1)
```

This is a geometric transport renewal, but it is not smoothing by itself.
If `T` is fiber sum, put `mu=Tc`,

```text
e = mu-3g >= 0,
epsilon = sum e = 1-3M,
v = e/epsilon                       (when epsilon>0).
```

Then

```text
mu = (1-epsilon)q+epsilon v.                         (5.2)
```

For the annealed operator

```text
A = tau S+(b/3)J_lambda T,
```

the normalized positive defect has the special form

```text
A c-c = (b epsilon/3)J_lambda v,
s(lambda)-1 = b epsilon/3,
(A c-c)/(s(lambda)-1) = J_lambda v.                (5.3)
```

The normalized last line is asserted only when `epsilon>0`, equivalently
`s(lambda)-1>0` for this critical vector.

There is an even sharper sign coupling.  Let `L` now denote the uniform fiber
lift and `D=I-LT`.  Transport commutes with `D`, so

```text
y = Dc = (1-tau)(I-tau S)^(-1)D J_lambda q,
min_d y_(x,d) = -(epsilon/3)v_x.                    (5.4)
```

Equations (5.1)--(5.4) are the nonlinear renewal-min fixed-point system a
selected-family proof must exploit.

Two simpler hopes fail rigorously:

1. The support statement in (5.3) supplies no cancellation by itself.  Given
   arbitrary coarse probabilities `q,v` and `0<theta<1`, put baseline
   `theta*q_x/3` in all three children of fiber `x` and place the remaining
   `(1-theta)v_x` in one child.  Its normalized minimum profile is `q` and its
   normalized excess profile is `v`.  Thus sign and support alone allow the
   whole coarse simplex.
2. The renewal operator in (5.1) is not uniformly-integrability improving.
   For a point input `q`, the `n=0`, type-two term alone contributes
   `(1-tau)/(1+lambda)` to one atom, so the total atom mass is at least this
   much; later renewal terms may revisit it. The corresponding Haar cylinder
   shrinks with the level. Strictly positive approximations retain the spike.

These examples show that the renewal and the local support geometry are
insufficient when considered separately; they do not construct a selected
critical family satisfying their conjunction. Any proof from this interface
must use the nonlinear relation (5.4), or comparably strong selection-specific
information, to rule out transport-shell concentration. A dimension-free
translation/Besov estimate for solutions of this renewal-min system would be
a genuine compactness route. A possible weaker endpoint target would be a
strict-lift inequality

```text
lambda_(k+1)-lambda_k >= phi(epsilon_k),
```

where `phi` is uniformly positive on every interval `epsilon>=epsilon_0>0`.
Together with attained positive critical vectors and bounded monotone
`lambda_k`, such an estimate would force `epsilon_k->0`. This is only an open
target; the unresolved step is making the gain uniform across the growing
transport cycle.

## 6. Current status and live statements

The all-level research derivation, independently audited but not fully
formalized, consists of:

- the induced block law and series representation;
- the Renyi-2 identity `sum p_e^2=1/3` and Shannon identity
  `H(E)=log 4`;
- the first-digit law `(8,2,11)/21`;
- the collision renewal (2.1) with a symmetric doubly stochastic alignment
  kernel;
- the product-measure no-go for inferring local Pearson decay from global
  linear collision growth;
- the critical renewal-min reduction (5.1)--(5.4).

The scalar terminal/slack portion is now partly kernel-checked in `9cdcfaf`, as
described after (4.3); trace intertwining, Perron uniqueness, the low-level
Perron floor, and the nonlinear renewal-min reduction are not.

The exact finite checker certifies:

- the low-level induced maps, geometric constants, first two marginals, and
  collision kernels through depth four;
- the normalized squared-`L2` detail-energy ratio `1605/1387` in the displayed
  signed direction;
- the sharp pointwise terminal factorization (4.1); and
- the algebraic core and depths through 256 of the sparse product-law no-go.

The live missing inputs are selection-specific:

- an affine pair-carry local-limit estimate such as (2.2), if global collision
  asymptotics are wanted;
- a selected mean-defect rate such as `delta=O(1/k)` plus the level-uniform
  anti-concentration estimate (4.3), if the `6/j^2` Pearson lane is to close
  through terminal defects; or
- regularity/strict lift derived from the full nonlinear coupling (5.4).

None of these is presently a theorem.  In particular, do not infer local
Pearson decay from Renyi criticality, do not infer smoothing from the renewal
operator alone, and do not promote the finite `6/j^2` calibration to an
annealed asymptotic.
