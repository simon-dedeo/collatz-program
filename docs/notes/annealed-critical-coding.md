# Critical coding of the annealed endpoint

**Status (2026-07-21): independently audited research derivation with exact
finite cores. Lean commits `9cdcfaf`/`764b815` check the scalar slack identity,
full weighted terminal-Pearson chain, and defect-plus-slack endpoint bridge. A
new exact
checker identifies the pair-carry kernel as a two-state affine Green kernel and
checks its conductor-shell decomposition at bounded levels. A separate audited
conditional argument proves strict adjacent growth from an attained positive
critical eigenvector; Lean formalization has been requested. Commit `f0e96a5`
checks the all-level annealed trace and the exact `r_2,r_3,Delta_2` floor.
Endpoint Perron uniqueness, the countable coding, the signed
conductor-cancellation estimate, and the selected-family Pearson estimate
remain open on the Lean/theorem side.**

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

The pair-carry Green-kernel audit is

```bash
python3 experiments/kl/verify_pair_carry_green_kernel.py
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

### 2.1 One fixed Green kernel and the conductor-shell correction

The level-dependent notation hides a useful exact simplification. Put
`u=(x-2)/3`. The normalized kernels `P_j` are finite quotients of one fixed
self-adjoint Haar-preserving Markov operator `P` on `Z_3`:

```text
P = (21/2) sum_(e!=f, same first digit) 2^(-e-f) U_(H_f^-1 H_e).
```

The countable sum has a two-state Green-kernel description. Start with raw
weights `1/15` in state `E` and `4/15` in state `O`, and follow the unique
alternating path

```text
E --1/2,  T--> O,       T(u)=2u+1,
O --1/32, V--> E,       V(u)=32u+24.
```

Sum every nonempty forward path, add its inverse, and multiply by `21/2`.
Two transitions cost exactly `1/64`; the total forward raw mass is `1/21`,
so the symmetric normalized operator has mass one. Truncating after five full
geometric cycles leaves normalized operator mass exactly

```text
8/64^5 = 1/134217728.
```

The two loop orders do not commute:

```text
T o V(u)=64u+49,
V o T(u)=64u+56,
(V o T) o (T o V)^(-1)(u)=u+7.             (2.3)
```

Because seven is a 3-adic unit, the generated support contains a translation
which is transitive on every finite quotient. This proves quotient
irreducibility and exposes a concrete Fourier-cancellation lever; it does not
give a spectral gap on the growing tower.

The martingale decomposition shows why (2.2) is subtler than termwise affine
equidistribution. Let `f_n=3^n r_n` be the Haar density, let

```text
d_m=f_m-E[f_m | F_(m-1)],
Delta_m=Q_m-Q_(m-1)=||d_m||_2^2,
M_(n+1)=3^n r_n^T P^(n) r_n.
```

Projectivity of the fixed operator preserves conductor shells and makes
distinct shells `P`-orthogonal. Therefore

```text
M_(n+1) = 1+sum_(m=1)^n <d_m,Pd_m>,
<d_m,Pd_m> = (7/2)(Delta_(m+1)-Delta_m).    (2.4)
```

Already the first shell is a fixed negative contribution:

```text
<d_1,Pd_1> = -2086/67963 = -298/9709.       (2.5)
```

Consequently, `M_n->1` requires the later signed conductor correlations to
cancel (2.5) in aggregate. Decay of each new shell, or absolute summability
without identification of the signed total, would only give convergence to an
unspecified constant. The easy `1/64` Green tail is not the missing estimate;
the hard part is cancellation among the low-weight but arithmetically
correlated affine maps.

Run `verify_pair_carry_green_kernel.py` for the bounded exact core. It checks
the path and four-family coefficients, normalization and tail, (2.3), exact
agreement with the independently coded alignment kernel on `3`, `9`, and `27`
parent states, quotient projectivity, (2.4) through detail level three, and
(2.5). An additional `81`-state comparison has been independently rerun. The
all-level Green representation and martingale algebra are short audited
research proofs; the checker does not certify (2.2), a Fourier decay bound, or
an asymptotic for `Q_n`.

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
input. Commit `764b815` now also exposes the intermediate public theorem
`(9/2)E[u^2] <= chi_terminal`, completing the full finite Pearson chain.

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

### 5.1 Projected tower and the exact anti-concentration target

The same renewal has an exact general-`lambda` code. Put

```text
theta = 1-epsilon = 3M
      = 3(1-tau)/b
      = 3(lambda-1)/lambda^alpha.
```

The branch mixture has masses `lambda/(1+lambda)` for type eight and
`1/(1+lambda)` for type two, while the number of preceding transport pairs
has law `(1-lambda^-2)lambda^(-2n)`. Combining the branch type and transport
run gives one block of length `e>=1` with

```text
p_e = (lambda-1)lambda^-e.                         (5.5)
```

The first output digit is classified by `e mod 6` just as at the endpoint, so

```text
S_2 = (lambda-1)(lambda^-2+lambda^-3)/(1-lambda^-6),
S_5 = (lambda-1)(lambda^-4+lambda^-5)/(1-lambda^-6),
S_8 = (lambda-1)(lambda^-1+lambda^-6)/(1-lambda^-6).
```

To state the projective consequence without mixing KL level and digit depth,
write

```text
X_j = Y/3^(j+1) Z_3,       |X_j|=3^j.
```

If a critical probability vector `c` lives on `X_n`, then its terminal
profiles `q,mu,v` live on `X_(n-1)`. Let `q_j,mu_j,v_j` be their projections
to `X_j`, with the depth-zero laws all equal to one. If `T_j` is projection
from `X_j` to `X_(j-1)` and `R_j` is the finite renewal channel induced by
(5.1), then

```text
c = R_n q_(n-1),
mu_j = R_j q_(j-1) = theta q_j+epsilon v_j,        1<=j<=n-1,
T_j q_j=q_(j-1),   T_j mu_j=mu_(j-1),
T_j v_j=v_(j-1).                                  (5.6)
```

Consequently `r_j=q_j/mu_j` is exactly the Radon--Nikodym martingale under
the `mu` filtration:

```text
E_(mu_j)[r_j | F_(j-1)] = r_(j-1).
```

The mixture in (5.6) gives `q_j<=mu_j/theta` and therefore only the automatic
bound

```text
chi^2(q_j || mu_j) <= 1/theta-1 = epsilon/theta.   (5.7)
```

The terminal anti-concentration constant has a sharper exact interpretation.
On the final parent level,

```text
u_x = 1/3-g_x/mu_x = epsilon v_x/(3mu_x),
delta = E_mu[u] = epsilon/3,
K = E_mu[u^2]/delta^2
  = sum_x v_x^2/mu_x
  = 1+chi^2(v || mu).                              (5.8)
```

Since `q-mu=-(epsilon/theta)(v-mu)`, this is equivalent to

```text
chi^2(q || mu) = (epsilon^2/theta^2)(K-1).         (5.9)
```

Thus bounded terminal `K` is exactly an `O(epsilon^2)` chi-square closeness
theorem for the minimum profile and its renewed image, uniformly whenever
`theta` is bounded below. The martingale estimate (5.7) is one full power of
`epsilon` too weak. This identifies the nonlinear cancellation which a
compactness or information argument must add.

There is nevertheless a useful weak regularity statement. For every target
atom and compatible block there is one source atom, so, with
`S_*=max(S_2,S_5,S_8)`,

```text
||R_j h||_infinity <= S_* ||h||_infinity,
||q_j||_infinity <= rho^j,       rho=S_*/theta<1
                                      for 6/5<=lambda<=2.       (5.10)
```

Hence any infinite projective tower, or any weak limit of growing selected
towers in this parameter range, has a uniform cylinder Frostman bound and is
non-atomic with positive lower dimension. A single finite tower is, of
course, still atomic. This is genuine compactness, but it does not imply the
quadratic chi-square estimate (5.9).

The equal-code-word collision factor is also exact:

```text
3 sum_e p_e^2/theta^2
    = lambda^(2alpha)/(3(lambda^2-1)),
p_1/theta = lambda^(alpha-1)/3 <= 1/2.             (5.11)
```

The first factor is below one only for `sqrt(2)<lambda<2`, and equals one at
`sqrt(2)` and `2`; it is above one for `1<lambda<sqrt(2)`. Equal code words
are therefore not the endpoint obstruction in the near-endpoint interval,
but this argument cannot be extended down to the whole range in (5.10).

Three simpler hopes fail rigorously:

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
3. Uniform fiberwise `L-infinity` flattening is incompatible even with an
   exact selected critical vector. The class-eight row at `-1` gives

   ```text
   g(-1)/c(-1)
     = lambda^(1-alpha)
       -lambda^(-1-alpha)c(-4)/c(-1)
     < lambda^(1-alpha).
   ```

   Since `c(-1)` is a member of that terminal fiber, its max-normalized range
   is greater than `1-lambda^(1-alpha)`. Along any endpoint family its
   liminf is at least `1/3`. This is an obstruction to fiberwise sup-norm
   flattening, not to decay of the mass-weighted terminal defect.

These examples show that the renewal and the local support geometry are
insufficient when considered separately; they do not construct a selected
critical family satisfying their conjunction. Any proof from this interface
must use the nonlinear relation (5.4), or comparably strong selection-specific
information, to rule out transport-shell concentration. The projective
Frostman estimate (5.10) is real but too weak; a dimension-free
translation/Besov or `O(epsilon^2)` chi-square estimate for solutions of this
renewal-min system would be a genuine endpoint route.

### 5.2 Coarse minimum supersolution

There is another exact all-level consequence of the minimum structure. For
`k>=3`, let `mathfrak m_k` take the minimum over each three-child fiber. The
branchwise inequality `min_i(A_i+B_i)>=min_i A_i+min_i B_i`, together with
the fact that transport permutes the three lifts and each carry map traverses
the corresponding coarse lifts, gives

```text
mathfrak m_k(F_(k,lambda)x)
    >= F_(k-1,lambda)(mathfrak m_k x).              (5.12)
```

For an exact critical `c`, normalize `g=mathfrak m_k c` to `q=g/sum g` and
write `epsilon(q)` for the normalized terminal excess of `q` one level down.
Then

```text
q >= F_(k-1,lambda)q,
sum(q-F_(k-1,lambda)q)
    = (b/3)(epsilon(q)-epsilon),
epsilon(q) >= epsilon.                              (5.13)
```

This makes a lower bound on the quadratic misalignment scale a concrete
quantitative target. No selected-record constant is claimed here: the exact
identity (5.13), rather than an unchecked finite fit, is the current evidence
for this lane.

### 5.3 Conditional strict adjacent growth

The full coupling does give a qualitative strict-lift theorem. This is an
independently audited all-level research proof with a bounded exact index core;
Lean formalization has been requested. Run

```bash
python3 experiments/kl/verify_strict_lift_mechanism.py
```

Assume that the level-`k` extremal
value `lambda=lambda_k` lies in `(1,2)` and is attained by a positive vector

```text
F_(k,lambda)c=c.
```

Let `C=sum c`, let `g` be the old fiber-minimum profile, and put

```text
E = sum_fibers (sum_children c-3g) = epsilon C.
```

Copy `c` to level `k+1`: `x_(m')=c_(m' mod 3^k)`. The ordinary lift proof
gives `d=F_(k+1,lambda)x-x>=0`. It also gives the exact slack rather than only
its sign. On a fine branch row the new minimum selects one particular member
`c_r` of the old fiber, whereas the old equation uses `g`; hence

```text
d_(m') = w_beta(c_r-g),       beta in {2,8},
```

and `d=0` on neutral rows. The three fine lifts permute all three old fiber
members, and each branch target is a bijection onto the old fibers. Therefore

```text
sum d = (w_2+w_8)E
      = b epsilon C
      = 3(s(lambda)-1)C > 0.                 (5.14)
```

Thus the lifted feasible vector has nonzero slack, although the slack is
localized. Let `F=F_(k+1,lambda)`, let `S` be fine transport, and let
`D=3^k` be the fine state count. The nonlinear map is monotone, positively
homogeneous, and superadditive, and `Fz>=tau Sz` for `z>=0`. From
`Fx=x+d`, induction gives

```text
F^n x >= x+sum_(i<n) F^i d.
```

Transport is one full `D`-cycle, so

```text
F^D x-x >= sum_(i=0)^(D-1) tau^i S^i d > 0
```

coordinatewise. With `y=sum_(i=0)^(D-1)F^i x`, superadditivity now gives

```text
Fy >= y+(F^D x-x) > y.                       (5.15)
```

Every coordinate of `F_(k+1,lambda')y-y` is continuous in `lambda'`.
The finite strict margin in (5.15), together with `lambda<2`, therefore
persists for some `lambda'>lambda`. Scaling `y` supplies a feasible vector at
that larger parameter. Consequently

```text
attained positive critical eigenvector at lambda_k in (1,2)
        ==> lambda_(k+1)>lambda_k.            (5.16)
```

This answers the qualitative adjacent-growth question under the usual
attainment/positivity hypothesis, but it does not prove `lambda_k->2`. The
propagated margin contains powers as small as `tau^D`, so this argument gives
no dimension-free gain. The endpoint target remains a quantitative refinement

```text
lambda_(k+1)-lambda_k >= phi(epsilon_k),
```

where `phi` is uniformly positive on every interval `epsilon>=epsilon_0>0`.
Together with attained positive critical vectors and bounded monotone
`lambda_k`, such an estimate would force `epsilon_k->0`. This is only an open
target; the unresolved step is making the gain uniform across the growing
transport cycle. Qualitative strictness alone permits summable adjacent gains.

## 6. Current status and live statements

The all-level research derivation, independently audited but not fully
formalized, consists of:

- the induced block law and series representation;
- the Renyi-2 identity `sum p_e^2=1/3` and Shannon identity
  `H(E)=log 4`;
- the first-digit law `(8,2,11)/21`;
- the collision renewal (2.1) with a symmetric doubly stochastic alignment
  kernel;
- the fixed two-state Green representation (2.3), its quotient
  irreducibility, and the signed conductor-shell identity (2.4);
- the product-measure no-go for inferring local Pearson decay from global
  linear collision growth;
- the critical renewal-min reduction (5.1)--(5.4), the general-parameter
  block code (5.5), and the projected Radon--Nikodym martingale (5.6)--(5.9);
- the cylinder Frostman estimate (5.10), with the infinite-tower/weak-limit
  scope stated there;
- the coarse minimum supersolution (5.12)--(5.13); and
- the conditional strict adjacent-growth theorem (5.14)--(5.16).

The scalar terminal/slack portion and full weighted Pearson chain are now
kernel-checked in `9cdcfaf`/`764b815`, as described after (4.3). Commit
`f0e96a5` additionally checks all-level one-step trace intertwining, mass
preservation, the exact endpoint vectors `r_2,r_3`, their projection, and
`Delta_2=622/1533>81/200`. Endpoint Perron uniqueness and the nonlinear
renewal-min reduction are not kernel-checked.

The original exact finite checker certifies:

- the low-level induced maps, geometric constants, first two marginals, and
  collision kernels through depth four;
- the normalized squared-`L2` detail-energy ratio `1605/1387` in the displayed
  signed direction;
- the sharp pointwise terminal factorization (4.1); and
- the algebraic core and depths through 256 of the sparse product-law no-go.

Two additional standard-library checkers certify bounded cores of the new
all-level arguments:

- `verify_pair_carry_green_kernel.py` checks the two-state paths through
  length sixteen, exact kernel agreement through 27 parent states (with an
  independent 81-state rerun), projectivity, and the first three martingale
  shells; and
- `verify_strict_lift_mechanism.py` checks the lift slack identity and target
  permutations on 21 positive integer vectors through `k=8`, and the exact
  transport-orbit mechanism through `k=7`.

The live quantitative missing inputs are selection-specific:

- signed cancellation of the full conductor-shell sum in (2.4), if the
  pair-carry local limit (2.2) and global collision asymptotics are wanted;
- a selected mean-defect rate such as `delta=O(1/k)` plus the level-uniform
  anti-concentration estimate (4.3), equivalently the `O(epsilon^2)`
  chi-square theorem (5.9), if the polynomial Pearson lane is to close
  through terminal defects; and
- a dimension-free quantitative version of the strict lift (5.16), such as a
  gain controlled below by the terminal excess.

None of these three quantitative endpoint inputs is presently proved. In
particular, do not infer signed cancellation from decay of individual
conductor shells, do not infer local Pearson decay from Renyi criticality, do
not infer smoothing from the renewal operator alone, and do not promote the
finite `6/j^2` calibration to an annealed asymptotic. The all-level trace and
exact low-level floor are kernel-checked in `f0e96a5`; Perron uniqueness still
remains the Lean-side seam needed to identify every normalized endpoint fixed
marginal with those exact vectors.
