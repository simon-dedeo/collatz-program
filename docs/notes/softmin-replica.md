# Soft minima, replica susceptibility, and the zero-temperature seam

2026-07-21. Status: **all-level research proof of the finite-temperature
monotonicity/rigidity reduction + bounded exact-rational structural gates +
floating diagnostic on SHA-pinned exact inputs + open uniform theorem
target**.  This note does not prove the KL endpoint.  The diagnostic is

```bash
python3 experiments/kl/diagnose_softmin_replica.py
```

The main conclusion is a useful split.  The **values** of the softened and
strict operators are uniformly close, independently of the KL level.  Their
**selectors and derivatives** need not be: near-tie susceptibility can move to
colder and colder scales.  A viable proof must use a value-level estimate, or
prove uniform integrability of the selector spikes.  Finite-temperature
smoothness by itself is not enough.

## 1. The homogeneous interpolation

For a positive ternary fiber `z=(z_0,z_1,z_2)` and `p in R`, define

```text
M_p(z) = ((z_0^p+z_1^p+z_2^p)/3)^(1/p),             p != 0,
M_0(z) = (z_0 z_1 z_2)^(1/3).                        (1.1)
```

This normalization gives exactly the two desired endpoints:

```text
M_1(z) = (z_0+z_1+z_2)/3,       annealed average,
lim_(p->-infinity) M_p(z) = min_i z_i.               (1.2)
```

If a literal temperature is desired, take `p(T)=1-1/T`.  Then `T->infinity`
is the annealed endpoint and `T->0` is the strict minimum.  Near the cold end
it is cleaner to put `p=-beta`, `beta>0`.  Notice that `beta=0` is the
geometric mean, not the annealed endpoint; the full path is `p<=1`.

Replace every KL fiber minimum by `M_p`:

```text
(F_(lambda,p)c)_m
 = lambda^-2 c_(4m)
   + 1_(m=2 mod 9) lambda^(alpha-2) M_p(c on the branch fiber)
   + 1_(m=8 mod 9) lambda^(alpha-1) M_p(c on the branch fiber). (1.3)
```

Unlike an additive soft-min in the original coordinates, (1.1) preserves
positive homogeneity.  Thus `F_(lambda,p)` remains a monotone homogeneous
Perron operator at every temperature.  In log coordinates `x_i=log z_i`,

```text
log M_p(z) = (1/p) log((1/3) sum_i exp(p x_i)),       (1.4)
```

so this is the ordinary log-sum-exp/Maslov deformation applied in the
coordinate system natural to the KL cone.

For a unit eigenvector `F_(lambda,p)c=c`, let

```text
epsilon_p(c) = 1-3 sum_fibers M_p(c_fiber)/sum_m c_m.
```

The usual sum-of-rows calculation is unchanged and gives, conditionally on
the eigenpair,

```text
1-epsilon_p(c) = 3(lambda-1)/lambda^alpha.            (1.5)
```

At `p=1`, `epsilon_1=0`, and the endpoint in `1<lambda<=2` is `lambda=2`.
At `p=-infinity`, (1.5) is the strict terminal-excess identity already used
in the KL program.  The soft family therefore joins the correct two objects;
it is not merely a different annealed surrogate.

## 2. Uniform convergence of values

Put `m=min_i z_i`, `g_i=log(z_i/m)>=0`, and

```text
S_beta=sum_i exp(-beta g_i).
```

Then

```text
M_(-beta)(z)/m
 = exp((log 3-log S_beta)/beta).                      (2.1)
```

Since `1<=S_beta<=3`, one has the dimension-free bound

```text
min z <= M_(-beta)(z) <= 3^(1/beta) min z.            (2.2)
```

If the minimum has multiplicity `r`, the upper factor improves to
`(3/r)^(1/beta)`.  Applying (2.2) row by row gives

```text
F_(lambda,-infinity)c
 <= F_(lambda,-beta)c
 <= 3^(1/beta) F_(lambda,-infinity)c.                 (2.3)
```

Consequently the corresponding cone spectral radii at fixed `lambda` obey

```text
0 <= log rho_(lambda,-beta)-log rho_(lambda,-infinity)
   <= (log 3)/beta,                                   (2.4)
```

uniformly in `k`.  Equations (2.2)--(2.4) are elementary research
derivations; the diagnostic checks (2.1) on bounded test fibers.  They are the
positive result of this lane: rare near-ties cannot destroy value-level
convergence.

There are two caveats.  First, the `lambda`-dependence is not coordinatewise
monotone because the type-eight coefficient grows with `lambda`; turning
(2.4) into a uniform statement about the roots `lambda_(k,p)` still needs a
closedness/transversality argument.  Second, an `O(1/beta)` value error is too
large to preserve an `epsilon^2` gain unless one first takes `beta->infinity`
or works at least on the scale `beta >> epsilon^-2`.

There is also a sharp limitation on what one **fixed** coldness can prove by
this sandwich alone.  Power-mean order gives

```text
rho_(lambda,-beta) <= rho_(lambda,1)=s(lambda).
```

Meanwhile (2.4) can transfer `rho_(lambda,-beta)>=3^(1/beta)` to
`rho_(lambda,-infinity)>=1`, but no smaller soft lower bound suffices through
(2.4).  Such a transfer is therefore possible only when

```text
s(lambda) >= 3^(1/beta).                            (2.5)
```

Since `s(2)=1` and
`-s'(2)=3(2-alpha)/8`, condition (2.5) requires, as `lambda->2-`,

```text
beta >= log(3)/log(s(lambda))
     = (8 log(3)/(3(2-alpha)) + o(1))/(2-lambda)
     = (7.05872...+o(1))/(2-lambda).                (2.6)
```

Thus no finite `beta` can by itself cover parameters arbitrarily close to
two using only the universal sandwich.  A target-dependent `beta->infinity`,
or a sharper selection-specific soft-to-hard comparison, is unavoidable.

## 3. Exact derivative and two-copy identities

Let `u=(1/3,1/3,1/3)` and

```text
Z_p=(1/3) sum_i z_i^p,
pi_i(p)=z_i^p/sum_j z_j^p.
```

Direct differentiation gives

```text
d/dp log M_p(z)
 = (p E_pi[log z]-log Z_p)/p^2
 = D(pi(p) || u)/p^2.                                (3.1)
```

The log-coordinate gradient and Hessian are

```text
grad_(log z) log M_p = pi(p),
Hess_(log z) log M_p
 = p (diag(pi)-pi pi^T).                             (3.2)
```

At `p=-beta`, draw two independent selectors `I,J` from
`pi_beta,i proportional to exp(-beta g_i)`.  Their collision probability is

```text
Q_beta=P(I=J)=sum_i pi_beta,i^2
       = (sum_i exp(-2 beta g_i))/(sum_i exp(-beta g_i))^2. (3.3)
```

Thus `beta(1-Q_beta)` is the magnitude of the trace of the selector Hessian
in (3.2).  The canonical temperature susceptibility is

```text
C_beta = beta^2 Var_(pi_beta)(g)
       = (beta^2/2) E[(g_I-g_J)^2].                  (3.4)
```

If `H_beta=-sum pi_beta log pi_beta`, then

```text
d H_beta/d log beta = -C_beta,
integral_(0,infinity) C_beta d log beta = log(3/r),  (3.5)
```

where `r` is the multiplicity of the exact minimum.  The first identity is
direct differentiation; the second uses `H_0=log 3` and
`H_infinity=log r`.

There is a corresponding implicit derivative for the nonlinear Perron
value.  Fix a finite `p` and a locally normalized positive eigenpair

```text
F_(lambda,p)(c_p)=rho_p c_p.
```

Put `J_p=D_c F_(lambda,p)(c_p)` and let `ell_p>0` be its left Perron vector,
`ell_p^T J_p=rho_p ell_p^T`.  The transport derivatives contain the full
positive cycle, so `J_p` is irreducible and its Perron root is simple.  The
implicit-function formula therefore applies along any local normalized
eigenpair branch.  If `z^(m)` is the branch triple in row `m`, `w_m` is its
type-two or type-eight coefficient, and

```text
nu_m = ell_(p,m) w_m M_p(z^(m))
       /(rho_p <ell_p,c_p>),       sum_(branch m) nu_m <= 1,
```

then differentiation and (3.1) give

```text
d/dp log rho_p
 = sum_(branch m) nu_m D(pi_m(p)||u)/p^2.            (3.6)
```

At `p=0`, each quotient `D/p^2` has the continuous limit
`Var_u(log z^(m))/2`.  In the cold parametrization,

```text
d/d beta log rho_(-beta)
 = -sum_(branch m) nu_m D(pi_m(-beta)||u)/beta^2.    (3.7)
```

The two-copy collision controls this value response through the Renyi bound

```text
D(pi||u) <= log(3Q) <= 3Q-1.                         (3.8)
```

This is distinct from the Hessian statistic `1-Q`: collision excess controls
the pressure derivative, while disagreement controls selector curvature.
The eigenvector derivative itself additionally contains the projective
resolvent of `rho_p I-J_p`, so (3.6) does not provide a level-uniform
eigenvector response without a separate resolvent bound.

Two related replica scalars should not be conflated.  `1-Q_beta` measures
selector/Hessian ambiguity.  The collision **excess** `3Q_beta-1` is the
Renyi-2 departure from the uniform selector and is the more natural scalar
in pressure or two-copy Perron calculations.  Neither one alone controls the
weighted squared-gap heat capacity (3.4); the gap sizes matter.

Equation (3.5) makes the spike picture precise.  For a unique minimum with
second log-gap `Delta`, the selector crosses over at `beta Delta` of order
one.  Making `Delta` smaller does not create more total susceptibility area;
it pushes the fixed area `log 3` toward `beta=infinity`.  A uniform
zero-temperature selector theorem is therefore a tightness/uniform-
integrability theorem for these susceptibility measures.

The script computes (3.3), (3.4), and the two independent forms of each
replica identity.  `C_beta` is min-profile-mass weighted.  The alternative
parent-mass weighting and the near-tie mass `P(Delta<=1/beta)` are also
reported where relevant.

## 4. The replica identity at the actual mismatch

The first coarse-minimum gap is not just analogous to a susceptibility.  It
has an exact finite-temperature Jensen representation.

For positive triples `x,y` and `p<1`, the power mean is concave and
homogeneous.  Its directional Hessian is

```text
D^2 M_p(x)[v,v]
 = (p-1) M_p(x)
   Var_(pi_p(x))(v_i/x_i)
 = ((p-1)/2) M_p(x)
   E_(I,J)[(v_I/x_I-v_J/x_J)^2].                     (4.1)
```

In particular `M_p(x+y)>=M_p(x)+M_p(y)`.  Normalize

```text
A=M_p(x), B=M_p(y), u=x/A, v=y/B, theta=A/(A+B),
w_t=(1-t)v+t u.
```

With

```text
K_theta(t) = (1-theta)t,  t<=theta,
             theta(1-t), t>=theta,
```

two integrations by parts give the exact concavity gap

```text
M_p(x+y)-M_p(x)-M_p(y)
 = (A+B)(1-p) integral_0^1 K_theta(t) M_p(w_t)
     Var_(pi_p(w_t))((u_i-v_i)/w_(t,i)) dt.          (4.2)
```

The variance in (4.2) is again half a two-replica squared difference.  At
`p=-beta->-infinity`, it localizes at values of `t` where the winning index
switches.  The limiting curvature is atomic, exactly as the curvature of a
piecewise-linear tropical minimum is concentrated at its kinks.

For a branch row in `coarse-minimum-gap.md`, let `a,z>0` be the underlying
transport and branch triples **before** their separate minima are subtracted,
and take

```text
x_d=tau a_d,       y_d=w_branch z_d.
```

Then the strict limit of the left side of (4.2) is precisely

```text
min_d(tau a_d+w_branch z_d)
 -tau min_d a_d-w_branch min_d z_d
 = min_d(tau A_d+w_branch Z_d),                      (4.3)
```

where `A=a-min a` and `Z=z-min z`.  This is the local transport/branch
anti-alignment gain, and the most promising
use of replicas here: not a global spin-glass ansatz, but an exact curvature
formula for the already isolated missing quantity.

There is also an explicit smoothing error.  From (2.2), if `h_p` and
`h_infinity` denote (4.2) and (4.3), respectively, then

```text
abs(h_(-beta)-h_infinity)
 <= (3^(1/beta)-1) min_i(x_i+y_i).                   (4.4)
```

Indeed, writing `e_beta(v)=M_(-beta)(v)-min v`, the difference is
`e_beta(x+y)-e_beta(x)-e_beta(y)`.  Its positive part is at most
`(3^(1/beta)-1)min(x+y)`; its negative part is at most the same quantity
because `min x+min y<=min(x+y)`.  The factor one is sharp for this argument.

Thus any aggregate replica lower bound that beats the summed right side of
(4.4) by `c G epsilon^2`, with `c>0` independent of the level, survives the
strict-min limit.

## 5. What the selected records say

The diagnostic streams the selected exact feasible records `k=12,...,19`,
SHA-checking each manifest and sidecar.  Every input coordinate is exact, but
logs, Gibbs weights, and displayed statistics are floating calculations.
The records are feasible subeigenvectors, not exact critical eigenvectors.
The `k=16,...,19` sidecars are local and not tracked by git.

There are no exact fiber-minimum ties in any of the eight records.  However,
the smallest positive second log-gap falls from

```text
4.309e-7 at k=12  to  3.082e-10 at k=19.             (5.1)
```

At the fixed cold scale `beta=1024`, the min-mass-weighted selector
disagreement and heat capacity move in the wrong direction for a uniform
selector theorem:

| level | strict defect | strict defect recovered by `M_(-1024)` | `E_q[1-Q]` | `E_q[C_beta]` |
|---:|---:|---:|---:|---:|
| 12 | 0.05237810 | 0.9808101 | 0.01583 | 0.02664990 |
| 19 | 0.02980585 | 0.9658360 | 0.02951 | 0.04903370 |

The scaled selector statistic
`epsilon beta E_q[1-Q]` is `0.84918577` at `k=12` and `0.90081544` at
`k=19`.  This is compatible with a near-zero gap density growing on the
scale `1/epsilon`, but eight records do not establish that scaling.

For every fixed level, absence of exact ties forces `Q_beta->1` and
`C_beta->0`.  The table and (5.1) show why this pointwise statement is not a
uniform one: the crossover scale itself drifts.  The finite data are
compatible with noncommuting `k->infinity` and `beta->infinity` limits for
selectors.  They do **not** prove noncommutation.  In contrast, the value
bound (2.2) is uniform, so there is no analogous ambiguity for raw operator
values.

## 6. The primary theorem target and kill conditions

The most direct finite-temperature target is a value theorem, not an
eigenvector-regularity theorem.

> **Fixed-temperature annealing conjecture.**  For every fixed
> `lambda in (1,2)` and every fixed finite `beta>0`,

```text
lim_(k->infinity) rho_(k,lambda,-beta) = s(lambda).   (6.1)
```

This cold subfamily is all that is needed for the endpoint.  Indeed, fix
`lambda<2` and choose

```text
beta > log(3)/log(s(lambda)),
```

so `s(lambda)>3^(1/beta)`.  If (6.1) holds at this fixed `beta`, then for all
sufficiently large `k`, equations (2.3)--(2.4) give

```text
rho_(k,lambda,-infinity)
 >= 3^(-1/beta) rho_(k,lambda,-beta) > 1.             (6.2)
```

The positive Perron eigenvector then gives strict-min feasibility at
`lambda`.  Since this works separately for every `lambda<2`, it implies
`lambda_k->2`.  Crucially, this argument needs neither convergence of the
soft eigenvectors nor a projective resolvent bound; it needs only the scalar
limit (6.1).

The following bounded floating diagnostic is favorable:

```bash
python3 experiments/kl/diagnose_softmin_spectral.py
```

At `lambda=1.9`, the annealed value is `s=1.017608034011`.  The table lists
the midpoint of a floating Collatz--Wielandt bracket with logarithmic width
at most `10^-11`:

| `k` | states | `p=-1` | `p=-2` | `p=-4` | `p=-8` |
|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 0.8209194943 | 0.7672890408 | 0.7146294603 | 0.6804244506 |
| 3 | 9 | 0.9175876820 | 0.8932287283 | 0.8678341677 | 0.8469951811 |
| 4 | 27 | 0.9559539767 | 0.9409085015 | 0.9227784567 | 0.9044810273 |
| 5 | 81 | 0.9747611967 | 0.9639239149 | 0.9500470112 | 0.9352071242 |
| 6 | 243 | 0.9850983526 | 0.9765841067 | 0.9653002638 | 0.9527341293 |
| 7 | 729 | 0.9919433234 | 0.9850418379 | 0.9757113468 | 0.9650549146 |
| 8 | 2,187 | 0.9968264298 | 0.9911319988 | 0.9832936961 | 0.9741039808 |
| 9 | 6,561 | 1.0005655911 | 0.9958361620 | 0.9892137428 | 0.9811815642 |
| 10 | 19,683 | 1.0034574862 | 0.9995009029 | 0.9938966275 | 0.9869332286 |
| 11 | 59,049 | 1.0057741878 | 1.0024454896 | 0.9976858033 | 0.9916611680 |
| 12 | 177,147 | 1.0076455124 | 1.0048309519 | 1.0007773293 | 0.9955746050 |
| 13 | 531,441 | 1.0091730617 | 1.0067802606 | 1.0033132304 | 0.9988128950 |

Every displayed column rises toward `s` on this window.  This is a numerical
trend with a convergence diagnostic, not an interval certificate or evidence
that excludes a lower limiting value.

A colder falsification run, using the same script with
`--levels 12-14 --powers=-1,-8,-128`, gives the gaps `s-rho`

| `p` | `k=12` | `k=13` | `k=14` |
|---:|---:|---:|---:|
| `-1` | `.00996252` | `.00843497` | `.00717923` |
| `-8` | `.02203343` | `.01879514` | `.01609681` |
| `-128` | `.04358888` | `.03878909` | `.03437362` |

The same monotone trend persists at `lambda=1.99` through `p=-16` and level
thirteen.  Very cold temperatures have a longer crossover, but this window
shows no finite-temperature plateau.  These are IEEE-754 diagnostics; an
eventual positive gap is not excluded.

### 6.1 Exact monotonicity and the projection residual

Finite temperature supplies one all-level research theorem which is stronger
than the raw value sandwich.  Let

```text
(P_k x)_u=M_p(x_u,x_(u+n),x_(u+2n)),   n=3^(k-2),       (6.3)
```

be the power-mean projection from level `k` to level `k-1`.  For `p<1`,
`M_p` is concave and homogeneous, hence superadditive.  Transport permutes the
three children of a coarse state, while the three fine branch targets become
the three children in the corresponding coarse branch fiber.  Therefore, for
every positive `x` and `k>=3`,

```text
P_k F_(k,lambda,p)x >= F_(k-1,lambda,p) P_kx.          (6.4)
```

The companion script checks every row of the rational indexing and inequality
on one deterministic positive test vector per level for the harmonic mean
through `k=6`.  Equation (6.4) for all `k,p<1` is the displayed handwritten
argument, not yet a kernel theorem.

This is a coordinatewise inequality.  On a neutral row it is equality.  On a
branch row its residual is exactly

```text
h=M_p(tau a+w z)-tau M_p(a)-w M_p(z) >= 0,             (6.5)
```

where `a` is the transported child triple and `z` is the triple of already
projected branch targets.  Thus (6.5) is the Jensen/two-copy quantity in
(4.2), now at the actual refinement seam rather than on an analogy.

Apply (6.4) to a positive Perron pair

```text
F_(k,lambda,p)c=rho_(k,lambda,p)c.
```

The Collatz--Wielandt comparison gives

```text
rho_(k-1,lambda,p) <= rho_(k,lambda,p) <= s(lambda).   (6.6)
```

The upper bound uses `M_p<=M_1`.  Hence the fixed-temperature limit exists;
the open part of (6.1) is its identification with `s(lambda)`, not existence.

There is an exact scalar form.  Put `C=sum c`, `g=P_kc`, `G=sum g`,
`b=w_2+w_8`, and

```text
epsilon_p(c)=1-3G/C.
```

Summing the eigen-equation gives

```text
rho_(k,lambda,p)=s(lambda)-(b/3)epsilon_p(c).          (6.7)
```

If `D=rho g-F_(k-1,lambda,p)g>=0`, then a second summation gives the exact
projection-residual identity

```text
(sum D)/G=(b/3)(epsilon_p(g)-epsilon_p(c)).            (6.8)
```

In particular the fixed-temperature annealing conjecture is precisely
`epsilon_p(c_k)->0` for the soft Perron vectors.

Vanishing of the residual in (6.8) is rigid.  If `D=0`, equality holds in every
instance of (6.5).  Strict concavity of `M_p` modulo positive rays says that
the transport and branch triples are then proportional.  The fine eigen-equation consequently
sends the normalized conditional triple in every fiber to the normalized
conditional triple in its transport-successor fiber, up to the carry
permutation.  The coarse transport has length `n`, while the fine transport
has length `3n`; after one coarse circuit the omitted digit is acted on by a
3-cycle.  Its only invariant probability triple is uniform.  Hence

```text
D=0  ==>  epsilon_p(c)=0  ==>  rho_(k,lambda,p)=s(lambda). (6.9)
```

If `D` is nonzero, its strict coordinate propagates around the full transport
cycle under iteration, so the strong Collatz--Wielandt comparison gives
`rho_(k-1,lambda,p)<rho_(k,lambda,p)`.  Thus the finite-temperature tower is
strictly increasing at each adjacent step `k-1 -> k`, `k>=3`, until it reaches
the annealed value.

This still does not prove (6.1).  The transport circuit has exponentially
growing length, so (6.9) has no dimension-free stability modulus: a slowly
rotating conditional profile can have order-one oscillation and arbitrarily
small local discrepancy around a long cycle.  Iterating the projection gives
the valid direct residuals

```text
D_j=rho P^j c-F_(k-j,lambda,p)P^j c >= 0,
(sum D_j)/(sum P^j c)
   =(b/3)(epsilon_p(P^j c)-epsilon_p(c)),              (6.10)
```

but the one-step Jensen gaps do **not** simply telescope: after the first
projection, inherited residual sits inside the nonlinear power mean.  Any
argument that treats the gaps as an additive budget without controlling this
term is invalid.

Equations (6.8)--(6.10) give a sharp counterexample shape.  If (6.1) is false,
there must be positive soft Perron vectors with persistent terminal defect and
projection residuals whose strictness degenerates along the growing transport
circuits.  In a local limit this is a calibrated multiplicative defect mode:
transport and branch conditional triples become proportional while a
nonuniform profile is carried to finer scales.  The same-policy defect
automaton in `same-policy-defect-automaton.md` is the right finite diagnostic
for such modes.  Its large recurrent components show why exact rigidity alone
does not provide a uniform estimate.

### 6.2 Exact dual-policy form

There is also a useful linear-policy reduction.  For `p<0`, put

```text
q=p/(p-1),        0<q<1.
```

Reverse Hölder, with equality at the tangent hyperplane, gives

```text
M_p(z)=inf {sum_i a_i z_i:
            a_i>=0, sum_i a_i^q=3^(1-q)}.            (6.11)
```

At a positive triple the minimizing coefficients are

```text
a_i=(1/3)M_p(z)^(1-p)z_i^(p-1).
```

The row choices are independent.  If `B_a` is the nonnegative KL matrix
obtained by using one admissible coefficient triple in each branch row, then

```text
rho_(k,lambda,p)=min_a rho(B_a).                      (6.12)
```

Indeed `F_p<=B_a` for every policy, while the tangent policy at a positive
soft Perron vector satisfies `B_a c=F_pc=rho c`; the transport cycle makes
that matrix irreducible.

For the cold parametrization `p=-beta`, define

```text
t_i=a_i^q/3^(1-q),       sum_i t_i=1.
```

Then the exact coefficient/selector dictionary is

```text
a_i=3^(1/beta)t_i^(1+1/beta),
t_i=z_i^(-beta)/sum_j z_j^(-beta).                   (6.13)
```

Thus a finite-temperature adversary may bias the lost digit, but bias has a
precise Renyi coefficient-inflation cost.  At the uniform policy the
coefficients are `1/3`; at a deterministic policy their total is
`3^(1/beta)`, exactly the universal soft-to-hard factor.  Formula (6.12)
turns (6.1) into a concrete pressure statement: no hierarchy of admissible
entropy-penalized row policies may retain a Perron advantage bounded away
from the uniform policy as the precision grows.  Conversely, one such policy
tower with `rho(B_a)<=s(lambda)-eta` would kill the conjecture.

Simple policy screens have not found that tower.  At `lambda=1.9,p=-1`, a
random search over constant digit policies through level ten selected the
uniform coefficients; periodically lifting tangent policies from levels
three through eight made their large-level linear Perron roots exceed `s`,
not fall below it.  These are floating bounded tests, not optimizations over
all policies.  The actual tangent policy changes at every level and has nearly
full state complexity, so a bounded-memory test cannot establish (6.1).

### 6.3 Finite-horizon consistency is not enough

Starting from the constant vector, the lost top digit stays outside the
dependency cone for a bounded number of iterations.  More precisely, for
every `n<=k-1`, every `p<=1`, and the level-`k` annealed operator `A_k`,

```text
F_(k,lambda,p)^n 1=A_(k,lambda)^n 1.                 (6.14)
```

The proof is induction: after `n-1` steps the value depends on at most the
first `n-1` effective ternary digits, so the three top-digit lifts entering
the next mean have equal values.  At step `k` this protection ends.

This exact locality is a warning, not a proof of annealing.  Using (6.14)
through the usual minimum-of-iterates spectral lower bound would require

```text
lim_(n->infinity) min_x (L_lambda^n 1(x))^(1/n)=s(lambda) (6.15)
```

for the infinite-precision annealed transfer operator.  But (6.14) holds just
as well for the strict minimum.  Therefore (6.15), together with the usual
`F^n1>=m_n 1` argument, would also settle the hard-min endpoint directly.
Finite-horizon convergence, consistency of the discretization, or a bare
Følner analogy cannot be the finite-temperature input that is missing.

The best current proof target is consequently quantitative stability in
(6.9): exclude slowly rotating, mass-concentrating calibrated profiles by
using the branch/carry edges in addition to the long transport circuit.  A
strictly subcritical detail-shell or pair-carry estimate for each fixed
`lambda<2` would do this.  There is an exact reason to look there.  Normalize
the annealed operator by `s`, and put

```text
a=tau/s,       b_2=w_2/(3s),       b_8=w_8/(3s).
```

After resolving transport runs, its block weights are
`q_(2l+1)=b_8 a^l` and `q_(2l+2)=b_2 a^l`.  Their equal-word collision
coefficient is

```text
kappa(lambda)=3 sum_e q_e^2
 =lambda^alpha(1+lambda^2)
   /((1+lambda)(2+lambda^alpha(1+lambda)/3)).          (6.16)
```

It is strictly below one for `1<lambda<2` and equals one at two.  Indeed this
is equivalent to
`lambda^alpha(lambda^2-lambda+1)<3(1+lambda)`; the ratio of the two sides is
strictly increasing and reaches one at `lambda=2`.  This is only the diagonal
part of the pair-carry renewal.  The off-diagonal affine carry correlations
have not been controlled, so calling `kappa` itself an `L2` contraction would
repeat the known collision-kernel gap.

### 6.4 Local-curvature alternative

At the first projection, let `h_(r,-beta)` be the local gap (4.2) on each
branch row and let `E_beta` be the sum of the explicit errors (4.4).  A more
selection-specific finite-temperature target is

```text
sum_(branch r) h_(r,-beta)-E_beta
 >= c G epsilon^2,                                   (6.17)
```

for some `c>0` independent of `k`, along the selected critical family.  The
fitted `3/2` iterated-defect law corresponds to the stronger first-stage
constant `c=(w_2+w_8)/2` in the normalization of
`coarse-minimum-gap.md`.  Any positive uniform constant would already give
the needed Riccati mechanism after iteration.

By (4.2), (6.17) is a weighted two-copy variance lower bound.  It asks for a
quantitative amount of selector switching between the transport and branch
triples.  This is the same global anti-alignment missing from equation (4.4)
of `coarse-minimum-gap.md`, now expressed as a smooth curvature integral.
The immediate next diagnostic should compute (4.2) row by row and compare
its mass with the hard mismatch, stratified by transport/branch argmin
agreement.

Three failure modes must remain explicit:

1. **Finite-temperature curvature can be false gain.**  If two triples share
   a strict hard argmin but are not proportional, (4.2) is positive at every
   finite `beta` while (4.3) can be zero.  The error subtraction in (6.17), or
   an equivalent uniform-integrability theorem, is essential.
2. **Local selector regularity is not global Perron regularity.**  Linear
   response of a softened eigenpair also contains the resolvent of its
   Jacobian.  The transport base is a cycle whose size grows exponentially;
   no level-uniform spectral gap is currently available.  Fixed-level
   analyticity therefore supplies no uniform theorem.
3. **The first projection is not the whole endpoint proof.**  Later minimum
   profiles are supersolutions with inherited immigration/slack, not exact
   critical eigenvectors.  A successful (6.17) must be stable under that
   inherited term, or be replaced by a direct all-stage estimate.

The exact positive feasible counterexample in `coarse-minimum-gap.md` also
remains a kill test: no inequality derived only from positivity or feasibility
can work.  The input class must retain critical renewal-min self-consistency.

## 7. External analogies (none selected for mentioning Collatz)

- Litvinov, *The Maslov dequantization, idempotent and tropical mathematics*
  (2005), https://arxiv.org/abs/math/0507014, is the general zero-temperature
  / tropical-deformation analogy behind (1.4).
- Savas, Ahmadi, Tanaka, and Topcu, *Entropy-Regularized Stochastic Games*
  (2019), https://arxiv.org/abs/1907.11543, supplies the neighboring game-
  theoretic language for smoothing adversarial selectors.  Their theorems do
  not supply the level-uniform limit needed here.
- Chazottes and Hochman, *On the zero-temperature limit of Gibbs states*
  (2010), https://arxiv.org/abs/0907.0081, gives a rigorous warning that
  finite-temperature uniqueness and regularity need not imply convergence of
  Gibbs selectors as temperature vanishes.

The imported ideas organize the seam but do not solve it.  The primary new
burden is the scalar fixed-temperature annealing limit (6.1); the constrained,
level-uniform replica lower bound (6.17) for the renewal-min selected family is
the more local alternative.
