# Fixed-temperature pair carries and the conductor-shell obstruction

2026-07-21. Status: **all-level research derivation for the normalized
annealed channel, bounded exact-rational checks, and floating diagnostics for
the physical channel; no fixed-temperature saturation theorem**. Run

```bash
python3 experiments/kl/diagnose_softmin_pair_carry.py
```

The useful outcome is a sharper target, together with a no-go.  The full
two-copy calculation does not contract every detail mode, even when its
equal-word coefficient is strictly subcritical.  In fact the affine support
is amenable and has almost-invariant modes on arbitrarily high conductor
shells, so no uniform unweighted `L2` operator-norm argument on the full detail
space can establish the fixed-temperature limit.  The actual stationary
density behaves much better: its measured signed shell correlation moves
close to zero over the tested depths.  Proving that **on-code** cancellation,
rather than generic contraction, is the surviving route.

The checker separates its scopes deliberately.  Its structural gates use the
exact rational channel `a=b_2=b_8=1/3`; its physical-`lambda` dashboard uses
floating arithmetic and makes no asymptotic claim.

## 1. The induced channel away from the endpoint

Put `alpha=log_2(3)` and normalize the annealed KL operator by its column sum

```text
s(lambda)=lambda^-2
          +(lambda^(alpha-2)+lambda^(alpha-1))/3.
```

The three normalized weights are

```text
a   = lambda^-2/s(lambda),
b_2 = lambda^(alpha-2)/(3s(lambda)),
b_8 = lambda^(alpha-1)/(3s(lambda)),
a+b_2+b_8=1,                    b_8/b_2=lambda.       (1.1)
```

Resolving the initial run of transport maps gives the same countable affine
code as at the critical endpoint, but with a different symbol law:

```text
q_(2l+1)=b_8 a^l,       q_(2l+2)=b_2 a^l,            (1.2)
H_e(x)=(3x+b_e)/2^e,
b_e=1 for e odd,        b_e=2 for e even.
```

The first free ternary digit of `H_e(x)` depends only on `e mod 6`.  Summing
the resulting geometric series gives

```text
S_2=(b_2+b_8 a)/(1-a^3),
S_5=a S_2,
S_8=(b_8+b_2 a^2)/(1-a^3),       S_2+S_5+S_8=1.     (1.3)
```

Two replicas with the same block have mass

```text
D=sum_e q_e^2=(b_2^2+b_8^2)/(1-a^2).                 (1.4)
```

The remaining pairs that can collide after the first free digit have mass

```text
omega=sum_(d in {2,5,8}) S_d^2-D.                    (1.5)
```

Both are positive.  It is convenient to put

```text
kappa=3D,                  eta=3 omega.               (1.6)
```

For the physical weights, elementary cancellation in (1.4) gives

```text
kappa(lambda)
 = lambda^alpha(1+lambda^2)
   /((1+lambda)(2+lambda^alpha(1+lambda)/3)).         (1.7)
```

This is strictly below one for `1<lambda<2` and equals one at `lambda=2`.
For example, after reducing (1.7), the required strict inequality follows
from the monotonicity on `(1,2]` of
`lambda^alpha(lambda^2-lambda+1)/(1+lambda)`, whose endpoint value is three.
Thus the equal-block part really is subcritical at every fixed interior
parameter.  The question is whether the unequal-block carries destroy that
gain.

## 2. The exact two-copy operator

At output depth `j+1`, on the `3^j` parent residues define

```text
B_j(x,y)=sum_(e != f) q_e q_f
          1[H_e(x)=H_f(y) mod 3^(j+2)].              (2.1)
```

For fixed `x,e,f` with the same first output digit, the affine congruence has
a unique solution `y` on the parent quotient.  It has no solution when the
first digits differ.  Therefore every row sum of `B_j` is `omega`.
Interchanging `(x,e)` and `(y,f)` proves symmetry, so

```text
P_j=B_j/omega                                      (2.2)
```

is symmetric and doubly stochastic.  These finite kernels are the quotients
of one self-adjoint Haar-preserving Markov operator `P` on `Z_3`.

Let `R_j` be one induced channel step and let `f` be a parent density relative
to normalized Haar measure.  Expanding the squared norm into two replicas and
separating `e=f` from `e!=f` gives the exact identity

```text
||R_j f||_2^2 = kappa ||f||_2^2 + eta <f,P_j f>.     (2.3)
```

This is the relevant replica calculation.  Keeping only `kappa` discards the
off-diagonal carries and gives the wrong contraction diagnostic.

There is also a compact Green representation of the complete unequal-pair
sum.  In the coordinate `u=(x-2)/3`, use

```text
T(u)=2u+1,                       V(u)=32u+24.         (2.4)
```

Start in parity states `E` and `O` with raw masses

```text
d_E=b_2^2/(1-a^2),               d_O=b_8^2/(1-a^2),
```

and alternate along the deterministic weighted graph

```text
E --t,T--> O,       t=(b_8/b_2)a=lambda a,
O --v,V--> E,       v=(b_2/b_8)a^2=a^2/lambda.       (2.5)
```

The two-edge weight is `tv=a^3`.  Sum every nonempty directed path, add its
inverse path, and divide by `omega`.  Its one-orientation mass is

```text
W=[d_E(t+a^3)+d_O(v+a^3)]/(1-a^3),
2W=omega.                                             (2.6)
```

Equivalently, before normalization the four path families have coefficients

```text
E -> O:  b_2 b_8 a^(3k+1)/(1-a^2),       k>=0,
O -> E:  b_2 b_8 a^(3k+2)/(1-a^2),       k>=0,
O -> O:  b_8^2     a^(3k)/(1-a^2),       k>=1,
E -> E:  b_2^2     a^(3k)/(1-a^2),       k>=1.       (2.7)
```

Equations (2.4)--(2.7) extend the endpoint two-state Green kernel to every
physical `lambda`; only the weights vary.

## 3. The on-code conductor statistic

Let `r_n` be the depth-`n` marginal of the stationary induced law, and set

```text
f_n=3^n r_n,                Q_n=||f_n||_2^2.
```

Write its Haar martingale decomposition as

```text
d_n=f_n-E[f_n | F_(n-1)],
Delta_n=||d_n||_2^2=Q_n-Q_(n-1).                     (3.1)
```

Affine 3-adic isometries preserve every congruence filtration, hence `P`
preserves each conductor shell.  Distinct shells are `P`-orthogonal.  Applying
(2.3) to the projective stationary marginals and subtracting consecutive
levels gives

```text
<d_n,Pd_n>=(Delta_(n+1)-kappa Delta_n)/eta.           (3.2)
```

For `Delta_n>0`, define the signed on-code correlation

```text
theta_n=<d_n,Pd_n>/Delta_n.                          (3.3)
```

Then the shell evolution is exactly

```text
Delta_(n+1)/Delta_n = kappa+eta theta_n.              (3.4)
```

This is the most useful output of the probe.  At every fixed `lambda<2`, the
surviving theorem target is exactly

```text
<d_n,Pd_n> = o(Delta_n),       equivalently theta_n -> 0.       (3.5)
```

It would give eventual exponential decay with limiting ratio
`kappa(lambda)<1`.  The precise one-step contraction threshold is

```text
theta_n < theta_crit(lambda)=(1-kappa)/eta.           (3.6)
```

The threshold itself vanishes at the endpoint.  In fact

```text
theta_crit(lambda)
 = [7(3alpha+4)/30+o(1)](2-lambda).                  (3.7)
```

Thus pointwise fixed-`lambda` cancellation would be meaningful, but it would
not automatically give a uniform passage to `lambda=2`, still less uniform
control as the power-mean temperature simultaneously tends to zero.

At `lambda=1.9`, the floating dashboard gives

```text
kappa=0.940737907400,       theta_crit=0.189449976138,

theta_1,...,theta_11
= -0.175164, -0.029850, -0.030550, -0.022967,
  -0.029120, -0.013477, -0.006885, -0.003819,
  -0.001129,  0.000428,  0.000804.                  (3.8)
```

The final shell ratio is `0.940989`, close to `kappa`.  At `lambda=1.99`, a
separate floating run gives `kappa=0.994154`,
`theta_crit=0.020276`, and late correlations around `0.0045--0.0052` through
the tested depth.  These are encouraging diagnostics only: they are neither
interval-certified nor evidence of a uniform asymptotic.

## 4. Why generic `L2` contraction is impossible

The Green support contains the two loop orders

```text
T o V(u)=64u+49,             V o T(u)=64u+56,
(V o T)(T o V)^(-1)(u)=u+7.                          (4.1)
```

Also `V=L_(-7) o T^5`, where `L_c(u)=u+c`.  Consequently the generated affine
group is isomorphic to

```text
7 Z[1/2] semidirect Z  ~=  Z[1/2] semidirect Z,       (4.2)
```

and is solvable, hence amenable.  Its action on `(Z_3,Haar)` is ergodic
because it contains translation by the 3-adic unit seven.

A theorem of Schmidt (Theorem 2.4) implies that an ergodic
probability-preserving action of a countable amenable group on a nonatomic
standard probability space is not strongly ergodic.  Applied here, there are
normalized centered functions
`g_m` that become almost invariant under every support element.  Since the
Green weights are summable, dominated convergence gives

```text
<g_m,Pg_m> -> 1.                                    (4.3)
```

Locally constant functions are dense.  Decomposing locally constant
approximants into the `P`-invariant conductor shells shows that some shell has
Rayleigh quotient arbitrarily close to one.  These shells must have
arbitrarily high conductor: on each fixed finite quotient, ergodicity and
finite dimensionality leave a strict spectral gap below one off the
constants.

Finally,

```text
kappa+eta=3 sum_d S_d^2 > 1,                         (4.4)
```

because `(S_2,S_5,S_8)` is nonuniform (`S_5=aS_2` with `0<a<1`).  Combining
(4.3)--(4.4), the response `kappa I+eta P` expands some arbitrarily high pure
detail shells for **every** `1<lambda<=2`.  This is an all-level research
proof, not a kernel-checked theorem.  It rules out a uniform unweighted scalar
`L2` contraction on the full detail space.  It does not rule out negative or
small `theta_n` for the specific stationary increments in (3.3), a weighted
norm, or a multistep selected estimate.

This obstruction comes from a source outside the Collatz literature: Klaus
Schmidt, [*Amenability, Kazhdan's property T, strong ergodicity and invariant
means for ergodic group-actions*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5463DCE69C0FA63534CDF222CDC55325/S014338570000924Xa.pdf/amenability-kazhdans-property-t-strong-ergodicity-and-invariant-means-for-ergodic-group-actions.pdf),
*Ergodic Theory and Dynamical Systems* **1** (1981), 223--236.  The paper does
not discuss this problem; only its general strong-ergodicity theorem is used.

## 5. An exact subcritical expansion witness

The bounded checker uses the abstract rational channel

```text
a=b_2=b_8=1/3.
```

It has the same affine block structure as the physical channel and gives

```text
D=1/4,                 kappa=3/4<1,
(S_2,S_5,S_8)=(6,2,5)/13,
omega=7/52,            eta=21/52.                    (5.1)
```

On the nine-coordinate parent quotient, the vector

```text
z=(1,2,-10, -1,3,-10, 0,-5,20)                      (5.2)
```

has zero sum on each three-child fiber, so it is a pure detail-shell mode.
The exact pair kernel gives

```text
<z,Pz>/||z||_2^2
 = 7032148513/10848324844,

kappa+eta <z,Pz>/||z||_2^2
 = 6272085579/6199042768
 = 1+73042811/6199042768 > 1.                        (5.3)
```

Thus even a visibly subcritical diagonal `kappa` does not imply contraction
once unequal branches and their carries are retained.  The checker verifies
the exact block and pair kernels through output depth four, the collision
renewal through four induced steps, the martingale-shell identity through
detail depth three, the Green mass and affine commutator, and (5.1)--(5.3).
This witness calibrates the mechanism; because its weights are abstract, it
is not itself a claim about a physical interior `lambda`.

At the physical endpoint, the already-audited first-shell vector
`(1,1,-2)` has response `1605/1387>1`.  The same fixed vector crosses one in a
floating physical-parameter calculation near `lambda=1.73458`; that crossing
is only a numerical orientation marker.  The amenability argument above is
the all-parameter obstruction.

## 6. Consequences for the soft-min route

This calculation does not identify
`lim_k rho_(k,lambda,p)` with the annealed value `s(lambda)` at finite
power-mean order `p<0`.  It says what a plausible proof cannot ignore.

At finite temperature, the derivative of a power mean assigns endogenous
selector probabilities to the three siblings.  A two-copy expansion then
contains their products and the same affine carry alignments as (2.1), but
with weights depending on the current eigenvector.  Replacing those products
by their annealed averages erases the state-dependent analogue of the signed
statistic `theta_n`.  Moreover, the generic warm reference already has
almost-invariant high-conductor modes, so finite-temperature smoothness alone
cannot yield a level-uniform unweighted spectral gap that persists to the
strict minimum.

The promising formulation is therefore a selected, state-dependent analogue
of (3.3): prove that the actual eigenvector's conductor increments have
off-diagonal pair-carry correlation below (3.6), ideally with a quantitative
bound compatible with the shrinking scale (3.7).  Such a theorem would
distinguish genuine on-code cancellation from an annealed surrogate.  Without
it, the replica calculation is a diagnostic and a sharp no-go, not a proof of
finite-temperature saturation or of the zero-temperature endpoint.
