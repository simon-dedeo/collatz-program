# The renewal-min system as a constrained Doeblin curve

2026-07-21. Status: **exact all-level algebraic reduction with bounded exact
checker; conjectural quadratic contraction**. This note does not prove the KL
endpoint. Run the finite core with

```bash
python3 experiments/kl/verify_doeblin_renewal_bridge.py
```

Lean commit `786c02e` independently checks the resulting qualitative
data-processing inequality for the concrete KL coarse-minimum operator. The
translated-law dictionary and the sharp generic curve below remain
research-side algebra.

The point of the reformulation is that the terminal minimum defect is not
merely analogous to an information coefficient. It is exactly a multiway
Doeblin coefficient, and the critical renewal is exactly a Markov channel.
This turns the new quadratic minimum law in `coarse-minimum-gap.md` into a
specific nonlinear information-contraction problem.

## 1. Terminal excess is a three-way common-overlap defect

Let `G=Z/(3n)Z`, let `U` translate a probability vector by `n`, and write

```text
W_x(d)=U^d x,                         d=0,1,2.
```

The greatest common component of these three laws has mass

```text
tau_D(W_x)=sum_(r in G) min_d (U^d x)_r.
```

Write `rho_D(W)=1-tau_D(W)` for the complementary coefficient.

Each orbit of the order-three translation occurs three times in this sum.
Consequently the normalized terminal excess is exactly

```text
epsilon(x)
 = 1-3 sum_(r mod n) min_d x_(r+dn)
 = 1-tau_D(W_x).                                      (1.1)
```

Thus `epsilon` is the complementary three-way Doeblin coefficient. The
common component itself is the uniform lift of the coarse fiber-minimum
profile. If `g=mathfrak m x`, `q=g/sum g`, and `epsilon=epsilon(x)`, then

```text
wedge_(d=0)^2 U^d x = ((1-epsilon)/3) Lq,             (1.2)
```

where `Lq` copies `q` to all three high-digit lifts.

This formulation avoids a false normalization shortcut: the three literal
high-digit slices of `x` need not have equal mass. The three **translated full
laws** in (1.1) are probability measures, so their Doeblin coefficient is
defined without an extra hypothesis.

## 2. The critical renewal is a Markov channel

Use residue-index coordinates `p` at a fine level, and put

```text
(Sx)_p=x_(4p+2),
K_tau=(1-tau)(I-tau S)^(-1)
     =(1-tau) sum_(j>=0) tau^j S^j,       tau=lambda^-2.
```

On every finite quotient `S` is one cycle, so `K_tau` is a stochastic
geometric-resolvent channel. Let `J_2,J_8` be the two mass-preserving branch
injections and

```text
J_lambda = a J_2+(1-a)J_8,
a=w_2/(w_2+w_8).
```

The critical renewal identity from `annealed-critical-coding.md` is

```text
c=K_tau J_lambda q.                                  (2.1)
```

Let `U_f` and `U_c` be the order-three high-digit translations on the fine
and coarse quotients. The carry maps give the exact intertwining laws

```text
U_f J_2=J_2 U_c,
U_f J_8=J_8 U_c^2,
U_f S=S U_f.                                         (2.2)
```

The branch supports are disjoint, and multiplication by two permutes the
three powers of `U_c`. Therefore

```text
rho_D({U_f^d J_lambda q}_d)=epsilon(q).               (2.3)
```

Applying the common channel `K_tau` and using data processing gives

```text
epsilon(c)
 =rho_D({U_f^d K_tau J_lambda q}_d)
 <=rho_D({U_f^d J_lambda q}_d)
 =epsilon(q).                                         (2.4)
```

This is the information-theoretic form of coarse-minimum monotonicity for an
exact critical vector. The checker verifies (1.1)--(2.4), including all
normalizations and carry permutations, with rational arithmetic on bounded
quotients and with two independent rational choices of `tau` and `a`.

There is a sharp generic refinement, but it has the wrong scale for the
endpoint. On the fine quotient of order `3n`, the transport and high-digit
translation obey

```text
S^(3n)=I,                    U_f=S^(2n).
```

Indeed, for `n` a power of three the binomial expansion gives
`4^(2n)=16^n=1+15n (mod 9n)`. Since the affine index map is
`p |-> 4p+2`, its `2n`-th iterate is `p |-> p+n (mod 3n)`.

Hence the finite geometric resolvent and the common overlap of three shifted
point-input columns are

```text
K_tau = ((1-tau)/(1-tau^(3n))) sum_(j=0)^(3n-1) tau^j S^j,
eta_n  = tau_D({U_f^d K_tau delta_y}_d)
       = 3 tau^(2n)/(1+tau^n+tau^(2n)),                (2.5)
```

independently of `y`. For any probability vector `x`, split its three
translates into their common `U_f`-invariant component and residual translates.
Applying (2.5) to the residual point-mass mixture gives

```text
rho_D({U_f^d K_tau x}_d)
  <= gamma_n rho_D({U_f^d x}_d),
gamma_n=1-eta_n.                                      (2.6)
```

This factor is sharp at every input defect `0<=t<=1`: if `h` is any
`U_f`-invariant probability law, then

```text
x_t=(1-t)h+t delta_y
```

has input defect `t` and output defect `gamma_n t`. Thus the unconstrained
Doeblin curve within the translated-family class is exactly linear. In
particular, (2.1) and (2.3) give the valid refinement

```text
epsilon(c) <= gamma_n epsilon(q).                     (2.7)
```

At the endpoint `tau=1/4`, the generic gain
`1-gamma_n=eta_n` is asymptotic to `3*4^(-2n)`. It is exponentially small in
quotient size (and doubly exponentially small in level), so this generic
channel bound cannot supply the desired dimension-free quadratic term. The
equality calibration allows arbitrary translated seeds `x`; it does not assert
sharpness on the smaller branch-injection image, much less on the selected
renewal-min fixed points. This is a sharp generic no-go, not a failure of the
selected renewal-min route.

## 3. The endpoint target is a nonlinear constrained curve

The selected exact records in `coarse-minimum-gap.md` suggest

```text
epsilon(q) >= epsilon(c)+(3/2)epsilon(c)^2.           (3.1)
```

Writing `t=epsilon(q)` and `e=epsilon(c)`, this is equivalent to

```text
e <= f(t):=(-1+sqrt(1+6t))/3
            =t-(3/2)t^2+O(t^3).                     (3.2)
```

So the missing theorem is a quadratic improvement over ordinary data
processing for the renewal channel. In the language of nonlinear information
contraction, it asks for a constrained Doeblin curve below the identity with
curvature `3/2` at the origin.

The relevant external theory was developed without this number-theoretic
application:

- Makur and Singh, *Doeblin Coefficients and Related Measures* (2024),
  https://arxiv.org/abs/2309.08475, proves the multiway-divergence, maximal-
  coupling, tensorization, and Bayesian-network properties used by the
  dictionary;
- Lee, Lu, Makur, and Singh, *Doeblin Curves* (2026),
  https://arxiv.org/abs/2606.19859, introduces nonlinear curves
  `F_K(t;G)=sup{rho(WK):rho(W)<=t,W in G}`, including constrained versions,
  variational partition formulas, data processing under composition, and
  coupling bounds.

The ordinary unconstrained curve is not enough. For a convex input class
containing both constant and identity kernels, the general sharpness result
gives `F_K(t)=rho(K)t`. Equations (2.5)--(2.6) are the exact finite-quotient
version for the translated-family class, and their slope tends to one far too
quickly. This matches the exact counterexample in `coarse-minimum-gap.md`:
positivity and even strict KL feasibility do not imply defect monotonicity.

The live class must retain the **selected renewal-min self-consistency**:

```text
c=K_tau J_lambda q,
q=(mathfrak m c)/(sum mathfrak m c),
wedge_d U_f^d c=((1-epsilon(c))/3)Lq.                (3.3)
```

At later iterated-minimum stages there is also inherited supersolution slack,
so (3.3) must be enlarged by a controlled immigration/common-component term.
This is why neither an arbitrary-channel theorem nor the first critical
projection alone proves the all-stage law.

## 4. Concrete proof program and kill tests

The strongest current route is:

1. Define the constrained class `G_crit` of translate kernels generated by
   (2.1), (3.3), and the inherited nonnegative slack at later stages.
2. Use the variational partition or maximal-coupling characterization to
   express the gain
   `tau_D(WK_tau)-tau_D(W)` as the global mismatch between transport and
   branch argmins. This is exactly equation (4.4) of
   `coarse-minimum-gap.md` at the first stage.
3. Prove
   `F_(K_tau)(t;G_crit)<=(-1+sqrt(1+6t))/3`, or first prove any uniform
   `F(t)<=t-c t^2` with `c>0`. The latter already gives the required
   `O(1/k)` terminal defect with a different constant.
4. Falsify candidate weakenings against the exact positive `k=3` feasible
   vector before attempting a proof. Any class broad enough to contain all
   feasible vectors is already too broad.

The significance of the bridge is narrow but high: it imports a newly
developed nonlinear-contraction toolkit into the exact place where the KL
program needs one extra power of defect. The unresolved burden is equally
clear. One must show that critical renewal-min self-consistency excludes the
identity extremizers of the Doeblin curve; ordinary data processing alone
only recovers (2.4).
