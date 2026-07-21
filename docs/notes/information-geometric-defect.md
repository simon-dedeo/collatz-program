# Information geometry of the selected transport--branch defect

2026-07-21. Status: **two all-level research identities, an information-
projection comparison, exact bounded/pinned checks, a kernel-Lean cold-limit
sandwich, and a sharp long-cycle obstruction; no coercive selected-profile
theorem**. Run

```bash
python3 experiments/kl/diagnose_information_defect.py
```

The main verdict is mixed. Ordinary divergences between the two conditional
triples have the wrong zero set. A forward-`D_KL` projection onto the union of
shared-minimizer order cones fixes that defect, but it is quadratically small
near an argmin wall and is far below the required scale on the selected
records. The more faithful object is an order-dependent Renyi divergence
between Gibbs escorts of the two minimum-subtracted triples. Its
zero-temperature **rate** converges to the exact hard mismatch, uniformly in
the KL level, with error at most `log(3)/beta`. This is a genuine
information-geometric description, but not yet a lower bound: it repackages
the local quantity whose selected all-stage coercivity remains open.

Here and below `D_KL` always means Kullback--Leibler divergence. The
Krasikov--Lagarias inequalities are called the **KL system**.

## 1. The exact two conditional triples

Let `c>0` be a level-`k` profile and let

```text
g_u=min_d c_(u,d)
```

be its first coarse minimum. For a coarse branch row `r`, the three lifted
fine equations pair two ternary fibers:

```text
a_d = c_(u,d),                 u=transport_source(r),
z_d = g_(v,pi_r(d)),           v=branch_target(r).       (1.1)
```

The permutation `pi_r in S_3` is not optional notation: it is the exact carry
map from the transport-source digit to the branch-target digit. The checker
reconstructs it from all three lifted residue equations and verifies the
closed indexing through level eight. Thus `z` in (1.1) is already expressed
in the transport label frame.

Normalize the two fibers separately:

```text
P=sum_d a_d,        Q=sum_d z_d,
p_d=a_d/P,          q_d=z_d/Q,
A=tau P,            B=w_r Q,        theta=A/(A+B),
x_d=p_d-min p,      y_d=q_d-min q.                       (1.2)
```

Here `tau=lambda^-2` and `w_r` is the type-two or type-eight branch weight.
The exact local coarse-projection slack is

```text
h_r = min_d(tau a_d+w_r z_d)-tau min a-w_r min z
    = (A+B) J_theta(p,q),

J_theta(p,q)=min_d [theta x_d+(1-theta)y_d].          (1.3)
```

This fixes an important normalization ambiguity. The two conditional triples
are `p` and the **carry-aligned** `q`, but their comparison is weighted by the
unnormalized row masses `A,B`. Normalizing the triples and then forgetting
`theta` changes the KL-system slack.

Let

```text
C_i={r in Delta_2 : r_i<=r_j for every j},
C_same=union_i (C_i x C_i).                           (1.4)
```

Then

```text
J_theta(p,q)=0
  iff argmin(p) intersects argmin(q)
  iff (p,q) belongs to C_same.                        (1.5)
```

This includes ties. It is the zero set that any honest information defect
must reproduce.

## 2. Why direct divergences have the wrong zero set

Directed `D_KL(p||q)`, reverse `D_KL(q||p)`, Jeffreys divergence,
Jensen--Shannon divergence, and squared Hellinger distance all vanish only
when `p=q`. The hard defect vanishes on the much larger set (1.4). For
example,

```text
p=(1/6,1/3,1/2),       q=(1/6,1/2,1/3)              (2.1)
```

share label zero as a strict minimizer, so `J_theta=0` for every `theta`, but

```text
D_KL(p||q)=D_KL(q||p)=(1/6) log(3/2)>0,
H^2(p,q)=1-(1/6+2/sqrt(6))>0.                         (2.2)
```

Jensen--Shannon and Jeffreys are likewise positive. Thus none can be a
universal lower bound for the hard information production. Directed and
symmetrized `D_KL` also become infinite under support mismatch; Jensen--
Shannon and Hellinger remain finite at zero coordinates, but still have the
wrong zero set.

This is visible rather than merely hypothetical on the selected records.
The table uses the row mass `A+B`, reports the hard value against the exact
quadratic target `(w_2+w_8)G epsilon^2/2`, and evaluates the divergences in
floating arithmetic on the SHA-pinned exact integer inputs. The first column
renders an exact rational comparison; the divergence columns are floating.

| `k` | hard / target | `D_KL(p||q)` / target | Jeffreys / target | JS / target | `H^2` / target | raw forward `D_KL` on hard-zero rows |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 1.81091 | 3.00609 | 6.01947 | .751688 | .752060 | 18.78% |
| 13 | 1.86386 | 2.95125 | 5.90937 | .738073 | .738372 | 19.11% |
| 14 | 1.94236 | 2.92866 | 5.86396 | .732490 | .732743 | 19.23% |

The large raw `D_KL` totals are therefore false comfort. Almost one fifth of
the forward total comes from rows with exactly zero hard mismatch, and no
inequality transfers the displayed numerical margin to (1.3).
The inputs are the selected rationally tightened feasible records, not exact
critical eigenvectors and not a coherent projective tower.

## 3. Projection onto the synchronizable-minimizer cone

There is a canonical way to repair the zero set. Define the forward
information projection

```text
phi_i(p)=inf_{r in C_i} D_KL(p||r),
I_theta(p,q)=min_i [theta phi_i(p)+(1-theta)phi_i(q)]. (3.1)
```

Then `I_theta=0` exactly on `C_same`. The direction of `D_KL` matters. In
three coordinates the forward projection has a closed isotonic-pooling form.
Sort the two labels other than `i` so that `p_a<=p_b`.

```text
phi_i(p)=0,                                      p_i<=p_a;

phi_i(p)=p_i log(p_i/m)+p_a log(p_a/m),
          m=(p_i+p_a)/2,                         p_i>p_a and m<=p_b;

phi_i(p)=D_KL(p||uniform),                       m>p_b.       (3.2)
```

The reverse projection uses geometric rather than arithmetic pooling and is
fragile at zero coordinates. Symmetrizing removes the simple formula without
improving the zero set, so (3.1) is the cleanest `D_KL` version.

Put `delta_i(p)=p_i-min p`. An elementary research proof gives

```text
(3/4) delta_i(p)^2 <= phi_i(p) <= log(3) delta_i(p). (3.3)
```

For the lower bound in the two-point pooling case, normalize the pooled pair
and apply Pinsker. Its total mass is at most `2/3` (the unpooled coordinate is
at least the pair average), giving `phi_i>=3 delta_i^2/4`. In the three-point
case, fix the range `delta_i` and maximize entropy. The middle coordinate at
the maximum is the geometric mean of the extremes, so the maximizing triple
is proportional to `(1,r,r^2)`, `r>=1`. The desired inequality reduces to

```text
log r >= 3(r^2-1)/(2(r^2+r+1)),
```

whose difference has derivative

```text
(r-1)^2(r+2)(2r+1)/(2r(r^2+r+1)^2) >= 0.
```

This proves the lower constant; it is sharp to second order at the uniform
triple in the direction `(-1,0,1)`. For the upper bound, the two-point
pooling cost in (3.2) is at most `delta_i log 2`. In the three-point case
`i` is the maximum and uniform pooling gives

```text
D_KL(p||uniform)=log 3-H(p)
                 <= (max p-min p) log 3.             (3.4)
```

To see (3.4), fix the range and vary the middle coordinate. Entropy is
concave, so its minimum occurs when two coordinates coincide or one is zero;
on each of the three resulting one-parameter boundary families the desired
inequality follows from concavity and its endpoint values. The upper constant
`log 3` is sharp at a point mass whose distinguished coordinate is the
maximum.

Weighted Jensen applied to (3.3) now gives the useful comparison

```text
(3/4) J_theta(p,q)^2
  <= I_theta(p,q)
  <= log(3) J_theta(p,q).                            (3.5)
```

This is an information-geometric characterization of distance **transverse**
to the synchronizable-policy cone. It also exposes the problem. Near an
argmin wall, `I_theta` is quadratic while the hard mismatch is linear. On the
selected records it is much too small:

| `k` | weighted `I_theta` / quadratic target | weighted `I_theta` / hard mismatch |
|---:|---:|---:|
| 12 | .034472 | .019036 |
| 13 | .031794 | .017058 |
| 14 | .029758 | .015321 |

These are floating logarithmic diagnostics, not exact inequalities. Their
decreasing scale is a negative result for using `D_KL` projection itself as
the missing coercive quantity. A theorem strong enough to recover the hard
target through the upper half of (3.5) would need an information lower bound
roughly thirty-seven times larger than the observed one already at level
fourteen.

## 4. The exact Renyi-rate representation

The hard defect does have an exact zero-temperature information formula at
the correct linear scale. For `beta>0`, form Gibbs escorts of the
minimum-subtracted conditional triples:

```text
P_beta(i)=exp(-beta x_i)/Z_x(beta),
Q_beta(i)=exp(-beta y_i)/Z_y(beta).                  (4.1)
```

Use Renyi divergence of order `theta`:

```text
D_theta(P||Q)
 =1/(theta-1) log sum_i P_i^theta Q_i^(1-theta).     (4.2)
```

With `c_i=theta x_i+(1-theta)y_i`, direct substitution gives

```text
R_beta(p,q)
 :=(1-theta)D_theta(P_beta||Q_beta)/beta
  =[-log Z_c(beta)
     +theta log Z_x(beta)+(1-theta)log Z_y(beta)]/beta. (4.3)
```

Since `min x=min y=0` and `min c=J_theta`, each three-term partition function
lies between its largest term and three times that term. Therefore

```text
|R_beta(p,q)-J_theta(p,q)| <= log(3)/beta,           (4.4)
R_beta(p,q) -> J_theta(p,q) as beta->infinity.       (4.5)
```

The error is independent of the profile, carry, level, weights, ties, and
smallest positive gap. Thus finite-temperature **value regularity survives
uniformly** to the strict minimum in this formulation.

At `theta=1/2`, (4.3) becomes

```text
R_beta=D_(1/2)(P_beta||Q_beta)/(2 beta)
      =-log BC(P_beta,Q_beta)/beta,                  (4.6)
```

where `BC=sum_i sqrt(P_i Q_i)` is the Hellinger affinity. This verifies the
two-copy interpretation exactly: the hard cost is the exponential separation
rate of two cold escorts. Squared Hellinger and Jensen--Shannon themselves
saturate when the minimizing labels differ and lose the amplitude. Taking
the negative logarithm and dividing by temperature recovers it.

Ties are handled correctly. If the two argmin sets intersect, the affinity
has a nonexponentially small common term and the rate is zero, even if the
limiting escort distributions are unequal and their ordinary Hellinger or
Jensen--Shannon distance stays positive. If the argmin sets are disjoint, the
affinity decays exponentially at rate `J_theta`.

The finite dashboard confirms the uniform calculation rather than proving an
asymptotic theorem:

| `k` | `R_64` / hard | `R_1024` / hard | `R_16384` / hard |
|---:|---:|---:|---:|
| 12 | .729711 | .997544 | .999985 |
| 13 | .702823 | .997556 | .999990 |
| 14 | .670832 | .996996 | .999989 |

The drift at fixed `beta=64` is the expected near-tie boundary layer. The
uniform bound (4.4), unlike selector convergence, is unaffected by that
drift.

After summing rows, however, the worst-case error is
`log(3) sum_r(A_r+B_r)/beta`. To resolve a target of order
`G epsilon^2` by this bound alone still requires a coldness on the order of
`epsilon^-2` (up to the row-mass ratio). Uniform survival of values is not a
free uniform coercivity theorem.

### 4.1 Strongest Lean-ready scalar statement

The most useful self-contained formalization target requires no probability
library. For nonnegative triples `x,y` with `min x=min y=0`,
`0<theta<1`, and `beta>0`, define

```text
Z(v)=sum_i exp(-beta v_i),
c_i=theta x_i+(1-theta)y_i,
R=(-log Z(c)+theta log Z(x)+(1-theta)log Z(y))/beta.
```

Then

```text
min c-log(3)/beta <= R <= min c+log(3)/beta.         (4.7)
```

It follows only from
`exp(-beta min v)<=Z(v)<=3 exp(-beta min v)`. This is
the strongest clean scalar lemma produced by the probe. Lean commit `8c3e1df`
checks it as `ternaryInformationRate_bounds` in
`CLEAN_LEAN/CleanLean/KL/InformationRate.lean`, without a probability library
or finite-data premise.  It formalizes the level-uniform local
zero-temperature passage; it does not prove that the sum of the limiting
local costs is large.

There is a useful multiway extension. For minimum-zero triples
`x^(1),...,x^(m)` and positive weights `theta_j` summing to one, set

```text
P_(j,beta)(i)=exp(-beta x^(j)_i)/Z_j,
C_beta=sum_i product_j P_(j,beta)(i)^theta_j.
```

Then

```text
|-log(C_beta)/beta-min_i sum_j theta_j x^(j)_i|
 <= log(3)/beta.                                    (4.8)
```

The number of competitors does not enter the error because the normalization
errors are averaged by the `theta_j`. For two competitors, `-log C_beta` is
exactly `(1-theta)D_theta`. Formula (4.8) shows that a separately identified
inherited-slack triple can be retained as a third replica without losing the
uniform cold limit. The unresolved issue at later projections is obtaining
the correct row decomposition, not the information algebra after it is known.

Lean commit `cc19c54` checks this arbitrary-finite-replica extension as
`multiTernaryInformationRate_bounds`.  Its full project build and axiom audit
pass with only the standard axioms reported by the project.  Commit `9ff6d64`
then connects the logarithmic expression to the literal geometric overlap
`sum_i product_j P_j(i)^theta_j` using positive Boltzmann probabilities and
checks (4.8) in that exact form; its full audit passes too.

## 5. Relation to the actual power-mean escorts

The derivative of the order-`s=-beta` power mean uses the different escorts

```text
E_beta(p)_i=p_i^(-beta)/sum_j p_j^(-beta)
           =exp[-beta log(p_i/min p)]/Z.             (5.1)
```

Applying the same order-`theta` Renyi calculation to these escorts recovers
the **log-ratio frustration**

```text
min_i [theta log(p_i/min p)+(1-theta)log(q_i/min q)] (5.2)
```

as its cold rate. It has the same shared-minimizer zero set, but it is not
uniformly equivalent to the linear-mass defect (1.3) without a lower bound on
the child probabilities. A tiny `p_min` turns an additive gap into an
arbitrarily large log ratio. Thus replacing (4.1) by (5.1) silently changes
the quantity being controlled. Formula (5.1) is well-defined on the selected
positive records; at a limiting zero coordinate it needs a support convention
or regularization, whereas the residual-cost escorts (4.1) remain positive
and tie-safe.

On the selected records, cold power-mean escort distances do accurately
diagnose the *label* mismatch. The `(A+B)`-weighted mismatch fractions at
`k=12,13,14` are `.67430,.67275,.67056`; at `beta=1024`, the corresponding
`JS/log 2` averages are `.66463,.66184,.65862` and squared Hellinger averages
are `.65989,.65653,.65290`. But these bounded divergences treat every cold
label disagreement as order one. They discard the second-gap/conductance
amplitude which turns a label disagreement into the hard cost.

There is nevertheless an exact information-production identity for the
*soft power-mean Jensen gap*. For order `s<1`, `s!=0`, let

```text
X=tau a,       Y=w_r z,
A_s=M_s(X),    B_s=M_s(Y),
u=X/A_s,       v=Y/B_s,       theta_s=A_s/(A_s+B_s),
w_t=(1-t)v+t u,
pi_t(i)=w_t(i)^s/sum_j w_t(j)^s.
```

If `I_FR(t)=sum_i pi_t(i)(d/dt log pi_t(i))^2` is the Fisher--Rao
information of the escort path, then the Hessian identity for `M_s` gives

```text
M_s(X+Y)-M_s(X)-M_s(Y)
 =(A_s+B_s)(1-s)/s^2
   integral_0^1 K_(theta_s)(t) M_s(w_t) I_FR(t) dt, (5.3)
```

where `K_theta(t)=(1-theta)t` below `theta` and
`theta(1-t)` above it. This is the genuine finite-temperature
information production. As `s->-infinity`, its Fisher energy localizes at
argmin-switching walls and the left side tends to (1.3). Endpoint
`D_KL`, Jeffreys, Jensen--Shannon, or Hellinger comparisons alone do not
retain the weighted path information in (5.3).

## 6. The explicit slowly rotating exception

The long transport circuit prevents a dimension-free conclusion from local
information geometry alone. A rational model makes the obstruction concrete.
Take

```text
v_0=(1/6,1/3,1/2),
v_1=(1/2,1/6,1/3),
v_2=(1/3,1/2,1/6),                                  (6.1)
```

and linearly interpolate each edge of the triangle
`v_0 -> v_1 -> v_2 -> v_0` with `L` equal steps. Compare neighboring triples
with identity carry and `theta=1/2`. Every fiber has macroscopic terminal
defect; its cycle average tends to `1/3`. Yet for `L=3m+1`:

```text
only three of the 3L edges have disjoint strict argmins,
sum_edges J_(1/2)=1/(4L),                            (6.2)
sum_edges D_KL(p_j||p_(j+1))=O(1/L),
sum_edges I_(1/2)(p_j,p_(j+1))=O(1/L^2).             (6.3)
```

The first two statements are checked exactly for `L=13,49,193`. The
logarithmic orders in (6.3) are floating diagnostics; the observed scaled
limits are about `.824/L` and `.0375/L^2`. If `3|L`, the mesh hits each tie
wall exactly. Every neighboring pair then shares a minimizing label and the
total hard production is exactly zero even though the minimizing label makes
a full rotation.

This family is not claimed to satisfy the KL system. It is a kill test for a
theorem based only on a long transport cycle, positivity, and nontrivial
fiber defect. It identifies the promised exceptional shape precisely:

> a slowly rotating conditional profile stays in the shared-minimizer cones,
> changes chambers through increasingly narrow tie walls, and carries
> macroscopic oscillation with vanishing transverse information production.

The actual proof burden is to show that the branch/carry cross-links and
selected renewal-min self-consistency forbid this family, or force it into an
explicit rigid form that is incompatible with the carry holonomy. Generic
cycle smoothness cannot do so.

## 7. What is newly measurable, and the remaining theorem

Two diagnostics survive this probe:

```text
InfoCone(c)=sum_(branch r) (A_r+B_r) I_(theta_r)(p_r,q_r),

InfoRate_beta(c)=sum_(branch r) (A_r+B_r)
                  (1-theta_r)D_(theta_r)(P_(r,beta)||Q_(r,beta))/beta.
                                                               (7.1)
```

`InfoCone` measures transverse squared distance to synchronizable active
policies. `InfoRate_beta` is a smooth, tie-safe approximation to the exact
hard mismatch, with the rowwise error (4.4). Neither is a finite-state
quotient; both retain sibling masses and the selected carry permutation, so
they do not confuse the selected dynamics with the annealed surrogate.

The cleanest possible coercivity statement would be

```text
InfoRate_beta(c) >= c G epsilon(c)^2                 (7.2)
```

at a temperature whose accumulated smoothing error is smaller than the
right side, uniformly across the selected all-stage profiles. Formula (5.3)
would recast (7.2) as a Fisher-information lower bound. The slowly rotating
family shows the necessary alternative: if (7.2) fails, one must prove that
the branch-weighted profile lies near a coherent rotating wall section and
then exclude that section using the exact carry/branch graph.

At present no such dichotomy is proved. `InfoCone` is a new continuous,
piecewise-smooth diagnostic but is numerically too weak for the quadratic target. `InfoRate` is
the right finite-temperature representation and survives uniformly to zero
temperature, but its limit is exactly the previously known hard mismatch.
The useful advance is therefore a precise proof interface and a calibrated
exceptional family, not a new endpoint theorem.

Three scope restrictions are load-bearing:

1. The exact identification (1.3) is the first coarse projection of the
   original profile. Later iterated minima are supersolutions. Their inherited
   slack sits inside the next fiber minimum and can change the minimizing
   label. One must include that immigration in the competing triple (or use a
   genuine multiway version of (4.3)); naively reusing the first-stage
   two-triple statistic does not equal the all-stage slack gain.
2. Positivity or KL-system feasibility alone cannot imply (7.2), by the exact
   feasible-cone counterexample in `coarse-minimum-gap.md`. Any theorem must
   retain selected critical renewal-min self-consistency.
3. Exact ties are not negligible in a theorem. Ordinary escort distances can
   remain positive when two argmin sets overlap. The order-cone zero set and
   the zero-temperature **rate**, rather than the unscaled divergence, are
   what make (3.1) and (4.3) tie-safe.

## 8. Outside sources and scope

- Imre Csiszár, *I-Divergence Geometry of Probability Distributions and
  Minimization Problems* ([DOI](https://doi.org/10.1214/aop/1176996454)),
  supplies the classical information-projection setting.  The ternary
  shared-minimizer union, pooling formula, and constants (3.3) are derived
  here rather than imported from that paper.
- Jean-François Bercher, *A Simple Probabilistic Construction Yielding
  Generalized Entropies and Divergences, Escort Distributions and
  q-Gaussians* ([arXiv:1206.0561](https://arxiv.org/abs/1206.0561)), gives
  neighboring escort-path/Rényi language.  It does not supply the
  transport--branch identity or a KL-system coercivity theorem.
- Chazottes and Hochman's
  [zero-temperature nonconvergence theorem](https://arxiv.org/abs/0907.0081)
  remains the global warning: finite-temperature uniqueness or smoothness
  need not select a uniform cold policy.  The local value estimate (4.4) is
  compatible with that warning because it does not assert selector or Perron-
  vector convergence.
