# Iterated coarse minima: an exact finite quadratic law and its limits

2026-07-21. Status: **exact selected-record audit + exact feasibility
counterexample + open all-level theorem target**. Nothing here proves the KL
endpoint. The exact finite claims are checked by

```bash
python3 experiments/kl/verify_iterated_minimum_growth.py
python3 experiments/kl/verify_argmin_frustration.py
```

Lean commits `5a8727f` and `786c02e` independently kernel-check the
unconditional coarse-minimum supersolution order and its normalized-defect
data-processing consequence. Commit `38f1497` kernel-checks the reciprocal
telescope and `lambda_k->2` consequence conditional on the selected quadratic
law. Commits `ee37cd9` and `27b9e69` check the exact rowwise joint-minimum
identity, the generic local/summed argmin-frustration lower bound including
ties, and its one-stage canonical specialization. Commit `d4b328b` tracks the
inherited supersolution slack that appears after the first coarse projection.
The canonical frustration implication is only a first-stage fixed-vector
theorem; the all-stage target must control the *increment* of normalized slack.
None of these commits proves that global selected-policy estimate.

The optional `--float-k20` block is explicitly non-exact.

## 1. Indexing and the statistic

At level `k`, use the standard increasing state order

```text
m=2+3i,                    0<=i<3^(k-1).
```

If `x` has length `N=3^ell`, its coarse fiber-minimum profile is

```text
(mathfrak m x)_r = min_(d=0,1,2) x_(r+dN/3),       0<=r<N/3.       (1.1)
```

Starting from `x^(0)=x`, put

```text
x^(j+1)=mathfrak m x^(j),
T_j=sum x^(j),
epsilon_j=1-3T_(j+1)/T_j.                           (1.2)
```

Thus `epsilon_0` is the ordinary normalized terminal excess, and the later
`epsilon_j` are the same statistic after successively deleting highest
ternary digits. No probability normalization is needed: (1.2) is invariant
under scaling at every stage.

For integers, set `E_j=T_j-3T_(j+1)`. The comparison

```text
epsilon_(j+1) >= epsilon_j+(3/2)epsilon_j^2          (1.3)
```

is exactly the integer inequality

```text
2 T_j^2 E_(j+1)
  >= 2 T_(j+1) T_j E_j + 3 T_(j+1) E_j^2.           (1.4)
```

The checker uses (1.4), not floating arithmetic.

## 2. Exact finite result on the selected records

Every adjacent pair of profiles in every selected exact certificate
`k=12,...,19` satisfies (1.3). The smallest exact ratio at each level is:

| `k` | `epsilon_0` | `epsilon_1` | minimum `(epsilon_(j+1)-epsilon_j)/epsilon_j^2` | stage `j` |
|---:|---:|---:|---:|---:|
| 12 | 0.0523781027 | 0.0598303369 | 1.644411750 | 4 |
| 13 | 0.0481832518 | 0.0546740361 | 1.678642863 | 5 |
| 14 | 0.0442644668 | 0.0499731046 | 1.641492305 | 6 |
| 15 | 0.0406992489 | 0.0457312995 | 1.551655682 | 7 |
| 16 | 0.0375185635 | 0.0419901723 | 1.561186722 | 8 |
| 17 | 0.0346626489 | 0.0386513473 | 1.591620467 | 9 |
| 18 | 0.0321136679 | 0.0356943499 | 1.543294688 | 10 |
| 19 | 0.0298058487 | 0.0330349389 | 1.552754264 | 11 |

These are exact rational comparisons rendered in decimal. The script
SHA-checks every certificate manifest and every large sidecar, computes all
profile totals exactly, and checks (1.4) with Python big integers. A bundled C
reducer memory-maps the NPY records and keeps one in-place minimum profile; it
uses unsigned 128-bit totals, while Python performs the larger cross-products.
The default full run takes about three seconds in the current
warm-cache worktree. The `k=16,...,19` sidecars are local and are not in git,
so a fresh clone cannot run those rows.

The uncertified floating `k=20` candidate has minimum ratio
`1.51441702875` at stage 12. This is unusually close to `3/2` and motivated
the displayed constant, but it is orientation only. The exact table is a
post-hoc finite law on eight specially selected records, not an all-level
inequality.

## 3. Why the all-stage statement would settle the endpoint

Here is the clean theorem target.

> **Iterated selected-minimum conjecture.** Let `c_k>0` be an attained exact
> critical vector, `F_(k,lambda_k)c_k=c_k`, with `1<lambda_k<2`. Then its
> profiles (1.1)--(1.2) satisfy (1.3) for every `0<=j<=k-3`.

The omitted `lambda_k=2` case is already the desired endpoint. The displayed
range ensures `epsilon_0>0`. This is stronger than a bound only at the first
coarse projection. It has an immediate telescoping consequence. If `a=3/2`,
then

```text
epsilon_(j+1) >= epsilon_j(1+a epsilon_j)
```

implies

```text
1/epsilon_j-1/epsilon_(j+1)
  >= a/(1+a epsilon_j) >= a/(1+a)=3/5,              (3.1)
```

because `0<epsilon_j<1`. There are `k-2` adjacent comparisons before the
one-point profile. Hence

```text
epsilon_0 <= 5/(3k-1)=O(1/k).                       (3.2)
```

For an exact critical vector, summing the KL equation gives

```text
1-epsilon_0 = 3(lambda_k-1)/lambda_k^alpha,
alpha=log_2(3).                                     (3.3)
```

The right side is strictly increasing on `1<lambda<=2` and equals one only
at `lambda=2`. Thus (3.2) would prove `lambda_k->2`. It would also supply the
missing mean-defect rate in the terminal Pearson program; the separate
anti-concentration estimate would still be needed for a Pearson `O(k^-2)`
law.

## 4. Exact first-stage mismatch formula

The coarse-minimum supersolution has a more local form than its mass identity
alone shows. Write

```text
tau=lambda^-2,
w_2=lambda^(alpha-2),
w_8=lambda^(alpha-1),
b=w_2+w_8.
```

Let `c>0` satisfy `F_(k,lambda)c=c`, let `g=mathfrak m c`, `C=sum c`,
`G=sum g`, and let `epsilon_0,epsilon_1` be (1.2). Group the three fine
equations lying above one coarse output row `r`. Fine transport permutes the
three members of one transport-source fiber. On a branch row of type
`beta in {2,8}`, the three fine branch targets likewise permute the three
members of the corresponding coarse branch fiber, and each fine branch
minimum is the appropriate entry of `g`.

After subtracting the two separate minima, there are nonnegative triples
`A_(r,d),Z_(r,d)` and permutations of their indices such that

```text
h_r := g_r-F_(k-1,lambda)(g)_r
     = min_d (tau A_(r,d)+w_beta Z_(r,d)).           (4.1)
```

Here `A` is the transport-source fiber above its minimum and `Z` is the
coarse branch-target fiber of `g` above its minimum. On neutral rows,
`h_r=0`. Consequently

```text
sum_r h_r = (bG/3)(epsilon_1-epsilon_0).             (4.2)
```

Equation (4.2) is equivalent to the normalized identity

```text
sum(q-F_(k-1,lambda)q)
  = (b/3)(epsilon(q)-epsilon_0),    q=g/G.           (4.3)
```

The first-stage case of (1.3) is therefore exactly the global anti-alignment
inequality

```text
sum_(branch r) min_d(tau A_(r,d)+w_beta Z_(r,d))
  >= (bG/2) epsilon_0^2.                            (4.4)
```

This is the sharply reduced algebraic target. There is no unconditional
local sum-of-squares or rearrangement proof: the summand in (4.1) vanishes
whenever the two triples share a minimizing index, regardless of their total
variation. The qualitative strict-lift proof shows that all mismatch cannot
vanish for a selected exact critical vector, but its transport-cycle
propagation loses powers as small as `tau^(3^(k-1))`. A dimension-free proof
of (4.4) must therefore establish global quantitative anti-alignment of the
selected argmin policy, or an equivalent conditional-variance/information
bound. The later-stage cases of (1.3) require a block version of this argument
applied back to the original critical equation: the iterated minimum profiles
are supersolutions, not themselves critical eigenvectors.

### 4.1 A label-extended frustration lower bound

The local mismatch has a useful exact lower bound suggested by synchronization
and connection-Laplacian methods.  Index the fibers of `c` by `u`, the fibers
of `g` by `v`, and retain canonical digit labels in `F_3`.  Each coarse branch
row `r` joins its transport-source fiber `u(r)` to its branch-target fiber
`v(r)`.  The two carry maps induce a permutation

```text
pi_r in S_3=AGL(1,F_3)
```

between their digit labels.  Thus the branch rows form a bipartite gain graph.
Its label extension has vertices `(u,a)` and `(v,z)`, with the three allowed
lifted edges `(u,a)--(v,pi_r(a))` above `r`.

Let `sigma(A),sigma(Z)` be deterministic minimizing labels and let
`gamma(A),gamma(Z)` be the second-smallest entries of the two
minimum-subtracted triples.  Define the edge conductance and the frustration
of the section selected by `c` by

```text
omega_r = min(tau gamma(A_r),w_beta gamma(Z_r)),
Fr(c) = sum_(branch r) omega_r
          1{sigma(Z_r) != pi_r(sigma(A_r))}.        (4.5)
```

If either triple has two minima, the corresponding second gap is zero.  If
both minima are unique and their labels disagree, every digit in (4.1) pays
at least one of the two weighted second gaps.  Therefore, without any
uniqueness assumption,

```text
min_d(tau A_(r,d)+w_beta Z_(r,pi_r(d)))
  >= omega_r 1{sigma(Z_r) != pi_r(sigma(A_r))},
sum_r h_r >= Fr(c).                                 (4.6)
```

Consequently the selection-specific estimate

```text
Fr(c) >= (bG/2) epsilon_0^2                         (4.7)
```

would imply (4.4) immediately.  The factor `1/2` is also the sharp elementary
constant for the two nonminimal coordinates,
`a^2+b^2>=(a+b)^2/2`; after division by the `bG/3` in (4.2), it becomes the
observed `3/2`.

Run

```bash
python3 experiments/kl/verify_argmin_frustration.py
```

for an exact bounded test of (4.7).  The checker derives every edge signature
from the residue maps, checks the closed index formulas and lift permutations,
exhausts a finite tied-argmin regression for (4.6), SHA-pins the selected
certificate inputs, and clears all denominators using the rationally
tightened certificate weights.  Its complete pinned reductions give:

| `k` | mismatching edges / branch edges | `Fr / ((bG/2)epsilon_0^2)` | `Fr / sum h` |
|---:|---:|---:|---:|
| 12 | 0.671848804 | 1.058359414 | 0.584436680 |
| 13 | 0.671323816 | 1.103163269 | 0.591869672 |
| 14 | 0.669469424 | 1.156422184 | 0.595368237 |
| 15 | 0.668907743 | 1.212688337 | 0.598781390 |

These are finite exact rational comparisons on the tightened feasible
certificate vectors, not exact critical eigenvectors or an all-level result.
They are nevertheless a stronger diagnostic than the total-defect fit: the
simple second-gap frustration alone already clears the full first-stage
quadratic target, narrowly at `k=12` and by a growing margin thereafter.

The qualification “first-stage” is load-bearing. If `S_f,S_c` denote Lean's
normalized slacks of a fine profile and its coarse minimum, `delta_f,delta_c`
their normalized defects, and `b=w_2+w_8`, the exact arbitrary-profile balance
is

```text
S_f-S_c=b(delta_c-delta_f).                         (4.8)
```

With `epsilon_f=3delta_f`, the desired next-stage law is therefore equivalent
to

```text
S_f-S_c >= (b/2)epsilon_f^2.                        (4.9)
```

For a supersolution Lean's `S` is nonpositive, so (4.9) asks for newly created
normalized super-slack, not merely a lower bound on total coarse slack. After
one projection the inherited pointwise term `x-Fx` lies inside the new fiber
minimum and can change its selected label. Thus (4.7) alone cannot simply be
iterated. Commit `d4b328b` kernel-checks the exact inherited-slack row identity
and supersolution preservation; the still-unproved mathematical burden is
the selected all-stage estimate (4.9), or a valid local theorem implying it.

There is an important structural limitation.  As an abstract graph this
bipartite system has flat label sections; its minimum frustration is zero.
Off-the-shelf magnetic Cheeger theory therefore does not prove (4.7).  The
missing theorem must use that both the section and the conductances come from
the same selected critical solution, and show that this endogenous section is
quantitatively far from the flat ones.  Connection-Laplacian synchronization
and cyclic-signature frustration inequalities provide a precise external
language for that question; see
[Bandeira--Singer--Spielman](https://arxiv.org/abs/1204.3873) and
[Lange--Liu--Peyerimhoff--Post](https://arxiv.org/abs/1502.06299).  The
selection-specific anti-alignment step is new.

## 5. Exact no-go outside the selected-critical class

The candidate is false for generic positive vectors and is not a consequence
of KL feasibility. In the standard level-three order

```text
(2,5,8,11,14,17,20,23,26),
```

take `lambda=1001/1000` and

```text
C=(487,1916,458,1178,485,777,1920,1175,1603).       (5.1)
```

Use the rationally tightened weights

```text
tau=lambda^-2,       W_2=lambda^-1,       W_8=1.
```

The checker verifies all nine inequalities `C_m<=(F_tight C)_m` exactly; the
smallest margin is

```text
166084/1002001 > 0.                                 (5.2)
```

This proves feasibility for the true KL operator without evaluating a
transcendental number. Indeed `2<3<4` gives `1<alpha<2`, and, since
`lambda>1`,

```text
lambda^(alpha-2)>lambda^-1,
lambda^(alpha-1)>1.
```

The three fiber minima of (5.1), in the orientation (1.1), are

```text
g=(487,485,458).
```

Direct integer arithmetic gives

```text
epsilon(C)=173/303,
epsilon(g)=28/715 < epsilon(C).                     (5.3)
```

Thus strict positivity and even strict KL feasibility do not imply
monotonicity of iterated terminal excess, much less (1.3). Supersolutions
alone are also insufficient for a positive bound in (4.3): at any attained
lower-level critical pair `F_(ell,lambda_ell)q=q`, its left side and
`epsilon(q)-epsilon(lambda_ell)` are exactly zero while the critical terminal
excess is positive.

What remains open is deliberately narrow: the all-stage inequality for the
minima of the **selected exact fine critical eigenvector**, or another
dimension-free consequence of the same global argmin-policy coupling. The
finite records make `3/2` a concrete regression constant; the counterexample
prevents promoting it to a cone theorem.
