# Exact multiscale genealogy of the KL feasible vectors

**Status (2026-07-21): exact finite diagnostic, not a limit theorem.**

The scalar depth-nine pressure split failed because a few individual parents
put too much mass into one child.  That is a supremum-over-parents
obstruction.  This audit asks a different question: after weighting by the
actual exact feasible vector, does the *total* high-oscillation mass contract
as one descends its 3-adic refinement genealogy?

For the eight certified feasible subeigenvectors at `k=12,...,19`, the answer
is strikingly favorable on the tested threshold grid.  It is still finite
evidence.  The vectors are feasible points satisfying `c <= F_lambda(c)`, not
certified exact critical eigenfunctions, and no all-level inequality is
claimed here.

## 1. Exact object

Index a level-`k` certificate by `i=(m-2)/3`, and, inside that one fixed
vector, define

```text
A_j(p) = sum { C[i] : i = p mod 3^(j-1) },       1 <= j <= k.
```

Thus `A_k=C`.  A node `p` at depth `j` has the three children
`p+d*3^(j-1)`, `d=0,1,2`, and their masses sum exactly to `A_j(p)`.  Define
the normalized child oscillation

```text
omega_j(p) = 3 (max_d A_(j+1)(p+d3^(j-1))
                  - min_d A_(j+1)(p+d3^(j-1))) / A_j(p).
```

At `j=k-1` this is the ordinary one-step fiber oscillation.  Weighting a
depth-`j` node by `A_j(p)` gives the induced coarse marginal of certificate
mass; only at `j=k-1` is this exactly the measure `nu_k` used in Proposition
R'. For a rational threshold `t`, set

```text
M_(k,j)(t) = sum_p A_j(p) 1[omega_j(p)>t] / sum_i C[i].
```

The inequality is strict; equality with `t` is classified as low.  For parent
threshold `s` and child threshold `t`, split the child high mass according to
whether its parent is high or low.  When `M_(k,j)(s)>0`, put

```text
qbar_(k,j)(s,t)
  = mass {parent high at s, child high at t}
      / mass {parent high at s},

E_(k,j)(s,t)
  = mass {parent low at s, child high at t} / total mass.
```

Then the following is an exact bookkeeping identity, not a modeled
recurrence:

```text
M_(k,j+1)(t) = qbar_(k,j)(s,t) M_(k,j)(s) + E_(k,j)(s,t).
```

The coarser arrays `A_j` are conditional aggregates of one level-`k` vector.
They are not asserted to be feasible points or eigenvectors for the lower
level KL systems.

## 2. Reproduction and trust boundary

Run the exact audit with:

```bash
python3 experiments/kl/multiscale_genealogy.py
```

That full default needs the local `k=16,...,19` sidecars. A fresh clone can
run the portable prefix without overwriting the tracked full tables:

```bash
python3 experiments/kl/multiscale_genealogy.py \
  --levels 12 13 14 15 \
  --tail-output /tmp/multiscale-tail.csv \
  --transition-output /tmp/multiscale-transitions.csv \
  --summary-output /tmp/multiscale-summary.csv
```

The default run verifies source SHA-256 values and writes:

- `analysis_cache/multiscale_tail_exact.csv` — 812 exact tail rows;
- `analysis_cache/multiscale_transitions_exact.csv` — 5,292 exact ordered
  threshold-transition rows, including all four low/high contingency cells
  and child-multiplicity counts;
- `analysis_cache/multiscale_recurrence_summary.csv` — 833 exact summary rows.

The threshold grid is
`{1/20,1/10,3/20,1/5,1/4,3/10,2/5}`.  All classifications, masses, and ratio
numerators and denominators are exact integers.  The implementation guards
every `int64` triple sum, falls back to Python integers before overflow, and
uses radix-`2^20` limbs with binary64 `bincount` only under an explicit
`<2^53` exactness bound.  Built-in tests cover strict threshold boundaries,
totals above `2^63`, and the object-array fallback.

An independent implementation reconstructed the `k=19` total

```text
4,845,180,013,388,557,558,821
```

and the headline finest-scale rows.  A second adversarial code audit checked
the indexing, transition orientation, threshold arithmetic, radix totals, and
overflow paths.  The full local run took about 25 seconds and peaked near
16 GB RSS.  A fresh clone can reproduce `k=12,...,15`; the SHA-pinned
`k=16,...,19` arrays are local ignored sidecars, while their exact aggregate
CSV rows are tracked here.

## 3. Exact finite findings

### 3.1 Every tested diagonal tail is nonincreasing

Across all 756 adjacent-scale rows with equal parent and child threshold,

```text
M_(k,j+1)(t) <= M_(k,j)(t)
```

in every case: zero increases for `k=12,...,19` and all seven thresholds.
This monotonicity is an observed property of these exact vectors, not a
structural identity. For example, the positive length-nine vector
`[10,4,4,1,4,4,1,4,4]` has coarse tail zero and finer tail `1/3` at
`t=1/5` under the same indexing.

Exactly 137 coarse rows are saturated, with both tails equal to one; these are
all the equality cases. Every nonsaturated tested row decreases strictly.
After excluding saturation, the worst observed child-tail/parent-tail ratios
are:

| `t` | equality rows | largest strict ratio | location |
|---:|---:|---:|---:|
| `1/20` | 36 | `4768652659328283563604 / 4778694649534947152591 = 0.997898591364...` | `k=19`, `7 -> 8` |
| `1/10` | 28 | `46805702314422648643 / 47049100452382107460 = 0.994826720689...` | `k=15`, `4 -> 5` |
| `3/20` | 24 | `0.984946463553...` | `k=19`, `4 -> 5` |
| `1/5` | 22 | `0.965058826025...` | `k=13`, `3 -> 4` |
| `1/4` | 11 | `0.992859770109...` | `k=18`, `4 -> 5` |
| `3/10` | 8 | `0.934796391441...` | `k=19`, `4 -> 5` |
| `2/5` | 8 | `0.902735712918...` | `k=17`, `4 -> 5` |

The rounded envelopes `(.999,.995,.99,.98,.995,.95,.95)` in the same
threshold order were chosen after seeing these rows.  They are not evidence
of independent validation; an eventual exact `k=20` certificate would be the
first out-of-sample falsifier.

### 3.2 The finest `t=1/5` recurrence

The transition into the true fiber scale has the following decimal rendering
of exact rational columns:

| `k` | parent tail | fiber tail | closure | `qbar` | `E` | all-three-high parents |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | .2576404 | .1263950 | .490587 | .368593 | .0314304 | 2 |
| 13 | .2045848 | .0974891 | .476522 | .352826 | .0253063 | 2 |
| 14 | .1611619 | .0758310 | .470527 | .346829 | .0199354 | 2 |
| 15 | .1264954 | .0597167 | .472086 | .346787 | .0158497 | 1 |
| 16 | .1007650 | .0470967 | .467392 | .341923 | .0126429 | 5 |
| 17 | .0815642 | .0379001 | .464665 | .341870 | .0100157 | 5 |
| 18 | .0660830 | .0306214 | .463378 | .339776 | .0081680 | 19 |
| 19 | .0535622 | .0248165 | .463322 | .335470 | .00684801 | 66 |

At `k=19`, the exact parent and child high masses are

```text
259,518,339,914,879,806,909
120,240,487,870,809,445,780.
```

Of the child mass, `87,060,665,601,245,638,356` descends from high parents and
`33,179,822,269,563,807,424` immigrates from low parents.  Hence the ancestry
share of the fiber tail is `0.724054493980...`.

### 3.3 Pointwise failure versus mass-averaged promise

At the final `k=19,t=1/5` transition, 66 high parents have all three children
high.  Thus the pointwise worst-case retention is exactly one, so a proof that
takes the supremum over individual parents cannot contract at this threshold.
But those 66 nodes carry only

```text
249,432,985,312,043,880 / 259,518,339,914,879,806,909
  = 0.000961138182...
```

of high-parent mass.  The mass-averaged retention is `0.335470185382...`.
This is the main strategic signal: retain the genealogy and its mass
distribution instead of replacing it by the single worst child.

At `t=3/10`, the `k=19` fiber tail is `0.00361238662821...`, the final closure
ratio is `0.282737512308...`, `qbar=0.213158275638...`, and
`E=0.000888976853819...`.  No all-three-high parent occurs at the final scale
for any tested `k=12,...,19`.  That finite absence is not a uniform theorem.

### 3.4 Cross-level terminal tails

For orientation, the exact CSVs render the following terminal tails:

| `k` | `t=.1` | `t=.2` | `t=.3` | `t=.4` |
|---:|---:|---:|---:|---:|
| 12 | .4957689181 | .1263949891 | .02247204868 | .0007408930 |
| 13 | .4372666363 | .09748913694 | .01517020849 | .0005312324 |
| 14 | .3767047524 | .07583102824 | .01196848993 | .0001901685 |
| 15 | .3205134093 | .05971666283 | .00891082755 | .0000888715 |
| 16 | .2719070901 | .04709673466 | .006982705478 | .0000692243 |
| 17 | .2305877415 | .03790006685 | .005454280157 | .0000353257 |
| 18 | .1951399123 | .03062141714 | .004390859521 | .0000177158 |
| 19 | .1649428408 | .02481651611 | .003612386628 | .0000080831 |

They decrease over the measured range.  The table does not establish a limit,
a rate, or even monotonicity for future selected vectors.

## 4. A theorem-shaped target

The exact identity isolates a sufficient package.  Fix `t`.  If there are
`rho<1` and a starting depth `j0` such that, uniformly for every relevant
`k>=j+2` and `j0 <= j <= k-2`,

```text
qbar_(k,j)(t,t) <= rho,
E_(k,j)(t,t) <= e_j,                  with e_j -> 0,
```

then unrolling gives

```text
M_(k,k-1)(t)
  <= rho^(k-1-j0)
     + sum_(j=j0)^(k-2) rho^(k-2-j) e_j  -> 0.
```

A version in which contraction begins at depths `j0(k)` also works provided
`k-j0(k)->infinity` and the corresponding error convolution vanishes.  Either
form supplies localization for this one threshold.  Proposition R' needs the
result for every positive rational `t`, or enough thresholds tending to zero,
as well as an all-level family of appropriate KL vectors and the pressure
bridge.  The CSV does none of those things.

For the triangular `k,j` data, a terminal-offset formulation is more natural
than an absolute-depth envelope. If `V_(k,j)` is a weighted high-bin potential,
`eta_(k,j)` its weighted low-to-high immigration, and

```text
V_(k,j+1) <= rho V_(k,j) + eta_(k,j),       rho < 1,
```

then it is enough that, for every fixed terminal offset `ell>=0`,

```text
eta_(k,k-2-ell) -> 0                         as k -> infinity.
```

Indeed, if the cone starts at a fixed depth `j0` and all high weights lie in
`[1,W]`, then

```text
M_(k,k-1)(t) <= V_(k,k-1)
  <= W rho^(k-1-j0)
     + sum_(ell=0)^(k-2-j0) rho^ell eta_(k,k-2-ell).
```

The last sum tends to zero by dominated convergence, because automatically
`0<=eta<=W`. This reduces the immigration target to convergence along each
fixed distance from the true fiber scale; it does not prove that convergence.

A fixed absolute burn-in is stronger than necessary. Let `b_k` be the start
of a terminal window and suppose the same recurrence holds for
`b_k<=j<=k-2`, with `k-1-b_k -> infinity`. The identical proof still works:
the initial term is at most `W rho^(k-1-b_k)`, and fixed-terminal-offset
immigration is convolved against the same summable geometric kernel. Thus even
a slowly expanding terminal window would suffice.

The rowwise cone can also be weakened. For nonnegative depth-dependent factors
`r_(k,j)` and a mass-weighted cone defect `zeta_(k,j)`, write

```text
V_(k,j+1) <= r_(k,j) V_(k,j) + eta_(k,j) + zeta_(k,j).
```

For a proposed factor `r_(k,j)` and high-block row `Q`, one admissible defect is

```text
zeta_(k,j) = sum_(a high) mu_(k,j)(a)
              [(Q_(k,j) w)_a - r_(k,j) w_a]_+.
```

If the backward products of the `r`'s are dominated by one summable sequence,
the full-window product tends to zero, the errors are uniformly bounded, and
both `eta` and `zeta` tend to zero at every fixed terminal offset, the same
dominated-convergence argument gives terminal localization. This formulation
can ignore rare bad rows through their actual mass-weighted excess; it does not
require worst-row contraction.

### 4.1 A summable martingale-increment target

There is an exact martingale restatement of the immigration seam. Work on one
common copy of `Z_3` with Haar probability `H`, extend each normalized finite
certificate density `f_k=d mu_k/dH` as a cylinder function, and let `F_j` be
the sigma-field generated by the first `j` ternary digits, so its atoms carry
the masses `A_(j+1)`. Set

```text
f_(k,j) = E_H[d mu_k/dH | F_j],
Delta_(k,j) = ||f_(k,j)-f_(k,j-1)||_L1(H).
```

For the three conditional child probabilities at a depth-`j` parent, an exact
three-number estimate gives

```text
(9/4) Delta_(k,j) <= E_(mu_k)[omega_(k,j)] <= 3 Delta_(k,j),
M_(k,j)(t) <= 3 Delta_(k,j)/t.
```

Consequently `eta_(k,j) <= 3W Delta_(k,j+1)/t`. Relative compactness in `L1` of
the selected densities would make conditional expectations converge uniformly
on that compact set. It would force `Delta_(k,j_k)->0` whenever `j_k->infinity`
and would directly close both terminal tails and immigration. This is only a
reduction:
fixed-depth convergence, weak convergence, bounded entropy, or even uniform
`L-infinity` bounds do not control a moving terminal digit without cross-level
coherence. The counterexample whose density depends only on the newest ternary
digit has perfectly flat earlier marginals and a permanent terminal defect.
With natural logarithms and `Ent_H(f)=integral f log(f) dH`, an entropy variant
sets

```text
h_(k,j) = Ent_H(f_(k,j)) - Ent_H(f_(k,j-1))
        = E_(mu_k)[D(p_children || uniform_3)].
```

The chain rule gives `Ent_H(f_k)=sum_j h_(k,j)`, while conditional Pinsker and
Jensen give `Delta_(k,j)^2<=2h_(k,j)`. There is also a sharp range form. If
`R=max_i p_i-min_i p_i` and `omega=3R`, the entropy variational formula with
the test values `(1,0,-1)` gives

```text
D(p || uniform_3) >= (3/4) R^2 = omega^2/12,
M_(k,j)(t) <= min(1, 12 h_(k,j)/t^2).
```

For the first inequality, bound
`(1+2 cosh(theta))/3 <= exp(theta^2/3)` coefficientwise and optimize at
`theta=3R/2`. The constant `12` is sharp to second order at
`p=(1/3-epsilon,1/3,1/3+epsilon)`.

There is now an exact finite audit of the increments themselves. Since the
atoms of `F_j` carry the masses `A_(j+1)`, integer arithmetic gives

```text
Delta_(k,j)
  = sum_children |3 A_(j+1) - A_j| / (3 sum_i C[i]).
```

Run:

```bash
python3 experiments/kl/verify_martingale_increment_envelope.py
```

A fresh clone can run the tracked prefix without replacing the full artifact:

```bash
python3 experiments/kl/verify_martingale_increment_envelope.py \
  --levels 12 13 14 15 --output /tmp/martingale-increments.csv
```

The verifier records the tracked inline-manifest hashes, verifies every
sidecar against its manifest SHA, checks all 116 exact increments for
`k=12,...,19`, and writes
`analysis_cache/martingale_increments_exact.csv`. The floating `k=20` audit in
`audit_float_k20_weighted_cone.py` writes the separate 19-row
`float_k20_martingale_increments.csv` table. An independent base-`2^32` limb
implementation reproduced every fraction, index, and source hash; the two
output SHA-256 values are `069dcf1623b04bc...` and `f3959866949c5fdd...`.
Every exact row at `j>=2`, and
every corresponding floating row, fits the deliberately simple post-hoc
envelope

```text
Delta_(k,j) <= (1/2) (9/10)^j.                 (finite calibration)
```

The worst exact ratio to this envelope is `.880784634` at `(k,j)=(19,2)`;
the floating `k=20` ratio is `.888668693`, again at `j=2`. Depth one is not in
the calibrated scope: its floating ratio is already `.994226449`, and coarse
depth is irrelevant to the terminal conclusion. The exponent `.9` is not
canonical. The finite scale/rate Pareto comparison is:

| `q` | exact `C_2(q)=max Delta/q^j` | active exact depth | floating `k=20` `C_2(q)` |
|---:|---:|---:|---:|
| `.85` | `.520822` | 15 | `.561354` |
| `.86` | `.482312` | 2 | `.486629` |
| `.88` | `.460638` | 2 | `.464761` |
| `.90` | `.440392` | 2 | `.444334` |
| `.92` | `.421453` | 2 | `.425225` |

Thus `(C,q)=(1/2,.9)` is a readable interior point, not an optimized law.
It was chosen after the floating vector had already been inspected; only a
future level can test it out of sample.

The annealed-floor argument below gives a stronger retrospective warning:
although every stated finite comparison is correct, this particular geometric
law cannot extend to a localizing critical or aggregate-slack-vanishing family.
The exact limiting floor already exceeds it at depth two.

The triangular trend is qualitatively compatible with a limiting density.
At every fixed depth `j=1,...,11`, `Delta_(k,j)` strictly increases through
the exact levels, but at each fixed terminal offset zero through four it
strictly decreases. At offsets zero through four the rows are

```text
k=12 exact: .0442916, .0558902, .0736882, .0916196, .109586
k=19 exact: .0246961, .0296746, .0374004, .0454960, .0534720
k=20 float: .0228944, .0273694, .0343411, .0416812, .0489149.
```

Any all-level estimate `Delta_(k,j)<=a_j` with `sum_j a_j<infinity` would be
decisive. (The displayed geometric choice is now known not to be such an
estimate.) Martingale telescoping gives, uniformly in `k`,

```text
||f_k - E[f_k | F_J]||_1 <= sum_(j>J) a_j.
```

The right side tends to zero, while the conditional expectations live in a
fixed finite-dimensional space. Hence the densities are relatively compact
in `L1`, all moving increments vanish, and the tail and immigration bounds
above close. For the displayed envelope the residual is at most
`5(9/10)^(J+1)` for `J>=1`. Equivalently, on the compact group `Z_3`, relative
`L1` compactness is uniform approximation by these conditional expectations,
or uniform translation continuity under `3^J Z_3`.

This summable-increment condition is sufficient, not necessary: a compact
family can have nonsummable `L1` martingale differences. Uniform integrability,
bounded entropy, fixed-depth convergence, and weak convergence are weaker and
do not control a newest-digit defect.

#### Entropy calibration and exact monotonicity obstruction

A second verifier computes the natural-log chain-rule increments:

```bash
python3 experiments/kl/verify_entropy_increment_envelope.py
```

A fresh clone can run the tracked prefix separately:

```bash
python3 experiments/kl/verify_entropy_increment_envelope.py \
  --levels 12 13 14 15 --output /tmp/entropy-increments.csv
```

The input masses and all coarsenings are exact integers, and the same manifest
and sidecar hashes are checked as above. The logarithms and output increments
are binary64, evaluated with a stable nonnegative KL kernel. Thus
`entropy_increments_exact.csv` is a floating diagnostic on exact inputs, not a
rational certificate. Its 116 rows have SHA-256
`8850a350801b4763...`. The pinned but uncertified floating `k=20` pass writes
19 more rows to `float_k20_entropy_increments.csv`, SHA-256
`b0c0e09a81a45a25...`.

Every one of the 135 observed rows fits the deliberately simple post-hoc
envelope

```text
h_(k,j) <= (1/5) (3/4)^j.                       (finite calibration)
```

The worst exact ratio is `.939571383` at `(k,j)=(19,1)`; the floating `k=20`
ratio is `.950720798`, also at `j=1`. This is not an out-of-sample success. At
fixed rate `.75`, the tight scale fitted through exact `k=19` is about
`.187914`, and floating `k=20` raises it to `.190144`, a `1.19%` overrun. The
round scale `.2` merely leaves a readable finite margin; future exact levels
are the first genuine tests.

As with the martingale fit, the annealed-floor argument below shows that this
specific geometric constant cannot be the all-level endpoint law. The table
remains an honest floating-log diagnostic of the finite exact inputs.

The finite triangular pattern is strong but selection-specific. Within every
observed level, `h_(k,j)` strictly decreases with depth. Every shared fixed
depth `j=1,...,11` increases across levels, while all eleven shared fixed
terminal offsets decrease. Total entropy rises

```text
k=12 exact:  .324539499
k=19 exact:  .444583263
k=20 float:  .459210510.
```

These numbers do not establish bounded or sublinear entropy. Counterfactually,
if the displayed geometric envelope held uniformly, then

```text
D(f_k || f_(k,J)) = sum_(j>J) h_(k,j)
                  <= (4/5)(3/4)^(J+1),
||f_k-f_(k,J)||_1 <= sqrt((8/5)(3/4)^(J+1)).
```

This would give the same relative `L1` compactness and localization as the
summable `Delta` envelope. More generally, if `b_j->infinity` and

```text
sup_k sum_j b_j h_(k,j) <= C,
b_*(J) = inf_(j>J) b_j,
```

then the same calculation gives
`||f_k-f_(k,J)||_1<=sqrt(2C/b_*(J))`. For terminal localization alone, the
triangular condition `B_k/b_(k-1-ell)->0` at every fixed `ell`, where
`B_k=sum_j b_j h_(k,j)`, is enough.

There is an even weaker selection-specific endpoint theorem. Put `n=k-1`. If
one proves for a selected all-level family that

```text
h_(k,1) >= ... >= h_(k,n) >= 0,
Ent_H(f_k) = o(n),
```

then `j h_(k,j)<=Ent_H(f_k)`, so every fixed terminal-offset entropy increment
and hence every corresponding `Delta` tends to zero. For critical
eigenvectors, `2delta<=Delta_terminal` then closes `lambda_k->2`; selected
feasible points still require vanishing aggregate normalized slack.

Crucially, KL feasibility alone cannot supply the monotonicity premise. Run

```bash
python3 experiments/kl/verify_entropy_monotonicity_counterexample.py
```

At `k=3`, `lambda=1001/1000`, in the standard coordinate order, the positive
vector

```text
(101,100,75, 101,100,75, 101,100,150)
```

satisfies all nine KL feasibility rows strictly. The checker replaces the two
irrational branch weights by the stricter rational lower bounds
`lambda^-1` and `1`; the minimum exact margin is `799900/1002001`. Its first
digit masses are `(303,300,300)`, while its only nonuniform terminal fiber is
`(75,75,150)`. The elementary bounds `D<=chi^2` and
`log(9/8)>1/9` give exactly

```text
h_1 < 2/90601 < 50/2709 < h_2.
```

This refutes entropy-depth monotonicity on the full feasible cone. By itself it
does not refute monotonicity or an endpoint-Cesaro estimate for a canonical
selection. The separate annealed-floor argument below does refute the displayed
geometric constant for critical and aggregate-slack-vanishing localizing
families.

#### Partial-annealing identity and limitation

One possible route to such a selection theorem is a partial-annealing
deformation. For child masses `x=(x_0,x_1,x_2)`, set

```text
M_t(x) = ((x_0^t+x_1^t+x_2^t)/3)^(1/t).
```

Then, exactly,

```text
d/dt log M_t(x)|_(t=1) = D(p_x || uniform_3).
```

Thus if `Z_(k,j)(t)` is the sum of `M_t` over all depth-`j` parent fibers,
then `Z_(k,j)(1)=sum C/3` and
`h_(k,j)=d/dt log Z_(k,j)(t)|_(t=1)`. At the terminal fibers, keep the KL
weights `q_0=lambda^-2,q_2=w_2,q_8=w_8` fixed and replace only each hard fiber
minimum by `M_t`. If

```text
R_c(t) = sum F_(lambda,t)(c) / sum c,
```

the branch bijections give
`R_c(t)=q_0+(q_2+q_8)Z_(k,k-1)(t)/sum c`, and hence

```text
d/dt log R_c(t)|_(t=1)
  = (w_2+w_8) h_(k,k-1) / (3 s(lambda)).
```

This is a genuine local bridge, not yet a pressure proof for the hard-min
critical vector. In fact, for
`p_i(t)=x_i^t/sum_l x_l^t`, the full identity is

```text
d/dt log M_t(x) = D(p(t) || uniform_3)/t^2.
```

The `t=1` endpoint therefore does not control the finite path to
`t=-infinity`, where `M_t` becomes the minimum, without estimates along the
whole deformation. Nor is `R_c(t)` generally a spectral radius for a selected
hard-min certificate; a spectral derivative at `t=1` uses the annealed
operator's right Perron vector. The entropy rate in the existing
policy-pressure formula is
also a different object: its equilibrium measure weights coordinates by a
left Perron vector times `c`, whereas the spatial genealogy weights them by
`c/sum c`. No uniform comparison of those measures is known. A successful
pressure revival therefore needs a new cross-scale partial-annealing
comparison; ordinary path entropy cannot simply be substituted for the
spatial increments above.

Finally, the increment connects directly to the KL endpoint. On one terminal
fiber, if `p_i` are the three conditional probabilities, put
`a=1/3-min_i p_i` and `d=sum_i |p_i-1/3|`. The sharp elementary inequalities
`2a<=d<=4a` give

```text
2 delta(c) <= Delta_(k,k-1) <= 4 delta(c).
```

For a feasible pair define its aggregate normalized slack

```text
Sigma(c,lambda) = sum_m (F_lambda(c)_m-c_m) / sum_m c_m.
```

Column-sum bookkeeping gives the exact bridge

```text
s(lambda)-1 = (w_2+w_8) delta(c) + Sigma(c,lambda).
```

Thus an all-level summable increment envelope closes `lambda_k->2` for exact
critical eigenvectors (`Sigma=0`), or for a selected near-critical feasible
family if `Sigma_k->0`. The present integer certificates are merely selected
finite feasible points; neither the all-level envelope nor vanishing
normalized slack has been proved.

#### Annealed floor and a polynomial Pearson-energy replacement

For endpoint sequences in the KL range `1<lambda_k<=2`, the two fitted
geometric constants can now be ruled out at independently audited
research-proof level, without disputing any finite row above. Let
`A_lambda^(k)` be the linear KL
operator obtained by replacing every three-fiber minimum by its arithmetic
mean. If `T_(k->ell)` aggregates the highest ternary digits, direct residue
indexing gives the exact intertwining identity

```text
T_(k->ell) A_lambda^(k) = A_lambda^(ell) T_(k->ell).
```

For a normalized critical or feasible vector, put

```text
d_k = A_(lambda_k)^(k) c_k - c_k >= 0.
```

The annealed column sum is `s(lambda_k)`, so
`||d_k||_1=s(lambda_k)-1`. For critical vectors the normalized nonlinear
slack is zero; for a feasible family assume it tends to zero. Terminal
localization and the exact identity
`s-1=(w_2+w_8)delta+Sigma` then force `lambda_k->2` and
`||d_k||_1->0`. At any fixed level `ell`, intertwining yields

```text
A_(lambda_k)^(ell) T_(k->ell)c_k - T_(k->ell)c_k
  = T_(k->ell)d_k -> 0.
```

Compactness of the fixed simplex and continuity therefore make every limit
point a normalized fixed vector of `A_2^(ell)`. Its transport edges form one
full cycle, so the nonnegative stochastic matrix is irreducible and its
normalized right Perron vector `r_ell` is unique. Consequently every fixed
marginal converges to this projectively consistent **annealed floor**.

The first two floor values already contradict the displayed fits. In state
order `[2,5,8]`,

```text
r_2 = (8,2,11)/21.
```

For `h_1=sum_i r_2(i) log(3r_2(i))`, rational bounds from the atanh series give

```text
h_1 > 6431/39690 > 3/20 = (1/5)(3/4),
```

with certified margin greater than `191/15876`. At the next level, in state
order `[2,5,...,26]`, the common denominator is `87381` and the numerators are

```text
(9632,4316,5240,6392,2408,17246,17264,1598,23285).
```

This vector projects to `r_2`, and its exact second martingale increment is

```text
Delta_2 = 622/1533 > 81/200 = (1/2)(9/10)^2,
```

with margin `227/306600`. Run the finite-core checker with

```bash
python3 experiments/kl/verify_annealed_envelope_floor.py
```

It checks the complete local quotient/carry reduction behind the general
intertwining identity, full symbolic-weight matrices through `k=8`, the exact
low-level Perron vectors and projectivity, and both rational inequalities. The
all-level convergence implication is the index/compactness/Perron argument
above and has received an independent research-side audit; Lean formalization
has been requested but is not yet complete. The conclusion is precisely scoped:
the two displayed
constants fail for a critical localizing family, or for a feasible localizing
family whose aggregate normalized slack vanishes. This does **not** refute
relative `L1` compactness, a looser summable law, polynomial entropy control,
or a direct selected-family endpoint argument.

A replacement diagnostic avoids logarithms and supplies a conservative finite
scale for the selected records. For one parent with children
`x_0,x_1,x_2`, put

```text
P = x_0+x_1+x_2,
N = sum_i (3x_i-P)^2,
chi_(k,j) = (1/(3T)) sum_parent N/P,       T=sum_i C[i].
```

This is the parent-mass average of `chi^2(p_children || uniform_3)`, and the
elementary inequality `log u<=u-1` gives `h_(k,j)<=chi_(k,j)`. To certify it
without a gigantic rational common denominator, write `N=qP+r` at every
parent. Then

```text
sum q/(3T) <= chi_(k,j)
             <= sum(q + 1_(r!=0))/(3T).
```

The endpoints and every decision are exact integers. Run

```bash
python3 experiments/kl/verify_chi_square_envelope.py
```

or, in a fresh clone without the larger local sidecars,

```bash
python3 experiments/kl/verify_chi_square_envelope.py \
  --levels 12 13 14 15 --output /tmp/chi-square-intervals.csv
```

The full SHA-pinned `k=12,...,19` audit writes the 116-row
`analysis_cache/chi_square_intervals_exact.csv`, SHA-256
`907c847e69cc6b0f...`. A tracked C++ helper uses
unsigned 128-bit arithmetic only while the proved bound `N<=6P^2` is safe,
then hands the short coarse tail to Python big integers. Synthetic cases,
including the dynamic safety stop, and the complete `k=12` record are
cross-checked against a plain Python-bigint implementation.

Every interval lies below the post-hoc selected-data fit `2/j^2`; its worst
certified upper ratio is `.850145269956` at `(k,j)=(19,8)`. This is explicitly
a finite fit and is not promoted to the theorem target. The deliberately
looser replacement calibration is

```text
chi_(k,j) <= 6/j^2,                         (finite calibration)
```

whose worst certified upper-bound ratio is `.283381756652` at the same row. It was
also screened against exploratory annealed profiles, but remains finite
evidence rather than an all-level theorem or a proved asymptotic constant. The
certified intervals separate all three observed trends: they decrease within
every level, rise at every shared fixed depth, and fall at every shared fixed
terminal offset.

The endpoint audit has since exposed a relevant global collision mechanism,
but not an explanation of those local exploratory profiles. Resolving the
`lambda=2` annealed isometric return gives
blocks `P(E=e)=2^-e`, `H_e(x)=(3x+b_e)/2^e`, with Shannon entropy
`log 4` but Renyi-2 mass exactly `1/3`. Its global collision energy has a
symmetric-stochastic-kernel renewal, but an independently audited sparse-product
derivation with a bounded exact core shows that even `Q_j=Theta(j)` does not
generically imply local Pearson decay. The first
annealed detail shell also has normalized squared-`L2` energy ratio
`1605/1387>1` in one exact direction. Late numerical windows are compatible with a mixed
exponential/power decay, so `6/j^2` is an upper-envelope candidate, not a
claimed annealed asymptotic. See
`docs/notes/annealed-critical-coding.md` and run
`experiments/kl/verify_annealed_critical_coding.py`.

If the constant-six law held uniformly for a suitable selected all-level
family, then `h<=chi` and `sum_(j>J)j^-2<=1/J` would give

```text
sum_(j>J) h_(k,j) <= 6/J,
||f_k-E[f_k|F_J]||_1 <= sqrt(12/J).
```

For a ternary fiber, putting `a=1/3-min p` gives the sharp bounds

```text
(9/2)a^2 <= chi(p) <= 18a^2 <= 6a.
```

Thus the terminal Pearson route needs both a selected mean-defect rate such as
`E[a]=O(1/k)` and the level-uniform anti-concentration estimate
`E[a^2]<=K(E[a])^2`, with `K` independent of the level. Qualitative endpoint
convergence only needs `E[a]->0` for exact critical vectors; merely feasible
vectors also need aggregate normalized slack tending to zero. The direct alternative is
regularity for the audited research-side nonlinear renewal-min fixed-point system derived in
the critical-coding note. Neither is proved. The polynomial rate remains a
deliberately conservative finite target rather than a consequence of the
annealed collision identity.

#### Exact terminal calibration of both missing inputs

The separate streamed checker

```bash
python3 experiments/kl/verify_terminal_defect_statistics.py
```

computes the terminal mean and second moment directly from the selected exact
certificates. On every `k=12,...,19` record it proves, by rational
comparisons,

```text
delta_k < 0.21/k,
E[a^2] < 1.533 delta_k^2,
chi_terminal < 0.483/k^2.                 (finite calibration)
```

This is the first single audit to monitor both hypotheses in the preceding
paragraph, but the constants are post-hoc. In particular,
`E[a^2]/delta^2` rises at every tested level, from `1.36411` to `1.53221`.
The window therefore supports the terminal program without proving a uniform
anti-concentration constant.

There is a useful exact interpretation. If `mu` is the normalized terminal
parent profile, `epsilon=3delta`, and `v` is the normalized profile of
`P-3min`, then

```text
E[a^2]/delta^2 = sum v^2/mu = 1+chi^2(v || mu).
```

The general-parameter renewal tower sharpens this. If `q` is the normalized
minimum profile and `theta=1-epsilon`, then

```text
chi^2(q || mu)
  = (epsilon^2/theta^2)(E[a^2]/delta^2-1).
```

Thus the desired constant is precisely an `O(epsilon^2)` chi-square closeness
theorem between the selected minimum profile and its renewed parent profile.
The automatic Radon--Nikodym martingale estimate is only
`chi^2(q||mu)<=epsilon/theta`, one power too weak. The same checker rigorously encloses the true
aggregate normalized slack; it is tiny on all eight records but not monotone.
See `docs/notes/terminal-defect-statistics.md` for the exact table, formulas,
provenance, and portability caveats, and
`docs/notes/annealed-critical-coding.md §5.1` for the tower derivation.

### 4.2 Weighted-bin fallback

The scalar diagonal recurrence may be too crude.  The generated transition
table already provides the exact mass matrix between the eight oscillation
bins. Let `mu_(k,j)(a)` be normalized mass in bin `a`, and let
`P_(k,j)(a,b)` be the fraction of bin-`a` parent mass carried by bin-`b`
children. Then, exactly,

```text
mu_(k,j+1) = mu_(k,j) P_(k,j),
```

and every nonempty row of `P` is stochastic. A more flexible target sets
`w=0` on the low bins and uses a common rational weight `w_b>=1` on every high
bin, with `rho<1`, such that the high block contracts while its low-to-high
source is bounded. In full-matrix shorthand this has the form

```text
P_(k,j) w <= rho w + e_j 1,            e_j -> 0,
```

coordinatewise and uniformly for `k>=j+2`. The weighted potential then obeys
the same contracting recurrence and dominates the desired tail. This is a
stronger sufficient form because `e_j` bounds the worst conditional low-bin
row. The weaker actual-genealogy form used below contracts the high-to-high
block rowwise and bounds only mass-averaged low-to-high immigration. The first
exact finite search is now complete.

## 5. Exact finite weighted-cone audit

The seven thresholds define eight bins `B_0,...,B_7`, where the bin index is
the number of thresholds strictly exceeded. For each transition `(k,j)`, let
`S_ab` be the mass with parent bin at least `a` and child bin at least `b`.
The cumulative fields in `multiscale_transitions_exact.csv` determine every
exact bin-to-bin mass by Möbius differencing:

```text
H_ab = S_ab - S_(a+1)b - S_a(b+1) + S_(a+1)(b+1).
```

All 6,912 reconstructed cells in the 108 observed transition matrices are
nonnegative and reproduce their exact row, column, contingency, and total
masses. Normalize a nonempty parent-bin row to a stochastic matrix `P`, and
write `Q=P_HH` for the high-to-high block at the chosen threshold.

The portable standard-library verifier is:

```bash
python3 experiments/kl/verify_weighted_bin_cone.py
```

It pins the input-table SHA-256, checks the Möbius reconstruction and all exact
minimal-burn-in obstructions, and writes 2,299 exact row inequalities plus 636
exact potential recurrences to:

- `analysis_cache/weighted_bin_cone_rows_exact.csv`;
- `analysis_cache/weighted_bin_recurrence_exact.csv`.

### 5.1 The minimal observed burn-in is exactly classified

The complete seven-threshold result is:

| threshold | high bins | minimal `j0` | matrices / rows | certified `rho` |
|---:|---:|---:|---:|---:|
| `1/20` | `B_1,...,B_7` | 6 | 68 / 476 | `.994429793194` |
| `1/10` | `B_2,...,B_7` | 3 | 92 / 503 | `.999589181062` |
| `3/20` | `B_3,...,B_7` | 3 | 92 / 427 | `.995557673853` |
| `1/5` | `B_4,...,B_7` | 3 | 92 / 349 | `.982167544381` |
| `1/4` | `B_5,...,B_7` | 3 | 92 / 260 | `.858256705178` |
| `3/10` | `B_6,B_7` | 2 | 100 / 184 | `.894665552979` |
| `2/5` | `B_7` | 2 | 100 / 100 | `.894665552979` |

For the first five thresholds, one-row-per-bin policy matrices give exact
lower bounds within `7e-10` of the displayed exact rational upper bounds; the
last two optima are exact. These are finite minimax calibrations, not universal
constants.

A common positive one-step cone cannot start at depth one: every observed
depth-one matrix has the exact `B_7 -> B_7` self-loop. More strongly, it cannot
start at depth two for any threshold at most `1/4`. At `k=17`, the depth-two
`B_7` row has exactly

```text
B_7 -> B_5 :  51,502,644,182,774,780,905
B_7 -> B_7 : 427,972,643,644,712,297,522,
```

and no other child mass, while the depth-four row sends all
`11,131,874,291,182,481,018` units of `B_5` mass to `B_7`. For any common
positive weight and `rho<1`, the first row forces `w_5<w_7` and the second
forces `w_7<w_5`. This is an exact cone obstruction, not a consecutive-depth
cycle or a failure of the actual tail recurrence.

At `t=1/20`, every start through depth five is still impossible. Among the
observed parent-depth-five rows, each high bin `B_1,...,B_7` has one that loses
no mass to `B_0`. Choosing a minimum-weight bin makes that row's stochastic
average at least its parent weight, contradicting `rho<1`. The seven displayed
cones then prove feasibility at the tabulated starts, completing the finite
classification.

For orientation, the systematic `t=1/5` frontier uses the normalized rational
weight

```text
w = (618715355/500000000,
     696512628/500000000,
     1,
     684092097/500000000)
```

It satisfies

```text
Q_(k,j) w <= .982167544381... w
```

for all 349 populated high-bin rows in all 92 observed matrices with
`k=12,...,19` and `j>=3`. The earlier, simpler preregistered witness
`w=(31/25,69/50,1,34/25)`, `rho=68/69` remains a separately checked
regression. The nonmonotone weights are legitimate: after normalization every
high-bin weight is at least one, so the potential dominates the `t=1/5` tail.
Every frontier weight was selected after seeing all eight exact levels.

At `t=3/10`, the simpler `w=(1,1)` satisfies

```text
Q_(k,j) w <= .894665552979... w             for j>=2,
```

over 184 populated rows in 100 matrices. Its exact optimum is

```text
4334815655959768610198 / 4845180013388557558821
  = 0.894665552978....
```

### 5.2 Immigration is now the exposed seam

For the weights above, define

```text
eta_(k,j) = total^(-1)
            sum_(parent low, child high) H_ab w_b.
```

The verifier checks the exact recurrence

```text
V_(k,j+1) = persistent_(k,j) + eta_(k,j)
            <= rho V_(k,j) + eta_(k,j).
```

At five fixed offsets from the terminal transition, the exact decimal
renderings decrease from `k=12` to `k=19` as follows:

| threshold | offset 0 | offset 1 | offset 2 | offset 3 | offset 4 |
|---:|---:|---:|---:|---:|---:|
| `1/5`, `k=12` | .0394473 | .0660194 | .125989 | .165237 | .171313 |
| `1/5`, `k=19` | .00857462 | .0171792 | .0344160 | .0597949 | .0818345 |
| `3/10`, `k=12` | .00651823 | .0147174 | .0358959 | .0732195 | .0890965 |
| `3/10`, `k=19` | .000888977 | .00295249 | .00717138 | .0156453 | .0235596 |

The all-threshold expansion also exposes a negative signal. At `t=1/20`,
offsets one through four rise rather than fall from `k=12` through floating
`k=20`:

```text
offset 1: .04573 -> .11951
offset 2: .02887 -> .11812
offset 3: .02388 -> .10841
offset 4: .01006 -> .09000.
```

Offset zero peaks at `.13940` at `k=18` and is still `.13437` at `k=20`,
above its `k=12` value `.08961`. The `t=.1` offsets show late turnovers but
are not monotone across the full range. Thus the `t=.2,.3` table is the right
direction for the fixed-threshold theorem, while the evidence currently gets
worse at the smallest tracked threshold. Intermediate immigration is not
uniformly tiny—the observed `t=.2,.3` maxima are `.174406...` and
`.144527...`—and no all-level decay theorem, uniform cone, vector-selection
theorem, or threshold-to-zero argument follows.

### 5.3 The floating `k=20` audit breaks every fitted margin, not the cones

The local untracked `eigvec_k20.npy` is a float64 approximate vector, not an
exact feasible certificate. It nevertheless provides a useful provisional
stress test for the fixed weights and bounds above. The reproducible audit is:

```bash
python3 experiments/kl/audit_float_k20_weighted_cone.py
```

It pins sidecar SHA-256
`35fa2453500ce4dec5d8a504e7dc29acd8d4088d4d3ebdc366b2f8796fb91681`
and writes `float_k20_weighted_{cone_rows,recurrence}.csv`. The systematic
exact-data margin is exceeded at every threshold, always at the earliest
permitted depth. But every maximum remains strictly below one at the same
depth, so the qualitative cone survives this provisional audit without
moving its burn-in:

| threshold | `j0` | exact-data `rho` | floating `k=20` maximum |
|---:|---:|---:|---:|
| `1/20` | 6 | `.994429793194` | `.995149954325` |
| `1/10` | 3 | `.999589181062` | `.999758748326` |
| `3/20` | 3 | `.995557673853` | `.997386118145` |
| `1/5` | 3 | `.982167544381` | `.993880660203` |
| `1/4` | 3 | `.858256705178` | `.933824793538` |
| `3/10` | 2 | `.894665552979` | `.895576168344` |
| `2/5` | 2 | `.894665552979` | `.895576168344` |

There are eleven systematic-margin violations and zero unit-contraction
violations. Dropping only the earliest admitted transition restores every
old exact margin. The original preregistered `t=1/5` witness also fails in two
depth-three rows, with maximum `.994172542989`, but remains below one. The
smallest systematic excess over a fitted bound is about `1.25e-4`; the maximum
observed mass-conservation error is `1.04e-15`, and the minimum distance of any
classified oscillation from a threshold is `1.64e-10`. Thus ordinary
summation roundoff does not explain the margin failures. The underlying vector
is still approximate, so none is an exact `k=20` countercertificate.

At the two original thresholds, the immigration evidence remains favorable.
At terminal offsets zero through four, the systematic `t=.2` values continue
from exact `k=19` to floating `k=20` as

```text
.00857462,.0171792,.0344160,.0597949,.0818345
  -> .00716757,.0143117,.0285297,.0500155,.0691789,
```

and the `t=.3` values similarly continue to
`.000755811,.00245109,.00583290,.0127437,.0192612`.

The correct conclusion is mixed but sharper than the first two-threshold
audit suggested. The nearly optimal exact-data fits overfit every quantitative
margin, while the minimal observed burn-ins and qualitative contraction
survived at all seven thresholds. The thinnest provisional margin is only
about `2.41e-4` at `t=1/10`, so future failure remains plausible. For the cone
route, the live mathematical content is an expanding terminal contraction
window, controlled mass-weighted defects, and terminal-offset immigration—not
any fitted finite constant.

## 6. Calibration and next decision

- The favorable result concerns eight particular exact feasible points, not
  all feasible subeigenvectors and not selected exact critical eigenfunctions.
- Within-vector aggregation does not turn an arbitrary nonlinear feasible
  vector into a lower-level feasible vector. It does, however, exactly
  intertwine the annealed linear operators, which produces the floor above.
- The eight vectors at successive levels are not known to be projectively
  consistent.
- The 756 monotone rows are finite observations.  There is no proof that tail
  monotonicity is structural.
- Pointwise scalar contraction at `t=1/5` is already false on these data.  Any
  successful statement must be mass-averaged, use a higher threshold, or
  carry more state.
- The rational common-weight search succeeded finitely after the minimal
  observed burn-in, while an earlier-start cone has an exact obstruction. The
  cone route remains a fallback because smallest-threshold immigration is
  currently adverse.
- The floating audit provisionally exceeds every fitted exact-data margin but
  not one qualitative cone or minimal burn-in. An exact `k=20` vector is still
  needed to decide those rows.
- The fitted `(1/2)(9/10)^j` martingale and `(1/5)(3/4)^j` entropy constants
  pass the reported finite rows, but the independently audited annealed-floor
  research proof closes both as all-level critical/vanishing-slack laws in
  `1<lambda_k<=2`. Lean formalization is pending; do not promote them again.
- The sharper live target is now the polynomial Pearson calibration
  `chi<=6/j^2` for a selected exact critical or normalized-slack-vanishing
  family, or relative `L1` compactness directly. The exact interval audit passes
  all 116 finite rows. The terminal follow-up also passes the post-hoc finite
  bounds `delta<0.21/k`, `E[a^2]<1.533 delta^2`, and
  `chi_terminal<0.483/k^2`, but its fitted anti-concentration ratio rises
  monotonically. None of these is an all-level theorem. Bounded entropy or
  unweighted entropy/energy bounds do not suffice.
- Depthwise entropy monotonicity is not a property of the full feasible cone:
  the exact positive `k=3` counterexample above has `h_2>h_1`. A surviving
  entropy theorem must exploit critical/canonical selection, a weighted
  budget, or a new cross-scale partial-annealing comparison.
- If both scalar and low-dimensional weighted recurrences fail, return to a
  direct primal construction of a cofinal feasible family rather than
  continuing to enlarge the annealed pressure surrogate.
