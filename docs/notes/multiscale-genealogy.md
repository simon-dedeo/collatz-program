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

It pins the input-table SHA-256, checks the Möbius reconstruction and two exact
cone obstructions, and writes 533 exact row inequalities plus 192 exact
potential recurrences to:

- `analysis_cache/weighted_bin_cone_rows_exact.csv`;
- `analysis_cache/weighted_bin_recurrence_exact.csv`.

### 5.1 A sharp finite burn-in at `t=1/5`

A common positive one-step cone cannot start at depth one: every observed
depth-one matrix has the exact `B_7 -> B_7` self-loop. More strongly, it cannot
start at depth two. At `k=17`, the depth-two `B_7` row has exactly

```text
B_7 -> B_5 :  51,502,644,182,774,780,905
B_7 -> B_7 : 427,972,643,644,712,297,522,
```

and no other child mass, while the depth-four row sends all
`11,131,874,291,182,481,018` units of `B_5` mass to `B_7`. For any common
positive weight and `rho<1`, the first row forces `w_5<w_7` and the second
forces `w_7<w_5`. This is an exact cone obstruction, not a consecutive-depth
cycle or a failure of the actual tail recurrence.

After the fixed burn-in `j0=3`, the obstruction disappears. On high bins
`B_4,...,B_7`, the normalized rational weight

```text
w = (31/25, 69/50, 1, 34/25)
```

satisfies

```text
Q_(k,j) w <= (68/69) w
```

for all 349 populated high-bin rows in all 92 observed matrices with
`k=12,...,19` and `j>=3`. The maximum is exactly `68/69`, attained by the
deterministic `B_5 -> B_7` row at depth four. The nonmonotone weights are
legitimate: every high-bin weight is at least one, so the potential still
dominates the `t=1/5` tail. The cone was selected after seeing all eight levels;
it is post-hoc, and an exact `k=20` vector is its first genuine level holdout.

At `t=3/10`, the simpler `w=(1,1)` satisfies

```text
Q_(k,j) w <= (179/200) w                    for j>=2,
```

over 184 populated rows in 100 matrices. Its exact maximum is

```text
4334815655959768610198 / 4845180013388557558821
  = 0.894665552978... < 179/200.
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
| `1/5`, `k=12` | .0394489 | .0659603 | .125727 | .164829 | .170793 |
| `1/5`, `k=19` | .00857639 | .0171795 | .0344012 | .0597367 | .0817288 |
| `3/10`, `k=12` | .00651823 | .0147174 | .0358959 | .0732195 | .0890965 |
| `3/10`, `k=19` | .000888977 | .00295249 | .00717138 | .0156453 | .0235596 |

This is the right direction for the terminal-offset theorem above, but it is
only eight points at two fixed thresholds. Intermediate immigration is not
uniformly tiny—the observed maxima are `.173908...` and `.144527...`—and no
all-level decay theorem, uniform cone, vector-selection theorem, or
threshold-to-zero argument follows.

### 5.3 The floating `k=20` holdout falsifies both earliest burn-ins

The local untracked `eigvec_k20.npy` is a float64 approximate vector, not an
exact feasible certificate. It nevertheless provides a useful provisional
falsifier for the fixed weights and bounds above. The reproducible audit is:

```bash
python3 experiments/kl/audit_float_k20_weighted_cone.py
```

It pins sidecar SHA-256
`35fa2453500ce4dec5d8a504e7dc29acd8d4088d4d3ebdc366b2f8796fb91681`
and writes `float_k20_weighted_{cone_rows,recurrence}.csv`. Both original cone
candidates fail, only at their earliest permitted depth:

| cone | scope | rows / matrices | worst ratio | outcome |
|---|---:|---:|---:|---:|
| `t=.2`, `rho=68/69` | `j>=3` | 61 / 16 | `.994172542989`, `j=3,B_7` | 2 violations |
| `t=.3`, `rho=.895` | `j>=2` | 31 / 17 | `.895576168344`, `j=2,B_7` | 1 violation |
| `t=.2`, shifted | `j>=4` | 59 / 15 | `.976332930340`, `j=4,B_4` | passes provisionally |
| `t=.3`, shifted | `j>=3` | 30 / 16 | `.833251699071`, `j=3,B_7` | passes provisionally |

The other failing `t=.2` row is `j=3,B_5`, with ratio
`.989901581202`. The smallest excess over a proposed bound is
`.000576168344`; the maximum observed mass-conservation error is
`1.04e-15`, and the minimum distance of any classified oscillation from a
threshold is `1.64e-10`. Thus ordinary summation roundoff does not explain the
violations. The underlying vector is still approximate, so this is not an
exact `k=20` countercertificate.

The immigration evidence remains favorable. At terminal offsets zero through
four, the `t=.2` values continue from exact `k=19` to floating `k=20` as

```text
.00857639,.0171795,.0344012,.0597367,.0817288
  -> .00716920,.0143126,.0285191,.0499714,.0690982,
```

and the `t=.3` values similarly continue to
`.000755811,.00245109,.00583290,.0127437,.0192612`.

The correct conclusion is mixed. The fixed `j0=3`/`j0=2` cones were genuine
finite patterns and are now provisional holdout failures. Moving each burn-in
one level later repairs this floating instance, but that repair is post-hoc
and could drift again. The live mathematical content is therefore the
terminal-offset immigration formulation and the search for a *uniformly
justified* burn-in/weight family, not the particular constants just falsified.

## 6. Calibration and next decision

- The favorable result concerns eight particular exact feasible points, not
  all feasible subeigenvectors and not selected exact critical eigenfunctions.
- Within-vector aggregation does not commute with changing KL level.
- The eight vectors at successive levels are not known to be projectively
  consistent.
- The 756 monotone rows are finite observations.  There is no proof that tail
  monotonicity is structural.
- Pointwise scalar contraction at `t=1/5` is already false on these data.  Any
  successful statement must be mass-averaged, use a higher threshold, or
  carry more state.
- The rational common-weight search succeeded finitely after the minimal
  observed burn-in, while an earlier-start cone has an exact obstruction. The
  next mathematical target is terminal-offset immigration decay for an
  all-level family, first at `t=1/5`, followed by thresholds tending to zero.
- The fixed weights and rational bounds are preregistered for the first exact
  `k=20` certificate. The floating candidate already falsifies their earliest
  burn-ins provisionally; an exact vector is still needed to decide the exact
  `k=20` rows.
- If both scalar and low-dimensional weighted recurrences fail, return to a
  direct primal construction of a cofinal feasible family rather than
  continuing to enlarge the annealed pressure surrogate.
