# KL-calibrated escape: branching entropy, cycle tax, and the finite `-1` counter

2026-07-23. Status: **the path/cycle tax, strict selected-cycle drift,
mixed-word budget, and pure minus-one rail obstruction are kernel-checked in
companion commits `9f307a9`, `ddff8d7`, and `7aa7c0d`; `cc9f441`
kernel-checks the exact ordinary size cost of tracking the minus-one spine;
`408cb2c`/`814fb00` prove the three-branch recharge ledger and that its
dyadic depth is exactly the next forced odd-burst length**.
The full
cross-precision rigidity problem remains research.  There is no
counterexample.
This note rereads Krasikov--Lagarias from the deliberately opposite direction:
not to prove that many integers terminate, but to identify what a single
escaping orbit would have to do that their extremal predecessor system refuses
to do.

Primary source: I. Krasikov and J. C. Lagarias, *Bounds for the 3x+1 Problem
using Difference Inequalities*, arXiv:math/0205002 (2002), especially
Theorem 2.2, Sections 3--5, and the equality discussion at the end of Section
6.  The source was checked against the local PDF
`papers/krasikov-lagarias-2002-bounds-3x1-difference-inequalities.pdf`.
Its printed deletion proof and equation (2.1) are not reused: their exact
defects and the replacement theorems are recorded in
`experiments/kl/TERMINATION_AUDIT.md`.

## 1. The equality object in the original paper

KL's Section 6 makes the right converse observation.  At a critical parameter
`lambda`, if the principal LP inequalities are equalities, the pure
exponentials

```text
phi_m(y)=c_m*lambda^y
```

solve the difference system with equality.  The repaired project strengthens
this point: the finite critical min-of-linear operator has a positive
eigenvector, and a minimizing lift can be selected on every chord row.  The
selected graph has the following edge shifts:

```text
transport m -> 4m:                 w=-2,
class-2 chord m -> (4m-2)/3:       w=log_2(3)-2,
class-8 chord m -> (2m-1)/3:       w=log_2(3)-1.
```

Only the class-8 chord has positive shift.  Reversing a predecessor edge turns
its shift into the leading logarithmic size change of the corresponding
forward block.  Thus positive total shift is exactly the symbolic resource an
escaping forward program needs.

## 2. Selected-policy cycles are strictly retarded

Let `c>0` be an exact critical eigenvector and retain the fiber-minimizing
chord on each chord row.  Every selected summand is bounded by the full row:

```text
lambda^w * c(target) <= c(source).                    (2.1)
```

Multiply (2.1) around a directed cycle.  The potential values telescope, so

```text
lambda^(sum w) <= 1, hence sum w <= 0.                (2.2)
```

The inequality is strict in the KL graph.  A cycle sum has the form
`A*log_2(3)-B` with integers `A>=0,B>0`.  Equality with `A>0` would give
`3^A=2^B`; with `A=0`, every used shift is already negative.

This changes how the critical KL eigenvector should be used in a construction
program.  Its active policy is not a hidden counterexample schedule.  Every
one of its cycles contracts in the forward-reversed size cocycle.  The
spectral radius reaches one because rows *add predecessor branches*--that is,
through branching entropy--not because one selected ray grows.  The old KL
method therefore cannot be tropicalized to a single escape path without
losing its entire source of gain.

At each fixed precision the graph is finite, so cycle erasure strengthens
this from cycles to arbitrarily long selected walks: after a bounded simple
remainder, every walk is a concatenation of negative-shift cycles.  Hence its
asymptotic shift is bounded above by the largest (strictly negative) simple
cycle mean.  There is no reason for that negative margin to be uniform in the
precision--the elementary lower bound from `|2^B-3^A|>=1` can be exponentially
small in the cycle length.  A hypothetical escape can therefore evade this
finite-level obstruction only through a genuinely precision-changing,
noncoherent limit policy.  This is the same quantifier seam that turns fresh
CRT digits into a 3-adic stack rather than one natural.

The path/cycle telescoping and strict KL cycle claims are kernel-checked as
QM127 in companion commit `9f307a9`.  The fixed-graph cycle-erasure corollary
in the preceding paragraph is not separately packaged in Lean.

## 3. Leaving the policy has an exact deviation tax

The full refinement fiber contains three possible chord targets.  Write
`c_min` for the selected value and `c_alt` for a different lift, and put

```text
d(e)=c_alt/c_min >= 1.
```

On transport and selected edges set `d(e)=1`.  Equation (2.1) becomes, for
every full-lift edge,

```text
lambda^w*c(target) <= d(e)*c(source).
```

Telescoping around any full-lift cycle gives the calibrated escape tax

```text
lambda^(sum w) <= product d(e).                       (3.1)
```

An outward cycle must therefore make non-minimal refinement choices, and the
product of their potential ratios must pay for at least all of its outward
shift.  This is a useful search ordering: enumerate recharge cycles in
increasing exact tax surplus, not seeds in increasing numerical size.  It is
also only a necessary condition.  The selected digit may change with the
precision, and a coherent inverse-limit digit table can describe a 3-adic
address without describing one ordinary natural.

The cycle formulation is not the real limit of the argument.  For an
arbitrary finite path `x_0 -> ... -> x_N`, multiplication gives

```text
lambda^(sum_(i<N) w_i) * c(x_N)
  <= product_(i<N) d_i * c(x_0).                    (3.2)
```

At one fixed KL precision the positive potential has finite condition number
`kappa=max(c)/min(c)`, hence

```text
lambda^(sum_(i<N) w_i)
  <= kappa * product_(i<N) d_i.                     (3.3)
```

Thus eventual periodicity is irrelevant: every aperiodic path with sustained
positive shift must pay non-minimizing-lift tax at a sustained asymptotic
rate.  The endpoint factor is only `kappa`, independent of path length.  This
is still a fixed-level theorem; `kappa` may grow with the precision, so a
precision-uniform escape-rate conclusion would require a new bound.  The
path-product statement is kernel-checked as QM130 in companion commit
`ddff8d7`.

For selected paths all `d_i=1`, so the fixed-level consequence is stronger
than a nonpositive asymptotic mean.  If `kappa<=lambda^B`, then every selected
path, of every length, satisfies

```text
sum_(i<N) w_i <= B.                                  (3.4)
```

The selected policy cannot accumulate unbounded outward shift at one
precision at all.  This corollary is kernel-checked in companion commit
`7aa7c0d`; a live path must either pay nonselected deviation tax or increase
precision so that the endpoint budget itself changes.

The certified feasible subeigenvectors show that this qualification is active
rather than cosmetic.  Over `k=12,...,19`, their exact condition numbers
increase strictly from `146.967160601293` to `2782.61599307298`.  These are
finite certificate facts, not critical-eigenvector identities or a limiting
growth law.  They identify the next rigidity question: either renormalize the
growing exceptional potential spike uniformly across the tower, or prove that
an ordinary path cannot track the spike cofinally.  A fixed-level argument
alone cannot decide that seam.

There is now one exact cross-precision constraint.  Companion commit
`cc9f441` proves for naturals

```text
n mod 3^k = 3^k-1  ->  3^k <= n+1.                 (3.5)
```

Consequently every fixed natural eventually avoids the exact all-`2` spine
and no natural represents `-1` at every ternary precision.  This does not
exclude a diagonal sequence `n_k` whose size grows with `k`; it proves that
such tracking costs at least exponential ordinary size.  A useful global
theorem must compare that cost with the height gain and counter recharge of
the same coherent orbit.

There is a second exact pruning budget which does not use `c`.  If a mixed
word contains `n8` class-8 chords, `n2` class-2 chords, and `ns` transports,
positive leading shift means

```text
(n8+n2)*log_2(3) > n8+2*n2+2*ns.
```

The already kernel-checked separator `3^41<2^65` gives
`log_2(3)<65/41`, hence the necessary integer inequality

```text
24*n8 > 17*n2+82*ns.                                 (3.6)
```

In particular each transport used by a recharge phase costs more than
`82/24` positive class-8 discharges before the leading multiplier can exceed
one.  This is a strong branch-and-bound rule for the mixed search, not a
sufficient condition for an actual trajectory.

## 4. The cheapest visible escape is the nonordinary point `-1`

On a class-8 chord, use the affine coordinate `z=m+1`.  The predecessor map is

```text
m -> (2m-1)/3,       z -> (2/3)z.                    (4.1)
```

Its forward reversal is `z -> (3/2)z`, the only positive-shift KL block.  The
point `m=-1` is a fixed point of (4.1).  It is also the unique rational
periodic point of a pure class-8 word: iterating gives

```text
R8^L(m)+1=(2/3)^L*(m+1),
```

so a positive period `L` forces `(3^L-2^L)(m+1)=0` and hence `m=-1`.

The certified feasible subeigenvector profiles near `-1` make the calibration
visible.  The self-lift is not the minimizing lift, and over the eight stored
levels the exact ratio `c(-1)/min_fiber(c)`, divided by the certified
class-8 lower weight, decreases from `1.00491098975441` to
`1.00029914602351`.  This is finite evidence consistent with saturation, not
a critical-eigenvector limit theorem.  The exact limiting local law, if its
critical-tower hypotheses hold, would give
`lambda^(log_2(3)-1)`, precisely the tax for the positive self-loop.  In every
case the exact equality object is the negative 3-adic fixed point, not the
required positive ordinary seed.

## 5. Ordinary finite rails consume a finite counter

The positive natural approximation to the `-1` loop is elementary and exact.
For `L,t>0`, define

```text
x_j=3^j*2^(L-j)*t-1,        0<=j<=L.
```

Every `x_j` with `j<L` is odd, and one shortcut step gives

```text
(3*x_j+1)/2=x_(j+1).
```

Hence

```text
T^L(2^L*t-1)=3^L*t-1,                                (5.1)
```

and the block grows strictly.  Its fuel is the finite counter `v_2(x_0+1)`.
If two such pure rails splice, then

```text
3^(L_i)*t_i=2^(L_(i+1))*t_(i+1),
```

and therefore

```text
v_2(t_(i+1))=v_2(t_i)-L_(i+1).                       (5.2)
```

No fixed positive payload supports infinitely many positive rail lengths:
the nonnegative counter in (5.2) cannot decrease forever.  This is the exact
version of the earlier intuition that an infinite escape needs a counter
which is repeatedly regenerated, not merely one which starts large.  Companion
commit `9f307a9` connects (5.1)--(5.2) to the literal Syracuse semantics and
proves the infinite-splice contradiction.

## 6. Recharge is an immediate forced burst, not stored fuel

The three literal KL predecessors of a positive target `a=2 (mod 3)` are

```text
advancedChild=(2a-1)/3,
retardedChild=2*advancedChild,
transportChild=4a.
```

Companion commit `408cb2c` connects them to one, two, and two shortcut
Syracuse steps respectively and proves the exact centered balances

```text
3*(advancedChild+1)=2*(a+1),
3*(retardedChild+2)=4*(a+1),
transportChild+4=4*(a+1).                           (6.1)
```

The corresponding dyadic depths are therefore `1+v_2(a+1)`,
`2+v_2(a+1)`, and `2+v_2(a+1)`.  Class-2 and transport do not reset an
independent battery for free; they move the exceptional center from `-1` to
`-2` or `-4` and pay the exact ordinary-size inequalities recorded in
`KLRechargeLedger.lean`.

Commit `814fb00` makes the operational meaning sharper.  For every natural
`n`, put

```text
r=v_2(n+1),       t=(n+1)/2^r.
```

Lean proves `t>0`, `t` odd, `n=2^r*t-1`, and

```text
T^j(n)=3^j*2^(r-j)*t-1,       0<=j<=r.              (6.2)
```

Every source before `j=r` is odd and the endpoint at `r` is even.  Thus
`v_2(n+1)` is exactly the maximal length of the next consecutive odd burst.
A deep recharge cannot be stored or assigned to a later program branch: it
forces its entire discharge immediately.

## 7. The hidden invariant is one two-place content ledger

The specific identities (6.1) have a moving-center form.  If `h=1 (mod 3)`
is the positive center of a negative controller, define

```text
h8=(2h+1)/3,       h2=(4h+2)/3,       hs=4h.
```

Direct substitution gives

```text
3*(advancedChild(a)+h8)=2*(a+h),
3*(retardedChild(a)+h2)=4*(a+h),
transportChild(a)+hs=4*(a+h).                       (7.1)
```

Consequently the `2,3`-primitive cofactor of the positive centered distance
`a+h` is unchanged by every coherent KL branch.  Moreover, for any positive
integer `z`,

```text
2^v_2(z) * 3^v_3(z) <= z.                           (7.2)
```

So ordinary height, ternary shadow precision, and dyadic burst depth are not
three resources which can be optimized independently.  They are the two
prime contents of one integer.  If `a=-h (mod 3^k)` and
`b=v_2(a+h)`, then (7.2) gives the combined address cost

```text
2^b*3^k <= a+h.                                     (7.3)
```

The special branch balances are kernel-checked in `408cb2c`.  Companion
commit `35200ca` proves QM131 in full: the complementary ternary balances,
two-place content divisor and height bound, the three abstract core-transfer
lemmas, and every moving-center invariant in (7.1).  Thus the collapse from
three apparent resources to one centered integer is a kernel-checked result.

## 8. Negative cycles are the finite near-equality templates

The fixed point `-1` is not the only signed equality object.  The new exact
worker checks the three explicitly supplied signed shortcut cycles through
`-1`, `-5`, and `-17`, whose KL positive-center presentations are

```text
1 -> 1,
7 -> 10 -> 7,
25 -> 34 -> 136 -> 91 -> 61 -> 82 -> 55 -> 37 -> 25.
```

Their branch counts give the strict outward separators `3>2`, `3^2>2^3`,
and `3^7>2^11`.  For each certified feasible subeigenvector at
`k=12,...,19`, the worker extracts the prescribed lift on every chord and
computes the exact rational product

```text
product(c_prescribed/minFiber) /
product(certified edge-weight lower bounds).         (8.1)
```

All 24 values exceed one.  Each finite sequence decreases strictly, and the
`-1` template is exactly cheapest in every row:

```text
template                 k=12              k=19
-1 fixed point        1.00491098975441   1.00029914602351
-5 cycle             1.14003194854355   1.06409075514007
-17 cycle            1.86455471354517   1.48129516352954
```

This suggests that the correct KL analogue of an Aubry/equality set is built
from signed cycles rather than a positive ray.  That interpretation is a
conjectural guide: the vectors are certified feasible subeigenvectors, the
levels are finite, and neither convergence nor completeness of the three
templates is claimed.  The exact artifact SHA-256 is
`f52afeca61dc4bd0683a2ab72e285377355e86edd5e52fec85e89a84ab534249` and
contains `counterexample:null`.

## 9. Coherent negative shadowing has universally finite depth

There is an elementary obstruction broader than periodic negative cycles.
Suppose two signed shortcut-Syracuse orbits have the same parity choices for
`N` steps, with `O_N` odd sources.  Subtracting their one-step affine laws and
iterating gives

```text
2^N*(T^N(x)-T^N(y))=3^O_N*(x-y).                    (9.1)
```

Because `3^O_N` is odd and the endpoint difference is integral,

```text
2^N divides x-y.                                    (9.2)
```

Thus two distinct ordinary integers cannot share an infinite parity
itinerary.  In particular, a positive orbit cannot coherently shadow any one
fixed signed negative orbit forever, even if that controller is aperiodic.
It may still reset to a different controller, but a post-reset shadow of
length `N` needs a fresh address modulo `2^N`.

Controller switching has a parallel ternary cost.  Each legal positive-center
step in (7.1) obeys `h'<=4h`.  A length-`L` connector therefore has
`h'<=4^Lh`.  If it imitates a distinct fixed target `g` modulo `3^k`, then

```text
3^k <= |h'-g| <= h'+g <= 4^L*h+g.                  (9.3)
```

No fixed-length connector can switch distinct negative controllers at
cofinally increasing precision.  Equations (9.1)--(9.3) are requested as
QM132--133 and remain pending kernel checking; they are recorded here to
define the next exact interface, not as a completed Collatz theorem.

## 10. The revised theorem-driven construction target

The KL reading now narrows a viable counterexample architecture much more
than “make the counters grow.”

1. **Coherent segment.**  Follow a signed near-equality controller.  The
   centered primitive cofactor stays fixed, and dyadic recharge immediately
   becomes a forced odd burst.
2. **Controller switch.**  Write a genuinely new negative center.  A shadow
   of length `N` requires a mod-`2^N` address, while ternary precision `k`
   requires connector length growing with `k` unless the connection is exact.
3. **KL payment.**  The complete word must obey
   `24*n8>17*n2+82*ns` and its non-minimal lift deviations must pay the
   calibrated path tax.  The three signed cycles supply the baseline prices.
4. **Autonomy.**  One positive payload must generate the next longer,
   finer controller switch.  Supplying fresh CRT digits externally merely
   constructs a 2- or 3-adic stack, not an ordinary counterexample.

This is not a counterexample.  It identifies the only remaining constructive
freedom: an aperiodic self-writing sequence of controller resets.  A big
positive result would be an exact recurrence that generates those resets and
beats both KL costs.  A big negative result would show that every such reset
changes or drains the primitive cofactor faster than the next coherent
segment can recover.  Pure seed widening and fixed-controller searches no
longer address the live seam.
