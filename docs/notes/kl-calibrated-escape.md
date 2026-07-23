# KL-calibrated escape: branching entropy, cycle tax, and the finite `-1` counter

2026-07-23. Status: **the path/cycle tax, strict selected-cycle drift,
mixed-word budget, and pure minus-one rail obstruction are kernel-checked in
companion commits `9f307a9`, `ddff8d7`, and `7aa7c0d`; `cc9f441`
kernel-checks the exact ordinary size cost of tracking the minus-one spine**.
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

## 6. The theorem-driven construction target

The KL reading narrows the next construction search to a renewal problem.

1. **Discharge.**  A class-8 block spends `r` units of `v_2(m+1)` and gains
   about `r*log_2(3/2)` in height.
2. **Recharge.**  Mixed class-2/transport or existing EC17 compiler blocks
   must recreate at least `r'` units of `v_2(m+1)`.  They have negative KL
   size shift and must be paid for by a longer discharge.
3. **Calibration.**  Among exact recharge blocks, prioritize the least
   product of KL deviation factors from (3.1).  The active policy itself is
   excluded by (2.2).
4. **Cofinality.**  A repeating finite residue cycle is insufficient.  The
   payload recurrence must close autonomously for one positive natural; fresh
   lift digits at each generation are only an externally preloaded 3-adic
   stack.

This does not yet construct a survivor.  It supplies a principled objective
and two exact kill tests--negative selected-cycle drift and finite `-1`
counter exhaustion--before any further computation.  The live big theorem
would be either an autonomous recharge law that beats both costs, yielding a
machine-checkable infinite orbit, or a uniform theorem that every admissible
recharge pays more contraction than its next discharge can recover.
