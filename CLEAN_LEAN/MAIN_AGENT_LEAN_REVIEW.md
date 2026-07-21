# Lean review for the main Collatz agent

Date: 2026-07-21.  Scope: the complete `CLEAN_LEAN` proof tree and its current
research handoffs.

## Executive result

The finite KL-to-counting route is complete.  The new theorem

```text
ResidueSystem.almostLinearPredecessorCounting_of_coarseMinimumTower
```

shows directly that positive exact fixed vectors, their literal successive
coarse minima, and a uniformly positive all-stage quadratic normalized-slack
gain imply `X^(1-epsilon)` one-halving Syracuse predecessor counting for every
positive target not divisible by three.  Positive fixed vectors are normalized
to exact finite feasibility inside Lean; the repaired history/pruning and
predecessor transfer then supply the counting theorem.  No Brouwer theorem,
informal eigenvector-to-feasibility step, or citation to the invalid printed
KL elimination is left in this composition.

This is not a proof of the endpoint because the all-stage gain premise is
open.  It is also not the Collatz conjecture even if that premise is proved.

## The actual load-bearing mathematical target

The strongest convenient current endpoint obligation is precisely

```text
HasQuadraticCoarseSlackGainWith (a k j) (j+2)
  (klWeights (lam k)) (x k (j+3))
```

at every genuine step of the selected coarse-minimum tower, with one uniform
lower bound `0 < a0 <= a k j`.  Its exact rowwise equivalent is research
equation (40.4), already kernel-checked in `ArgminFrustration.lean`.  This
quantity is the increment of normalized super-slack; a bound on total new
slack alone is insufficient because inherited slack can change the selected
minimum.

Lean now accepts two strictly weaker targets.  The coefficients may be merely
nonnegative if `sum a_(k,j)/(1+a_(k,j)) -> infinity`.  More importantly for
the carry-cycle lane, the inequality may be imposed only across selected
multi-step checkpoints.  Intermediate projections need satisfy no sign
condition.  Thus an internal carry/renewal analysis need only produce a net
bound across an unbounded family of precision blocks; an all-stage
inherited-slack inequality is no longer logically necessary.  Precision
blocks and the fixed-level `5 -> 2 -> 8` state cycle are distinct objects.

The reciprocal telescope, factor-three normalization, oscillation identity,
`lambda -> 2` limit, finite feasibility, repaired KL comparison, and counting
transfer are all complete downstream of this premise.

## Alternative load-bearing route

For every fixed rational `lambda < 2`, an all-level/cofinal construction of
exact feasible vectors would bypass selected eigenvectors, C1', Brouwer, and
the coarse-minimum gain.  The theorem

```text
almostLinearPredecessorCounting_of_feasible_sequence_concrete
```

already consumes exactly such a sequence.  A stable symbolic ansatz for those
vectors would therefore be at least as valuable as a pressure proof.

There is now a second exact alternative in `SoftKLOperator.lean`.  The literal
order-`-beta` ternary mean and softened KL operator satisfy

```text
F_hard x <= F_beta x <= 3^(1/beta) F_hard x.
```

Hence a positive soft subeigenvector with factor greater than
`3^(1/beta)` is automatically a hard feasibility witness.  The theorem
`almostLinearPredecessorCounting_of_coldSubeigen_sequence` permits arbitrary
sparse witness levels and composes these finite witnesses all the way to
counting.  The remaining research theorem is fixed-temperature saturation of
the soft values at `annealedKL(lambda)`; neither that limit nor soft Perron
existence has been smuggled into the Lean statement.

## Lean work that becomes directly useful when research supplies data

1. Isolate a selected carry/renewal theorem that aggregates to net quadratic
   gain on an unbounded sequence of precision checkpoints.  Generic holonomy forces a label
   mismatch but cannot bound near-tie second gaps; the checked rotating
   tie-wall counterexample proves that this distinction is essential.  The
   checkpoint endpoint already consumes the desired block inequality.
2. Ingest higher-level GPU certificates only when the integer vectors and all
   scaling/branch-bound metadata are available.  The generic scaled checker
   is already sound; the remaining work is generated data plus a reproducible
   front end, not new certificate mathematics.
3. If a finite pressure or cone certificate is found, instantiate the existing
   exact sparse pressure-row and Chernoff checkers before proving new analytic
   infrastructure.

## Work that is currently lower value

- Porting Brouwer: positive critical eigenvector existence is unnecessary for
  the direct-feasibility route and does not prove the missing gain.
- Additional generic information inequalities: equation (4.8), including its
  literal weighted-geometric overlap, is already checked; the missing step is
  aggregate selected self-consistency.
- More finite extrapolation: finite exponents, dimensions, and tail ratios do
  not imply the required uniform all-level estimate.
- A policy-free contraction automaton: exact counterexamples and marginal
  modes show that it forgets the global shared-value constraints.

## Trust and review status

The full project builds without `sorry`, `admit`, project-defined axioms, or
unsafe declarations.  Headline assumptions are printed in `Audit.lean`; the
new composed endpoint uses only standard Lean/mathlib principles.  The
history/pruning proof is intricate but kernel-checked: human review is for
confirming that its definitions model the intended KL system, not for making
the Lean implication logically valid.

The top-level trust ledger had become stale and incorrectly listed the
predecessor lower bound, concrete oscillation identity, and all large
certificates as absent.  `AUDIT.md` and `BLUEPRINT.md` have been corrected to
distinguish the checked level-12 artifact from unavailable higher-level GPU
certificates and to identify the all-stage gain as the current endpoint gap.
