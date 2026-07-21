# Trust and build audit

Last checked: 2026-07-21 with Lean `v4.33.0-rc1` and the matching mathlib tag.

## Mechanical checks

- `lake build` succeeds.
- The Lean source tree contains no `sorry`, `admit`, or project-defined
  `axiom` declaration.
- `CleanLean/Audit.lean` prints the axioms used by representative headline
  theorems.  The reported axioms (`propext`, `Classical.choice`, and
  `Quot.sound`, depending on the theorem) are standard Lean/mathlib
  foundations, not Collatz assumptions.

## Proved in the current build

- The standard functional and relational Collatz formulations are equivalent.
- The standard and one-halving Syracuse formulations are equivalent.
- The descent criterion implies the standard Collatz conjecture.
- The abstract finite KL fiber minimum and operator are monotone.
- A passing exact-rational finite KL certificate casts to a real feasible
  point; the executable checker is proved sound.
- The integer-scaled row format used by the GPU certificates is checked
  exactly and proved, together with the integer alpha and branch-weight
  checks, to decode to feasibility for the true irrational KL weights.
- The exact level-12, 177,147-coordinate scaled certificate is checked in
  Lean and supplies its fixed predecessor-counting exponent.
- The corrected finite eigenvector-mass tail inequality holds.
- The full abstract weighted-tail reduction R' holds for varying finite levels.
- A geometric restricted-pressure estimate forces the required tail decay.
- A rational finite-kernel subeigenvector certificate forces geometric decay.
- Exact rational pressure-row and integer-power Chernoff-gap certificates have
  executable soundness theorems.
- The exact finite-cycle transport resolvent identity holds.
- The advanced fixed-fiber eigen-equation gives the claimed normalized minimum.
- The pure-branch root self-loop requires an extra nontrivial-child condition;
  a concrete counterexample to the weaker claimed equivalence is checked.
- The valid two-input mixer range bound and a counterexample to the stronger
  one-sided oscillation claim are checked.
- The concrete KL oscillation identity is checked.
- The repaired history/pruning construction and literal predecessor base
  system turn every exact finite feasible certificate into an explicit
  one-halving Syracuse predecessor-count lower bound.
- A cofinal feasible sequence tending to two implies `X^(1-epsilon)`
  predecessor counting for every positive target not divisible by three.
- The literal coarse-minimum tower plus a uniform positive all-stage
  quadratic slack gain implies the same counting conclusion directly.
- More weakly, divergent accumulated effective gain suffices; gain may be
  checked only across selected multi-step blocks, with no condition at the
  intermediate projections.
- The literal ternary cold power mean satisfies the hard/soft factor
  `3^(1/beta)` sandwich.  A positive soft subeigenvalue above that factor is
  converted into hard KL feasibility and, along sparse levels tending to two,
  into almost-linear predecessor counting.

## Explicitly not proved

- The Collatz conjecture.
- The asymptotic weighted-tail conjecture C1'.
- Any divergent all-stage or checkpoint-block normalized-slack gain for
  selected KL profiles.
- Fixed-temperature saturation of the softened KL spectral values at the
  annealed value; the finite soft-to-hard comparison is proved, not this
  all-level limit.
- Unconditional convergence `lambda_k -> 2`.
- GPU certificates beyond the checked-in level-12 artifact.
- General positive nonlinear eigenvector existence at every finite level;
  the direct-feasibility route does not require it.
- A uniform domination of the concrete KL refinement by the abstract pressure
  kernel.
- The shell-mass ratio without an additional uniform bound on the free
  min-harmonic boundary data.

See `RESEARCH_AUDIT.md` for the mathematical critique and proposed proof route.
