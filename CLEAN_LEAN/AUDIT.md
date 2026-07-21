# Trust and build audit

Last checked: 2026-07-20 with Lean `v4.33.0-rc1` and the matching mathlib tag.

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

## Explicitly not proved

- The Collatz conjecture.
- A Krasikov--Lagarias predecessor-count lower bound.
- The KL oscillation identity in the concrete residue system.
- The asymptotic weighted-tail conjecture C1'.
- Any of the large numerical KL certificates.
- A uniform domination of the concrete KL refinement by the abstract pressure
  kernel.
- The shell-mass ratio without an additional uniform bound on the free
  min-harmonic boundary data.

See `RESEARCH_AUDIT.md` for the mathematical critique and proposed proof route.
