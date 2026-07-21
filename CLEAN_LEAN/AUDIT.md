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
- The corrected finite eigenvector-mass tail inequality holds.

## Explicitly not proved

- The Collatz conjecture.
- A Krasikov--Lagarias predecessor-count lower bound.
- The KL oscillation identity in the concrete residue system.
- The asymptotic weighted-tail conjecture C1'.
- Any of the large numerical KL certificates.

