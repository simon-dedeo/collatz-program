# CLEAN_LEAN

A Lean 4 formalization project for the Collatz work in the parent repository.

The project begins by fixing the standard conjecture itself, then proves that
independently shaped relational and Syracuse specifications are equivalent.
An abstract finite Krasikov--Lagarias operator, the corrected weighted-tail
reduction, exact local algebra, transport resolvents, and exact rational
restricted-pressure machinery have also been added.  The concrete `ZMod`
residue arithmetic, fiber partition, branch counting, oscillation identity,
terminal-potential/Chernoff estimate, and defect-to-`lambda = 2` limit bridge
are now kernel checked.  The scaled integer checker now also proves
feasibility for the true irrational KL weights, and the analytic implication
from `lambda_k -> 2` to `X^(1-epsilon)` Syracuse predecessor counting is
formalized.  There is also a second, shorter endgame: any sequence of exact
finite feasible parameters tending to two implies the same counting result
directly, without choosing critical eigenvectors.  The central missing
theorem remains either a uniform localization/domination argument forcing the
weighted oscillation defect to vanish, or a cofinal construction of exact
feasible vectors below every fixed parameter less than two.

`LevelLift.lean` formalizes the paper's level monotonicity argument: copying a
feasible vector to all three new top-digit lifts preserves feasibility.  Thus
the exact critical feasibility suprema are nondecreasing in the residue
precision, with no spectral-radius theorem imported.

`RetardedComparison.lean` formalizes the analytic core of KL Theorem 5.1.
For any finite nested sum/min difference system whose leaves all have positive
backward shifts, LP feasibility propagates an exponential lower bound from an
initial strip to every nonnegative time.  Its final corollary derives the
paper's exact `1/(4 max c)` constant.  The still-unformalized literature bridge
is now the advanced-term elimination and the proof that its retarded trees
preserve both the Collatz inequalities and LP feasibility.

`TreeRewrite.lean` handles the splitting substep: substituting a valid rule
inside any sum/min context preserves the functional inequality, while the
associated exponential coefficient inequality moves in the opposite, feasible
direction.  It also kernel-checks a counterexample showing that deleting a
minimum alternative is not a local consequence of positivity and monotonicity;
the paper's global critical-path argument is genuinely required.

The first charged spine-face Lyapunov proposal has been exactly falsified,
not assumed away: `MarginalObstruction.lean` proves that its aligned mean and
co-spine modes have the same eigenvalue.  This is a no-go theorem for that
certificate class, not evidence against `lambda_k -> 2`.  The concrete KL
system also has the retarded `2 -> 2` self-lift at every precision; proving
that this loop is outside the proposed truncated charge set still requires a
separate exact orbit-hitting lemma.

`FiniteRecord.lean` contains a small Lean-native certificate at level 2.  It
checks the integer rows and logarithmic cross-products by kernel reduction and
then invokes the same soundness path intended for the large streamed records.

`RESEARCH_AUDIT.md` separates the statements supported by the live research
notes from the pressure/mass estimate that is still open, including the exact
marginal obstruction discovered by the combined-automaton experiment.

`GPU_CERTIFICATE_SPEC.md` distinguishes ordinary finite-level KL certificates
from the combined localization/pressure artifact actually needed for the
`lambda_k -> 2` proof.

## Trust policy

- The final project must build without `sorry` or project-specific axioms.
- Every headline theorem is inspected with `#print axioms` in an audit file.
- Numerical exploration may suggest certificates, but theorem-producing
  certificates must be checked by Lean or explicitly labelled external.
- The standard, relational, and accelerated Collatz formulations will be
  proved equivalent before any result is advertised as a Collatz result.

Build with:

```text
lake exe cache get
lake build
```
