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
formalized.  The central missing theorem remains a uniform
localization/domination or direct-feasibility argument forcing the weighted
oscillation defect to vanish.

The first charged spine-face Lyapunov proposal has been exactly falsified,
not assumed away: `MarginalObstruction.lean` proves that its aligned mean and
co-spine modes have the same eigenvalue.  This is a no-go theorem for that
certificate class, not evidence against `lambda_k -> 2`.

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
