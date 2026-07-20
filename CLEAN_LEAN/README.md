# CLEAN_LEAN

A Lean 4 formalization project for the Collatz work in the parent repository.

The project begins by fixing the standard conjecture itself, then proves that
an independently shaped relational specification is equivalent.  Finite
Krasikov--Lagarias systems and their certificate checker will be added beneath
this specification.

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

