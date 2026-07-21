# formal

This is the small original Lean 4 scaffold for the project.  It defines the
unaccelerated Collatz map, the conjecture, an exact strong-induction descent
reduction, basic cycle/counterexample-shape lemmas, and a fueled checker proving
that every positive `n <= 10000` reaches one.

The bounded theorem `reachesOne_of_le_10000` uses `native_decide`, so it trusts
Lean's compiler in addition to the kernel.  The remaining declarations in
`Formal/Collatz.lean` are sorry-free ordinary Lean proofs.

This directory is not the main Krasikov--Lagarias formalization.  The active,
audited proof development, its trust ledger, and build instructions are in
[`../CLEAN_LEAN/README.md`](../CLEAN_LEAN/README.md).

## Build

```bash
lake build
```

The project pins `leanprover/lean4:v4.33.0-rc1` and the matching mathlib
revision through `lean-toolchain` and `lake-manifest.json`.
