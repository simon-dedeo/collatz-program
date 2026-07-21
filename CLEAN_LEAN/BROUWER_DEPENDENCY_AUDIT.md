# Brouwer dependency audit

Status: audited on 2026-07-21; not yet imported.

## Result

Updating mathlib does not currently close the fixed-point gap.  A source
search of mathlib master at commit
`6e593caa39bbd85e5b437ad7e69eb2e5beb1e0fa` found no Brouwer, Schauder, or
Poincare--Miranda fixed-point theorem suitable for a continuous self-map of a
finite simplex.

The best existing Lean 4 implementation found is the paper artifact
[Solo-ary/Game-Theory-Formalization](https://github.com/Solo-ary/Game-Theory-Formalization/tree/camera-ready-icml2026),
stable tag `camera-ready-icml2026`, commit
`8e252837d9322609c5d7de98c2e6948dd5390ade`.  It is MIT-licensed and accompanies
the 2026 paper *Formalizing Scarf, Brouwer, and Nash in Lean*.

Its relevant theorem is

```lean
theorem Brouwer {n : PNat}
    (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))
    (hf : Continuous f) : ∃ x, f x = x
```

This is the correct mathematical endpoint for
`CleanLean.KL.FiniteSystem.normalizedOperator`, after relabeling the finite KL
state type by `Fintype.equivFin`.

## Trust checks performed

The upstream artifact was checked out at the exact tag and built completely
with its pinned toolchain, Lean/mathlib `v4.22.0`.  The build completed without
`sorry` warnings in any compiled dependency of `Gametheory.Brouwer`.  The
occurrences of `sorry` found textually in `Gametheory/Scarf.lean` are inside
block comments.

An independent audit file imported `Gametheory.Brouwer` and ran

```lean
#print axioms Brouwer
```

Lean reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

Thus the theorem is kernel-checked and introduces no project axiom.  This is a
logical audit, not a claim that the package has undergone mathlib's review
process.  The theorem statement and the relabeling/application to the KL
operator must still be reviewed for semantic fit.

## Compatibility test

The upstream proof comprises 3,513 lines across `Simplex.lean`, `Scarf.lean`,
and `Brouwer.lean`.  It does not compile unchanged against this project's
mathlib `v4.33.0-rc1`, owing to API changes between Lean 4.22 and 4.33.

A disposable port test repaired the 119-line simplex module and the full
2,600-line Scarf module on 4.33.  The 794-line Brouwer module then advanced
substantially but still required migrations involving `Lex` coercions,
locally synthesized finite-order instances, explicit simplex coercions, and
changed ordered-ring rewrite lemmas.  These are ordinary compatibility
issues, but the port is not yet complete and therefore has not been vendored.

## Integration decision

Do not downgrade the Collatz project to mathlib 4.22: that would trade one
isolated library gap for broad regression risk.  Do not postulate Brouwer as
an axiom.  The safe options are:

1. continue the audited source port under a separate namespace, preserve the
   upstream MIT license and exact provenance, and require the normal project
   axiom audit to pass; or
2. wait for this theorem (or an equivalent one) to enter mathlib, then prove
   only the finite-state relabeling and continuity/application layer here.

Until nonlinear eigenpair existence becomes the load-bearing obstacle to the
KL limit theorem, the existing conditional boundary in
`NormalizedEigenpair.lean` is the lower-maintenance choice.  The principal KL
gap remains the all-stage normalized slack-gain/pressure inequality, not
Brouwer.
