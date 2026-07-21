# KontoroC

Lean 4 formalization support for the Kontorovich disproof challenge.

This is intentionally separate from `CLEAN_LEAN`: it imports the faithful
standard Collatz definition from that package, but develops the fully
accelerated odd map and replayable counterexample-certificate interfaces here.

Current checked target:

- exact maximal-power-of-two odd step;
- legal finite valuation words;
- the affine identity
  `2^(sum k) * T^N(x) = 3^N*x + A_N`;
- a replayable Boolean cycle checker whose soundness theorem concludes the
  literal negation of `CleanLean.Collatz.Conjecture`.

For a nonempty legal word, Lean also proves closure equivalent to the exact
search equation `(2^S-3^N)*seed=A_N`, proves the denominator strictly positive,
and identifies the seed with `A_N/(2^S-3^N)`.  Divisibility does not replace
the separate exact-valuation replay premise.

The richer `CycleArtifact` mirrors the worker's
`collatz-accelerated-cycle-v1` mathematical payload (`word`, `seed`, `orbit`,
affine constant, both step counts).  Lean recomputes every redundant field.
`checkNontrivial = true` is an end-to-end kernel theorem yielding
`¬ CleanLean.Collatz.Conjecture`.

`MacroGlider` is the corresponding infinite symbolic endpoint.  It accepts
variable nonempty valuation blocks connecting a strictly increasing sequence
of states above `4`, expands them to ordinary Collatz time, and proves the
literal negation of the conjecture.  Constructing such a glider remains the
open mathematical/search problem.

Literal periodic software is ruled out: `repeated_legal_block_fixed` proves
that if one nonempty valuation block remains exactly legal under every
successive repetition, its first endpoint already equals its start.  The proof
uses denominator growth in a coprime integer recurrence, not a numerical
search.  Thus an outward glider must use genuinely unbounded symbolic memory.
The package also exposes the arbitrary-state periodic-tail form and proves
that an infinitely repeatable positive block necessarily has
`3^length < 2^totalValuation`; the opposite sign is impossible.

Nothing here currently supplies a counterexample.  A finite prefix is not an
ordinary positive infinite orbit certificate.

Build locally with:

```text
lake update
lake build
```

The small numerical regressions in `KontoroC/Examples.lean` use
`native_decide` and therefore trust the Lean compiler.  They are not imported
by any certificate-soundness proof.  `KontoroC/Audit.lean` prints the axioms of
the headline mathematical theorems separately.
