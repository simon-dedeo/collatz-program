# CLEAN_LEAN restart note

Last updated: 2026-07-21

Last CLEAN_LEAN milestone commit: `4419b30` (`Add intermittent and soft KL endpoint bridges`), pushed to `origin/main`.

## Read this first

This project formalizes substantial conditional Krasikov--Lagarias machinery,
but it does **not** prove the Collatz conjecture and it does **not yet** prove
`klLambda k -> 2`.  The main achievement is that several proposed research
routes now terminate in exact Lean theorems whose remaining premises are
stated explicitly.

Before doing new work:

1. Read `README.md`, `AUDIT.md`, `BLUEPRINT.md`, and
   `MAIN_AGENT_LEAN_REVIEW.md`.
2. Read the newest research-side messages in `../docs/FOR_CLEAN_LEAN.md`.
3. Read the tail of `FOR_FABLE.md` to avoid repeating an outgoing request.
4. Run `lake build` locally from this directory.
5. Run:

   ```text
   rg -n '\bsorry\b|\badmit\b|^axiom\b|^unsafe\b' CleanLean -g '*.lean'
   ```

At this checkpoint, the full build completed successfully with 8,784 jobs.
The audited headline theorems used exactly
`[propext, Classical.choice, Quot.sound]`; there were no project axioms,
`sorry`, or `admit`.

## Communication protocol

- Fable/research side to CLEAN_LEAN:
  `../docs/FOR_CLEAN_LEAN.md`
- CLEAN_LEAN to Fable/research side:
  `FOR_FABLE.md`

After each coherent task, check the incoming file and append a numbered round
to the outgoing file.  Do not edit the incoming file.  The parent repository
is shared with other workers; preserve unrelated changes and stage only files
owned by the task.

## Exact current proof boundary

There are now two principal conditional routes to almost-linear predecessor
counting.

### Route A: hard-min defect gain

`CleanLean/KL/QuadraticDefect.lean` proves that a reverse quadratic defect
recurrence can force terminal defect to zero even when the gains are
nonuniform or intermittent.  It is enough that the effective gain sum

```text
sum a_j / (1 + a_j)
```

diverges.  There is also a precision-checkpoint form that permits temporary
losses between selected projections.

The concrete endpoints are in:

- `CleanLean/KL/ConcreteQuadraticEndpoint.lean`
- `CleanLean/KL/CoarseTowerCounting.lean`

Headline consumers include:

```text
klLambda_tendsto_two_of_coarseMinimumTower_divergentGain
klLambda_tendsto_two_of_coarseMinimumTower_checkpointGain
almostLinearPredecessorCounting_of_coarseMinimumTower_divergentGain
almostLinearPredecessorCounting_of_coarseMinimumTower_checkpointGain
```

The missing theorem is an **all-level structural gain estimate** for the
literal selected KL tower.  Finite numerical increments are evidence, not
this theorem.

Important axis warning: precision checkpoints are not the internal
fixed-precision `5 -> 2 -> 8` state cycle.  A holonomy or carry argument must
first be aggregated into a net inequality across precision projections.

### Route B: fixed-temperature soft operator

`CleanLean/KL/TernaryColdMean.lean` defines the literal normalized negative
power mean

```text
M_(-beta)(z) = ((z_0^(-beta)+z_1^(-beta)+z_2^(-beta))/3)^(-1/beta)
```

and proves, for positive inputs and `beta > 0`,

```text
min z <= M_(-beta)(z) <= 3^(1/beta) * min z.
```

`CleanLean/KL/SoftKLOperator.lean` replaces only the refinement-fiber minimum
in the literal finite KL operator and retains its transport term.  It proves

```text
F_hard(x) <= F_beta(x) <= 3^(1/beta) * F_hard(x).
```

`CleanLean/KL/SoftHardTransfer.lean` turns a positive soft subeigenvector

```text
r * x <= F_beta(x),     3^(1/beta) < r
```

into an exact hard `LevelFeasible` witness.  Exact soft eigenvectors are not
required.  `CountingTransfer.lean` also permits arbitrary sparse witness
levels, and

```text
almostLinearPredecessorCounting_of_coldSubeigen_sequence
```

composes the route through to the literal `X^(1-epsilon)` one-halving
Syracuse predecessor-counting statement.

The missing theorem is **fixed-temperature saturation** (or enough certified
finite soft subeigenvectors): for parameters tending to `2`, obtain soft
factors strictly above `3^(1/beta)`.  Fable was asked to audit the cold-mean
normalization and branch-only replacement against
`docs/notes/softmin-replica.md` before this lane is extended.

## Other important scope restrictions

- The top-level Collatz conjecture in `Collatz/Defs.lean` is faithful, but no
  unconditional theorem proves it.
- The counting result concerns the one-halving Syracuse map, not literal
  unaccelerated-Collatz predecessor sets.
- Its target is positive and not divisible by three.
- `LevelFeasible` is subeigenvector feasibility, not an eigenvector or
  uniqueness assertion.
- The finite level-12 certificate gives only its fixed exponent.  It cannot
  instantiate a sequence converging to parameter `2` by itself.
- `lambda_k -> 2` would give almost-linear predecessor counting; it would not
  prove that every positive integer reaches `1`.

## Best next actions

1. Check whether Fable has replied to Round 83 in
   `../docs/FOR_CLEAN_LEAN.md`.  Resolve any mismatch in the exact softened
   operator before building on it.
2. If the soft operator matches, formalize the weakest research lemma that
   supplies soft subeigenvectors with factor above `3^(1/beta)`.  Prefer a
   finite rational/interval certificate interface over unnecessary spectral
   theory.
3. In the hard-min lane, accept only a checkpoint family chosen from renewal,
   carry, or policy structure independently of observed defect values.  Do
   not mistake a fit to finite increments for an all-level proof.
4. Keep theorem names and prose explicit about every conditional premise.
5. After a coherent milestone, run the full build and axiom audit, update both
   audit documents and `FOR_FABLE.md`, commit only CLEAN_LEAN changes, and
   push when convenient.

## Useful verification commands

Run from `/Users/simon/Desktop/COLLATZ/CLEAN_LEAN`:

```text
lake build
lake env lean CleanLean/Audit.lean
rg -n '\bsorry\b|\badmit\b|^axiom\b|^unsafe\b' CleanLean -g '*.lean'
git diff --check
git status --short
```

The repository root is `/Users/simon/Desktop/COLLATZ`.  There may be
unrelated edits and experimental files belonging to other workers.  Never
stage them merely to make the worktree look clean.

## Suitable stopping-point summary

Lean currently checks the downstream logic of both plausible routes.  The
research bottleneck is no longer an ambiguous transfer step: it is either a
restricted-pressure/gain theorem for the hard adversarial tower or a
fixed-temperature saturation theorem for the literal soft KL operator.  A
future session should attack one of those premises directly and resist
formalizing cleaner substitutes that do not instantiate the existing exact
interfaces.
