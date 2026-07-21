# Audit of the KL advanced-term termination proof

**Status (2026-07-21): three exact defects in the published construction.** The
positive-return history, all-three-deletion history, and split-invariant
countermodel are all independently reconstructed and kernel-checked in Lean.
Lean also proves the abstract branch-arrival compactness theorem. The printed
construction remains invalid. Lean commit `3d6a186` now kernel-checks the
occurrence-aware replacement through the abstract feasible-point comparison.
Commit `331ff48` defines the actual predecessor family and proves target-pool
nonemptiness and P1/P2; D1--D3 and the final exponent wrapper remain open. Run:

```sh
python3 verify_termination_obstruction.py
python3 verify_all_three_deletion.py
python3 verify_split_invariant_counterexample.py
python3 verify_two_phase_small_levels.py
python3 verify_equation_2_1_obstruction.py
python3 verify_predecessor_base_inequalities.py
```

The checkers use exact integer or affine arithmetic throughout; the finite
tree traversals do not use floating point. The first verifies a legal `k=5` path in
the Krasikov--Lagarias back-substitution tree:

```text
188 -B8-> 206 -B8-> 137 -B2-> 182 -B2-> 161
    -B8-> 107 -B8-> 71 -B8-> 47 -T-> 188.
```

`CLEAN_LEAN/CleanLean/KL/TerminationObstruction.lean` separately checks the
same path against the formal `ResidueSystem` definitions, including lift
indices, symbolic shifts, ancestry tests, the positive return, and the
re-expanded child's deletion eligibility.

Writing every shift as the exact pair `(a,b)` for `a+b log_2(3)`, the
successive shifts are

```text
(-1,1), (-2,2), (-4,3), (-6,4),
(-7,5), (-8,6), (-9,7), (-11,7).
```

All are nonnegative by exact comparisons of powers of two and three. All seven
three-lift destinations are new on their ancestor paths and therefore survive
the deletion test. The closing edge is a transport edge, to which the paper's
deletion rule is not applied. It returns to residue `188` at the strictly
larger shift

```text
7 log_2(3) - 11 > 0  iff  3^7 = 2187 > 2048 = 2^11.
```

This invalidates the deletion-rule inference used to derive equation (3.2) in
the printed proof of Theorem 3.1: a finite legal return to the same residue can
have larger shift. (Equation (3.2) itself is stated only after assuming an
infinite path, which this finite certificate does not supply.) The return also
directly falsifies the next history-free self-similarity claim. When the returned `188`
is split, its `B8` child `206` is now above the earlier `206` and is deleted;
that child survived below the original root. The pruned subtree depends on the
ancestor history, not only on the root residue and a translated shift.

This certificate is **not** a nontermination lasso. The re-expanded subtree is
different, and the path cannot simply repeat. The precise remaining theorem is
that the finitely branching tree of legal histories has no infinite path for
every `k>=2` and every advanced root. A fixed breadth-first schedule would
suffice downstream; a proof of confluence for arbitrary schedules is not
needed for existence of the final retarded witness.

## A second obstruction: the rule can delete all three leaves

The paper states, without a separate combinatorial proof, that its deletion
rule cannot remove all three alternatives of a newly created minimum. The
second checker falsifies that assertion at `k=5`. From root residue `161`, the
following 11-edge legal history reaches residue `242`:

```text
161 -B8.1-> 107 -B8.1-> 152 -B8.2-> 182 -B2.0-> 80
    -B8.1-> 134 -B8.1-> 89 -B8.0-> 59 -T-> 236
    -B2.1-> 152 -B8.2-> 182 -B2.2-> 242.
```

The successive shifts are

```text
(-1,1), (-2,2), (-3,3), (-5,4), (-6,5), (-7,6),
(-8,7), (-10,7), (-12,8), (-13,9), (-15,10).
```

They are all positive, and every followed branch leaf survives the complete
ancestor test. Splitting the final `242` creates the three targets
`80,161,242`, all at the positive shift `(-16,11)`. Each has a strictly lower
same-residue ancestor:

```text
80  at (-5,4),    difference (-11,7) > 0;
161 at (0,0),     difference (-16,11) > 0;
242 at (-15,10),  difference (-1,1) > 0.
```

Thus the literal rule makes all three alternatives deletion-eligible and
produces the empty-minimum case the paper says cannot occur. The checker also
exhausts `k=2,3,4` and all `k=5` histories of depth at most ten, so depth eleven
is the first such event under these exact path semantics. This does not prove
nontermination; it shows that the printed recursive construction is not a
well-defined inequality-tree construction as stated. Arbitrarily retaining one
eligible alternative is not harmless: here the eligible `242 -> 242` branch is
an immediate positive self-loop.

## A third gap: splitting can activate an unconstrained outer minimum

The paper's deletion proof maintains (3.4) only for critical assignments. Its
split induction says inherited principal bounds survive because the base
inequality is substituted at the split leaf. This inference is false at the
abstract tree level. `verify_split_invariant_counterexample.py` checks the
four-value countermodel

```text
old tree = min(P[L+X], B),   P=5, L=9, X=1, B=8.
```

Initially the left alternative has value `10`, so the unique critical
assignment chooses `B` and the bound at `P` is vacuous. Replace `L=9` by a
locally valid KL-shaped split body `2+min(3,3,3)=5`. The left alternative now
has value `6<8` and becomes critical, but its selected sum violates the
principal bound `6>5`. Thus old assignment-specific (3.4) plus local split
validity is not a split-stable invariant. This is a generic semantic
countermodel, not yet a claim that these four values arise from one concrete KL
function family; it blocks the published induction and any backjump repair that
silently assumes the same invariant.

## Adjacent counting-transfer erratum: equation (2.1)

A separate audit of the later predecessor-count instantiation found that the
paper's printed equality

```text
φ^m_k(y) = φ^{2m}_k(y−1),  m ≡ 1 (mod 3)
```

is false under its literal definitions. At `k=2, m=7, y=1`, every target
`a=9q+7` has the three bounded predecessors
`a`, `2a`, and `(4a−1)/3`, while `a=7` has exactly `{7,9,14}` below `14`.
Thus `φ^7_2(1)=3`. Every target `b=9q+5` has `b` and `(2b−1)/3`, while
`b=14` has exactly `{9,14}` below `14`, so
`φ^{14}_2(0)=φ^5_2(0)=2`. Both witnesses are nonperiodic points.
`verify_equation_2_1_obstruction.py` checks the parametric lower bounds in
exact affine arithmetic and the witness sets with independent forward-orbit
and reverse-tree enumerators.

Writing `P*_a(x)` for the set counted by `π*_a(x)`, the correct targetwise
statement for nonperiodic `a ≡ 1 (mod 3)` and `x ≥ 2a` is

```text
P*_a(x) = {a} ⊔ P*_{2a}(x).
```

This elementary all-`k` identity is kernel-checked in Lean commit `58f0ef8`.
After taking infima, doubled targets are only a subset of the
class `2m`, so the valid statement is

```text
φ^m_k(y) ≥ 1 + φ^{2m}_k(y−1),  y ≥ 1.
```

This is a genuine printed error but not an additional fatal gap: the useful
lower-bound direction survives (even with `+1`) and yields the same exponent
with the usual factor `λ^{-1}`. The formal counting bridge must use this
inequality or the direct inclusion `π_a(x) ≥ π_{2a}(x)`, not the equality.

## Consequence for the record certificate

The `k=19` feasible point and its 387,420,489 inequalities remain exactly
verified. The inference from that feasible point to the predecessor-counting
bound uses KL Theorem 2.2, whose published supporting chain invokes Theorem
3.1. The corrected retarded-elimination witness is kernel-checked in commit
`3d6a186`, while commit `331ff48` defines the actual function family and proves
nonemptiness, normalization, and monotonicity. The formal trust chain now has
one visible construction gap: prove D1--D3 for that family and discharge the
final counting transfer using the correction above. Until that is checked, the numerical certificate is exact but the
headline exponent is conditional. This is a trust-chain correction, not
evidence that the bound or Theorem 3.1 is false.

## Repair frontier

The global deletion-lifting lemma is now kernel-checked in both left and right
orientations: under occurrence-specific whole-tree `NoCriticalUse`, every
post-deletion critical assignment has a pre-deletion lift with the same selected
sum and the same principal-bound status. This closes the new-tie problem for a
*soundly justified* deletion, but does not prove that every syntactically
eligible KL leaf satisfies `NoCriticalUse`, nor that the principal-bound
invariant survives a later split after earlier deletions.

A separately reviewed and now kernel-checked termination theorem compresses a
hypothetical infinite record-admissible path to its B2/B8 arrivals `(r_n,h_n)`.
Same-residue arrival heights are nonincreasing, while consecutive heights obey
`h_(n+1)-h_n=log_2(3)-c_n` for positive integers `c_n`. Finite states bound the
heights and hence the typed edges `(r_n,r_(n+1),c_n)`. On recurrent edge types,
statewise limits would telescope around a directed cycle to
`q log_2(3)=C`, contradicting irrationality. CLEAN_LEAN proves the abstract
theorem, the exact B2/B8 compression formulas, and irrationality of
`log 3 / log 2`. This is a termination component, not by itself a sound rewrite.

The earlier backjump idea would handle an all-three event by deleting an entire
unused containing alternative at an ancestor minimum. The split countermodel
blocks its present justification: later splits can activate an alternative for
which the assignment-specific principal bounds were never established. It is
therefore deprioritized unless a materially stronger provenance invariant is
found.

The leading replacement is **finite policy-menu compilation**. Build the
universal occurrence-annotated history forest by expanding every nonnegative
leaf, retaining all transport and branch children but marking a branch child
which is strictly above an earlier same-state occurrence on *that path*.
Complete policies expand both children of every addition, choose one child of
every minimum, end only at negative leaves, and contain no mark. Compile their
finite menu into one outer minimum of min-free additive retarded expressions.

For fixed positive monotone `phi`, state, and time, recursively choosing an
actual raw `phi` minimizer supplies a complete policy. It cannot contain a
marked higher repeat: the finite segment from the earlier occurrence would
bound its value below by the later value plus positive additive siblings, while
monotonicity gives the reverse weak inequality. Thus at least one menu member
is functionally sound, and the outer minimum is functionally sound. Every menu
member is coefficient-sound because the NT fiber coefficient minimum is at
most every chosen lift coefficient; taking their minimum preserves the common
lower bound. The checked compactness theorem makes the universal forest finite,
and its finitely many terminal shifts give one common `0<mu_k<=2`.

The construction must be occurrence-aware. At `k=4`, two exact legal histories
from root `26` reach the identical label `74@(-7+5*alpha)`, but it is a higher
repeat on one path (`2*alpha-3>0`) and a lower repeat on the other
(`3*alpha-5<0`). Therefore a mark keyed only by `PrincipalLabel` is unsound.

```text
bad occurrence:
26 -B8.1-> 44 -B8.2-> 56 -B2.2-> 74 -B2.2-> 71 -B8.2-> 74
shifts 0, (-1,1), (-2,2), (-4,3), (-6,4), (-7,5)

live occurrence:
26 -B8.2-> 71 -B8.2-> 74 -B2.1-> 44 -B8.2-> 56 -B2.2-> 74
shifts 0, (-1,1), (-2,2), (-4,3), (-5,4), (-7,5).
```

In the first path the final-minus-earlier difference is `(-3,2)>0` because
`3^2>2^3`; in the second it is `(-5,3)<0` because `3^3<2^5`. All nonroot
shifts are positive and every preceding branch destination survives.
`verify_two_phase_small_levels.py` checks this ambiguity and implements the
occurrence-sensitive policy compiler for every advanced root at `k=2,3,4`; it
reproduces KL Table 1's maximum literal counts `8,84,12829` exactly.

The replacement proof chain is now sharply factored:

1. construct the full word-indexed raw forest by well-founded recursion at
   surviving branch-arrival checkpoints, using ordinary finite recursion along
   each deterministic transport spine;
2. prove that every selected marked hit realizes its recorded earlier prefix
   and later split, yielding the already checked global occurrence-provenance
   interface;
3. prove the deterministic pruner is live using one target positive monotone
   base-system family at `y=2`, and combine surviving shifts in `[-2,0)` into
   one common `mu_k` over all root states;
4. assemble `TwoPhaseEliminationData`, whose checked consumer already produces
   the abstract retarded comparison with the correct functional and coefficient
   directions; and
5. prove the now-defined predecessor `phi` satisfies D1--D3 and close the
   corrected counting transfer.

Commit `3d6a186` kernel-checks steps 1--4, including
`BranchChild.wellFounded`, `buildHistory`, root-only mark provenance, live
pruning, the common lag, `builtRetardedEliminationWitness`, and
`quarter_lower_bound_of_feasible`. A full 8,714-job build passes, and the axiom
audit reports no `sorryAx`. Commit `331ff48` also completes the definition,
target-pool nonemptiness, normalization, and monotonicity portion of step 5;
its base inequalities and exponent wrapper are the sole remaining finite-level
seam.

The preferred termination implementation uses
`wellFounded_iff_isEmpty_descending_chain` directly on compressed branch
checkpoints, so no literal König API is needed. A twice-audited but not
kernel-checked alternative supplies the explicit occurrence-word bound

```text
N = 3^(k-1),  M = N(N-1),
D_k = M^2 3^M ceil((N-1)/2).
```

Its fractional-part proof is in
`docs/notes/kl-explicit-history-bound.md`. The bound is proof fuel, not a
practical enumeration limit.

This replacement has survived independent audits of ties, transport returns,
all-three events, off-path additive children, uniformity in `phi,y`, and the
opposite functional/coefficient orientations. CLEAN_LEAN already checks the
occurrence-indexed one-pass pruner, exact functional semantics, coefficient
monotonicity, localized positivity, the global repeat-provenance interface, and
the complete two-phase-to-retarded consumer. CLEAN_LEAN commit `2f17afe` checks
the rich word syntax and raw-tree shift, local-validity, functional,
coefficient, and negative-terminal invariants; commit `3d6a186` completes the
producer and witness assembly. Commit `331ff48` defines the predecessor-count
family and proves P1/P2. Only D1--D3 and its final exponent transfer remain
provisional.
