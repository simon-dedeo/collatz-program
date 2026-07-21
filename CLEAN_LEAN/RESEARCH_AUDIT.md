# Audit of the fiber-geometry program

Last updated: 2026-07-21.  This audit compares the current Lean development
with the live notes in `../docs/notes/`, especially `fiber-geometry.md`,
`adversarial-operator.md`, `sol-pressure.md`, and
`renormalization-at-minus-one.md`.

## Bottom line

The numerical geometry is strong evidence for a useful theorem, but the
restricted-pressure inequality C1' has not been proved.  The missing step is
not the elementary weighted-tail reduction.  It is a uniform, global bound
showing that the exact extremal eigenvector cannot move enough mass into the
exceptional return tree as the precision grows.  The published advanced-term
elimination derivation does contain a kernel-checked obstruction, but that
bridge is now repaired by a different two-phase construction: Lean builds a
finite occurrence-indexed history, proves its marking sound, prunes it, and
constructs the exact retarded witness.

This is a plausible target for formalization.  The downstream implications
from weighted-tail decay to `lambda_k -> 2`, and from that endpoint to
`x^(1-epsilon)` predecessor counting, are formalized.  Finite feasibility now
implies the abstract KL difference-function bound without a literature
elimination hypothesis.  Those functions are now instantiated by actual
Syracuse predecessor counts using a targetwise one-sided doubling argument
that avoids the false printed equation (2.1).  Thus exact finite feasibility
now reaches the ordinary counting exponent.  The uniform localization premise
is still not proved, so this is not presently a proof of `lambda_k -> 2`, the
almost-linear counting result, or Collatz.

## Claims that survive the audit

1. **Finite nonlinear Perron theory.**  The argument in
   `adversarial-operator.md` that the transport edges form a strongly
   connected cycle appears to match Gaubert--Gunawardena's finite-dimensional
   positive-eigenvector theorem.  Together with the continuity argument in
   `kl-limit-object.md`, this plausibly discharges `(H_k)` whenever the
   threshold is below 2.  This imported theorem and its hypotheses still need
   to be represented carefully in Lean.

2. **The oscillation identity.**  Given a positive exact unit eigenvector,
   summing the finite eigen-equations gives the displayed defect identity.
   `OscillationIdentity.lean` and `ResidueSystem.lean` now prove both its
   algebra and the concrete fiber/branch bijections.

3. **Corrected Proposition R'.**  If, for every fixed `t > 0`, the
   eigenvector-weighted tail mass `nu_k {o_k > t}` tends to zero, then the mean
   oscillation defect tends to zero.  `WeightedTail.lean` proves both the
   finite inequality and its asymptotic form.

4. **The exact root minimum.**  At the advanced fixed fiber, the exact
   eigen-equation determines the normalized minimum.  The abstract algebraic
   statement and the pure-branch root consequence are proved in
   `RootLaw.lean`.

5. **Exact transport unrolling.**  A transport recurrence can be unrolled
   around a finite cycle into a resolvent identity.  This is proved in
   `TransportResolvent.lean` and is a better starting point for a return-kernel
   proof than an empirical per-level dilution factor.

6. **The downstream limit bridge.**  `KLWeights.lean` proves exactly that the
   annealed scalar is strictly decreasing on `[1,2]` and equals one at two.
   `ConcreteLimit.lean` proves that vanishing normalized defect therefore
   forces `lambda_k -> 2`; no extrapolation is used.

7. **Exact irrational certificate soundness.** `IrrationalWeights.lean` now
   proves that the stored integer cross-products lower-bound the true
   `Real.rpow` branch coefficients. `ScaledCertificate.lean` composes this
   with the integer row checker, yielding feasibility for the actual KL
   operator without floating point.

8. **The counting endgame.** `PredecessorCount.lean` defines the count using
   the actual Syracuse iterate. `PredecessorBase.lean` proves the literal
   residue-infimum functions satisfy the KL base system, and
   `CountingTransfer.lean` proves exact feasibility at any `k>=2` supplies the
   exponent `logb 2 lambda` for every eligible target.  Consequently an exact
   feasible sequence tending to two gives `X^(1-epsilon)` counting, with no
   remaining literature-transfer hypothesis.

9. **The retarded difference comparison.** `RetardedComparison.lean`
   represents the eliminated right-hand sides as finite nested sum/min trees
   and proves the strip induction of KL Theorem 5.1.  It also derives the
   exact `1/(4 max c)` constant from `lambda <= 2`, maximum lag at most two,
   and the initial lower bound one.  `HistoryWitness.lean` now produces these
   trees by the repaired two-phase history construction and states the fully
   discharged `quarter_lower_bound_of_feasible` theorem.

10. **Sound tree splitting, with deletion kept explicit.** `TreeRewrite.lean`
    proves substitution inside arbitrary sum/min contexts on both the
    functional and exponential-coefficient sides.  A concrete positive,
    nondecreasing counterexample shows that simply removing a child from a
    minimum can destroy the root inequality.  Thus the global
    critical-assignment argument in KL Theorem 3.2 cannot be replaced by a
    generic local monotonicity lemma.

11. **Critical-assignment semantics and the exact deletion interface.**
    `CriticalAssignment.lean` defines the finite choices made at sum and
    minimum vertices, proves existence at every evaluation point, and proves
    that a critical assignment's selected-leaf sum equals the nested tree
    value.  If the global labelled-path argument establishes that no critical
    assignment uses a proposed minimum alternative, Lean now proves that the
    alternative can be deleted inside an arbitrary surrounding context and
    the root functional inequality survives.  On the LP coefficient side,
    the same deletion is automatically monotone in the feasible direction.
    The occurrence-indexed construction in item 25 now supplies the
    KL-specific avoidance premise from repeated residue/shift labels.

12. **Labelled critical paths and the KL deletion contradiction.**
    `EliminationTree.lean` retains internal principal labels `(state,shift)`,
    selected root-to-leaf paths, and the assignment-specific version of KL
    equation (3.4).  Local validity before deletion implies this invariant.
    A selected-subassignment relation then propagates a decomposition through
    arbitrary surrounding principal, sum, and minimum nodes.  Lean proves the
    key strict contradiction: if a branch leaf repeats an ancestor state at a
    later shift, the split's positive transport sibling makes the selected
    sum strictly larger than that leaf, contradicting monotonicity and the
    ancestor bound.  This checks the mathematical heart of the deletion rule.
    Item 25 now instantiates the exact shape in a two-phase splitter and avoids
    any need for split/delete order-independence.

13. **Concrete KL split and coefficient identity.**
    `ConcreteElimination.lean` constructs the exact residue-system split with
    transport shift `beta-2` and retarded/advanced three-lift shifts
    `beta+alpha-2` and `beta+alpha-1`.  The translated functional rule follows
    from the unshifted base inequalities, every permitted split keeps all new
    shifts at least `-2`, and erasure to `RetardedExpr` preserves evaluation.
    Lean also proves that the unshifted erased coefficient expression is
    exactly `ResidueSystem.system.operator (klWeights lambda)`.  Hence a
    feasible KL vector makes every split increase the coefficient right-hand
    side, even inside an arbitrary labelled tree context, while decreasing
    the functional right-hand side.  This is the concrete splitting half of
    KL Theorems 3.2 and 4.1; item 25 supplies the terminating global repair.

14. **Global safe deletion.** `EliminationTree.lean` defines occurrence of a
    chosen minimum branch as a selected subassignment of a critical assignment
    of the entire surrounding tree.  If no whole-tree critical assignment
    uses the proposed alternative, Lean proves that deleting it preserves the
    expanded functional value under arbitrary nested principal, sum, and
    minimum contexts.  The proof handles the important outer-minimum case:
    an unselected path is only raised, so it cannot become newly minimizing.
    This is a valid formal counterpart of KL's “totally non-critical” pruning,
    unlike the false local deletion rule.  The occurrence-specific zipper in
    item 25 derives the required whole-tree avoidance after all splitting is
    complete, so the failed split-time invariant is not used.
    Symmetric left/right deletion and automatic coefficient-side monotonicity
    are both checked.

15. **Explicit completed-elimination interface.**
    `EliminationWitness.lean` packages exactly what the recursive KL argument
    must produce: finite labelled trees, one common lag in `(0,2]`, functional
    soundness for every positive monotone solution of the base system, and
    coefficient soundness for every feasible KL vector.  From this package
    Lean derives the exact `1/(4*C)` comparison bound.  Item 25 now constructs
    the witness rather than assuming its existence.

16. **Portable sparse pressure rows.** `PressureCertificate.lean` now has an
    executable exact-rational checker matching a finite source/target/weight
    edge table and proves its cast to the real pressure inequalities.  The two
    Chernoff gaps in the portable Lemma-5 artifact are kernel-checked.
    `PortablePressureData.lean`, generated from the payload hash, also checks
    `h >= 1` and all 2,187 concrete tilted rows using `decide +kernel`.  For
    every one of the nine parameter pieces Lean now composes those rows into
    the all-length terminal-potential estimate
    `pressureMass K n q <= R^n * h(q)` over the concrete real kernel.
    `PressureWeightBounds.lean` also kernel-checks the exact rational upper
    bound for `alpha`, every interval endpoint and tiling relation, and proves
    that the stored rational edge weights dominate the three true irrational
    KL weights throughout each piece.  The certificate's scope remains the
    ball automaton rather than C1' localization; a general theorem connecting
    the graph to all-level aggregated KL ball masses is still separate.

17. **Exact symbolic elimination shifts.** `SymbolicShift.lean` represents
    every splitter increment in `Z + Z*alpha` and proves exact evaluation and
    translation invariance for finite path words.  This removes floating-point
    shift comparisons from the completed checkpoint termination proof; no
    finite control quotient is required by the repaired argument.

18. **Finite termination-rank checker.** `TerminationCertificate.lean`
    checks a finite edge table and natural rank by exact reduction and proves
    that every represented path has at most the starting rank many edges.
    This remains a valid alternative certificate interface, but the completed
    checkpoint proof uses irrational branch-arrival compactness instead.

19. **Independent pressure-graph semantics.** `BallPressureAutomaton.lean`
    defines the 243-state depth-six graph directly from the concrete KL
    transport, branch-target, and fiber formulas, rather than from certificate
    data.  It also checks the charged states are the first six points of the
    backward-four orbit from `-1`.  Every generated portable adjacency row is
    kernel-checked equal to this graph, including its target tilt.  This closes
    the finite S1/S2 table-identity check.  The exact S3 interval-weight
    domination and S4 interval tiling are also now kernel-checked.  A general
    all-level ball-mass domination theorem and C1' localization remain
    separate obligations.

20. **Obstruction to the printed derivation of KL equation (3.2).**
    `TerminationObstruction.lean` checks a legal level-five principal path
    whose seven refinement destinations are new, followed by a transport
    return to the root residue at shift `7*alpha-11 > 0`.  It also checks that
    re-expansion makes the previously surviving child 206 deletion-eligible,
    so the pruned subtree is history-dependent.  This invalidates the
    finite-step inference used in the printed derivation of (3.2), while
    (3.2) itself assumes an infinite path; it directly falsifies the
    translated-subtree claim.  It is not a nontermination lasso and does not
    refute the intended theorem.

21. **Critical-assignment lifting through deletion.**
    `DeletionInvariant.lean` proves that every critical assignment after a
    globally unused left alternative is deleted lifts to a pre-deletion
    critical assignment with identical selected evaluation and equivalent
    principal-bound invariant.  The symmetric theorem is also checked for
    right-alternative deletion.  This handles newly exposed outer-minimum ties
    and proves preservation of `(3.4)` in both orientations.  Termination is
    wholly separate and remains open.

22. **Abstract branch-arrival compactness.**
    `BranchArrivalTermination.lean` proves that no infinite sequence on a
    finite state space can have nonnegative heights, statewise nonincreasing
    returns, and increments `alpha-c_n` for natural costs.  The proof derives
    bounded costs, constructs recurrent-state limits, and excludes the
    resulting finite coboundary by a new Lean proof that `alpha=log_2 3` is
    irrational.  It also checks the exact compressed KL costs after any
    number of transport steps.  `CheckpointTermination.lean` now supplies the
    concrete interface: its well-founded checkpoint relation maps any
    hypothetical descending chain to exactly this abstract arrival sequence.

23. **All-three-deletion obstruction.**
    `AllThreeDeletionObstruction.lean` checks an eleven-edge legal level-five
    history ending at residue 242.  Every followed branch child is
    nonnegative and survives the full ancestor test, including two lower
    repeated arrivals.  The next advanced split has targets 80, 161, and 242
    at one positive shift, and all three are deletion-eligible against explicit
    lower ancestors.  This falsifies the printed assertion that the rule
    cannot empty a new three-way minimum.  It is not a nontermination proof.

24. **Split-time invariant obstruction.**
    `SplitInvariantObstruction.lean` gives a finite countermodel using positive
    constant, hence monotone, functions and the actual critical-assignment
    definitions.  All old critical assignments respect the principal bounds,
    and the inserted three-way split is locally valid; nevertheless splitting
    activates a formerly losing outer-minimum alternative whose new critical
    assignment violates an inherited principal bound.  Therefore deletion
    lifting and branch-arrival compactness cannot by themselves justify the
    proposed backjump repair; a split-stable invariant or new semantics is
    required.

25. **Completed two-phase elimination repair.**
    The repaired construction builds a raw good-history tree using splits
    only, marks higher repeated branch leaves, and performs deterministic
    occurrence pruning afterward.  `CheckpointTermination.lean` proves the
    compressed recursive-call relation well founded from branch-arrival
    compactness; `HistoryBuilder.lean` combines this with finite transport
    spines to construct `buildHistory k root` for every root.
    `RawZipper.lean` mirrors all nine selected child shapes of the compiled
    grammar.  It turns every marked hit into an exact raw path, factors that
    path at the certified source and earlier-prefix words, recovers the source
    addition and arbitrary expanded transport sibling, and proves
    `RawHistoryTree.allMarkProvenance_root`.
    `HistoryWitness.lean` then proves the structural prune live, obtains a
    positive lag at every finite root output, takes their finite minimum, and
    constructs `builtRetardedEliminationWitness`.  The resulting theorem
    `quarter_lower_bound_of_feasible` has no termination, deletion,
    provenance, or eliminated-tree hypothesis: finite KL feasibility and the
    base functional assumptions imply the exact quarter-factor exponential
    bound.  The axiom audit reports only `propext`, `Classical.choice`, and
    `Quot.sound`.

## Corrections to the current notes

### The printed predecessor identity (2.1) is false

The literal identity `phi_k^m(y) = phi_k^(2m)(y-1)` for `m = 1 (mod 3)`
fails already at `k=2, m=7, y=1`: the two sides are 3 and 2.  The intended
counting transfer must instead use the one-sided inclusion
`phi_k^m(y) >= 1 + phi_k^(2m)(y-1)` under the appropriate nonperiodicity and
range hypotheses, then pass from arbitrary targets by sufficiently many
doublings while avoiding the finitely many points of a cycle.  This actual
predecessor-family instantiation is not yet in Lean; no theorem in the current
project assumes the false equality.

### The pure-branch root needs a special condition

Theorem 2(a) of `renormalization-at-minus-one.md` is false as written at
`q = 0`.  The self-loop means

`H(0) = min(H(0), H(1/3), H(2/3))`

only forces both nontrivial child values to be at least 1.  The original root
equation is stronger: at least one of them must equal 1.  Equivalently, the
smaller nontrivial `Pi` child is `A^(-1)`.  `RootLaw.lean` proves the correct
root law and gives a concrete counterexample to the claimed unrestricted
"if and only if."

This does not invalidate the useful conclusion that the small root lift is
`A^(-1)`.  It changes the stated classification of all pure-branch solutions.

### The shell-mass law assumes the missing global bound

Section 6.2 writes `Pi(q) asymp A^(-nu(q))` by assuming the free
min-harmonic factor `H` is uniformly `O(1)`.  The preceding local theorem does
not supply that bound; it explicitly leaves boundary data free.  Along the
finite tower those free values may depend on `k`, and this is exactly how the
normalized eigenvector mass could concentrate.

Consequently, the ratio `A/3` is a well-supported measurement and a valid
conditional calculation under uniform two-sided bounds on `H`.  It is not yet
a theorem about the globally selected KL eigenvectors.  Proving the required
uniform-integrability or pressure estimate is C1', not a corollary of the
local min system.

### The local spectrum is not yet a global contraction theorem

The labels `{0,1}` describe selected-coordinate linearizations away from ties.
A rigorous spectral assertion also needs a specified function space, a fixed
selection pattern, control of arbitrarily small argmin gaps, and a theorem
relating the finite boundary-selected eigenvectors across levels.  The notes
themselves record deep margins approaching zero.  Thus this calculation
explains the observed marginality but does not prove tail decay.

### A two-input mixer does not give the proposed one-sided C3

For a nonnegative mixture `x = p t + q b`, its range is at most the weighted
sum of the two input ranges.  Its normalized oscillation is therefore bounded
by a convex combination of the two input oscillations.  It need not be no
larger than the transport input alone: the branch input can import variation.
`Mixer.lean` proves the valid range bound and an exact counterexample to the
stronger assertion.

### Finite data do not decide the asymptotic regime

The k=15--19 values, tail ratios, dimensions, and localization at `-1` are
valuable diagnostics.  Fits and pre-registered predictions are evidence, not
uniform estimates.  Slowly varying, polynomial, or renewal-critical behavior
cannot be excluded by the present number of levels.

### The first charged spine-face Lyapunov architecture is impossible

The aligned profile action is a scalar combination of the identity and the
swap of lift labels 1 and 2.  Both the mean vector `(1,1,1)` and the co-spine
oscillation vector `(2,-1,-1)` are fixed by that swap, so their eigenvalues
are exactly equal.  A zero-charge residue cycle can therefore carry a
normalized multiplier of one. `MarginalObstruction.lean` proves the
J-independent algebraic part of this no-go result and the concrete retarded
`2 -> 2` self-lift at every precision.  `OrbitHitting.lean` now supplies the
previously missing location theorem: by LTE, the first `t` with
`2*4^t = -1 (mod 3^J)` is exactly `(3^(J-1)-1)/2`.  In particular, for every
`J >= 3` the first `J` backward-orbit points do not charge the `2 -> 2`
self-loop.  `retarded_zero_uncharged_selfLift` packages the two facts.

This falsifies the proposed strict relative-contraction certificate class; it
does not imply a finite ceiling for the KL exponents.  The abstract corrected
charged-carrier and pressure theorems remain valid conditional tools.

## Revised proof route: global equality-case rigidity

Write the exact finite eigen-equation schematically as

`c = p U c + b(c)`,

where `U` is the multiplication-by-four transport permutation and `b` is the
branch/min contribution.  Unrolling for `n` steps gives

`c(x) = p^n c(U^n x) + sum_{j<n} p^j b(c)(U^j x)`.

On a transport cycle of length `N`, this becomes an exact resolvent formula.
The failed charged construction shows that a product automaton allowing
independent local policies contains marginal paths which need not arise from
one globally compatible eigenfunction.  The revised architecture is:

1. Characterize equality in the local `min <= mean` inequalities underlying
   the exact defect identity.
2. Retain overlap constraints forcing every local minimizing choice to come
   from one global eigenfunction, instead of treating sibling sources as
   independent profiles.
3. Classify globally compatible zero-dissipation eigenfunction/eigenmeasure
   pairs.  The expected exceptional possibility is concentration on the
   negative-cycle spine and its backward orbit.
4. Prove a mass or renewal estimate excluding sufficient concentration.  A
   qualitative decay theorem is enough; an exponential spectral gap is not
   required.
5. Invoke the formal weighted-tail, defect, endpoint, and counting bridges.

The hard mathematical step is the global compatibility classification.  GPU
eigenvectors can suggest its equality locus, but a finite over-approximation
which forgets shared values is too weak by construction.

The subsequent combined-automaton experiment sharpens this diagnosis.  Its
portable tilted rows are exact for an annealed window-split model, but the
split law and multi-input localization remain hypotheses; the residue-charged
strict Lyapunov route is exactly marginal and cannot close.

## Other proof routes worth keeping alive

- **Direct subeigenvectors.**  For each fixed rational `lambda < 2`, construct
  feasible KL vectors at every sufficiently large precision.  This would show
  `lambda_k -> 2` without first proving convergence of extremal eigenvectors.
  It may be easier to certify than C1' if a uniform symbolic ansatz is found.

- **Multiscale energy.**  Track a vector of seminorms: internal fiber range,
  variation of fiber minima, and mass near exceptional return classes.  Seek a
  block contraction after a full `5 -> 2 -> 8` phase rather than at one branch.

- **Compactness contradiction.**  Normalize the eigenvector masses and take a
  weak limit.  This requires tightness/uniform integrability and a valid limit
  equation; those requirements are close to C1' itself, so this is currently
  less direct.

## Lean dependency path to the counting theorem

1. The repaired two-phase history construction, retarded comparison, literal
   predecessor base system, and arbitrary-target counting transfer are now
   kernel checked.  This completes the finite-feasibility-to-counting path
   without using the invalid printed derivation.
2. Prove either a cofinal exact feasible-vector construction with parameters
   tending to two, or the critical-eigenvector localization theorem.  The
   first route is already connected to the counting endgame and needs no
   nonlinear Perron existence theorem.
3. If pursuing localization, ingest the portable finite pressure certificate
   into a Lean-computable certificate value (the generic exact checker is
   already proved sound).
4. Formalize the combined uniform localization/domination theorem.  The later analytic step
   from `lambda_k -> 2` to `x^(1-epsilon)` is already kernel checked.

The last conclusion is not the Collatz conjecture.  It says that every
positive target not divisible by three has very many predecessors up to `x`
in the one-halving Syracuse graph; it does not say every positive integer's
forward orbit reaches 1.  The standard Collatz statement is already fixed in
the project so that no later theorem can silently substitute the counting
milestone for the conjecture.
