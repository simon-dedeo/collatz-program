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
feasible vectors below every fixed parameter less than two.  The finite-level
counting bridge is now complete: the KL difference functions are instantiated
with actual Syracuse predecessor counts using the corrected one-sided
doubling argument, not the false printed equation (2.1).

This is not an end-to-end formal verification of the original KL paper as
printed.  Exact counterexamples invalidate its printed advanced-term-
elimination construction.  The project instead kernel-checks a replacement
history/pruning argument and the downstream counting transfer needed here.

The annealed comparison is now stated at the actual finite-system level.  Lean
defines the linear operator obtained by replacing each fiber minimum by its
three-point average and proves the exact slack identity
`s(lambda)-1=(w_2+w_8)delta+Sigma`.  It also proves
`2 delta <= Delta_terminal <= 4 delta`, the sharp local ternary Pearson bounds,
their parent-mass-weighted Jensen corollary, and the resulting sequential
bridge: terminal localization together with vanishing aggregate normalized
slack forces `lambda -> 2`.  This kernelizes the algebra around the current
research gap without asserting the missing uniform pressure/localization
estimate.  The annealed endpoint now also has an all-level, concrete `ZMod`
trace theorem: summing the three new top-digit lifts commutes with the literal
annealed KL operator.  At levels two and three Lean checks the exact normalized
stationary laws, their trace compatibility, and the exact terminal-variation
floor `622/1533 > 81/200` directly by rational arithmetic.  Mathlib's exact
order theorem for `4=1+3` modulo powers of three proves that the affine
transport is one full cycle at every level.  A tight projective domination
therefore propagates through every coordinate, proving uniqueness of every
normalized nonnegative annealed fixed vector (nonzero fixed vectors first
become strictly positive) and making the one-step trace consistency theorem
canonical.  In particular, the displayed level-two and level-three rational
laws are now identified as the only normalized nonnegative endpoint fixed
vectors, rather than merely checked examples.

`LevelLift.lean` formalizes the paper's level monotonicity argument: copying a
feasible vector to all three new top-digit lifts preserves feasibility.  Thus
the exact critical feasibility suprema are nondecreasing in the residue
precision, with no spectral-radius theorem imported.

`StrictLift.lean` proves a qualitative strengthening of finite feasibility.
If `1 < lambda < 2` is exactly feasible at level `k >= 2`, then level `k+1`
is feasible at some `lambda'` strictly between `lambda` and `2`.  The proof
kernel-checks superadditivity, propagation of a nonzero lift slack around the
full transport cycle, finite-coordinate continuity in `lambda`, and final
subeigenvector normalization.  Iterating gives an infinite strictly increasing
ladder of exact feasible parameters from any nontrivial starting certificate.
This still does not prove `lambda_k -> 2`: the theorem supplies no uniform size
for the increase, so the ladder may converge to a value below two.

`CoarseMinimum.lean` proves the complementary one-level comparison.  Taking
the minimum over each three-point top-digit fiber after applying the fine
operator dominates applying the coarse operator to the fiber minima.  Hence
the coarse minimum of an exact fine fixed vector is a coarse supersolution.
This is only an order statement: it does not prove the conjectural quadratic
growth of iterated terminal excess, which the research notes correctly
restrict to selected critical fixed vectors and explicitly falsify for generic
feasible vectors.
For a positive exact fine fixed vector, the same module subtracts the two
finite oscillation identities to identify normalized coarse super-slack with
the increase in normalized minimum defect.  It consequently kernel-checks the
ordinary data-processing inequality: the defect cannot decrease under this
selected coarse projection.  The missing research claim is the stronger
uniform quadratic increase.

`QuadraticDefect.lean` now kernel-checks the exact endgame proposed by the
iterated-minimum experiments, without assuming it has been proved for KL
vectors.  Each inequality
`e_(j+1) >= e_j + (3/2)e_j^2` drops the reciprocal defect by at least `3/5`;
after `n` stages this gives `e_0 <= 5/(5+3n)`.  A triangular family with an
unbounded number of such stages therefore has vanishing initial defect, and
the exact oscillation identity implies `lambda_k -> 2`.  The missing theorem
is still the all-level quadratic inequality for the selected critical
profiles, not this scalar telescoping argument.

`ArgminFrustration.lean` kernel-checks the local algebra behind that missing
inequality.  For an exact fine fixed vector, every coarse slack row is exactly
the minimum of its three fine-versus-coarse residuals.  Retarded and advanced
residuals split as the weighted sum of nonnegative transport and refinement
excesses.  A generic three-label lemma proves that mismatched minimizing
labels pay at least the smaller weighted second-gap, and sums this bound over
an arbitrary finite edge set.  What remains open is the global, selected-
critical lower bound saying that enough weighted label frustration is present
to dominate a fixed multiple of the squared terminal defect.  The module now
defines this remaining premise verbatim as `HasQuadraticFrustration` using
canonical ternary argmins.  It proves that the canonical frustration mass is
bounded above by the exact total coarse slack and that
`HasQuadraticFrustration` implies one step of the `3/2` terminal-excess law.
Thus the local algebra, the global reduction, and the reciprocal telescope are
checked; only the selected-critical frustration lower bound itself is open.

`RetardedComparison.lean` formalizes the analytic core of KL Theorem 5.1.
For any finite nested sum/min difference system whose leaves all have positive
backward shifts, LP feasibility propagates an exponential lower bound from an
initial strip to every nonnegative time.  Its final corollary derives the
paper's exact `1/(4 max c)` constant.  `HistoryWitness.lean` now supplies the
previously missing advanced-term elimination by a repaired two-phase
construction, rather than by the invalid printed finite-step derivation.

`TreeRewrite.lean` handles the splitting substep: substituting a valid rule
inside any sum/min context preserves the functional inequality, while the
associated exponential coefficient inequality moves in the opposite, feasible
direction.  It also kernel-checks a counterexample showing that deleting a
minimum alternative is not a local consequence of positivity and monotonicity;
the paper's global critical-path argument is genuinely required.

`CriticalAssignment.lean` now formalizes the algebraic core of that global
argument.  A critical assignment keeps both sides of every sum and one
minimizing side of every minimum; Lean proves that one always exists and that
the tree value is exactly the sum of its selected leaves.  It also proves the
precise safe-deletion interface: once a path argument shows
that no critical assignment can use an alternative, deleting it preserves the
functional inequality, while coefficient feasibility is weakened in the
sound direction automatically.  This first model deliberately omits the
labels and ancestry supplied by the richer tree below.

`EliminationTree.lean` adds the richer tree that the literature proof really
needs: internal principal vertices retain their residue/shift labels, and
critical assignments retain complete selected root-to-leaf paths.  Lean proves
that valid local split inequalities imply KL's assignment-specific bound
(equation 3.4), formalizes selected subassignments through arbitrary nested
sums/minima, and proves the deletion contradiction: a later leaf repeating an
ancestor state cannot be selected when its split has the mandatory positive
transport sibling.  The later occurrence-indexed two-phase construction
instantiates this argument without interleaving splits and deletions, so no
order-independence claim is needed.

`ConcreteElimination.lean` now instantiates one complete split.  Its labelled
body is exactly the KL transport leaf plus the appropriate three-lift minimum
with shifts `-2`, `alpha-2`, and `alpha-1`.  Translation by an arbitrary
parent shift is proved exact; permitted splits preserve the lower shift bound
`-2`; fully retarded finite trees acquire a positive common lag bound; and
erasing internal labels preserves functional evaluation.  On the LP side,
the erased base split's coefficient is proved equal to the concrete nonlinear
KL operator, so exact finite feasibility makes splitting monotone in the
correct direction inside any surrounding labelled context.  The repaired
repeated construction and its termination proof are supplied by the indexed
history modules described below.

`SymbolicShift.lean` records every path shift exactly as an integer pair
`a + b*alpha`; the transport, retarded, and advanced increments are
respectively `-2`, `alpha-2`, and `alpha-1`.  Finite control words are proved
translation invariant at this symbolic level.  This is the appropriate input
for a cycle-negativity termination certificate: the shifts are not integer
weights, despite a shorthand suggestion in the research handoff.
`TerminationCertificate.lean` supplies the complementary finite checker: a
natural-number rank table that strictly decreases on every declared control
edge gives an explicit bound on every path length.  Applying it still requires
a sound finite control quotient of the ancestor-dependent KL grammar.

`TerminationObstruction.lean` kernel-checks a level-five legal history which
returns to residue 188 by a transport child at the strictly larger shift
`7*alpha-11 > 0`.  All seven preceding refinement destinations are new and
therefore survive the published ancestor-repeat deletion test.  Re-expanding
the returned root makes its child 206 deletion-eligible against the earlier
206, proving the surviving subtree depends on its ancestry.  This invalidates
the finite-step inference used to derive printed equation (3.2), which itself
assumes an infinite path, and directly refutes the following history-free
subtree argument.  It does not establish nontermination or refute the intended
elimination theorem; that theorem now requires a repaired proof.

`EliminationWitness.lean` pins the exact output required of the elimination
construction.  A witness is a finite family of labelled trees with a common
positive lag, functional soundness, and coefficient soundness.  Lean proves
that any such witness immediately gives KL's exact `1/(4*C)` exponential
lower bound.  It also proves that the original retarded and neutral rows are
already fully retarded, so only the advanced rows require recursion.  This
turns Theorems 3.1--4.1 from an informal literature citation into one explicit
construction obligation.

The global safe-deletion theorem is now also formal.  “Totally
non-critical” is defined at the whole-tree level using selected
subassignments, not as a local inequality.  Lean proves by induction through
arbitrary principal, sum, and minimum contexts that removing such an
alternative leaves the functional value unchanged.  In the subtle case where
an outer minimum does not select the path to the deletion, raising that path
cannot make it newly minimizing.  This is precisely the global fact the local
counterexample does not provide.
Both left- and right-alternative deletion are covered, and the erased
coefficient expression moves monotonically upward in either case, so the LP
feasibility side of deletion needs no additional analytic hypothesis.

`DeletionInvariant.lean` closes the separate “new critical tie” issue for
both deletion orientations.  Every critical assignment after a globally safe
deletion lifts to a pre-deletion critical assignment with the same selected
sum, and satisfaction of every principal bound is equivalent across the
lift.  Hence the `(3.4)` invariant passes through that deletion even when an
outer minimum acquires a new tie.  Neither orientation supplies termination.

`BranchArrivalTermination.lean` proves the new abstract compactness argument:
over finitely many residues there is no infinite nonnegative sequence whose
return heights are nonincreasing and whose successive branch-arrival
increments are `alpha` minus a natural number.  The proof includes a Lean
proof that `alpha = log_2 3` is irrational and the exact compressed B2/B8
shift formulas.  To turn this into a repair of the KL elimination theorem we
still must derive those sequence hypotheses from an infinite path obeying the
actual ancestry-sensitive deletion rule.

Two further kernel-checked obstructions explain why this termination component
does not yet repair the literature proof.  `AllThreeDeletionObstruction.lean`
exhibits a legal level-five history whose next split makes all three new
minimum alternatives deletion-eligible, contradicting the claimed
nonempty-minimum invariant.  `SplitInvariantObstruction.lean` then shows that
even a locally valid split can activate a formerly losing outer-minimum branch
and violate an inherited principal bound.  The latter countermodel uses
positive constant (therefore monotone) functions and the actual formal
critical-assignment semantics.  A corrected proof needs a genuinely
split-stable invariant or different rewrite semantics, not only a termination
argument and backjump rule.

A current repair candidate separates the operations into two phases.  First,
build the entire finite good-history expansion using splits only, marking
higher repeated branch leaves as terminal; compactness supplies finiteness and
global local validity survives every split.  Second, with no later splits,
propagate marked/dead occurrences upward and delete them only at minima with a
live sibling.  This architecture is designed to handle the all-three case
without an empty minimum while avoiding the split-after-deletion activation
counterexample.  `MarkedPruning.lean` now checks the structural dead recursion,
live-root criterion, mark-free output, and coefficient monotonicity;
`TwoPhasePruning.lean` checks pointwise functional deletion and invariant
preservation.  `OccurrencePruning.lean` replaces label-based marks by marks on
individual syntax occurrences and proves the full one-pass Phase-B theorem:
if every marked occurrence contradicts inherited principal bounds, the root
is live, functional evaluation is exactly preserved, leaf bounds survive,
and coefficient evaluation moves in the feasible direction.  The repeated
branch contradiction now also accepts arbitrary recursively expanded
transport siblings and assumes positivity only at the nonnegative arguments
actually used.
The exact provenance payload and the theorem turning it into a sound mark are
kernel checked; the indexed builder now constructs that payload recursively.
The global form allows each marked hit to name a different earlier ancestor;
`AllMarkProvenance` plus the universal `shift>=-2` invariant now implies
`MarkingSound` without an additional semantic assumption.
`HistoryWords.lean` and `RawHistoryTree.lean` now pin the builder to exact
edge words and the real KL split grammar.  Lean derives local functional
validity, the raw root comparison, the feasible-coefficient comparison, and
the terminal shift invariants from any finite such tree.  Consequently the
construction contract contains no analytic or LP soundness fields: it asks
for the finite histories, their syntactic mark provenance, a live pruning,
and one common retarded lag bound; all four are now supplied below.
`TwoPhaseWitness.lean` packages the builder contract and proves that any
inhabitant is automatically the existing `RetardedEliminationWitness`.
`CheckpointTermination.lean`, `HistoryBuilder.lean`, and `RawZipper.lean` now
construct that inhabitant: compressed branch recursion is well founded,
finite transport spines terminate, and every selected mark yields exact
prefix provenance for its source split and earlier principal.
`HistoryWitness.lean` proves deterministic pruning live, takes the finite
minimum of the positive output lags, and constructs the full witness.  Its
`quarter_lower_bound_of_feasible` theorem derives the exact comparison bound
directly from finite KL feasibility, with no remaining elimination or
provenance assumption.

`PredecessorTransfer.lean` begins the concrete counting construction.  It
defines the literal path-bounded predecessor set using the actual Syracuse
iterate and kernel-checks the corrected replacement for the false printed
equation (2.1): for a positive nonperiodic `a = 1 (mod 3)` and `2a <= X`,
`P*_a(X)` is the disjoint union of `{a}` and `P*_(2a)(X)`.  It also proves
`predecessorCount (2^r a) X <= predecessorCount a X` and the finite-cycle
lemmas needed to manufacture nonperiodic targets.  `KLPredecessorFunctions.lean`
now defines the literal floor cutoff, path-bounded target count, and natural
infimum in every concrete residue state.  It proves every target pool
nonempty by Euler multiplication above a finite periodic orbit, and therefore
proves positivity and monotonicity of the infimum functions without additional
hypotheses.  `PredecessorBase.lean` proves the two reverse subtrees disjoint
for a nonperiodic target, checks all real `log_2(3)` cutoff identities, maps
the transformed targets into the exact transport/refinement residue fibers,
and proves `predecessorPhi_satisfiesBaseSystem` for every `k>=2`.  Thus the
abstract elimination theorem is now instantiated by the literal predecessor
functions.  `CountingTransfer.lean` completes the finite-level seam: exact
feasibility at `k>=2` and `1<lambda<=2` implies
`HasPredecessorExponent a (logb 2 lambda)` for every positive `a` not divisible
by three.  It proves the exact real cutoff identity, bounds a feasible vector
by its finite coordinate sum, escapes arbitrary finite cycles by a sufficiently
large power-of-two multiple, and transfers the count back to the original
target.  Consequently, any exact feasible sequence tending to two proves
almost-linear predecessor counting with no separate literature-transfer
hypothesis.

`PressureCertificate.lean` now also accepts the portable sparse-edge format
used by `lemma5_exact_cert.json`: it compiles a finite edge table to a rational
kernel and proves that a successful Boolean row check yields the real pressure
inequalities. `PortablePressureData.lean` is generated from the hashed JSON and
kernel-checks `h >= 1` and all 2,187 tilted rows: the `lambda=2` instance and all
eight pieces covering `[lambda_18,2]`.  Each checked piece is then composed with
the terminal-potential theorem to give an all-length real bound
`pressureMass K n q <= R^n * h(q)`.  The two Chernoff gaps are likewise checked
by exact rational arithmetic.  More importantly, this ball-automaton
certificate is not the missing localization theorem.

`BallPressureAutomaton.lean` independently reconstructs the 243-state graph
at window depth six from the concrete KL residue formulas.  Lean proves that
its transport, branch targets, and three lifts agree with `ResidueSystem`, and
that the six charged states form the advertised initial backward-four orbit
of `-1`.  The generator checks every imported adjacency list equal to this
independent graph, including the target-dependent tilt.  This closes the
finite state/edge-table identity.  `PressureWeightBounds.lean` additionally
checks an exact rational upper bound for `alpha`, verifies that all nine
rational parameter pieces tile their advertised intervals, and proves that
the stored rational edge weights dominate the true irrational KL weights on
every piece.  The remaining pressure-side semantic obligation is a general
all-level ball-mass domination theorem; C1' localization is still the central
open implication.

The first charged spine-face Lyapunov proposal has been exactly falsified,
not assumed away: `MarginalObstruction.lean` proves that its aligned mean and
co-spine modes have the same eigenvalue.  This is a no-go theorem for that
certificate class, not evidence against `lambda_k -> 2`.  The concrete KL
system also has the retarded `2 -> 2` self-lift at every precision.
`OrbitHitting.lean` now proves with mathlib's LTE theorem that the first time
`2*4^t = -1 (mod 3^J)` is exactly `(3^(J-1)-1)/2`; hence for every `J >= 3`
this self-loop is outside the proposed first-`J`-orbit-point charge set.  The
arithmetic qualification in the earlier no-go statement is therefore closed.

`FiniteRecord.lean` contains a small Lean-native certificate at level 2.  It
checks the integer rows and logarithmic cross-products by kernel reduction and
then invokes the same soundness path intended for the large streamed records.
`hasPredecessorExponent_four_thirds` now carries that certificate through the
entire chain to an unconditional ordinary-predecessor exponent theorem for
every eligible target.  The same path accepts large streamed records once
their data are converted to the checked certificate format.

`FiniteRecordK12.lean` is the first large exact import.  Its deterministic
generator pins the SHA-256 digest of `experiments/kl/cert_k12.json`, translates
all 177,147 integer coordinates, and kernel-reduces the normalization and row
inequalities in small synchronous blocks.  A separately proved semantic map
identifies the direct natural-number checker with the generic `ZMod` KL
system, including transport, branch, refinement target, and all three fiber
lifts.  No `native_decide` or external-verifier result is used.  The resulting
theorem gives the exact certified exponent
`logb 2 (18064231 / 10000000)` (approximately `0.85313584`) for every eligible
target.  The multi-gigabyte `k=15--19` records still require a more scalable
artifact than embedding every coordinate in Lean source.

`FiniteRecordLadder.lean` combines that level-12 certificate with the strict
adjacent lift.  Unconditionally, there exists a strictly increasing exact
feasible parameter at every level `12+n`, all below two; in particular, every
later level admits some feasible parameter strictly above the certified
level-12 value.  The selected ladder is noncomputable and may converge below
two, so this is not the almost-linear counting theorem.  As a direct counting
corollary, every positive target not divisible by three has some one-halving
Syracuse predecessor exponent strictly larger than the level-12 exponent.
This improvement is existential rather than a new numerical certificate.

The provenance boundary is explicit: Lean checks the generated integers and
their mathematical meaning, but does not hash the JSON.  Running
`python3 scripts/generate_finite_record_k12.py --check` validates the fixed
source digest and fails unless every checked-in generated module is current.
CI or a reviewer can use that command to enforce JSON-to-Lean reproducibility.

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
