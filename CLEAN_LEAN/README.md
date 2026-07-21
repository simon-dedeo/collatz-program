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

`CriticalAssignment.lean` now formalizes the algebraic core of that global
argument.  A critical assignment keeps both sides of every sum and one
minimizing side of every minimum; Lean proves that one always exists and that
the tree value is exactly the sum of its selected leaves.  It also proves the
precise safe-deletion interface: once the still-missing path argument shows
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
transport sibling.  What remains is to instantiate this abstract theorem with
the recursive concrete KL splitter and then prove termination and
order-independence.

`ConcreteElimination.lean` now instantiates one complete split.  Its labelled
body is exactly the KL transport leaf plus the appropriate three-lift minimum
with shifts `-2`, `alpha-2`, and `alpha-1`.  Translation by an arbitrary
parent shift is proved exact; permitted splits preserve the lower shift bound
`-2`; fully retarded finite trees acquire a positive common lag bound; and
erasing internal labels preserves functional evaluation.  On the LP side,
the erased base split's coefficient is proved equal to the concrete nonlinear
KL operator, so exact finite feasibility makes splitting monotone in the
correct direction inside any surrounding labelled context.  The remaining
construction is repeated splitting plus deletion and its termination proof.

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
206, proving the surviving subtree depends on its ancestry.  This refutes
printed equation (3.2) and the following history-free subtree argument.  It
does not establish nontermination or refute the intended elimination theorem;
that theorem now requires a repaired proof.

`EliminationWitness.lean` pins the exact output required of that remaining
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
left-alternative deletion.  Every critical assignment after a globally safe
deletion lifts to a pre-deletion critical assignment with the same selected
sum, and satisfaction of every principal bound is equivalent across the
lift.  Hence the `(3.4)` invariant passes through that deletion even when an
outer minimum acquires a new tie.  The right-alternative symmetric statement
is still to be added; neither orientation supplies termination.

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
finite state/edge-table identity, but not yet the all-level ball-mass
domination or the irrational interval-weight bounds.

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
The inference from any finite feasible record to a predecessor-counting bound
still depends on the now-unrepaired KL advanced-term elimination theorem.

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
