# Audit of the fiber-geometry program

Last updated: 2026-07-20.  This audit compares the current Lean development
with the live notes in `../docs/notes/`, especially `fiber-geometry.md`,
`adversarial-operator.md`, `sol-pressure.md`, and
`renormalization-at-minus-one.md`.

## Bottom line

The numerical geometry is strong evidence for a useful theorem, but the
restricted-pressure inequality C1' has not been proved.  The missing step is
not the elementary weighted-tail reduction.  It is a uniform, global bound
showing that the exact extremal eigenvector cannot move enough mass into the
exceptional return tree as the precision grows.

This is a plausible target for formalization.  The downstream implication
from weighted-tail decay to `lambda_k -> 2` is now formalized, but its uniform
localization premise is not proved.  Thus this is not presently a proof of
`lambda_k -> 2`, the `x^(1-epsilon)` predecessor-counting result, or Collatz.

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

## Corrections to the current notes

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

## Most promising proof route: a certified first-return pressure bound

Write the exact finite eigen-equation schematically as

`c = p U c + b(c)`,

where `U` is the multiplication-by-four transport permutation and `b` is the
branch/min contribution.  Unrolling for `n` steps gives

`c(x) = p^n c(U^n x) + sum_{j<n} p^j b(c)(U^j x)`.

On a transport cycle of length `N`, this becomes an exact resolvent formula.
This suggests the following proof architecture.

1. Define a nonnegative exceptional energy that records both within-fiber
   range and the cross-fiber variation imported by a branch minimum.
2. Collapse transport stretches exactly with the cycle resolvent and define a
   first-return kernel to the 2- and 8-branch exceptional states.
3. Construct a finite product cone or finite automaton that dominates every
   policy, every precision, and every admissible profile.  A state recording
   only the `-1` itinerary is insufficient; it must retain the genealogy of
   variation imported from sibling fibers.
4. Prove an analytic bound on the omitted long-return tail.
5. Exhibit rational `h > 0` and a tilted rational gap `R^b < z^a` satisfying
   `K h <= R h`.  `PressureCertificate.lean` now proves the explicit
   terminal-potential bound and block-Chernoff geometric decay; `R` itself
   need not be below one.
6. Connect that decay to the actual eigenvector-weighted tails and invoke the
   formal R' theorem.

The hard mathematical step is item 3: proving that the finite kernel really
dominates the full nonlinear KL refinement uniformly in `k`.  GPU eigenvectors
can suggest `h`, `R`, and the relevant states, but Lean must check an exact
domination theorem, not the floating-point spectrum.

The subsequent ball-automaton experiment confirms this diagnosis.  Its
portable tilted pressure certificate now passes an independent exact verifier,
but its single-profile localization matrices fail on aligned top-digit classes
at every block length.  See `GPU_CERTIFICATE_SPEC.md` for the refined combined
automaton needed to prove localization.

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

1. Formalize critical nonlinear Perron eigenfunction existence and define the
   critical parameters `lambda_k` without importing an unchecked theorem.
2. Ingest the portable finite pressure certificate into a Lean-computable
   certificate value (the generic exact checker is already proved sound).
3. Formalize the combined uniform localization/domination theorem or a direct feasible-vector
   construction.
4. Formalize the Krasikov--Lagarias difference-inequality transfer from
   `lambda_k -> 2` to predecessor counts `x^(1-epsilon)`.

The last conclusion is not the Collatz conjecture.  It says that every target
has very many predecessors up to `x`; it does not say every positive integer's
forward orbit reaches 1.  The standard Collatz statement is already fixed in
the project so that no later theorem can silently substitute the counting
milestone for the conjecture.
