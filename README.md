# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, and formalization, with every claim backed by a
machine-checkable artifact. Started 2026-07-20 (Claude Fable 5 +
GPT-5.6-sol; PSC Bridges-2 grant mth260010p).

Made possible by the support of Grant 63750, "Explaining Universal Truths",
from the John Templeton Foundation. Additional support from research funds
of the Laboratory for Social Minds and from the Survival and Flourishing
Fund. Proofs and Reasons — https://proofsandreasons.io

Continually updated until we hit usage limits.

## A note from the human

I (Simon) am a cognitive scientist, not a mathematician; http://santafe.edu/~simon/cv.pdf

This is a purely experimental project to see what these systems do, and how they reason. There are *many* problems with using AI for mathematics, some of which my colleagues and I have written about---see, e.g., https://arxiv.org/pdf/2603.13680 (*A correspondence problem for mathematical proof*, Eamon Duede and I). One of the things I'm most aware about is the fact that these machines are leveraging insights from real mathematicians, but are unable to properly credit their insights. Anything here should be credited to "the human mathematics community, with apologies." Our colleague, and Proofs and Reasons board member, Michael Harris has written eloquently about the core issues in a recent Boston Review article, https://www.bostonreview.net/articles/knowledge-collapse/

I chose the Collatz Conjecture for three reasons:

1. I understand the theorem!
2. A bit like Fermat's Last Theorem, everyone and their grandmother has worked on it, and any progress towards a proof is unlikely to harm an early-career researcher carving out a new niche.
3. There have been some lovely quanta articles about Collatz and the related Busy Beaver numbers recently, so it was a nice way to learn more https://www.quantamagazine.org/busy-beaver-hunters-reach-numbers-that-overwhelm-ordinary-math-20250822/ I had an idea that there was wisdom hiding in the Busy Beaver community that was partially orthogonal to what "regular" mathematicians know.

Everything below this line, and everything else in this repo, has been automatically generated. Claude Fable 5 drove the initial numerics and research program; a Codex/GPT instance is now the research driver. A separate GPT instance is formalizing the work in Lean in `CLEAN_LEAN`; it was told to make something that would not annoy Kevin Buzzard. If you want the inter-company drama, visit https://github.com/simon-dedeo/collatz-program/blob/main/CLEAN_LEAN/FOR_FABLE.md

## What we are trying to prove now

The long-range quantitative target remains `λ_∞=2` for the Krasikov–Lagarias
predecessor-counting systems. It would imply `π_a(x)≥x^{1−ε}` for every
`ε>0`, but it is open, and the autonomous charged/projective-contraction route
is now closed for every admissible precision `J≥3`. That no-go is about a proof
method, not evidence that `λ_∞<2`.

The finite-level counting bridge is now complete. Commit `76ec861` converts
exact KL feasibility at every `k≥2` and `1<λ≤2` into
`HasPredecessorExponent a (log₂λ)` for every positive target not divisible by
three. The immediate mathematical target is therefore the limit again: build
a cofinal feasible sequence with `λ→2`, or prove the pressure/localization
statement that supplies one. In parallel, the first larger streamed record is
being imported into Lean to make the mixed Python/Lean trust chain portable.
An exact within-vector genealogy audit has now isolated a sharper candidate
for the localization half: the required pointwise depth-nine split fails, but
mass-weighted high-oscillation tails are nonincreasing at every one of 756
tested adjacent-scale rows through `k=19` (strictly decreasing in all 619
nonsaturated rows). This is finite evidence, not an all-level
recurrence. A rational bin cone then closes exactly on all tested rows after a
fixed burn-in, but the floating `k=20` holdout violates both earliest-burn-in
constants. Moving the burn-ins one level later passes provisionally. The live
theorem target is now uniform control of the burn-in and of weighted
immigration at every fixed terminal offset.
The preceding advanced-term elimination gap is repaired by a replacement,
not by validating the printed construction.
The printed proof still has three exact, kernel-checked defects—its descent
inference, nonempty-minimum assertion, and split-invariant induction must not be
reused—but commit `3d6a186` supplies a different occurrence-aware construction.
Lean now builds the finite raw history forest by well-founded recursion, proves
root-level repeat provenance, deterministically prunes it to a live retarded
tree with a common positive lag, and feeds that tree into the abstract
comparison theorem. In particular, `quarter_lower_bound_of_feasible` derives
the exact `1/(4C) · c_m · λ^y` lower bound from finite feasibility for every
positive monotone solution of the base system, with no remaining termination,
deletion, provenance, or retarded-tree assumption.

The closed bridge cannot quote the paper literally. An exact `k=2` audit
refutes printed counting identity (2.1):
`φ^7_2(1)=3 ≠ 2=φ^{14}_2(0)`. Lean commit `58f0ef8` checks the exact targetwise
replacement and ordinary-count transfer. Commit `331ff48` defines the literal
statewise infimum, proves every target pool nonempty, and checks normalization
and monotonicity for the class-2 family. At the paper level, infimizing the
targetwise identity over the full target classes gives
`φ^m_k(y)≥1+φ^{2m}_k(y−1)` in the useful direction. The final Lean path
bypasses a separate class-1 `φ` by using the checked ordinary-count inclusion.
Commit `729f5fa` now proves the full D1–D3 residue-infimum theorem
`predecessorPhi_satisfiesBaseSystem`; the 8,717-job Lean audit passes with only
the standard mathlib axioms. Commit `76ec861` closes the exact cutoff,
fixed-target, arbitrary-cycle-target, and all-level transfer wrappers. Combined
with the exact `k=19` certificate, this proves the headline bound under the
repo's mixed trust policy: the 387,420,489 feasibility rows are checked by the
exact Python bigint verifier, while the generic implication is kernel-checked
in Lean. The large record is not yet a single Lean-native theorem.

The clearest bounded theorem-shaped side target is the all-dimension
**arctic/max-plus no-go** for Zantema's Collatz string-rewriting system. A successor audit replaced a
false reducible-matrix cyclicity argument with an elementary weighted-walk
pumping candidate. Exact word macros and bounded witnesses are checked, but the
general argument remains provisional until Lean review. Longer-horizon bets are
mixed-radix `2–3` anti-concentration and genuinely non-autonomous/arithmetic
mechanisms for the KL limit.
An audited handwritten argument also overturns the former unsigned-zeta
natural-boundary bet at its claimed first circle; its exact finite checker is
in-repo, while formalization of the general analytic step remains open.

None of these statements settles Collatz, positive density, divergence, or
nontrivial cycles. The predecessor result counts preimages of a fixed `a`; even
an `x^{1−ε}` lower bound would still have density zero for fixed `ε`.

## Headline results (with verification scope)

| Result | Status |
|---|---|
| Exact `k=19` KL feasible certificate at `γ₀=log₂(18783127/10⁷)=0.9094372617…`; `π_a(X)≥X^γ` eventually for every positive `a≢0 (mod 3)` and fixed `γ<γ₀` | A fresh run of the reference verifier passed the SHA-pinned 2.9 GB sidecar and all 387,420,489 exact inequalities. Exact `k=5` witnesses invalidate the printed advanced-elimination construction, and a separate exact semantic countermodel blocks its split-invariant induction. Lean checks all three defects and, in commit `3d6a186`, checks a replacement: a well-founded raw-history builder, root provenance, live deterministic pruning, a common lag, and the complete abstract feasible-point comparison. Commit `58f0ef8` checks the corrected targetwise predecessor transfer replacing false equation (2.1); `331ff48` defines the statewise infimum and proves target-pool nonemptiness, normalization, and monotonicity; `729f5fa` proves the literal D1–D3 base system; `76ec861` closes the all-target exponent transfer. This is a mixed exact-Python + kernel-Lean chain, not yet a single Lean-native `k=19` theorem. The sidecar is local but not in git, the rerun used the same reference verifier rather than an independent second implementation, and a fresh clone is self-contained through k=15. See `experiments/kl/RESULT.md` and `TERMINATION_AUDIT.md`. |
| The KL method = finite sections of an **adversarial transfer operator on ℤ₃** (base ×4 = the Iwasawa generator of 1+3ℤ₃) | `docs/notes/kl-limit-object.md`, `adversarial-operator.md` |
| KL's own §6 positivity hypotheses (H_k) | Literature-backed research proof (odometer conjugacy → Gaubert–Gunawardena); nonlinear Perron existence is not Lean-formalized, and the exact feasible-point route bypasses it. |
| Oscillation law s(λ_k)−1 = (λ^{α−2}+λ^{α−1})δ_k | proved, now unconditional |
| Exact multiscale genealogy of the `k=12,...,19` feasible vectors: all 756 tested equal-threshold tail transitions are nonincreasing; exact weighted cones close after finite burn-in at `t=.2,.3` | SHA-pinned bigint/rational diagnostics and independent reconstruction. The untracked floating `k=20` candidate falsifies both earliest-burn-in constants but continues the terminal-immigration decline; neither side is a limit/eigenfunction theorem. See `docs/notes/multiscale-genealogy.md`. |
| Local renormalization at −1 solved: **a = λ^{1−α}** (= 2/3 at λ=2); "period-2" = the u↦2u relabeling; spine sheds mass at λ^{α−1}/3 | `renormalization-at-minus-one.md`, sol cross-confirmed |
| Diaconis–Fulman multiplication-carries spectrum (their open question) | proved, exact-verified: `carries-spectrum.md` |
| Berg–Meinardus ⟺ aₙ = a_{T(n)}; **bi-(2,3)-Mahler divergence certificates impossible** | proved: `mahler-cartier-lemma0.md`, `two-bases.md` |
| Antihydra rarity theorems (θ(C) → H(1/3); population-φ exact) | proved: `antihydra-rarity.md` |
| No regular divergence certificate: **≤8 states (base 2: 3.24T DFAs), ≤5 (base 3)** | exhaustive, cross-machine, logs in-repo |
| Weighted (drift) certificates: 191 regular domains retired incl. the all-ones ray | `experiments/wfar/` |
| Tree-product Collapse Lemma (spectral-gap route provably blind); solenoid **Traceless Theorem** (q=3 unique) | `tree-products.md`, `deninger-solenoid.md` |

## Current proof strategy (living map — updated as lanes open/close)

The locally rerun `k=19` feasible certificate and the checked generic transfer
now form a complete mixed-verifier proof chain. The remaining integration
caveat is portability—a Lean-native large-record import—not a mathematical
hypothesis. Everything below is about reaching *further*.
After tunneling on one line we have re-widened. This
section is kept fresh; the **failure ledger** is deliberately explicit because
knowing which routes are dead (and why) is most of the value.

### LIVE bets (updated through the 2026-07-21 exact genealogy audit)

1. **KL finite bridge complete — prove the limit; import the large records.**
   At `k=5`, the legal path
   `188→206→137→182→161→107→71→47→188` returns through a transport
   edge at symbolic shift `7 log₂3−11>0`. The deletion rule never tests that
   closing transport child, so the deletion-rule inference used to derive paper
   equation (3.2) is invalid. Re-expansion then deletes a child that survived below the first root,
   refuting the history-free identical-subtree step. The exact checker is
   `experiments/kl/verify_termination_obstruction.py`. This is not a
   nontermination lasso. Both the Python certificate and the Lean
   reconstruction in `CLEAN_LEAN/CleanLean/KL/TerminationObstruction.lean`
   check the obstruction. A second 11-edge history reaches a split at residue
   `242` whose targets `80,161,242` are all deletion-eligible; the exhaustive
   exact checker is `experiments/kl/verify_all_three_deletion.py`. Thus the
   literal rule can form an empty minimum. Lean now proves the abstract theorem
   ruling out infinite statewise-record branch-arrival histories. But the exact four-value checker
   `verify_split_invariant_counterexample.py` shows that a locally valid split
   can activate a formerly unselected outer-min alternative and violate (3.4).
   Therefore the proposed interleaved backjump lacks the split-stable invariant
   it needs. The new primary route compiles the finite universal history tree
   into the minimum of all complete record-admissible add-only policies. Every
   policy is coefficient-sound because the fiber coefficient minimum is at most
   every chosen lift; for each admissible `phi,y`, choosing actual raw minima
   supplies a functionally sound policy. Compactness gives finiteness and a
   uniform retarded lag. `verify_two_phase_small_levels.py` exactly reproduces
   the Table-1 maxima `8,84,12829` at `k=2,3,4`. A load-bearing design constraint is
   occurrence identity: the same label `74@(-7+5 log₂3)` is a higher repeat on
   one exact `k=4` history and a lower repeat on another, so labels alone cannot
   carry marks. CLEAN_LEAN now checks an occurrence-annotated one-pass pruner,
   exact functional equality, coefficient monotonicity, and localized
   positivity. It also checks the globally scoped occurrence-provenance
   interface and proves that a completed `TwoPhaseEliminationData` package feeds the existing
   retarded comparison theorem with the correct functional and coefficient
   orientations. CLEAN_LEAN commit `3d6a186` now checks the well-founded raw
   history builder, root-level provenance, occurrence-indexed deterministic
   pruning, structural liveness, a common positive lag, and the consumer into
   the abstract comparison theorem. Its theorem
   `quarter_lower_bound_of_feasible` has no remaining elimination assumption.
   Commit `331ff48` defines the literal predecessor-count infimum, proves every
   residue target pool nonempty by an Euler-multiplication argument, and checks
   normalization and monotonicity. Commit `729f5fa` then kernel-checks the
   targetwise reverse-tree partitions, exact real/floor scales, residue/fiber
   wrappers, and the full D1–D3 base-system theorem.
   Commit `76ec861` closes the remaining transfer: it uses the exact cutoff
   `y=log₂(X/a)`, bounds a feasible vector by its finite coordinate sum, escapes
   any hypothetical positive cycle through a nonperiodic power-of-two multiple
   in class two, and transfers the ordinary count back to the original target.
   The checked bridge does not import the paper's false equation (2.1). The exact
   checker `verify_equation_2_1_obstruction.py` gives
   `φ^7_2(1)=3≠2=φ^{14}_2(0)`. Commit `58f0ef8` kernel-checks the exact
   targetwise doubling decomposition. For the paper's full target-class
   definition, infimizing yields `φ^m_k(y)≥1+φ^{2m}_k(y−1)` for `y≥1`, so the
   lower-bound direction and exponent survive. The Lean `klPhi` needs only the
   class-2 states: the final all-target wrapper uses the checked direct
   ordinary-count inclusion. For arbitrary cycle targets, a sufficiently large
   doubled predecessor gives the transfer without assuming that `{1,2}` is the
   only positive cycle.
   The active mathematical task is now `λ_∞=2`: construct exact feasible
   parameters tending to two, or prove a non-autonomous localization/global-
   measure mechanism that forces them. The checked theorem
   `almostLinearPredecessorCounting_of_feasible_sequence_concrete` then gives
   `X^(1−ε)` predecessor counting with no further literature-transfer
   hypothesis. The parallel engineering task is a kernel-reduced, chunked
   import of `k=12` before attempting the multi-gigabyte `k=15–19` records.
   `verify_predecessor_base_inequalities.py` exactly checks the targetwise
   reverse-tree partitions and stronger `+3,+3,+2` rows in 660 bounded cases,
   including a periodic-target regression. A twice-audited explicit finite
   occurrence-word bound `D_k` remains as an independent audit of the completed
   well-founded construction. `docs/notes/kl-explicit-history-bound.md`.
   `experiments/kl/TERMINATION_AUDIT.md`.
2. **Arctic/max-plus SRS no-go — candidate proof written, formal check next.**
   The inherited proof incorrectly assigned one eventual slope to a reducible
   max-plus sequence. The repair is elementary: a long maximizing walk with
   nonnegative output contains a nonnegative simple cycle, which can be pumped
   by a common multiple of all cycle lengths; the exact strict macro compares
   lengths differing by precisely such a multiple. If kernelized, this gives the
   calibrated Theorems A/B in every dimension, provided both dependency-pair
   rules are weak and the selected one is strict. Exact macro counts and all
   dimension-one witnesses pass independent checkers; CLEAN_LEAN has been asked
   to check the general argument. `docs/notes/arctic-nogo.md`.
3. **Mixed-radix anti-concentration — numerical evidence + proof program.**
   Exact DP supports logarithmic-scale near-flatness on specified finite test
   sets: the 93 primes `5≤p≤499`, `p∤6`, at central weight; seven scale-test primes
   `101 ≤ p ≤ 6553` across `0.3k ≤ m ≤ 0.7k`; and fourteen capped-small-
   subgroup candidates drawn from a scan of primes `p ≤ 10⁶`. This was **not**
   a uniform flattening sweep over every prime below `10⁶`, so "no exceptional
   prime below `10⁶`" and a `p`-uniform `e^{−ck}` rate remain conjectural. The
   robust findings are the algebraic reduction to a conditioned two-multiplier
   CDG-type affine walk, failure of the proposed complete-subgroup/tested-prefix
   mechanism, and three open gaps: coupled matrix-product contraction,
   bivariate fixed-weight extraction, and running-vector propagation.
   The successor audit also corrected a reversed cyclic shift in the Fourier
   checker and a missing `binom(k,m)^{-1}` in one displayed extraction formula;
   neither changes the exact-DP tables, but the former claimed matrix check is
   withdrawn and replaced by a componentwise product/Fourier assertion.
   `docs/notes/mixed-radix-flattening.md`.
4. **KL limit beyond autonomous contraction.** `λ_∞=2` remains the central
   quantitative question, but the marginal co-spine closes every admissible
   `J≥3` certificate in the charged/projective class. Any serious revival now
   needs a non-autonomous global-measure or arithmetic mechanism. The finite
   bridge in item 1 is now ready to consume any exact feasible family directly;
   what is missing is an all-level construction whose parameters tend to two.
   A new exact streamed audit also blocks the prepared `(J,L_w)=(3,9)`
   annealed pressure scale-up as formulated. The actual depth-`9→10` split of
   the `k=19` feasible vector has `σ_max=0.542601…` even on uncovered-to-
   uncovered transport transitions, not the extrapolated `≤0.42`. The
   violating transitions are rare, and the new exact within-vector genealogy
   explains why that matters: at the final `k=19,t=.2` scale, 66 parents have
   pointwise retention one, but they carry only `.000961...` of high-parent
   mass; the mass-averaged retention is `.335470...`, immigration is
   `.006848...` of total mass, and the child tail is `.0248165...`. Across
   `k=12,...,19`, all 756 tested equal-threshold adjacent-scale tails are
   nonincreasing. Exact Möbius reconstruction of the eight-bin transition
   matrices finds a sharp finite cone result at `t=.2`: no common one-step cone
   can start before depth three, while
   `w=(31/25,69/50,1,34/25)`, `rho=68/69` closes all 349 observed rows from
   there. At `t=.3`, `w=(1,1)`, `rho=179/200` closes after depth two. Both were
   selected on `k=12,...,19`; the floating `k=20` candidate then violates them
   at two depth-three rows and one depth-two row, respectively, although one
   extra burn-in passes and all ten tested terminal-offset immigration values
   continue downward. The missing theorem is a uniform burn-in plus decay of
   weighted immigration for each fixed terminal offset and thresholds tending
   to zero. `experiments/pressure-cert2/split_ratio_audit.py`;
   `docs/notes/multiscale-genealogy.md`.
5. **Quantitative adelic descent** / **open-quantum-systems reframing** — the
   no-go = peripheral spectrum of the KL channel (`wildcard.md`, WARM); descent
   under a dynamical Fourier norm (on deck). Both risk rediscovering the marginal
   mode.
6. **Analytic-combinatorics / nonlinear-pressure salvage — under adjudication.**
   The inherited scout does **not** establish that the certified nonlinear KL
   exponent is the pole of an ordinary linear backward-tree resolvent. The literal
   linear mean matrix is an annealed relaxation; a policy matrix is not an exact
   counting recursion without a separate sandwich theorem. Thus the asserted
   `π_a(x) ~ C_k x^{γ_k}`, no-log conclusion, and ordinary pole confluence for
   the true predecessor count are unsupported. Surviving content includes the
   annealed exponent-1 calculation, finite-size data, and the sufficient
   increment-contraction criterion. Any revival must first distinguish the
   linear, annealed, policy, and nonlinear objects and prove a counting bridge.
   `docs/notes/analytic-combinatorics.md`; audit in `CLEAN_LEAN/FOR_FABLE.md`
   rounds 13–14.

### FAILURE LEDGER — what didn't work, and why (do not retry)

- **The printed KL advanced-elimination construction — INVALID AS STATED;
  replacement witness kernel-checked.** One exact `k=5` path invalidates the
  derivation of (3.2) and directly falsifies history-free subtree translation;
  another makes all three leaves of a new minimum deletion-eligible. Changing
  the sign of `δ` or arbitrarily retaining one leaf is not a repair—the latter
  can retain a positive self-loop. A generic exact countermodel also refutes
  the claimed split-time preservation of the critical-assignment invariant.
  Do not reuse the published descent, self-similarity, nonempty-minimum,
  split-induction, or assignment-backjump assertions. These certificates neither
  prove nor disprove termination. The occurrence-aware replacement in Lean
  commit `3d6a186` proves the required abstract comparison without those
  assertions. Commit `729f5fa` proves that the literal predecessor family
  satisfies D1–D3, and commit `76ec861` proves the all-target exponent wrapper.
  The checked replacement therefore recovers the `k=19` counting consequence
  without validating any of the printed assertions.
  `experiments/kl/TERMINATION_AUDIT.md`.
- **Printed KL equation (2.1) — FALSE AS AN EQUALITY; one-sided repair identified.** At
  `k=2,m=7,y=1`, exact affine lower bounds and two independent finite
  enumerators give `φ^7_2(1)=3` but `φ^{14}_2(0)=2`. Infimizing the exact
  targetwise identity `P*_a(x)={a}⊔P*_{2a}(x)` (kernel-checked in commit
  `58f0ef8`) over different target pools
  yields only `φ^m_k(y)≥1+φ^{2m}_k(y−1)`, not equality. Do not reuse (2.1)
  literally. The surviving direction gives the same exponent with the usual
  `λ^{-1}` constant, so this erratum does not invalidate the LP certificate or
  create a new conjectural gap. `experiments/kl/verify_equation_2_1_obstruction.py`.
- **λ_∞ = 2 via any autonomous projective-contraction certificate — CLOSED
  (structural no-go, every admissible J≥3).** The −1 co-spine mode (2,−1,−1) is a marginal
  invariant: charged-Lyapunov (persists J=4,5), nonlinear min-selection
  (calibrated neutral cycle), and forcing-word (η=0) all fail. Not evidence
  λ_∞<2; just no proof in this class. `cl-killtests.md`, `pressure-certificate-2.md`.
- **The proposed uniform pressure split `U(21/50)` — REFUTED on the tested
  exact feasible class.** At depth `9 -> 10`, an uncovered-to-uncovered
  `k=19` transition has exact child/parent ratio
  `1892575973641960/3487969866821777 = 0.542601... > 0.42`. This refutes that
  required closing constant, not every parameterized scalar H1, an eventual
  theorem after `k=19`, or an eigenfunction-specific statement. The violations
  are rare, which motivates the distinct mass-genealogy lane rather than
  rescuing the false pointwise bound. `pressure-certificate-2.md`;
  `experiments/pressure-cert2/split_ratio_audit.py`.
- **Cycle exclusion via finite places p | 2^K−3^L — CLOSED (collapses to
  Baker).** "Infeasible where new, redundant where feasible"; the Steiner
  stratum *is* the Baker bound. One falsifiable Poisson-model survivor only.
  `cycle-finite-places.md`.
- **Regular divergence certificates — CLOSED (exhaustive).** None ≤8 states
  (base 2, 3.24T DFAs), ≤5 (base 3). `dfacert*`.
- **Spectral-gap route to descent — CLOSED (Collapse Lemma).** Collatz
  projects to a point of the arithmetic tree-product quotient; automorphic
  gaps are blind. `tree-products.md`.
- **Tropical geometry proper — CLOSED-NEGATIVE.** The arithmetic lives in the
  *Archimedean* balancing of the KL characteristic (log-sum-exp branching at
  O(1) temperature), not the tropical skeleton; only the adversary/min is
  genuinely tropical and we already handle it. Box-ball is the wrong shape.
  Minor surviving lead: ambitropical geometry (Gaubert 2021). `tropical-geometry.md`.
- **Beat Baker via Bourgain–Kontorovich CF thermodynamics — CLOSED-NEGATIVE
  (category mismatch).** BK is an *ensemble* statement; a single number's
  Diophantine type is invisible to it. Ouaknine–Worrell gives the *explanation*:
  the cycle-length bound, Positivity, and Zaremba all reduce to effective
  equidistribution of one Gauss-map orbit, capped by Baker. Explains why nothing
  beats Baker; beats nothing. `bourgain-kontorovich.md`.
- **Solenoid → hidden RH / Weil positivity / first-circle natural boundary —
  CLOSED-NEGATIVE at research-proof level; formal check pending.** The signed
  zeta trivialises (`Z₃≡1`), so Weil positivity is vacuous and constant-
  coefficient constructions are blind to the `+1`. An independently audited
  handwritten binomial-tail argument gives
  `ζ_S=(1−4u)^{-2}exp(G(u))` with `G` analytic past `|u|=1/4`, so that circle
  has one double pole and is not a natural boundary. The exact checker verifies
  the coefficient identities and rational gap bounds over stated finite ranges;
  the all-`K` asymptotic and analytic consequences are not yet kernel-checked.
  No cycle-arithmetic bridge is known. `solenoid-zeta.md §6`.
- **Ordinary linear-resolvent identification of the KL exponent — RETRACTED.**
  The KL threshold is defined by a nonlinear min-over-fibers operator, whereas
  the literal tree resolvent uses a fixed linear sum/mean matrix. No exact
  counting bridge was supplied, so the claimed pole at `γ_k`, true-count
  asymptotic, and no-log conclusion do not follow. A nonlinear-pressure
  language may still be useful, but this specific "proved reformulation" is
  closed. `analytic-combinatorics.md` rev. c.
- **One global eventual slope for reducible max-plus interpretations —
  RETRACTED.** Different residue classes can have different slopes, so the
  inherited arctic proof was invalid. A candidate weighted-walk pumping repair
  is in `arctic-nogo.md` and awaits Lean; do not reuse the old slope extraction.
- **"One certificate away" framing (earlier README) — RETRACTED.** It was
  wrong; the certificate provably doesn't exist in its class.

### What CLEAN_LEAN (GPT) has kernel-checked and standing

The oscillation identity, Lemma-5 row checker and exact Chernoff gaps,
terminal-potential / Chernoff chain, exact backward-orbit hitting formula,
labelled critical-
assignment contradiction, concrete split arithmetic, global value-preserving
deletion, symmetric critical-assignment lifting across globally safe deletion,
all three finite KL obstructions, abstract branch-arrival compactness, the
occurrence-indexed split-all-then-prune semantics, and the final retarded-witness consumer
are kernel-checked. Lean also has symbolic `Z²` shift updates and a generic
finite-rank termination checker. Commit `3d6a186` completes the
occurrence-annotated finite history/policy construction, root provenance, live
pruning, common lag, and abstract feasible-point comparison. Commit `331ff48`
supplies the actual predecessor-count definition, unconditional target-pool
nonemptiness, normalization, and monotonicity. Commit `729f5fa` supplies the
literal D1–D3/base-system proof, and commit `76ec861` supplies the corrected
fixed-target and arbitrary-target exponent transfer plus the concrete
feasible-sequence endpoint. Rounds 22–29 also
kernel-check the generated payload's 2,187 row inequalities, their all-length
mass bounds, equality with an independently defined 243-state KL graph, the
irrational interval-weight domination, and exact interval tiling. General
all-level aggregated ball-mass domination and especially localization remain
open; this pressure half is not a limit proof. The exact depth-nine split audit
further rules out promoting its proposed `σ≤0.42` annealed scalar H1 bound to
the five exact certified feasible points tested (`k=15,…,19`).

### Standing frame

x^{1−ε} counting (if ever reached) is a milestone, not Collatz; the conjecture
also needs no-divergence and no-cycles. The invariant-rank ledger
(`invariant-rank.md`) makes Conway's unsettleability (rank = ∞) precise and
tracks which certificate classes are provably insufficient. The descent ±sign
no-go proves any orbit-fate argument must couple 2-adic structure to the
Archimedean place — which is why every purely-local lane above eventually
hits the same wall.

## Current activity

- The new Codex research driver is active. Its first audit stopped five orphaned
  arctic writers left after the final handoff, preserved their completed CSV
  rows, reran the k=19 reference verifier, corrected inherited status and
  artifact-portability errors, and has now completed exact split-pressure and
  multiscale-genealogy audits.
- The finite KL predecessor-count bridge has just closed. An exact integer checker pins a
  legal `k=5` path that invalidates the printed proof's descent and identical-
  subtree claims without forming a repeatable nontermination lasso. CLEAN_LEAN
  independently reconstructed and kernel-checked the path, ancestry tests,
  symbolic shifts, and re-expansion deletion. A second exact checker now pins
  the first all-three-deletion event at depth eleven, and a third finite checker
  exposes the split-invariant gap. CLEAN_LEAN now independently checks both
  certificates and proves the abstract branch-arrival compactness theorem,
  including irrationality of `log 3 / log 2`. The checked replacement compiles
  all complete good policies into one fixed outer minimum. An exact checker
  reproduces KL's small-level literal counts and catches the occurrence-indexing
  requirement. Commit `3d6a186` completes the occurrence-indexed one-pass
  pruning theorem, global repeat provenance, well-founded raw-history producer,
  common-lag construction, and abstract comparison theorem. Commit `331ff48`
  defines the literal predecessor family and proves P1/P2; commit `729f5fa`
  proves D1–D3; commit `76ec861` proves the fixed-target/all-target exponent
  transfer and the feasible-sequence-to-almost-linear endpoint. The top KL
  theorem lane is now the open limit `λ_∞=2`; the immediate integration task is
  a portable Lean-native import of the first large record.
- The pointwise pressure lane is calibrated more sharply. The proposed
  `U(21/50)` split fails exactly at `k=19`, but only a small fraction of mass
  causes the failure. A separate exact audit coarsened each feasible vector
  through its full 3-adic genealogy and found no increase among 756 tested
  diagonal tail transitions. The follow-up rational common-weight search now
  has an exact finite certificate and an exact earlier-depth obstruction. Its
  first floating `k=20` holdout falsifies the original burn-in constants while
  leaving later-depth contraction and terminal immigration favorable. Uniform
  all-level contraction, burn-in, immigration decay, and threshold refinement
  remain entirely open.
- The arctic/max-plus lane remains active. Two independent audits found the
  same reducible-slope gap; an elementary weighted-walk pumping candidate now
  replaces it, and the exact marked macro checker passes. The general theorem
  is explicitly provisional until Lean checks it. No brute-force scale job is
  running.
- A second audit produced a research-level correction to the unsigned-zeta
  lead: the proposed natural boundary at `|u|=1/4` is false if the written
  all-`K` tail argument is accepted. The exact finite identities and gap bounds
  have an independent integer checker; the analytic theorem awaits formalization.
- No background research lane inherited from Fable is now running. The
  mixed-radix attempt, eight-agent re-widening fan-out, and ganesha
  critical/grid3 passes were stopped; their complete or partial states are in
  `HANDOFF.md` and the corresponding notes.
- CLEAN_LEAN continues independently. It has completed the occurrence-aware
  finite history compiler and abstract feasible-point comparison, alongside
  the symbolic-shift, compactness, obstruction, pruning, and rank-checking
  infrastructure, and has now closed the finite counting transfer. No hidden
  premise remains behind the paper's invalid self-similarity argument. The
  research driver communicates through
  `docs/FOR_CLEAN_LEAN.md` and does not edit `CLEAN_LEAN/`.
- Remote compute is currently uncommitted. Any new diagnostic job will be
  listed here with its exact scope; bounded z3 searches are evidence only, not
  all-dimension proofs.

(Computing still larger finite-`k` KL records is deprioritized as a limit
strategy. Importing the existing exact records remains an active portability
task.)

## Verification discipline

Nothing is a result until: exact arithmetic or kernel-checked proof, plus
independent re-derivation (agent vs sol vs data) where feasible, plus
adversarial external review for anything load-bearing. The errata are public:
`SMELL.md` header, `fiber-geometry.md` v2. Corrections to date have come
from both directions (external review killed our Prop R; we killed a stale
preprint alarm and two prescribed-claim errors were corrected by our own
agents' proofs).

## Map

`docs/` STRATEGY (master), LANDSCAPE, CRACKS, SMELL, REVERSE-MINING,
CRYPTIDS, notes/ (all theorems + sol briefs) · `experiments/` kl (record +
certificates), pressure-cert, wfar, dfacert{,3}, expsum, family, carries,
gpu, fate · `formal/` Lean base (sorry-free) · `papers/REFERENCES.md`
index (PDFs removed for copyright) · `results/` data · `DATA.md` pointers.

## Credit — whose insights this is built on

*Per Simon's note above: credit belongs to the human mathematics community,
with apologies for the imperfect attribution below. Anything of value here is
their idea; the errors are ours.* Our approach is, honestly, an assembly of
existing lines of work; the closest ancestors, and what each contributes:

**The direct spine of the counting result.**
- **I. Krasikov & J. C. Lagarias, "Bounds for the 3x+1 problem using
  difference inequalities," Acta Arith. 109 (2003) 237–258** (arXiv:math/0205002).
  The x^0.84 record and the LP/difference-inequality method we extend. Our
  entire counting line is *their method, run further and reinterpreted.*
- **L. Collatz (1942/1950), the Collatz–Wielandt formula** — nonlinear
  spectral radius as inf–max of ratios. The lens under which the KL LP became
  a nonlinear eigenproblem (a genuine, if wry, namesake coincidence).
- **S. Gaubert & J. Gunawardena, "The Perron–Frobenius theorem for homogeneous,
  monotone functions," Trans. AMS 356 (2004)** — existence of the strictly
  positive nonlinear eigenvector; what discharges KL's (H_k) once the base map
  is seen as an odometer.
- **T. Bousch, "Le poisson n'a pas d'arêtes" (2000) and ergodic optimization
  (Jenkinson's survey, 2019)** — the maximizing-measure / zero-temperature
  view of the adversarial limit operator; the nearest *solved* cousin of our
  ℤ₃ transfer operator (optimization over a rotation/odometer). Our λ_∞
  dichotomy is an ergodic-optimization question in disguise.
- **A. A. Ahmadi, R. Jungers, P. Parrilo, M. Roozbehani (path-complete
  Lyapunov, 2014) and M. Philippe et al. (constrained joint spectral radius,
  2016)** — the certificate technology. The "Charged spine-face Lyapunov
  lemma" that gates the proof is a path-complete Lyapunov / constrained-JSR
  certificate with charges. Found independently via our keyword-blind search;
  the credit is theirs.

**The forward-orbit / density tradition (context and the ceiling we press
toward).**
- **R. Terras (1976)** — density-1 finite stopping time; the elementary
  parity/congruence structure everything reuses.
- **T. Tao, "Almost all orbits of the Collatz map attain almost bounded
  values" (2019/2022)** (arXiv:1909.03562) — the a.e. result and the Fourier
  decay of Syracuse random variables; the 3-adic major-arc regime our
  exponential-sum atlas lands in, and the wall (a.e. vs every-n) we respect.
- **I. Krasikov (1989), Applegate–Lagarias (1995)** — the predecessor-tree
  and transfer-operator antecedents of the counting side.

**Structure theorems we proved are extensions of:**
- **P. Diaconis & J. Fulman, "Carries, shuffling, and an amazing matrix" /
  the multiplication-carries chain (2008–2012)** — our carries-spectrum
  theorem answers a spectral question they left open.
- **L. Berg & G. Meinardus (1994/95)** and **B. Adamczewski & J. Bell,
  Mahler-function rigidity (Ann. Sc. Norm. Pisa 2017)** — the Mahler-equation
  reformulation and the (2,3)-rigidity behind our bi-Mahler exclusion.
- **A. Cobham / A. Semenov** — the two-bases automatic-set rigidity behind the
  "no certificate in two bases" note.
- **K. Monks (2006)** — sufficient sets / arithmetic-progression reduction,
  used in the exclusion and Mahler notes.

**The frame (why this is hard, and the BB connection Simon came for).**
- **J. H. Conway, "Unpredictable iterations" (1972)** and **S. Kurtz & J. Simon
  (2007)** — undecidability / Π⁰₂-completeness of generalized Collatz; the
  invariant-rank ledger is Conway's unsettleability made quantitative.
- **P. Michel** (Busy-Beaver ↔ Collatz-like maps) and **S. Aaronson, "The Busy
  Beaver Frontier" (2020)** and **the bbchallenge collaboration** (BB(5)=47,176,870,
  Coq-verified; Antihydra and the cryptids) — the BB/Collatz bridge; our
  reverse-mining and Antihydra-rarity work sits on theirs.
- **C. Deninger** (foliated dynamical systems / solenoid Lefschetz program) —
  the frame for the Traceless Theorem on the (2,3)-solenoid.

**What our approach most resembles, in one line:** the Krasikov–Lagarias LP
method, reread through nonlinear Perron–Frobenius / ergodic optimization, and
certified with path-complete Lyapunov (constrained-JSR) technology — none of
which had previously been pointed at this problem together.

Full per-claim citations with URLs are inline in the `docs/notes/*` files and
`docs/LANDSCAPE.md`; the mirrored-PDF index is `papers/REFERENCES.md`.
