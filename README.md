# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, and formalization. Certified claims are backed by
machine-checkable artifacts; research derivations and finite evidence are
scoped explicitly. Started 2026-07-20 (Claude Fable 5 +
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

The quantitative target is `λ_∞=2` for the Krasikov–Lagarias (KL)
predecessor-counting systems. It would imply
`π_a(x)≥x^(1−ε)` for every `ε>0`. The finite bridge is complete: a mixed
exact-Python/kernel-Lean chain transfers the `k=19` certificate to the current
predecessor-count exponent, the `k=12` record is fully Lean-native, and Lean
constructs an infinite strictly increasing feasible ladder. What remains is a
dimension-free rate; strict growth by itself can converge below two.

The leading conjecture is now the selected quadratic coarse-minimum law

```text
epsilon_(j+1) >= epsilon_j+(3/2)epsilon_j^2
```

It holds by exact arithmetic at every available stage of the selected
`k=12,...,19` records. It is false on the generic feasible cone. Lean commit
`38f1497` proves that an all-level selected-critical version would telescope to
`λ_∞=2`; it does not prove the selected law.

Two formulations sharpen that missing theorem:

- The defect is a three-way Doeblin overlap. Generic channel contraction is
  exponentially too weak, but a renewal-min-constrained Doeblin curve—or the
  equivalent weighted anti-alignment of endogenous argmin labels—would supply
  the observed quadratic gain. The finite frustration lower bound already
  clears the first-stage target on `k=12,...,15`.
- For the homogeneous power means, `F_min≤F_(-β)≤3^(1/β)F_min` uniformly in
  the level. Power-mean projection also proves that `ρ_(k,λ,p)` is increasing
  in `k` and bounded by the annealed value `s(λ)`, so its fixed-temperature
  limit exists. It would therefore suffice to identify that limit with `s(λ)`
  for every fixed `λ<2` and finite `p<0`, choosing
  `−p>log(3)/log(s(λ))`. Near-tie selector spikes drift to colder scales, so
  uniform eigenvector regularity is neither assumed nor presently credible.

The same-policy defect audit found genuine recurrent split/merge dynamics, not
an annealed artifact. Its natural carry/policy quotient nevertheless refines
to essentially the full Jacobian, so it is a diagnostic rather than a compact
finite-state invariant. A selected mean-defect plus anti-concentration theorem
and the older expanding-window cones remain secondary endpoint routes. The
detailed evidence, counterexamples, and live kill tests are in the strategy
map and linked notes below.

None of these statements settles Collatz, positive density, divergence, or
nontrivial cycles. The predecessor result counts preimages of a fixed `a`; even
an `x^{1−ε}` lower bound would still have density zero for fixed `ε`.

## Headline results (with verification scope)

| Result | Status |
|---|---|
| Exact `k=19` KL certificate and predecessor exponent `γ₀=log₂(18783127/10⁷)=0.9094372617…` | The SHA-pinned 2.9 GB sidecar passes all 387,420,489 exact inequalities. Lean commits through `76ec861` replace two false printed steps and prove the generic transfer to `π_a(X)≥X^γ` eventually for every eligible fixed target and every `γ<γ₀`. This is a mixed exact-Python/kernel-Lean chain; the large record is not one Lean-native theorem and a fresh clone is self-contained through `k=15`. See `experiments/kl/RESULT.md` and `experiments/kl/TERMINATION_AUDIT.md`. |
| Fully Lean-native `k=12` counting checkpoint | Commits `4c7fcc3`/`659dc81` kernel-reduce all 177,147 feasibility rows, pin the generator/source provenance, and prove `HasPredecessorExponent a (log₂(18064231/10^7))` for every eligible target. The audited build uses no `sorry`, `native_decide`, or project axiom. |
| Strict existential improvement and infinite feasible ladder | `78602d4` proves that every positive feasible point below two lifts to a strictly larger feasible parameter at the next level. `882a00e`/`9323f26` specialize this to `k=12` and produce an existential predecessor exponent strictly above the Lean-native decimal. The gain is non-numerical and may be exponentially small, so this is not `λ_∞=2`. |
| Coarse-minimum/defect package | `5a8727f`/`786c02e` prove coarse-minimum order and defect data processing; `ee37cd9`/`27b9e69` expose the exact rowwise mismatch and one-stage canonical frustration seam; `d4b328b` retains inherited supersolution slack. Commits `ca0a6e9`/`e2723e2` isolate the exact all-stage normalized and rowwise slack-gain premises. Exact selected `k=12,...,19` data obey `ε_(j+1)≥ε_j+(3/2)ε_j²`, while an exact feasible `k=3` counterexample rules out a cone-wide theorem. `38f1497` proves that the all-stage law would imply the endpoint. See `docs/notes/coarse-minimum-gap.md`. |
| Uniform zero-temperature control and a monotone soft tower | For `p=-β`, `F_min≤F_p≤3^(1/β)F_min`, including the same level-uniform spectral-radius bound. For every fixed `p<1`, power-mean projection proves `ρ_(k-1,λ,p)≤ρ_(k,λ,p)≤s(λ)`, so the fixed-temperature limit exists. Identifying it with `s(λ)` would imply the endpoint; floating results through `k=13` support this and prove nothing asymptotic. See `docs/notes/softmin-replica.md`. |

Other checked results include the exact oscillation identity, the annealed
critical coding and renewal algebra, local renormalization at `−1`, the
Diaconis–Fulman multiplication-carries spectrum, the Mahler/Cartier and
two-base exclusions, Antihydra rarity, exhaustive small-DFA exclusions, the
tree-product Collapse Lemma, and the solenoid Traceless Theorem. Their scopes
and artifacts are indexed below and in `docs/notes/`.

## Current proof strategy (living map — updated as lanes open/close)

The locally rerun `k=19` feasible certificate and the checked generic transfer
now form a complete mixed-verifier proof chain. The remaining integration
caveat is portability of the headline `k=19` record, not a mathematical
hypothesis: the first chunked Lean-native import is complete at `k=12`, while
the larger sidecar-backed records, culminating in 2.9 GB at `k=19`, still need
a scalable representation.
Everything below is about reaching *further*.
After tunneling on one line we have re-widened. This
section is kept fresh; the **failure ledger** is deliberately explicit because
knowing which routes are dead (and why) is most of the value.

### LIVE bets (updated through the coarse-minimum, soft-min, and defect audits)

These lanes are grouped to keep the completed foundation and its remaining
portability work together; they are not priority-ranked. The central live
mathematical lane is item 4, the KL limit/localization problem.

1. **KL finite foundation complete — scale the record imports.**
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
   `experiments/kl/verify_split_invariant_counterexample.py` shows that a locally valid split
   can activate a formerly unselected outer-min alternative and violate (3.4).
   Therefore the proposed interleaved backjump lacks the split-stable invariant
   it needs. The new primary route compiles the finite universal history tree
   into the minimum of all complete record-admissible add-only policies. Every
   policy is coefficient-sound because the fiber coefficient minimum is at most
   every chosen lift; for each admissible `phi,y`, choosing actual raw minima
   supplies a functionally sound policy. Compactness gives finiteness and a
   uniform retarded lag. `experiments/kl/verify_two_phase_small_levels.py` exactly reproduces
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
   checker `experiments/kl/verify_equation_2_1_obstruction.py` gives
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
   hypothesis. The first kernel-reduced, chunked import is now complete at
   `k=12` in commits `4c7fcc3`/`659dc81`: all 177,147 rows, their semantic map,
   and the resulting literal predecessor-count theorem are kernel-checked. The
   remaining engineering task is a smaller or streamed representation for the
   larger sidecar-backed `k=15–19` records, culminating in the 2.9 GB `k=19`
   record; raw embedding at the upper sizes is
   impractical.
   `experiments/kl/verify_predecessor_base_inequalities.py` exactly checks the targetwise
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
   Qualitative adjacent strictness is no longer the missing lemma. Commit
   `78602d4` kernel-checks the stronger feasible-vector theorem: every positive
   feasible point below two lifts to a strictly larger feasible parameter at
   the next level, and an infinite strict ladder follows without critical
   attainment. The argument supplies no uniform lower bound on that gain—a
   bounded strictly increasing sequence may still converge below two—so the
   localization/rate problem below is unchanged.
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
   matrices now classifies the complete threshold grid: the minimal observed
   burn-ins for `t=.05,.10,...,.40` are `(6,3,3,3,3,2,2)`, with explicit
   obstruction rows below them and rational cones above them. All 2,299 exact
   row inequalities pass. Every fitted, nearly optimal rational margin is then
   exceeded by the floating `k=20` candidate, but every maximum remains below
   one at the same burn-in; the thinnest surviving margin is about `2.4e-4` at
   `t=.1`.
   The ten tracked fixed-offset values at `t=.2,.3` continue downward, but at
   `t=.05` offsets one through four instead rise strongly through the floating
   candidate. This is the sharpest current obstacle to threshold refinement. A
   corrected sufficient theorem needs only an expanding terminal window, not
   a fixed absolute burn-in, and can absorb rare bad rows through their
   mass-weighted defect.
   More promisingly, the exact density martingale has 116 exact-checked
   increments. All 108 at depths `j>=2` obey the post-hoc envelope
   `Delta_(k,j)<=(1/2)(9/10)^j`; the 18 floating `k=20` rows do too. Fixed-depth
   increments rise across levels while every tracked fixed-terminal-offset
   increment falls, from terminal `.044292` at `k=12` to exact `.024696` at
   `k=19` and floating `.022894` at `k=20`. The finite measurements are valid,
   and a hypothetical summable envelope would give relative `L1` compactness by
   martingale telescoping. However, the independently audited annealed-floor
   research argument excludes the displayed constant at the endpoint for
   `1<lambda_k<=2`: projection intertwining and Perron uniqueness force the
   fixed-depth floor `Delta_2=622/1533>81/200` in every localizing critical
   family, or feasible family whose aggregate normalized slack vanishes. Thus
   future exact levels are useful diagnostics, but cannot
   rescue this particular fitted law.
   A companion floating-log diagnostic on the exact integer masses computes
   116 entropy-chain increments. Every selected profile decreases strictly
   with depth, all rows fit the post-hoc envelope
   `h_(k,j)<=(1/5)(3/4)^j`, and total entropy rises from `.324539` at `k=12`
   to `.444583` at exact `k=19` (`.459211` at floating `k=20`). A uniform
   entropy envelope would give relative `L1` compactness by chain rule and
   Pinsker. A weaker selected-family route is depth monotonicity plus
   `Ent(f_k)=o(k)`, which already forces terminal localization. Neither is
   proved. The geometric entropy fit is also closed as an endpoint law:
   `r_2=(8,2,11)/21` has the rigorously bounded
   `h_1>6431/39690>3/20`. Exact tightened feasibility at `k=3` admits a
   positive vector with `h_2>h_1`, so monotonicity cannot be a theorem about
   the whole feasible cone.
   The live replacement is polynomial rational energy. With child masses
   `x_i`, parent mass `P`, and total mass `T`, define
   `chi_(k,j)=(1/(3T)) sum_parent sum_i(3x_i-P)^2/P`. Quotient/remainder bounds
   give certified intervals without floating decisions. All 116 exact rows fit
   `chi<=6/j^2`; the worst certified ratio is `.283381756652` at `(k,j)=(19,8)`.
   The tighter `2/j^2` selected-data fit has worst ratio `.850145269956`, but
   exploratory annealed calculations overtake it, so it is explicitly
   finite-only. The audited endpoint coding identifies a global quadratic
   critical mechanism without supplying this local law. Its induced block
   distribution has `H(E)=log 4` but `sum p_e^2=1/3`; the resulting collision
   renewal has Haar-uniform benchmark increment `2/7`. The alignment kernels
   are quotients of a fixed two-state Green operator whose generators have
   commutator `u->u+7`. The exact first conductor correlation is
   `-2086/67963`, so its open local-limit factor is a signed cross-shell
   cancellation problem rather than termwise affine mixing. Even a linear global collision theorem would be insufficient: an
   audited sparse product law has `Q_j=Theta(j)` while its local Pearson energy is
   one at infinitely many depths. A separate exact `k=3` calculation gives the
   normalized squared-`L2` detail-energy ratio `1605/1387>1`, excluding a
   uniform unweighted one-step scalar `L2` contraction for that shell-response
   operator. Late annealed fits are compatible with mixed
   exponential/power decay, so `6/j^2` is not being proposed as the endpoint
   asymptotic. Since
   `h<=chi`, proving the constant-six polynomial law for a coherent critical or
   vanishing-slack family would yield entropy tail `<=6/J` and conditional-
   Pinsker residual `<=sqrt(12/J)`. The sharp fiber inequality
   `(9/2)a^2<=chi<=18a^2<=6a`, `a=1/3-min p`, reduces the terminal route to
   a selected mean-defect rate plus level-uniform defect anti-concentration.
   The new exact streamed terminal audit turns those two missing hypotheses
   into a compact finite falsifier. On every selected record `k=12,...,19`,
   it proves
   `delta<0.21/k`, `E[a^2]<1.533 delta^2`, and
   `chi_terminal<0.483/k^2`, while rigorously bracketing the true normalized
   feasibility slack. The observed `K=E[a^2]/delta^2` nevertheless rises at
   every level, from `1.36411` to `1.53221`; no uniform constant or asymptotic
   rate is inferred. Algebraically, if `mu` is the parent profile and `v` is
   the normalized terminal excess profile, then
   `K=sum v^2/mu=1+chi^2(v||mu)`, locating the required
   anti-concentration exactly. The general-parameter renewal tower sharpens
   this further. If `theta=1-epsilon`, then
   `chi^2(q||mu)=(epsilon^2/theta^2)(K-1)`, whereas the automatic
   Radon--Nikodym martingale estimate gives only
   `chi^2(q||mu)<=epsilon/theta`. The missing input is therefore exactly one
   extra power of terminal excess. The induced channel does give
   `||q_j||_infinity<=rho^j` with `rho<1` on `6/5<=lambda<=2`, hence a
   Frostman/non-atomicity statement for infinite towers or weak limits. It
   cannot be upgraded to uniform fiberwise flattening: the exact `-1` row
   leaves max-normalized fiber oscillation with endpoint liminf at least
   `1/3`.
   Direct compactness now has a research-side nonlinear renewal-min fixed-point
   interface; audited algebra shows why renewal and defect support separately
   supply no smoothing. The exact coarse-minimum projection
   `q>=F_(k-1,lambda)q` and
   `sum(q-Fq)=(b/3)(epsilon(q)-epsilon)` is now complemented by exact selected
   data: every adjacent iterated-minimum stage at `k=12,...,19` satisfies
   `epsilon_next>=epsilon+(3/2)epsilon^2`. An all-level selected-critical version
   would telescope to `epsilon=O(1/k)` and close the endpoint. The translated
   three-law Doeblin formulation proves only an exponentially small generic
   gain, so the missing theorem must use renewal-min self-consistency or the
   equivalent weighted global anti-alignment of argmin labels. Homogeneous
   softening gives a second, scalar route: prove
   `rho_(k,lambda,-beta)->s(lambda)` at each fixed finite temperature. The
   soft radii are now proved research-side to increase with refinement and
   have a limit bounded by `s(lambda)`; the missing theorem is that no positive
   phase gap remains. The level-uniform hard/soft sandwich would then close the
   endpoint even though the selector develops a cold boundary layer. The same-policy active graph
   has genuine recurrent defect lineages, but its natural finite quotient has
   failed. Exact finite diagnostics now also rule out the natural ordered
   read-once, aligned-grammar, sparse-polynomial, and low-rank-tensor
   representations of the selected policy; unrestricted succinct circuits
   remain open.
   `experiments/pressure-cert2/split_ratio_audit.py`;
   `docs/notes/multiscale-genealogy.md`;
   `docs/notes/terminal-defect-statistics.md`;
   `docs/notes/annealed-critical-coding.md`;
   `docs/notes/coarse-minimum-gap.md`;
   `docs/notes/doeblin-renewal-bridge.md`;
   `docs/notes/softmin-replica.md`;
   `docs/notes/same-policy-defect-automaton.md`;
   `docs/notes/policy-circuit-complexity.md`.
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
- **A bounded same-policy defect automaton from carry/policy labels — CLOSED
  for the natural quotient.** The active Jacobian really does contain large
  recurrent SCCs with defect splitting and merging, and an exact tightened
  step retains every selected `k=12` argmin. But deterministic refinement of
  the 81 carry/digit/policy states reaches 176,464 of 177,147 coordinate states
  in seven rounds; adding sibling order reaches 177,119, and every normalized
  sibling-gap pair is distinct. This leaves a future coarse conditional cone
  open, but the literal finite-state defect picture is the full Jacobian in
  disguise. `docs/notes/same-policy-defect-automaton.md`.
- **The proposed uniform pressure split `U(21/50)` — REFUTED on the tested
  exact feasible class.** At depth `9 -> 10`, an uncovered-to-uncovered
  `k=19` transition has exact child/parent ratio
  `1892575973641960/3487969866821777 = 0.542601... > 0.42`. This refutes that
  required closing constant, not every parameterized scalar H1, an eventual
  theorem after `k=19`, or an eigenfunction-specific statement. The violations
  are rare, which motivates the distinct mass-genealogy lane rather than
  rescuing the false pointwise bound. `pressure-certificate-2.md`;
  `experiments/pressure-cert2/split_ratio_audit.py`.
- **Entropy-increment monotonicity from feasibility alone — REFUTED.** At
  `k=3`, `lambda=1001/1000`, the positive vector
  `(101,100,75,101,100,75,101,100,150)` is strictly feasible even after both
  irrational branch weights are replaced by tighter rational lower bounds,
  yet its entropy increments satisfy `h_2>h_1`. The standard-library verifier
  checks all nine rational feasibility rows and the exact comparison
  `h_1<2/90601<50/2709<h_2`; the analytic inputs are the stated elementary
  logarithm inequalities. This closes a theorem about the full feasible cone,
  not a critical-eigenvector or canonical vanishing-slack entropy route.
  `experiments/kl/verify_entropy_monotonicity_counterexample.py`.
- **The two fitted geometric localization envelopes — CLOSED as all-level
  critical/vanishing-slack laws; scalar bridge, trace, explicit floor, and
  Perron identification kernel-checked.** For
  `1<lambda_k<=2`, the audited projection/
  Perron argument implies that any localizing critical family—or feasible
  family with aggregate normalized slack tending to zero—has the fixed-depth
  annealed Perron marginals. Their first exact obstructions are
  `h_1>6431/39690>3/20` and
  `Delta_2=622/1533>81/200`. Hence neither
  `(1/5)(3/4)^j` nor `(1/2)(9/10)^j` can be the needed uniform law, even though
  both still pass every finite row on which they were reported. This does not
  close relative `L1` compactness, looser summable bounds, polynomial
  entropy/Pearson control, or direct selected-family arguments.
  Commits `9cdcfaf`/`764b815` check the slack identity, the full weighted
  terminal-Pearson chain, and defect-plus-slack endpoint convergence. Commit
  `f0e96a5` checks the trace and the displayed fixed vectors/floor; `2bdb286`
  proves transport irreducibility, normalized nonnegative Perron uniqueness,
  and the low-level identifications.
  `experiments/kl/verify_annealed_envelope_floor.py`.
- **Renyi-2 criticality or global `L2` growth generically implies local Pearson
  decay — FALSE at audited research-proof level.** The annealed block
  derivation has `sum_e p_e^2=1/3`, and its global collision energy has a
  stochastic-kernel renewal. But an independent ternary product law,
  uniform except at power-of-two depths, has `Q_j=Theta(j)` while
  `chi_j=1` infinitely often. Moreover the normalized squared-`L2`
  detail-energy ratio is `1605/1387` on the exact direction `(1,1,-2)` at `k=3`.
  The product law closes the generic collision-growth implication. The signed
  detail witness separately closes only a uniform unweighted one-step scalar
  contraction for this linear shell-response operator—not weighted, multistep,
  or selection-specific energy arguments. The all-level product/coding algebra
  is an independently audited research proof with a bounded exact core.
  The fixed Green-kernel decomposition also closes a subtler shortcut: decay of
  each new conductor shell, even with absolute summability, does not identify
  the local-limit constant. The first shell contributes
  `-2086/67963`, so the proof must evaluate the signed sum and recover exact
  cancellation rather than merely discard high shells.
  `experiments/kl/verify_annealed_critical_coding.py`;
  `experiments/kl/verify_pair_carry_green_kernel.py`;
  `docs/notes/annealed-critical-coding.md`.
- **Renewal and positive-defect support, with the nonlinear minimum coupling
  removed, are insufficient for compactness.** The audited critical-vector
  algebra gives a geometric transport renewal, and
  the normalized annealed defect is a branch injection of the normalized
  fiber-excess profile. That profile can nevertheless be arbitrary without
  the nonlinear minimum coupling, while the renewal of a point input retains
  fixed mass on a shrinking cylinder. These are separate no-gos and do not
  construct a selected critical family satisfying their conjunction. Any
  compactness proof must add the full renewal-min coupling or comparably strong
  selection-specific information. This does not close direct compactness
  itself; the all-level reduction is research-proof-level, pending
  formalization. Uniform fiberwise `L-infinity` flattening is separately
  refuted by the exact critical class-eight row at `-1`: its max-normalized
  range has endpoint liminf at least `1/3`. The weaker cylinder Frostman bound
  for infinite towers and weak limits survives, as does the mass-weighted
  terminal-defect route. `docs/notes/annealed-critical-coding.md`.
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
feasible-sequence endpoint. Commits `4c7fcc3`/`659dc81` then make the literal
level-12 record an exact theorem: Lean reduces all 177,147 rows, proves their
semantic equality with the generic KL system, derives
`LevelFeasible 12 (18064231/10^7)`, and carries it through to the unconditional
literal-predecessor counting theorem. The full 8,765-job build and axiom audit
pass with only `propext`, `Classical.choice`, and `Quot.sound`; this record path
uses neither `native_decide` nor a project axiom. Rounds 22–29 also
kernel-check the generated payload's 2,187 row inequalities, their all-length
mass bounds, equality with an independently defined 243-state KL graph, the
irrational interval-weight domination, and exact interval tiling. General
all-level aggregated ball-mass domination and especially localization remain
open; this pressure half is not a limit proof. The exact depth-nine split audit
further rules out promoting its proposed `σ≤0.42` annealed scalar H1 bound to
the five exact certified feasible points tested (`k=15,…,19`).
Commits `9cdcfaf`/`764b815` additionally define the annealed linear operator and
normalized slack, prove the exact scalar slack/oscillation identity and sharp
terminal variation/Pearson bounds including the weighted mean-square lower
bound, and derive endpoint convergence from
vanishing defect plus slack. Commit `f0e96a5` proves all-level trace
intertwining and checks the explicit normalized endpoint vectors, their
projection, and exact low-level floor. Commit `2bdb286` proves the full
transport cycle, normalized nonnegative Perron uniqueness, and the endpoint
identifications. Commits `5a8727f`/`786c02e` check coarse-minimum
supersolution order and terminal-defect data processing; `78602d4` checks the
unconditional strict feasible lift and infinite strict ladder. Commits
`882a00e`/`9323f26` specialize that ladder to the exact `k=12` certificate and
transfer one strict step to an existential predecessor-count exponent above
the current Lean-native numerical exponent.

### Standing frame

x^{1−ε} counting (if ever reached) is a milestone, not Collatz; the conjecture
also needs no-divergence and no-cycles. The invariant-rank ledger
(`invariant-rank.md`) makes Conway's unsettleability (rank = ∞) precise and
tracks which certificate classes are provably insufficient. The descent ±sign
no-go proves any orbit-fate argument must couple 2-adic structure to the
Archimedean place — which is why every purely-local lane above eventually
hits the same wall.

## Current activity

- The exact iterated-minimum, translated-Doeblin, and `S_3` frustration views
  now isolate one missing selected-policy anti-alignment theorem. The local
  frustration lower bound clears the first-stage quadratic target on
  `k=12,...,15`, but only as finite exact data.
- The soft-min investigation found uniform zero-temperature control of values,
  a nonuniform near-tie boundary layer for selectors, and exact refinement
  monotonicity of the softened Perron radii. Their bounded limit exists; the
  stronger scalar target is to prove that it equals the annealed value.
  Floating Collatz--Wielandt diagnostics currently support this through `k=13`.
- The same-policy defect investigation is complete. It confirms real recurrent
  split/merge lineages, then rules out the natural bounded carry/policy quotient.
  The circuit probe is also complete at finite levels: the operator has a short
  output-linear uniform circuit, while selected policies at `k=12,...,15`
  defeat the tested OBDD, aligned-grammar, sparse-ANF, and tensor-train models.
  This is not a lower bound for unrestricted `poly(k)` coordinate circuits.
- CLEAN_LEAN has closed the finite counting bridge, exact `k=12` import,
  transport/Perron identification, coarse-minimum order, strict feasible lift,
  the conditional quadratic telescope, the one-stage canonical frustration
  seam, inherited-slack bookkeeping, and the exact scalar/rowwise all-stage
  slack-gain interfaces. Commit `174b16b` reduces nonlinear positive-eigenpair
  existence to a simplex fixed point; the pinned mathlib lacks Brouwer. Lean
  still does not prove the all-stage gain, localization, or a dimension-free
  endpoint rate.
- Larger-record computation is deprioritized as a limit strategy. Scaling the
  Lean-native import beyond `k=12` remains an engineering task; the active
  mathematical work is the all-level endpoint mechanism.

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

## Credit and mathematical inspiration

*Per Simon's note above: credit belongs to the human mathematics community,
with apologies for the imperfect attribution below. Anything of value here is
their idea; the errors are ours.* Our approach is, honestly, an assembly of
existing lines of work; the closest ancestors, and what each contributes:

**The direct spine of the counting result.**
- **I. Krasikov & J. C. Lagarias, "Bounds for the 3x+1 problem using
  difference inequalities," Acta Arith. 109 (2003) 237–258** (arXiv:math/0205002).
  The x^0.84 record and the LP/difference-inequality method we extend. Our
  entire counting line is *their method, run further and reinterpreted.*
- **[L. Collatz (1942)](https://eudml.org/doc/168987) and
  [H. Wielandt (1950)](https://doi.org/10.1007/BF02230720), the
  Collatz–Wielandt formula** — nonlinear
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
  2016)** — the certificate language. It enabled the structural no-go for
  autonomous charged/projective contraction; it is no longer a live endpoint
  route. Found independently via our keyword-blind search; the credit is theirs.

**Current endpoint inspirations — none selected for mentioning Collatz.**

- **A. Makur & J. Singh, [Doeblin Coefficients and Related
  Measures](https://arxiv.org/abs/2309.08475), and D. Lee, W. Lu, A. Makur &
  J. Singh, [Doeblin Curves](https://arxiv.org/abs/2606.19859)** supply the
  multiway-overlap and constrained-contraction language. Their generic theory
  is too weak here; renewal-min self-consistency is the project-specific input.
- **G. Litvinov, [Maslov
  dequantization](https://arxiv.org/abs/math/0507014); Y. Savas et al.,
  [entropy-regularized stochastic
  games](https://arxiv.org/abs/1907.11543); and J.-R. Chazottes & M. Hochman,
  [zero-temperature nonconvergence](https://arxiv.org/abs/0907.0081)** motivate
  the homogeneous soft-min family and warn that smooth finite-temperature
  selectors need not converge uniformly as temperature vanishes.
- **A. Bandeira, A. Singer & D. Spielman, [graph connection
  Laplacians](https://arxiv.org/abs/1204.3873), and C. Lange et al., [magnetic
  frustration inequalities](https://arxiv.org/abs/1502.06299)** provide the
  synchronization/frustration language. Their spectral theorems do not close
  the KL estimate because the abstract gain graph has flat sections.
- **M. Pivato, [defect-particle
  kinematics](https://arxiv.org/abs/math/0506417), and R. Paige & R. Tarjan,
  [partition refinement](https://doi.org/10.1137/0216062)** motivated the
  concrete same-policy propagation and quotient tests. This is inspiration and
  methodology, not a transferred cellular-automaton theorem.
- **R. Bryant, [ordered decision
  diagrams](https://doi.org/10.1109/TC.1986.1676819); I. Oseledets,
  [tensor trains](https://doi.org/10.1137/090752286); and Balle, Panangaden &
  Precup, [weighted-automaton
  minimization](https://arxiv.org/abs/1501.06841)** supply the restricted
  representation models used in the policy-circuit audit. Their machinery
  diagnoses exact finite complexity; it gives no unrestricted circuit lower
  bound.

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
method reread through nonlinear Perron–Frobenius and ergodic optimization, with
information contraction, zero-temperature smoothing, and exact formal and
computational audits used to expose the remaining selected-policy seam.

Full per-claim citations with URLs are inline in the `docs/notes/*` files and
`docs/LANDSCAPE.md`; the mirrored-PDF index is `papers/REFERENCES.md`.
