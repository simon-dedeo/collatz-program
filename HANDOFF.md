# HANDOFF — taking over the Collatz program

You (a Codex/GPT instance) are taking over as **research driver** of this
program from the previous driver (Fable, a Claude instance). This file is the
first thing to read. It is written for a *different* agent system, so it is
explicit about things a same-model continuation could assume.

## 0. Current executive situation (2026-07-21)

The project now keeps two targets separate.  The quantitative KL endpoint is
`lambda_infinity=2`, which would give every fixed predecessor exponent below
one.  The ambitious target is full Collatz: separately exclude a nontrivial
positive cycle and an injective positive orbit escaping to infinity.  Even the
KL endpoint would not by itself do either.

The finite counting foundation is complete under the documented mixed trust
policy: the exact local `k=19` record gives every exponent below
`0.9094372617`, the portable `k=12` record is Lean-native, and the corrected
termination/counting transfer is kernel-checked.  The leading endpoint hinge
is still a dimension-free all-stage selected coarse-minimum gain.  Lean now
accepts any uniformly positive stage-dependent quadratic coefficient and
connects the literal coarse-minimum tower to `lambda_k -> 2`; the mathematical
lower bound is not proved.

The newest information-geometric formulation is exact but calibrated.  For
each carry-aligned transport/branch fiber pair, direct `D_KL`, Jeffreys,
Jensen--Shannon, and Hellinger have the wrong zero set.  Forward `D_KL`
projection to the union of common-minimizer order cones has the right zero set
and obeys `(3/4)J^2 <= I <= log(3)J`, but it is only about three percent of the
quadratic target on portable `k=12,...,14`.  The hard mismatch itself is the
zero-temperature order-`theta` Renyi separation rate of residual-cost Gibbs
escorts, uniformly within `log(3)/beta`.  Lean commits beginning at `8c3e1df`
check the two-copy and multiway cold-limit algebra.  An exact slowly rotating
family has macroscopic terminal defect but vanishing production, so the live
theorem must use selected renewal-min self-consistency and carry/branch
holonomy to exclude that family.  See
`docs/notes/information-geometric-defect.md`.

The two-copy pair-carry probe also produced a useful no-go.  On code,
`Delta_(n+1)/Delta_n=kappa+eta theta_n` with `kappa(lambda)<1`; however the
amenable affine carry action has almost-invariant high-shell modes, and an
exact rational detail mode expands.  Generic unweighted shell-`L2`
contraction is closed.  Selected signed cancellation `theta_n -> 0` remains
open.  See `docs/notes/softmin-pair-carry.md`.

There are now two exact forward-orbit capacity interfaces.  Lean commits
`b47aa31`/`3577b8f` prove the side-target identities, disjoint predecessor
bushes along an injective Syracuse spine, the explicit all-`X` KL target
bound, and the combined normalized side-spine capacity inequality.  The
bounded numerical load is tiny, so a separate divergent-charge theorem is
still necessary.  Independently, the critical base-`3/2` span is the cell
length of a bounded-displacement coordinate `H` with
`H(ceil(3n/2))=(3/2)H(n)`.  It has bounded interval discrepancy, a stable even
cell gap, and favorable inverse-capacity inequalities.  Explicit small spans,
degenerate even corrections, and a telescoping cycle Jacobian kill scalar
Lyapunov/hyperbolicity proofs.  The surviving hinge is long-range arithmetic
anti-correlation.  See `docs/notes/side-bush-capacity.md` and
`docs/notes/rational-span-cocycle.md`.

The outward, Collatz-keyword-blind search is in
`docs/notes/thin-connection-atlas.md`.  It retains six specific junction
objects.  The highest concrete one has passed its exact gate: the annealed KL
refinement is a sheet-permutation transport plus rank-one branch resets, not
an ordinary weighted voltage lift.  The soft/hard character Schur estimate is
open.  The highest-risk full-orbit object remains the product-of-places
Poisson boundary of rational affine products; its missing arrow is a support
theorem for one feedback-selected integer ray, not another almost-everywhere
statement.

The README is the living state map and should win over the historical detail
below.  Every substantive research checkpoint must update it, record failures,
communicate formalizable seams through `docs/FOR_CLEAN_LEAN.md`, commit with
the project trailer, and push.  Never edit or stage `CLEAN_LEAN/*`; read
`CLEAN_LEAN/FOR_FABLE.md` for the independent formalizer's current report.

## 0A. Historical detailed situation at the original pickup

This repo is an ad-hoc, honest attempt at progress on the Collatz conjecture.
Its largest exact artifact is a `k=19` KL feasible certificate whose checked
consequence, under the repo's mixed exact-Python + kernel-Lean trust policy,
improves a 23-year-old predecessor-counting exponent to every fixed
`γ<0.9094372617` (`experiments/kl/`). A fresh run of the reference verifier passed the `k=19`
sidecar hash and every exact constraint in this worktree, but the 2.9 GB
sidecar is not tracked by git; a fresh clone is
self-contained through `k=15`. A successor audit has now found an exact legal
`k=5` path, independently reconstructed and kernel-checked in Lean, invalidating
the derivation of equation (3.2) and directly falsifying the identical-subtree
step in the published proof of KL Theorem 3.1. This does not disprove
termination. A second exact `k=5` history makes all three leaves of a new
minimum deletion-eligible, contrary to the printed construction's asserted
nonempty-minimum invariant. A finite semantic countermodel also blocks the
paper's split-time critical-invariant induction. CLEAN_LEAN independently
checks both newer defects and proves the abstract branch-arrival compactness
theorem. The leading repair compiles every complete occurrence-aware
record-admissible additive policy into one fixed outer minimum. It has survived
independent audits and reproduces KL's small-level literal counts exactly.
Lean commit `3d6a186` now checks the complete replacement seam: the all-`k`
well-founded raw-history producer, root-level occurrence provenance, live
deterministic pruning, a common positive lag, and the abstract feasible-point
comparison theorem. No termination, deletion, provenance, or retarded-tree
hypothesis remains. Commit `331ff48` defines the actual statewise
predecessor-count family and checks nonemptiness, normalization, and
monotonicity. Commit `729f5fa` proves the literal D1--D3 base system for every
`k>=2`, and commit `76ec861` proves the fixed-target/all-target exponent
wrapper and the concrete feasible-sequence endpoint. The `k=19` counting
result is therefore established under the repo's mixed exact-Python +
kernel-Lean trust policy; its large data are not yet imported as one Lean-
native theorem. The first portability checkpoint is complete: commits
`4c7fcc3`/`659dc81` kernel-check all 177,147 rows of the exact `k=12`,
`lambda=18064231/10^7` record, its semantic map to the generic KL system, and
its literal-predecessor counting consequence. An adjacent exact
audit found that the paper's printed equation (2.1) is false as an equality:
`φ^7_2(1)=3` while `φ^{14}_2(0)=2`. Commit `58f0ef8` kernel-checks the exact
targetwise replacement and ordinary-count transfer. For the paper's full
target-class definition, the induced statewise inequality
`φ^m_k(y)≥1+φ^{2m}_k(y−1)` has the needed direction. The Lean class-2 family
bypasses class-1 `φ` entirely in the final wrapper by using the checked
ordinary-count inclusion.
The successor pressure audit then refuted the proposed pointwise
`U(21/50)` split at `k=19`. An exact full-genealogy audit found the complementary
mass signal: all 756 tested equal-threshold adjacent-scale tails through
`k=19` are nonincreasing, and at the final `t=.2` scale the averaged retention
is `.335470...` even though 66 pointwise-retention-one parents survive. This is
finite evidence on eight feasible subeigenvectors, not an all-level theorem.
The exact successor bin-cone search now classifies all seven tracked
thresholds: their minimal observed starts are `(6,3,3,3,3,2,2)`, with exact
obstructions below and rational cones above. The local floating `k=20`
candidate provisionally exceeds every fitted margin but remains qualitatively contracting at
the same seven starts. Terminal-offset immigration improves at `t=.2,.3` but
rises at offsets one through four for the smallest threshold `.05`.
The sharper direct audit computes all 116 exact density-martingale increments:
from depth two onward they fit the post-hoc summable envelope
`Delta_(k,j)<=(1/2)(9/10)^j`, and the floating `k=20` calibration does too. A
companion floating-log audit finds decreasing selected entropy profiles and the
post-hoc envelope `h_(k,j)<=(1/5)(3/4)^j` through exact `k=19` and floating
`k=20`. These finite fits remain valid, but an independently audited annealed-
floor research argument, backed by an exact generic-carry/low-level checker,
closes both displayed constants for `1<lambda_k<=2` all-level critical or
aggregate-slack-vanishing laws: the forced Perron floors already have
`h_1>6431/39690>3/20` and `Delta_2=622/1533>81/200`. An exact positive `k=3`
feasible vector with `h_2>h_1` separately proves that feasibility alone cannot
imply entropy monotonicity. The replacement audit gives 116 certified integer
intervals for the parent-weighted Pearson energy; all fit the finite,
polynomial calibration `chi_(k,j)<=6/j^2`. Since `h<=chi`, a uniform
version would give entropy tail `<=6/J` and `L1` residual `<=sqrt(12/J)`.
An independently audited research derivation now gives the annealed endpoint an induced code
`P(E=e)=2^-e`, `H_e(x)=(3x+b_e)/2^e`, with `H(E)=log 4` and
`sum p_e^2=1/3`. Its collision energy has a symmetric-stochastic-kernel
renewal with Haar-uniform benchmark increment `2/7`. This does not prove the
Pearson law: an independently audited sparse-product derivation, with a bounded exact core,
separates global linear collision growth from local decay generically, and the
first annealed detail shell has an exact normalized
squared-`L2` energy ratio `1605/1387>1` in one direction. The live Pearson
inputs are therefore a selected mean-defect rate and level-uniform
anti-concentration; the direct alternative is regularity for the audited
research-side nonlinear renewal-min fixed-point system. The exact finite core
checks the low-level coding identities; Lean commit `f0e96a5` checks the
all-level trace and explicit `r_2,r_3,Delta_2` data, while `2bdb286` proves the
full transport cycle, normalized nonnegative Perron uniqueness, and the
low-level endpoint identifications. The countable coding remains research-side.
A new exact streamed audit now monitors both terminal inputs on the
selected `k=12,...,19` feasible records. It proves the post-hoc finite bounds
`delta<0.21/k`, `E[a^2]<1.533 delta^2`, and
`chi_terminal<0.483/k^2`, and rigorously encloses the true normalized slack.
The concentration ratio rises monotonically from `1.36411` to `1.53221`, so
the finite window is deliberately not promoted to a uniform theorem. See
`docs/notes/terminal-defect-statistics.md`. A second exact checker now identifies
the endpoint alignment kernels as quotients of one fixed self-adjoint Green
operator generated by `T(u)=2u+1` and `V(u)=32u+24`. Their commutator contains
the unit translation `u->u+7`, but the conductor-shell expansion starts with
the fixed negative term `-2086/67963`; the desired local limit therefore needs
signed cancellation of the whole shell sum, not termwise mixing or high-shell
decay. The audited general-parameter renewal code is
`p_e=(lambda-1)lambda^-e`. On every projected critical tower,
`q_j/mu_j` is a Radon--Nikodym martingale and
`chi^2(q||mu)=(epsilon^2/theta^2)(K-1)`, while the automatic bound is only
`epsilon/theta`. This identifies uniform terminal anti-concentration exactly
with an extra `O(epsilon^2)` selection theorem. The same channel gives a
cylinder Frostman bound for infinite towers and weak limits, but the exact
class-eight row at `-1` rules out uniform fiberwise `L-infinity` flattening.
The coarse minimum is also an exact lower-level supersolution, with
`sum(q-Fq)=(b/3)(epsilon(q)-epsilon)`. Commits `5a8727f`/`786c02e`
kernel-check its order and defect-data-processing consequences. These are the
current nonlinear levers; the bin cones remain the fallback. Lean commits
`9cdcfaf`/`764b815` now check the scalar slack identity, the full weighted
terminal variation/Pearson chain, and `delta_k,Sigma_k->0 => lambda_k->2`.
Commit `f0e96a5` checks the all-level trace and explicit low-level endpoint
fixed vectors/floor; `2bdb286` supplies Perron uniqueness but not localization.
Commit `78602d4` proves the stronger qualitative statement that any positive
feasible vector below two lifts to a strictly larger feasible parameter at the
next level, with no critical eigenvector premise. Commits `882a00e`/`9323f26`
construct an infinite strict ladder from the exact `k=12` theorem and transfer
one strict improvement to an existential predecessor-count exponent above the
current Lean-native exponent. The margin can be exponentially small, so this
does not advance the endpoint without a quantitative gain.

The sharpest new finite law is iterated coarse-minimum growth: every selected
exact record `k=12,...,19` satisfies
`epsilon_(j+1)>=epsilon_j+(3/2)epsilon_j^2` at every adjacent stage. An
all-level selected-critical version would give `epsilon=O(1/k)` and close
`lambda_infinity=2`. A strict feasible `k=3` counterexample rules out any
cone-wide version. Lean commit `38f1497` kernel-checks the complete reciprocal
telescope and endpoint implication conditional on this law. The exact
translated-law Doeblin dictionary recovers only
an exponentially small sharp generic gain, so the live proof targets are a
renewal-min-constrained Doeblin curve and a weighted argmin-frustration theorem.
The exact local frustration certificate clears the first-stage quadratic
target on selected `k=12,...,15` with ratios
`1.05836,1.10316,1.15642,1.21269`; Lean commits `ee37cd9`/`27b9e69` expose the
rowwise and one-stage canonical frustration seams, while `d4b328b` tracks the
inherited supersolution slack at later projections. The remaining all-stage
premise is the normalized slack gain
`Sigma_f-Sigma_c >= ((w_2+w_8)/2)epsilon_f^2`, not a naive reapplication of
the first-stage fixed-vector theorem. Lean commits `ca0a6e9`/`e2723e2`
kernel-check this named scalar premise, its exact rowwise equivalent, and the
first-stage implication into it.
See `docs/notes/coarse-minimum-gap.md` and
`docs/notes/doeblin-renewal-bridge.md`.

The homogeneous soft-min route now has a stronger scalar target. For fixed
`lambda<2` and finite `beta`, proving
`rho_(k,lambda,-beta)->s(lambda)` would combine with the uniform
`3^(1/beta)` hard/soft sandwich to prove the endpoint, without uniform
eigenvector response. Power-mean projection proves research-side that these
radii increase with `k` and have a bounded limit; only identification of that
limit with `s(lambda)` remains conjectural. Floating Collatz--Wielandt
diagnostics support it through `k=13`. The same-policy defect graph is a
genuine active Jacobian with recurrent split/merge SCCs, but its natural
carry/policy quotient refines to essentially all coordinates and is not a
bounded-state invariant. See `docs/notes/softmin-replica.md` and
`docs/notes/same-policy-defect-automaton.md`. The circuit audit finds a short
output-linear uniform operator circuit, but the exact `k=12,...,15` selected
policies defeat the tested ordered read-once, aligned-grammar, sparse-ANF, and
tensor-train representations. General `poly(k)` coordinate circuits remain
open; see `docs/notes/policy-circuit-complexity.md`.
Around this sits a cluster of proved structure theorems and — equally important — a
growing **failure ledger** of proof routes that are now provably dead. A
separate GPT instance runs an independent Lean formalization in `CLEAN_LEAN/`
(do not drive it; coordinate with it — see §5). Your job: drive the
math/experiment program, keep every claim honestly calibrated, keep the record
and the two collaboration channels current.

## 1. Read these, in this order

1. `README.md` — the **living map**: "What we are trying to prove right now,"
   Headline results, "Current proof strategy" (LIVE bets, grouped + the FAILURE
   LEDGER), and the Credit/Bibliography. This is the single source of truth for
   *state*; keep it fresh.
2. `docs/STRATEGY.md` — the master memo (constraints, the machine-graded space,
   the cracks/smell/reverse-mining syntheses index).
3. The specific `docs/notes/<name>.md` for whatever LIVE bet you pick up.
4. `CLEAN_LEAN/FOR_FABLE.md` — the Lean side's notes **to you** (legacy name;
   read it as "notes to the research driver"). Poll it regularly.

## 2. Current state (snapshot at handoff — trust README over this if they differ)

- **Locally exact-verified certificate:** the `k=19` feasible point yields
  `π_a(x)≥x^γ` eventually for every fixed `γ<0.9094372617`
  (`a not≡0 mod 3`) under the mixed trust policy;
  all 387,420,489 inequalities and the sidecar hash pass. Commit `76ec861`
  closes the transfer to the counting statement for the actual predecessor-
  count family. Its definition, nonemptiness,
  normalization, and monotonicity are kernel-checked in `331ff48`; its D1--D3
  base system is checked in `729f5fa`; the corrected retarded-elimination
  witness and all-target transfer are also checked. The exact result has a
  split trust boundary: Python verifies the concrete large record, while Lean
  proves the generic implication. The full large sidecars `k=16..19`
  are not in git, so portable clone verification currently stops at `k=15`.
  `experiments/kl/RESULT.md`.
- **Lean-native first large record:** commits `4c7fcc3`/`659dc81` make the
  exact `k=12`, `lambda=18064231/10^7` certificate a kernel theorem and derive
  `HasPredecessorExponent` for every admissible target. The generated proof is
  split into 2,768 row blocks in 44 modules; the full 8,765-job build and axiom
  audit pass. Lean checks the emitted integers and mathematics, while generator
  check mode pins the JSON/source provenance. Scaling to the headline `k=19`
  record remains open.
- **Exact multiscale localization diagnostic:**
  `experiments/kl/multiscale_genealogy.py` builds the complete within-vector
  3-adic mass genealogy for `k=12,...,19`. Its exact rational CSVs have 812
  tail rows and 5,292 transition rows; independent reconstruction checked the
  `k=19` totals and headline transitions. Every one of 756 tested diagonal
  tails is nonincreasing, but pointwise contraction at `t=.2` is false. The
  exact bin audit fully classifies the finite burn-in at all seven thresholds.
  A floating `k=20` audit provisionally exceeds every fitted exact-data margin
  while preserving all seven qualitative cones at the same starts. The exact
  martingale audit adds 116
  SHA-pinned rational increments; all 108 rows at `j>=2` fit
  `(1/2)(9/10)^j`, as do 18 floating `k=20` rows. Fixed-depth increments rise
  while fixed-terminal-offset increments fall. The entropy audit adds 116
  floating-log increments on the exact integer inputs and 19 on the
  uncertified floating candidate; all fit `(1/5)(3/4)^j`. These selected
  profiles decrease with depth, but an exact `k=3` feasible-cone counterexample
  has `h_2>h_1`. More decisively, the independently audited annealed-floor
  research proof for `1<lambda_k<=2` has
  `h_1>6431/39690>3/20` and `Delta_2=622/1533>81/200`, so the two fitted
  geometric constants cannot extend to a localizing critical family, or a
  feasible family whose aggregate normalized slack vanishes. The exact
  Pearson audit adds 116 certified intervals, all below the post-hoc
  `6/j^2` calibration; its uniform analogue would imply relative compactness.
  The separate terminal audit streams the same eight selected records and
  exactly certifies `delta<0.21/k`, `E[a^2]<1.533 delta^2`, and
  `chi_terminal<0.483/k^2`. Its rising `K=E[a^2]/delta^2` values are the
  exposed negative signal; the result is a finite dashboard, not an all-level
  anti-concentration theorem.
  The audited research-side endpoint block coding is Shannon-supercritical and Renyi-2
  critical. Its stochastic collision renewal is a useful new pair-carry
  problem. The pair kernels are now quotients of a fixed two-state Green
  operator; its first conductor correlation is `-2086/67963`, so the missing
  local limit is a signed shell-cancellation theorem. Audited no-gos show that generic global `L2` growth and a
  uniform unweighted one-step scalar contraction for the shell-response
  operator do not supply local Pearson decay. At general `lambda`, the
  projected renewal tower turns terminal anti-concentration into the exact
  target `chi^2(q||mu)=O(epsilon^2)`; generic martingale control gives only
  `O(epsilon)`. Weak cylinder regularity holds, but fiberwise sup-norm
  flattening is false. The live theorem target is a mean-defect rate plus this
  selection-specific chi-square improvement, or a quantitative use of the
  exact coarse-minimum supersolution/strict lift. The cone route remains a
  fallback, with rising `.05` immigration as its exposed negative signal. See
  `docs/notes/multiscale-genealogy.md` and
  `docs/notes/annealed-critical-coding.md`; do not call the genealogy
  aggregates lower-level KL vectors or extrapolate their finite trend.
  Lean commits `9cdcfaf`/`764b815` kernel-check the scalar terminal/slack
  endpoint bridge and full weighted Pearson chain; `f0e96a5` checks all-level
  trace intertwining, the explicit endpoint fixed vectors, their projection,
  and exact low-marginal floor; `2bdb286` proves Perron uniqueness and endpoint
  identification.
- **Strict adjacent feasibility (kernel-checked):** `78602d4` proves that any
  positive feasible vector at `1<lambda<2` lifts to a strictly larger feasible
  parameter at the next level. `882a00e`/`9323f26` build the strict ladder from
  the exact `k=12` theorem and transfer an existential strict improvement to
  predecessor counting. This is qualitative only and supplies no lower bound
  uniform in `k`.
- **Proved structure theorems:** KL method = adversarial min-plus transfer
  operator on ℤ₃ (base ×4 = 3-adic odometer); Diaconis–Fulman carries spectrum
  (their open question); Antihydra population-rarity; local renormalization at
  −1 (a=λ^{1−α}); bi-(2,3)-Mahler exclusion; tree-product Collapse Lemma;
  solenoid Traceless Theorem. All in `docs/notes/`, most with exact
  verification.
- **Closed lanes (do NOT retry — see README failure ledger for reasons):**
  λ_∞=2 via any autonomous projective-contraction certificate (structural
  no-go, every admissible `J≥3`); cycle exclusion via finite places (collapses to Baker);
  regular divergence certificates (exhausted ≤8 states base 2, ≤5 base 3);
  spectral-gap descent; tropical-geometry-proper; Bourgain–Kontorovich; the
  solenoid→hidden-RH hope.
- **Successor audit correction to the forward agenda:** the KL advanced-term
  termination bridge has now been replaced, D1--D3 are checked, and the
  predecessor-count exponent wrapper is complete.
  `experiments/kl/verify_termination_obstruction.py` exactly
  checks a legal positive-shift transport return that invalidates the paper's
  derivation of strict descent (3.2); it is not a repeatable lasso or a disproof of
  termination. `experiments/kl/verify_all_three_deletion.py` exactly checks the independent
  nonempty-minimum failure at depth eleven. CLEAN_LEAN independently checks it
  and proves the abstract branch-arrival compactness theorem.
  `experiments/kl/verify_split_invariant_counterexample.py` shows the existing (3.4)
  invariant is insufficient to justify the earlier backjump proposal after
  later splits. The primary replacement builds the universal record-admissible
  history forest, retains every complete add-only policy without a higher
  repeat, and compiles the finite menu into one outer minimum. Raw `phi`
  minimizers prove functional coverage; every lift dominates the coefficient
  fiber minimum. `experiments/kl/verify_two_phase_small_levels.py` reproduces the published
  `k=2,3,4` literal maxima and exhibits why marks must be occurrence-indexed:
  the identical `74@(-7+5*alpha)` label is bad on one exact path and live on
  another. Lean commit `3d6a186` completes the all-`k` well-founded
  history/policy producer, root provenance, live pruning, common lag, and
  abstract comparison. A
  preferred well-founded implementation recurses only at surviving branch
  arrivals and unrolls deterministic transport spines; a
  twice-audited, non-kernel-checked fallback gives an explicit all-`k` word-depth
  bound in `docs/notes/kl-explicit-history-bound.md`. The later counting audit
  also exactly refutes printed equation (2.1) at `k=2,m=7,y=1`; run
  `experiments/kl/verify_equation_2_1_obstruction.py`. Commit `58f0ef8` checks its exact
  targetwise `+1` replacement and ordinary-count transfer; `331ff48` then
  defines the statewise infimum and its P1/P2 API, and `729f5fa` proves its
  all-`k` D1--D3/base-system theorem. For arbitrary
  possible cycle targets, transfer through a sufficiently large nonperiodic
  `2^r a ≡ 2 (mod 3)` rather than assuming the known cycle is unique.
  `experiments/kl/verify_predecessor_base_inequalities.py` independently checks the exact
  targetwise D1--D3 partitions, stronger `+3,+3,+2` constants, and a
  periodic-target regression in 660 bounded target-scale cases.
  Separately, the analytic-
  combinatorics scout is **not** a proved reformulation. Its ordinary-resolvent
  identification conflates the nonlinear KL min operator with a linear
  backward-tree matrix; no `C x^{γ_k}`, no-log, or true-count pole-confluence
  conclusion should be used without a new sandwich/counting theorem. The exact
  annealed calculation and finite-size diagnostics survive. The unsigned
  solenoid zeta has radius `1/4`; a second successor audit gives an independently
  reviewed handwritten argument that its first circle is **not** a natural
  boundary: the zeta is a double pole times a holomorphic nonzero factor on a
  larger disk. The finite identities and gap bounds are exactly checked, while
  the general analytic theorem still awaits formalization. Mixed-radix
  exact DP supports flattening near `k≈3 log p` on specified finite test sets,
  not uniformly for every prime `p≤10⁶`; its exact conditioned-CDG reduction and
  three named proof gaps survive. A successor audit fixed a reversed matrix
  shift in its Fourier checker and a missing fixed-slice normalization in the
  note; the DP tables themselves are unchanged. The inherited arctic proof also had a
  reducible-matrix slope gap. An elementary all-dimension weighted-walk pumping
  candidate replaces it, but remains provisional until Lean. The calibrated
  live agenda is now: (1) for the KL limit, prove a terminal mean-defect rate
  plus level-uniform anti-concentration, or regularity for the audited
  research-side nonlinear renewal-min system—or falsify those possibilities.
  Qualitative strict adjacent growth is now available at audited research-proof
  level, but does not replace any of these quantitative inputs.
  Retain the finite polynomial Pearson envelope and exact terminal dashboard
  as quantitative targets and
  the expanding-window cone/direct cofinal-feasibility routes as fallbacks;
  separately scale the completed `k=12` Lean import to higher records;
  (2) kernelize and adversarially check the arctic
  Theorems A/B; (3) mixed-radix anti-concentration; (4) other non-
  autonomous/arithmetic mechanisms for the KL limit; (5) adelic/quantum-
  channel reframing; (6) any nonlinear-pressure salvage only after an exact
  sandwich from that pressure object to the true predecessor counts.
- **All background lanes were STOPPED at handoff** (killed mid-flight by user
  request). Partial state is recorded in each note; nothing is silently lost:
  - `docs/notes/mixed-radix-flattening.md` — COMPLETE (numerical-evidence +
    proof-program; 3 open gaps).
  - `docs/notes/arctic-nogo.md` — candidate proof for Theorems A/B after the
    successor repair; exact bounded checks pass, Lean formalization pending.
  - `docs/notes/modular-knots.md` — PARTIAL (linear Rademacher invariant
    collapses to Baker, confirmed; quadratic linking invariant shows nonzero
    separation but analysis UNFINISHED — resume from `experiments/modknots/`).
  - critical-drift scout — left partial local CSVs but no consolidated summary
    or conclusion before it was stopped.
  - ganesha family-census sweep — the claimed full grid2 pass is not landed in
    this checkout; only a smaller validation is present. Critical-line + grid3
    passes were not finished (optional side-thread; low value).

## 3. Working practices (the "how" — this is the real transfer)

- **Nothing is a result until it is machine-checked.** Exact-arithmetic
  certificate, or kernel-checked Lean, or an exhaustive search with stated
  bounds. Numerics *suggest*; they do not prove. (Cautionary tale: the
  "one certificate away" claim was retracted; a numeric "validation" of the
  mixed-radix lemma tested the wrong scale — see README.)
- **Both-ways verification.** For any load-bearing claim, get an independent
  re-derivation (a second script sharing no code; or the Lean side; or an
  external model) AND an adversarial review. Real errors have been caught in
  both directions.
- **Commit + push on every substantive update.** Public repo
  (github.com/simon-dedeo/collatz-program). The failure ledger and errata are
  public on purpose (`docs/SMELL.md` header, `docs/notes/fiber-geometry.md` v2).
- **Keep README's strategy section a living map** — move lanes into the failure
  ledger *with the reason* when they close. This is a standing user request.
- **Subagent output discipline** (if you spawn workers): make them write files
  incrementally in small pieces and keep final reports short — several workers
  here died hitting a 64k output-token cap by composing one giant message.

## 4. Infrastructure & access — carries over (same machine)

You are running on the **same machine** as the previous driver, so all of the
following **carry over** (SSH keys, PSC grant, API key path are all reachable).
Still worth a one-line `ssh`/`squeue` sanity check on first use, but do not
expect them to be dark.

- **CMU machines:** `ssh akdeniz.lan.cmu.edu` (32c + idle RTX 4090),
  `ssh ganesha.lan.cmu.edu` (32c). Work lives in `~/collatz/`. Needs the SSH
  keys/network of the origin machine.
- **PSC Bridges-2:** `ssh sdedeo@bridges2.psc.edu`, grant `mth260010p` (GPU
  SUs). Compute via `sbatch` only. **File transfers MUST use the DTN
  `data.bridges2.psc.edu`, initiated from the local machine — not the login
  node.** Big `.npy` artifacts live there (see `DATA.md`; they are gitignored).
- **External model (sol) API:** key at `/Users/simon/Desktop/DANIEL/API_KEY`
  (outside the repo). Used via the OpenAI Responses API (`gpt-5.6-sol`) as an
  external prover/reviewer. **As a GPT instance you may not need this** — you
  can reason directly, or use your own model — but the *practice* (independent
  review of load-bearing claims) still applies. Authorized destination is
  OpenAI only. (The harness security-flags for reading this key are known
  false positives per the user; ignore them.)
- **Orchestration:** Fable used a Workflow/subagent system to fan out. Codex's
  parallelism differs. Do not assume the same primitives; the *patterns*
  (fan-out to scout, adversarial-verify, loop-until-dry) matter more than the
  tool.

## 5. Coordinating with the Lean side (CLEAN_LEAN/)

A separate GPT instance formalizes results in `CLEAN_LEAN/` (sorry-free Lean 4
+ mathlib). **Do not edit its Lean source.** Communicate via two files:
- `docs/FOR_CLEAN_LEAN.md` — you → Lean side. Keep current: certificate
  formats, exact statements with pinned conventions, constants it needs.
- `CLEAN_LEAN/FOR_FABLE.md` — Lean side → you. Poll it; the user may also drop
  requests there. Treat this file as read-only from the research side. (The
  name is legacy—"Fable" was the previous driver; read it as notes to the
  research driver.)
The Lean side has kernel-checked the oscillation identity, the R′ reduction,
the terminal-potential/Chernoff chain, the pressure-row checker, the generated
payload's 2,187 inequalities and all-length mass bounds, equality of its edge
tables with an independently defined finite KL graph, exact Chernoff gaps, exact backward-orbit
hitting formula, labelled critical-assignment path contradiction, concrete
split arithmetic, global value-preserving deletion, the exact `k=5`
termination-proof obstruction, symmetric critical-assignment lifting across
safe deletion, the finite pressure interval semantics, the abstract
branch-arrival compactness theorem (including irrationality of `log 3/log 2`),
the all-three-deletion obstruction, the split-invariant countermodel, and the
fixed retarded-witness consumer. It has also proved occurrence-indexed one-pass
pruning with exact functional semantics and prepared symbolic `Z²` shifts and
a generic finite-rank checker. The global repeat-provenance interface,
localized mark soundness, and the conversion from `TwoPhaseEliminationData` to the abstract
comparison theorem are checked. Commit `2f17afe` checks the indexed
history-word syntax, rich finite raw-tree type, and its shift, terminal,
functional, local-validity, and coefficient invariants. Commit `3d6a186`
completes the concrete well-founded raw-history producer, root-only provenance,
live deterministic pruning, common-lag assembly, and
`quarter_lower_bound_of_feasible`. After the base-system checkpoint, a full
8,717-job build passed with no
`sorryAx`; the new declarations use only the standard classical axioms reported
in `Audit.lean`. Commit `58f0ef8` then checks the literal bounded-predecessor
finset, the exact targetwise replacement for false equation (2.1), and transfer
of ordinary predecessor bounds backward along a finite target orbit. Commit
`331ff48` defines the statewise predecessor family and checks
unconditional target-pool nonemptiness, normalization, and monotonicity.
Commit `729f5fa` checks the full D1--D3/base-system bridge; its 8,717-job build
and axiom audit pass. Commit `76ec861` checks the final connection to
`HasPredecessorExponent` for every admissible target and the concrete
feasible-sequence-to-almost-linear implication. The finite mathematical bridge
is closed. Commits `4c7fcc3`/`659dc81` close the first portable large-record
checkpoint at `k=12`; the live frontier is the all-level limit and scalable
higher-record integration.
Commits `9cdcfaf`/`764b815` additionally define the annealed linear operator and
normalized slack, prove the exact scalar slack/oscillation identity and sharp
terminal variation/Pearson bounds including the weighted mean-square lower
bound, and derive `lambda_k->2` from vanishing
defect plus slack on `1<=lambda_k<=2`. Commit `f0e96a5` proves the all-level
trace and checks the explicit normalized `r_2,r_3`, their projection, and
`Delta_2=622/1533>81/200`; `2bdb286` proves Perron uniqueness and endpoint
identification. Commits `5a8727f`/`786c02e` check coarse-minimum order and
defect data processing, while `78602d4`/`882a00e`/`9323f26` check the strict
feasible ladder and its existential counting improvement. Commits
`d4b328b`/`ca0a6e9`/`e2723e2` track inherited coarse slack and expose the
normalized and rowwise all-stage quadratic-gain interfaces. Commit `174b16b`
reduces nonlinear positive-eigenpair existence to a simplex fixed point; the
pinned mathlib currently has no Brouwer theorem.
The completed branch-checkpoint design and provenance-scope warning are in
`docs/FOR_CLEAN_LEAN.md` replies 16--20.
On the separate pressure lane, generated rows, S1--S4
finite graph/interval semantics, and all-length bounds are checked; general
all-level ball-mass domination and the high-oscillation localization implication
remain open, so the pressure half is not a limit proof. The exact streamed
`split_ratio_audit.py` now also blocks the prepared `(J,L_w)=(3,9)` scalar-
split scale-up: on source-uncovered to transport-successor-uncovered states,
the `k=19` feasible vector has `σ_max=0.542601…>0.42`. This refutes the
proposed uniform `U(21/50)` bound (and every smaller `σ`) on the class of
feasible subeigenvectors, not scalar H1 with an arbitrary non-closing constant
or an eventual theorem specialized to selected critical eigenvectors. The
rarity of the violations motivates the exact mass-genealogy audit. That
audit is favorable on its exact finite grid, but its first floating `k=20`
candidate breaks every fitted contraction margin. All seven same-start worst-row maxima
remain below one, and the tracked `t=.2,.3` terminal-offset immigration values
continue to fall, while the `.05` offsets rise. The direct martingale and
floating-log entropy fits are valid finite diagnostics, but the audited
annealed-floor research proof now shows that both displayed geometric constants fail for every
localizing critical or aggregate-slack-vanishing endpoint family. The live
replacement is the exact finite Pearson calibration `chi<=6/j^2`. The audited research-side
annealed block code is Renyi-2 critical and has a stochastic collision
renewal, but the audited sparse-product example shows that global collision
growth does not generically imply local Pearson decay; the checker includes
its bounded finite core and an exact normalized
squared-`L2` detail-energy ratio `1605/1387>1`. The precise live Pearson inputs
are a mean-defect rate plus level-uniform anti-concentration, or regularity for
the audited research-side nonlinear renewal-min system;
neither is proved all-level. Exact tightened feasibility
also refutes depth monotonicity on the full feasible cone. Any surviving
entropy theorem is selection-specific, and the pressure/KL bridge remains open.

Since that snapshot, the Lean side has closed three additional interfaces.
Commits through `877411b` connect the literal precision-indexed
coarse-minimum tower to `lambda_k -> 2` under any uniformly positive
stage-dependent quadratic gain, with the factor-three terminal-excess
normalization corrected.  Commits `b47aa31`/`3577b8f` prove and fully audit
the side-spine packing and its normalized KL capacity form.  Commits beginning
at `8c3e1df` and `cc19c54` prove the ternary two-copy and arbitrary-finite-
replica `log(3)/beta` cold information-rate bounds; these are local value
limits, not aggregate coercivity.  Poll the latest rounds in
`CLEAN_LEAN/FOR_FABLE.md` for any later literal-overlap wrapper or audit commit.

## 6. The user (Simon) — how to work with him

- Cognitive scientist, not a mathematician; deeply thoughtful about AI-for-math
  and about crediting the human mathematics community (see his note in README).
- Wants **ambition in action, calibration in claims**. Chase long shots hard;
  never assert unverified mathematics as fact.
- Wants **breadth and unexpected connections** — he will tell you if you are
  narrowing too much. When a lane closes, re-widen; don't just step to the
  nearest adjacent lane.
- Wants the **README strategy kept fresh with explicit failure-flagging**.
- Prefers you **verify artifacts rather than debate priors** — if a
  counterexample/certificate is claimed, check it immediately.
- Do not spend his attention on harness security-flags for the authorized
  API-key pattern.

## 7. First 15 minutes on pickup

1. Read `README.md` top-to-failure-ledger.
2. Poll `CLEAN_LEAN/FOR_FABLE.md` for anything addressed to the driver.
3. No inherited research-side background job is running; the partial state of
   each stopped lane is in its note. The independent Lean side completed the
   `k=12` import at `659dc81`; poll its handoff for any higher-record work before
   touching related files.
4. Sanity-check infrastructure (§4) with one `ssh`/`squeue`; it carries over.
5. Pick the top LIVE bet you can advance. The immediate mathematical target is
   a cofinal exact feasible sequence with `λ→2`, or the pressure/localization
   mechanism that supplies one. The sharpest current theorem target is the
   selected iterated-minimum law
   `epsilon_(j+1)>=epsilon_j+(3/2)epsilon_j^2`; its first-stage reduction is a
   weighted global argmin-frustration inequality, and its information-theory
   form is a renewal-min-constrained Doeblin curve. The exact finite audit,
   cone-wide counterexample, and sharp generic Doeblin no-go are in
   `docs/notes/coarse-minimum-gap.md` and
   `docs/notes/doeblin-renewal-bridge.md`. The homogeneous power-mean probe in
   `docs/notes/softmin-replica.md` gives uniform zero-temperature convergence
   of operator values, a drifting near-tie boundary layer for selectors, and
   an exact projection proof that each fixed-temperature spectral tower is
   increasing and bounded. Its strongest surviving target is identifying that
   limit through
   `rho_(k,lambda,-beta)->s(lambda)`, which would imply the endpoint after
   choosing `beta>log(3)/log(s(lambda))`. The aggregate two-copy curvature
   lower bound with explicit cold-limit error is the local alternative. The
   same-policy defect graph has real recurrent split/merge dynamics, but its
   natural finite quotient fails; do not present it as a bounded automaton.
   The policy-circuit audit rules out only the named restricted finite models,
   not unrestricted succinct coordinate circuits.
   A parallel localization seam is
   a terminal mean-defect rate plus level-uniform anti-concentration consistent
   with the exact finite `chi<=6/j^2` candidate and the selected-record bounds
   `delta<0.21/k`, `E[a^2]<1.533 delta^2`, or regularity for the audited
   research-side nonlinear renewal-min system of selected critical or
   normalized-slack-vanishing densities. The induced
   annealed code and its exact limitations are in
   `docs/notes/annealed-critical-coding.md`. Do not promote either the fitted
   terminal constants (`K` rises throughout `k=12,...,19`; consult
   `docs/notes/terminal-defect-statistics.md`) or the geometric martingale and
   entropy constants: the audited annealed-floor
   argument refutes both as endpoint laws in `1<lambda_k<=2`. The scalar
   slack/terminal endpoint bridge and full weighted Pearson chain are
   kernel-checked in `9cdcfaf`/`764b815`; `f0e96a5` checks trace and the
   explicit endpoint vectors/floor, while `2bdb286` closes Perron uniqueness
   and endpoint identification.
   Feasibility-only entropy monotonicity is also refuted, so
   any weaker entropy endpoint needs an explicit selection hypothesis. The expanding-window cone with
   terminal-offset defect/immigration decay is the fallback and is described in
   `docs/notes/multiscale-genealogy.md`. Kernel/adversarial review of the repaired
   arctic proof is the bounded side target; mixed-radix has three named gaps.
   Do not
   revive the retracted AC resolvent or first-circle zeta boundary. If you advance
   it, update README (living map) + commit + push, and tell the Lean side via
   `docs/FOR_CLEAN_LEAN.md` if it affects a formalization target.

Welcome. Keep it honest; the failure ledger is as valuable as the theorems.
This handoff is a living successor record, updated through 2026-07-21.
