# HANDOFF — taking over the Collatz program

You (a Codex/GPT instance) are taking over as **research driver** of this
program from the previous driver (Fable, a Claude instance). This file is the
first thing to read. It is written for a *different* agent system, so it is
explicit about things a same-model continuation could assume.

## 0. The one-paragraph situation

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
Polynomial energy/entropy control or direct selected-family compactness is now
the live localization target; the bin cones remain the fallback. Lean
formalization of the all-level projection/Perron implication has been requested.
Around this sits a cluster of proved structure theorems and — equally important — a
growing **failure ledger** of proof routes that are now provably dead. A
separate GPT instance runs an independent Lean formalization in `CLEAN_LEAN/`
(do not drive it; coordinate with it — see §5). Your job: drive the
math/experiment program, keep every claim honestly calibrated, keep the record
and the two collaboration channels current.

## 1. Read these, in this order

1. `README.md` — the **living map**: "What we are trying to prove right now,"
   Headline results, "Current proof strategy" (LIVE bets, ranked + the FAILURE
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
  A floating `k=20` audit provisionally exceeds every fitted exact-data margin but no
  qualitative cone or minimal start. The exact martingale audit adds 116
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
  The live theorem target is polynomial energy/entropy control consistent with
  the annealed floor, or direct compactness for a genuinely selected critical/aggregate-
  slack-vanishing family. The cone route remains a fallback, with rising `.05`
  immigration as its exposed negative signal. See
  `docs/notes/multiscale-genealogy.md`; do not call its aggregates lower-level
  KL vectors or extrapolate its finite trend.
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
  predecessor-count exponent wrapper is complete. `verify_termination_obstruction.py` exactly
  checks a legal positive-shift transport return that invalidates the paper's
  derivation of strict descent (3.2); it is not a repeatable lasso or a disproof of
  termination. `verify_all_three_deletion.py` exactly checks the independent
  nonempty-minimum failure at depth eleven. CLEAN_LEAN independently checks it
  and proves the abstract branch-arrival compactness theorem.
  `verify_split_invariant_counterexample.py` shows the existing (3.4)
  invariant is insufficient to justify the earlier backjump proposal after
  later splits. The primary replacement builds the universal record-admissible
  history forest, retains every complete add-only policy without a higher
  repeat, and compiles the finite menu into one outer minimum. Raw `phi`
  minimizers prove functional coverage; every lift dominates the coefficient
  fiber minimum. `verify_two_phase_small_levels.py` reproduces the published
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
  `verify_equation_2_1_obstruction.py`. Commit `58f0ef8` checks its exact
  targetwise `+1` replacement and ordinary-count transfer; `331ff48` then
  defines the statewise infimum and its P1/P2 API, and `729f5fa` proves its
  all-`k` D1--D3/base-system theorem. For arbitrary
  possible cycle targets, transfer through a sufficiently large nonperiodic
  `2^r a ≡ 2 (mod 3)` rather than assuming the known cycle is unique.
  `verify_predecessor_base_inequalities.py` independently checks the exact
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
  live agenda is now: (1) prove polynomial Pearson/entropy control consistent
  with the annealed floor, or direct selected-family compactness—or falsify that possibility—while
  retaining the expanding-window cone and direct cofinal
  feasibility as the fallback and scaling the completed `k=12` Lean import to
  higher records; (2) kernelize and adversarially check the arctic
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
  requests there. Writing back into it is authorized. (The name is legacy —
  "Fable" was the previous driver; treat it as "notes to/from the research
  driver.")
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
replacement is the exact finite Pearson calibration `chi<=6/j^2`, or a direct
compactness theorem; neither is proved all-level. Exact tightened feasibility
also refutes depth monotonicity on the full feasible cone. Any surviving
entropy theorem is selection-specific, and the pressure/KL bridge remains open.

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
   mechanism that supplies one. The current localization seam is
   polynomial Pearson/entropy control consistent with the annealed floor (the
   exact finite candidate is `chi<=6/j^2`) or direct relative compactness for selected
   critical or normalized-slack-vanishing densities. Do not promote the fitted
   geometric martingale or entropy constants: the audited annealed-floor
   argument refutes both as endpoint laws in `1<lambda_k<=2`, with Lean
   formalization pending. Feasibility-only entropy monotonicity is also refuted, so
   any weaker entropy endpoint needs an explicit selection hypothesis. The expanding-window cone with
   terminal-offset defect/immigration decay is the fallback. Both are described in
   `docs/notes/multiscale-genealogy.md`. Kernel/adversarial review of the repaired
   arctic proof is the bounded side target; mixed-radix has three named gaps.
   Do not
   revive the retracted AC resolvent or first-circle zeta boundary. If you advance
   it, update README (living map) + commit + push, and tell the Lean side via
   `docs/FOR_CLEAN_LEAN.md` if it affects a formalization target.

Welcome. Keep it honest; the failure ledger is as valuable as the theorems.
This handoff is a living successor record, updated through 2026-07-21.
