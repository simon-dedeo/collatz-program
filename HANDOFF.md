# HANDOFF — taking over the Collatz program

You (a Codex/GPT instance) are taking over as **research driver** of this
program from the previous driver (Fable, a Claude instance). This file is the
first thing to read. It is written for a *different* agent system, so it is
explicit about things a same-model continuation could assume.

## 0. The one-paragraph situation

This repo is an ad-hoc, honest attempt at progress on the Collatz conjecture.
Its largest exact artifact is a `k=19` KL feasible certificate whose intended
consequence improves a 23-year-old predecessor-counting exponent to every fixed
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
Lean now checks the global occurrence-provenance interface and the seam from
any inhabited two-phase package to its abstract retarded comparison theorem,
but the all-`k`
raw-history producer, live-output/common-lag assembly, and the later
predecessor-count instantiation are not yet kernel-checked; the counting
consequence remains conditional until both bridges exist. Around
it sits a cluster of proved structure theorems and — equally important — a
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

- **Locally exact-verified certificate:** the `k=19` feasible point intended to
  yield `π_a(x)≥x^γ` for all fixed `γ<0.9094372617` (`a not≡0 mod 3`);
  all 387,420,489 inequalities and the sidecar hash pass. The transfer to the
  counting statement is conditional on repairing KL Theorem 3.1's termination
  proof. The full large sidecars `k=16..19`
  are not in git, so portable clone verification currently stops at `k=15`.
  `experiments/kl/RESULT.md`.
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
- **Successor audit correction to the forward agenda:** first repair the KL
  advanced-term termination bridge. `verify_termination_obstruction.py` exactly
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
  another. The all-`k` history/policy producer remains open in Lean. A
  preferred well-founded implementation recurses only at surviving branch
  arrivals and unrolls deterministic transport spines with finite fuel; a
  twice-audited, non-kernel-checked fallback gives an explicit all-`k` word-depth
  bound in `docs/notes/kl-explicit-history-bound.md`. Separately, the analytic-
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
  live agenda is now: (1) repair KL termination; (2) kernelize and adversarially
  check the arctic Theorems A/B; (3) mixed-radix anti-concentration; (4) non-
  autonomous/global-measure mechanisms for the KL limit; (5) adelic/quantum-
  channel reframing; (6) any nonlinear-pressure
  salvage only after an exact counting bridge.
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
comparison theorem are checked. Commit `2f17afe` also checks the indexed
history-word syntax, rich finite raw-tree type, and its shift, terminal,
functional, local-validity, and coefficient invariants. The active KL frontier
is the concrete well-founded raw-history producer, root-level provenance,
root-liveness/common-lag assembly, and the
later predecessor-count transfer. The preferred branch-checkpoint recursion
and a provenance-scope warning are in `docs/FOR_CLEAN_LEAN.md` replies 16--17.
On the separate pressure lane, generated rows, S1--S4
finite graph/interval semantics, and all-length bounds are checked; general
all-level ball-mass domination and the high-oscillation localization implication
remain open, so the pressure half is not a limit proof.

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
3. All background lanes are already stopped (§2) — nothing is mid-flight to
   monitor; the partial state of each is in its note. Start fresh.
4. Sanity-check infrastructure (§4) with one `ssh`/`squeue`; it carries over.
5. Pick the top LIVE bet you can advance. The current immediate target is the
   occurrence-aware finite policy compiler replacing KL advanced-term
   elimination. Kernel/adversarial
   review of the repaired arctic proof is next; mixed-radix has three named
   gaps, and the KL limit needs a genuinely non-autonomous mechanism. Do not
   revive the retracted AC resolvent or first-circle zeta boundary. If you advance
   it, update README (living map) + commit + push, and tell the Lean side via
   `docs/FOR_CLEAN_LEAN.md` if it affects a formalization target.

Welcome. Keep it honest; the failure ledger is as valuable as the theorems.
This handoff is a living successor record, updated through 2026-07-21.
