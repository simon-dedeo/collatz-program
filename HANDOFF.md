# HANDOFF — taking over the Collatz program

You (a Codex/GPT instance) are taking over as **research driver** of this
program from the previous driver (Fable, a Claude instance). This file is the
first thing to read. It is written for a *different* agent system, so it is
explicit about things a same-model continuation could assume.

## 0. The one-paragraph situation

This repo is an ad-hoc, honest attempt at progress on the Collatz conjecture.
The concrete achievement is a **certified improvement of a 23-year-old record**
(π_a(x) ≥ x^0.9033, exact-arithmetic certificates, `experiments/kl/`). Around
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

- **Certified:** π_a(x) ≥ x^γ for all γ < 0.9032885984 (a ≢ 0 mod 3). k≤14
  chain externally reviewed; k≤18 certified. `experiments/kl/RESULT.md`.
- **Proved structure theorems:** KL method = adversarial min-plus transfer
  operator on ℤ₃ (base ×4 = 3-adic odometer); Diaconis–Fulman carries spectrum
  (their open question); Antihydra population-rarity; local renormalization at
  −1 (a=λ^{1−α}); bi-(2,3)-Mahler exclusion; tree-product Collapse Lemma;
  solenoid Traceless Theorem. All in `docs/notes/`, most with exact
  verification.
- **Closed lanes (do NOT retry — see README failure ledger for reasons):**
  λ_∞=2 via any autonomous projective-contraction certificate (structural
  no-go, all J); cycle exclusion via finite places (collapses to Baker);
  regular divergence certificates (exhausted ≤8 states base 2, ≤5 base 3);
  spectral-gap descent; tropical-geometry-proper; Bourgain–Kontorovich; the
  solenoid→hidden-RH hope.
- **LIVE bets (ranked in README) — your forward agenda:** (1) analytic-
  combinatorics reframing of the counting side (γ_k = dominant pole of an
  explicit multitype Dirichlet GF; λ_∞=2 = confluence of singularities; the
  cleanest next step is writing M(s) explicitly and connecting to BRW
  derivative-martingale theory); (2) the unsigned solenoid zeta's natural
  boundary at |u|=1/4 / Pólya–Carlson dichotomy (connects Bell–Lagarias — two
  independent threads meeting); (3) mixed-radix anti-concentration — flattening
  is numerically TRUE at k≈3 log p and reduces exactly to a conditioned
  two-multiplier Chung–Diaconis–Graham walk (publishable framing); the one hard
  open piece is a rank-two matrix-product contraction (Prop P) no cited theorem
  supplies; (4) arctic no-go — Theorem B proved, Theorem A provable-looking;
  essentially done (closes the YAH problem for arctic); (5) adelic descent /
  quantum-channel reframing (the no-go = the KL channel's peripheral spectrum).
- **All background lanes were STOPPED at handoff** (killed mid-flight by user
  request). Partial state is recorded in each note; nothing is silently lost:
  - `docs/notes/mixed-radix-flattening.md` — COMPLETE (numerical-evidence +
    proof-program; 3 open gaps).
  - `docs/notes/arctic-nogo.md` — COMPLETE (Theorem B proved).
  - `docs/notes/modular-knots.md` — PARTIAL (linear Rademacher invariant
    collapses to Baker, confirmed; quadratic linking invariant shows nonzero
    separation but analysis UNFINISHED — resume from `experiments/modknots/`).
  - critical-drift scout — produced nothing before it was stopped (no artifacts).
  - ganesha family-census sweep — grid2 pass done (`results/`), critical-line +
    grid3 passes NOT finished (optional side-thread; low value — grid2 gives the
    main phase-diagram picture).

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
the terminal-potential/Chernoff chain, and the pressure rows — these are
*conditional consumers* of a localization certificate we proved doesn't exist
in the autonomous class, so they stand unused on that path but are correct.

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
5. Pick the top LIVE bet you can advance (the AC reframing and the natural-
   boundary lead are the two freshest; arctic is nearly closeable; mixed-radix
   is a real research program with one hard named gap). If you close or advance
   it, update README (living map) + commit + push, and tell the Lean side via
   `docs/FOR_CLEAN_LEAN.md` if it affects a formalization target.

Welcome. Keep it honest; the failure ledger is as valuable as the theorems.
This handoff is FINAL as of 2026-07-20 — the record is settled, not mid-flight.
