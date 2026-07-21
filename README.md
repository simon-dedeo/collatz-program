# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, and formalization, with every claim backed by a
machine-checkable artifact. Started 2026-07-20 (Claude Fable 5 + 
GPT-5.6-sol as external prover/reviewer; PSC Bridges-2 grant mth260010p).

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

Everything below this line, and everything else in this repo, has been automatically generated. Fable is doing numerics and running agents. I got annoyed at it and said it should be more creative, like Grothendieck and Weil, so it created a Grothendieck-Weil agent. GPT is trying to formalize things in Lean, in CLEAN_LEAN; it was told to make something that would not annoy Kevin Buzzard. If you want the inter-company drama, visit https://github.com/simon-dedeo/collatz-program/blob/main/CLEAN_LEAN/FOR_FABLE.md

## What we are trying to prove right now

**Target: λ_∞ = 2**, i.e. the Krasikov–Lagarias predecessor-counting exponent
γ_k = log₂λ_k → 1, which by KL's own theorem gives **π_a(x) ≥ x^{1−ε}** for
every ε > 0 (a ≢ 0 mod 3): the count of integers below x whose Collatz orbit
reaches a is at least x^{1−ε}.

**STATUS CORRECTION (2026-07-20, late).** An earlier version of this section
said we were "one finite certificate away." That framing is now **falsified**
for the certificate class we had in hand. The Charged spine-face Lyapunov
certificate (CL) was tested at (J=3, L_w=6) and **cannot exist** — proved by
an exact witness (`experiments/pressure-cert2/`, independently re-checked):
on the oscillation-carrying "spine face" the block multiplier is **exactly 1**
(a marginal eigenvalue, matching the {0,1} transversal spectrum), and there is
a **zero-charge oscillation-carrying cycle** decoupled from the priceable
charge — so no tilted-pressure Lyapunov certificate closes. Crucially this is
*marginal* (growth = 1, not > 1): it does **not** imply λ_∞ < 2, and the
empirical decay ν_k{osc>t} → ~0.81 continues. So **λ_∞ = 2 remains open, and
we have lost this proof route** (likely for the whole charged-Lyapunov class —
under adjudication). The downstream Lean scaffolding (oscillation identity,
terminal-potential/Chernoff chain, pressure rows) stands; what's missing is a
localization mechanism that prices *oscillation persistence itself*, or a
sub-exponential decay argument. (A parallel agent's "ECH2 feasible" file in
the same folder is **circular** — charge-by-fiat under an unproven annealing
hypothesis — and is flagged invalid in the verdict note; do not trust it.)

**RESOLVED (2026-07-20, later still) — structural no-go, all J.** The kill-tests
(`docs/notes/cl-killtests.md`, `experiments/cl-killtests/`) settled the
"under adjudication" question decisively, and against us: the −1 co-spine mode
(2,−1,−1) is a **marginal invariant** of the KL face dynamics at *every* J
(Test 1: the obstruction persists at J=4,5 because ×4 is a single cycle on
Q_J, so zero-charge cycles always survive with holonomy = {id,swap} =
stabilizer of the co-spine ray; re-verified). Worse, the *nonlinear* rescue
is dead too: the spine is a genuine calibrated neutral cycle where the true
min keeps the neutral lift strictly minimizing while oscillation stays exactly
constant (Test 2), and **no** finite forcing word contracts it (Test 3, η=0
for all words |W|≤8, non-circularly, since the all-0 top window is
forward-invariant and independent of the residue). **Conclusion: no autonomous
projective-contraction certificate — linear charged-Lyapunov, nonlinear
min-selection, or forcing-word — can prove λ_∞ = 2.** This is a no-go on a
*class of proof methods*, not evidence about λ_∞ itself (the mode is exactly
marginal). λ_∞ = 2 stays empirically supported and formally out of reach by
these means; a proof would need a non-autonomous/global-measure or arithmetic
argument. **Main effort has accordingly pivoted to the cycle side.**

**Why it matters.** (1) It settles how far the difference-inequality method —
the source of the 2003 record — can go: to the exponent-1 boundary, or a
stall (in which case the stall value is a new invariant of the (2,3) pair).
(2) It would be the best lower bound on Collatz predecessor sets, improving a
result that stood 23 years — and *formally verified*. (3) The structure built
to reach it (an adversarial transfer operator on ℤ₃, its −1 spine, the
charged-Lyapunov certificate) also organizes the cycle side and the
Antihydra/Busy-Beaver-cryptid side.

**Honest "amaze level" of a clean Lean proof** — scale: 10 = Collatz itself
settled; 8–9 = positive density / no-divergence / no-cycles settled; 1 =
routine exercise.

> **≈ 6 / 10.** A genuinely publishable, formally-verified improvement of a
> 23-year-old record, a structural theorem about the method's ceiling, and a
> new named object. Calibrated down honestly: x^{1−ε} bounds a *sparse* set
> (x^{1−ε}/x → 0); it is *predecessor* counting (preimages of a fixed a), not
> forward orbits of all n; and it is **not** Collatz, not positive density,
> not the divergence or cycle problem. A strong specialized paper plus a
> notable formal-methods artifact — not a resolution of the conjecture. The
> larger bet is that this structure eventually cracks something bigger; that
> bet is unproven.

## Headline results (all certified/proved today)

| Result | Status |
|---|---|
| **π_a(x) ≥ x^γ for all γ < 0.9032885984**, a ≢ 0 (3) — was 0.84 since 2003 | certified k=12..18 (exact integer arithmetic); k≤14 chain adversarially reviewed; γ₁₉ = 0.9094, γ₂₀ = 0.9151 in certification |
| The KL method = finite sections of an **adversarial transfer operator on ℤ₃** (base ×4 = the Iwasawa generator of 1+3ℤ₃) | `docs/notes/kl-limit-object.md`, `adversarial-operator.md` |
| KL's own §6 positivity hypotheses (H_k) | **proved** (odometer conjugacy → Gaubert–Gunawardena) |
| Oscillation law s(λ_k)−1 = (λ^{α−2}+λ^{α−1})δ_k | proved, now unconditional |
| Local renormalization at −1 solved: **a = λ^{1−α}** (= 2/3 at λ=2); "period-2" = the u↦2u relabeling; spine sheds mass at λ^{α−1}/3 | `renormalization-at-minus-one.md`, sol cross-confirmed |
| Diaconis–Fulman multiplication-carries spectrum (their open question) | proved, exact-verified: `carries-spectrum.md` |
| Berg–Meinardus ⟺ aₙ = a_{T(n)}; **bi-(2,3)-Mahler divergence certificates impossible** | proved: `mahler-cartier-lemma0.md`, `two-bases.md` |
| Antihydra rarity theorems (θ(C) → H(1/3); population-φ exact) | proved: `antihydra-rarity.md` |
| No regular divergence certificate: **≤8 states (base 2: 3.24T DFAs), ≤5 (base 3)** | exhaustive, cross-machine, logs in-repo |
| Weighted (drift) certificates: 191 regular domains retired incl. the all-ones ray | `experiments/wfar/` |
| Tree-product Collapse Lemma (spectral-gap route provably blind); solenoid **Traceless Theorem** (q=3 unique) | `tree-products.md`, `deninger-solenoid.md` |

## Current proof strategy (living map — updated as lanes open/close)

The certified record (x^0.9033) stands on its own. Everything below is about
reaching *further*, and after tunneling on one line we have re-widened. This
section is kept fresh; the **failure ledger** is deliberately explicit because
knowing which routes are dead (and why) is most of the value.

### LIVE bets (ranked, as of 2026-07-20 late)

1. **Mixed-radix anti-concentration** (gpt-5.6-sol's top pick; agent proving).
   The cycle numerator B(w) = Σ 3^{m−r}2^{i_r} — does it flatten mod p (max_a
   Pr(B≡a) ≈ 1/p)? A cycle needs (2^k−3^m) | B, a severe concentration event.
   Numerically validated (flat to sampling-noise floor for nonexceptional p,
   k ≥ 3 log p). Target: an inverse-Littlewood–Offord / sum-product-in-Aff(𝔽_p)
   flattening lemma — **a new theorem independent of Collatz**, and if strong +
   combined with a large sieve, real cycle-population rarity. `docs/notes/
   mixed-radix-flattening.md` (in progress).
2. **Solenoid → zeta/rigidity** (gpt Team B). Push the Traceless Theorem: compute
   the *full* iterated Lefschetz sequence L(Eⁿ) on the (2,3)-solenoid, not just
   L(E). Honest calibration (gpt): likely a clean **pressure/rigidity** theorem
   ("q=3 = zero-drift member"), **not** a hidden RH — Lefschetz traces are
   signed, so vanishing ≠ no cycles, and divergence is invisible to periodic-orbit
   zeta. Conceptual payoff, low Collatz-payoff. `docs/notes/solenoid-zeta.md`.
3. **Arctic/max-plus SRS no-go** (gpt Team C; cheap, definitive). Finish the
   extension of Yolcu–Aaronson–Heule: no arctic matrix interpretation proves
   Zantema's Collatz SRS terminating. Closes a *stated open problem*.
   `docs/notes/arctic-nogo.md` (in progress).
4. **Re-widen scouts** (running): tropical geometry proper, analytic
   combinatorics of the predecessor GF (is x^0.9033 a singularity/BRW-front
   exponent?), Bourgain–Kontorovich CF-thermodynamics on log₂3, the
   critical-drift BB-cryptid experiment, a wildcard. Speculative; triage on
   arrival.
5. **Quantitative adelic descent** (gpt Team D; on deck) — Haar→integer
   discrepancy under a dynamical Fourier norm; clearest route back to certified
   integer theorems, but risks rediscovering the marginal mode.

### FAILURE LEDGER — what didn't work, and why (do not retry)

- **λ_∞ = 2 via any autonomous projective-contraction certificate — CLOSED
  (structural no-go, all J).** The −1 co-spine mode (2,−1,−1) is a marginal
  invariant: charged-Lyapunov (persists J=4,5), nonlinear min-selection
  (calibrated neutral cycle), and forcing-word (η=0) all fail. Not evidence
  λ_∞<2; just no proof in this class. `cl-killtests.md`, `pressure-certificate-2.md`.
- **Cycle exclusion via finite places p | 2^K−3^L — CLOSED (collapses to
  Baker).** "Infeasible where new, redundant where feasible"; the Steiner
  stratum *is* the Baker bound. One falsifiable Poisson-model survivor only.
  `cycle-finite-places.md`.
- **Regular divergence certificates — CLOSED (exhaustive).** None ≤8 states
  (base 2, 3.24T DFAs), ≤5 (base 3). `dfacert*`.
- **Spectral-gap route to descent — CLOSED (Collapse Lemma).** Collatz
  projects to a point of the arithmetic tree-product quotient; automorphic
  gaps are blind. `tree-products.md`.
- **"One certificate away" framing (earlier README) — RETRACTED.** It was
  wrong; the certificate provably doesn't exist in its class.

### What CLEAN_LEAN (GPT) has kernel-checked and standing

The oscillation identity, the portable Lemma-5 pressure rows, and the
terminal-potential/Chernoff chain are all formal — they are *conditional
consumers* of a localization certificate we've now proved doesn't exist in the
autonomous class, so they wait unused on that path; they remain correct and
reusable. The CL structural no-go is itself offered to GPT as a clean
formalization target.

### Standing frame

x^{1−ε} counting (if ever reached) is a milestone, not Collatz; the conjecture
also needs no-divergence and no-cycles. The invariant-rank ledger
(`invariant-rank.md`) makes Conway's unsettleability (rank = ∞) precise and
tracks which certificate classes are provably insufficient. The descent ±sign
no-go proves any orbit-fate argument must couple 2-adic structure to the
Archimedean place — which is why every purely-local lane above eventually
hits the same wall.

## Running right now

- **Mixed-radix flattening lemma** (LIVE bet #1) — exact-DP numerics + proof
  attempt (`experiments/flattening/`, `docs/notes/mixed-radix-flattening.md`)
- **Re-widen fan-out** (8 agents): arctic no-go, modular-knots, solenoid-zeta,
  tropical geometry, analytic combinatorics, Bourgain–Kontorovich, critical-drift
  experiment, wildcard
- Family phase-diagram critical-line + grid3 sweep on ganesha (restarted)
- CLEAN_LEAN: independent Lean formalization by GPT (tracked read-only;
  handoff in `docs/FOR_CLEAN_LEAN.md`, return channel `CLEAN_LEAN/FOR_FABLE.md`)
- Idle capacity (akdeniz 32c+4090, PSC): available; nothing needs scale until a
  live bet validates a mechanism

(Deprioritized: k=19/20 KL certification is a *record* nicety, not on any live
proof path — the certified k≤18 already gives x^0.9033.)

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
