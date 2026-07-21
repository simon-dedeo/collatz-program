# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, and formalization, with every claim backed by a
machine-checkable artifact. Started 2026-07-20 (Simon DeDeo + Claude Fable 5
+ GPT-5.6-sol as external prover/reviewer; PSC Bridges-2 grant mth260010p).

Made possible by the support of Grant 63750, "Explaining Universal Truths",
from the John Templeton Foundation. Additional support from research funds
of the Laboratory for Social Minds and from the Survival and Flourishing
Fund. Proofs and Reasons — https://proofsandreasons.io

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
| No regular divergence certificate: ≤7 states (base 2, q=8 finishing), ≤5 (base 3) | exhaustive, cross-machine, logs in-repo |
| Weighted (drift) certificates: 191 regular domains retired incl. the all-ones ray | `experiments/wfar/` |
| Tree-product Collapse Lemma (spectral-gap route provably blind); solenoid **Traceless Theorem** (q=3 unique) | `tree-products.md`, `deninger-solenoid.md` |

## Current proof strategy

**Counting half (the active critical path).** The chain, each link proved
except the last:

> pressure certificate (Lemmas 3+5 of `sol-pressure.md`)
> ⟹ C1′ (eigenvector mass of the high-oscillation set → 0)
> ⟹ δ_k → 0 ⟹ λ_∞ = 2 ⟹ **π_a(x) ≥ x^{1−ε}** (KL's own theorem).

The obstruction set is fully identified: a thin 3-adic neighborhood of the
backward ⟨4⟩-orbit of −1 (the shadow of the negative Collatz cycle; the
unique fixed point of the advanced branch). Its local theory is solved
(a = λ^{1−α}); its bare mass multiplier is λ^{α−1}/3 ≈ 0.48 (subcritical).

**Status of the two remaining lemmas** (`experiments/pressure-cert/`):
**Lemma 5 (the pressure gap — the piece all reviewers called the genuine
open step) is CERTIFIED** in exact rational arithmetic, at λ = 2 and
uniformly over [λ₁₈, 2], with a structural theorem (ρ(W_J) = s(λ) at every
depth; the spine's tilt budget halves per digit) showing it is
asymptotically free. **Lemma 3 (localization) fails in single-profile form
for an exactly-identified reason**: label-alignment lives in top-window
u-classes (base-4 transport overflows) invisible to mod-3^J states, and the
aligned class contains precisely the −1 spine. The repair — a combined
(mod 3^J) × (u-class) automaton with a spine-face cone / pathwise charge
lemma — is designed, costed, and running (`experiments/pressure-cert2/`).
Nothing in the current results estimates λ_∞ < 2; the empirical spine mass
tracks the certified bound from below with shrinking increments.

**Cycle half.** Cycles = monodromy identities in Aff(ℤ/(2^K−3^L));
four of five known cycles forced by the unit stratum |2^K−3^L| = 1.
Finding: the entire exclusion literature is archimedean-only — the sporadic
primes p | 2^K−3^L are untouched (`dynamical-hasse.md`). Empirics: typical-ξ
square-root cancellation; obstruction confined to 3-power major arcs
(`experiments/expsum/`, Tao's regime).

**Honest framing.** x^{1−ε} counting is a milestone, not Collatz. The full
conjecture also needs the divergence side (no orbit escapes) and the cycle
side closed. The invariant-rank ledger (`invariant-rank.md`) tracks what
certificate classes are provably insufficient (Conway's unsettleability =
rank ∞ conjecture, made precise). The descent ±sign no-go proves any orbit-
fate argument must couple 2-adic structure to the Archimedean place.

## Blockers (open mathematics, precisely stated)

1. **C1′ / Lemma 3 localization** — now the sole analytic blocker on the
   counting path (Lemma 5 is certified). Needs the combined-automaton
   contraction: block contraction off the aligned u-class plus a spine-face
   cone or pathwise charge argument on it. Prototype (J=3, L_w=6) running;
   scaled version (J=6, L_w=10, ~2.5×10⁸ states) costed for akdeniz/PSC.
2. **Boundary-data bound** — the co-spine pinning b = 2−a is a *global*
   selection fact (provably not local); both our note and CLEAN_LEAN's audit
   flag the same missing uniform bound on min-harmonic boundary data.
3. **Ratio-drift falsification test** — k=20 ν-tail ratio ≥ 0.816 would
   flip the "drift is transient" reading (pre-registered).
4. **Concrete oscillation identity in Lean** — conventions pinned in
   `docs/FOR_CLEAN_LEAN.md` §3.
5. Everything else in `docs/STRATEGY.md` §7 and the notes' honesty sections.

## Running right now

- `experiments/pressure-cert2/` — combined localization automaton, the
  critical path (Lemma 5 already certified in `pressure-cert/`)
- k=19, k=20 exact certifications (9.3 GB eigenvector via PSC DTN)
- Eigenvector geometry ρ₁₉ finish; k=20 pre-registered drift test on arrival
- Base-2 q=8 exhaustion on akdeniz (~3.20T of ~3.2T DFAs)
- Family phase-diagram critical-line sweep on ganesha
- CLEAN_LEAN: independent Lean formalization by GPT (tracked read-only;
  handoff of formats/statements in `docs/FOR_CLEAN_LEAN.md`)

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
gpu, fate · `formal/` Lean base (sorry-free) · `papers/` ~130 mirrored
references · `results/` data · `DATA.md` large-artifact pointers.
