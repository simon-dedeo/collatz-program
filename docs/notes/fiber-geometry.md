# Fiber geometry of the KL extremal eigenvectors: measurements, one theorem, three conjectures

**v2 — corrected after external review (GPT), same night.** The original
Proposition R mixed Haar weighting with the eigenvector-mass weighting that
the oscillation law actually uses; the corrected reduction (§3) requires a
*pressure/mass* bound, not a dimension bound. Dimension language, the T2
hypothesis, the transport-suppression rate, and the nesting/persistence
distinction are also corrected below. New measurement M7 added: the corrected
(mass-weighted) diagnostics, which empirically still support λ_∞ = 2.

2026-07-20 (late). Data: certified eigenvectors k = 15..18
(`experiments/kl/cert_k*_C.npy`); scripts `scratchpad/fiber_geometry.py`,
`scratchpad/fiber_theorems.py`. Notation as in `kl-limit-object.md`:
level-k states are residues m ≡ 2 (mod 3) mod 3^k; the fiber of a level-(k−1)
state r is its three level-k refinements {r + j·3^{k−1}}; α = log₂3;
branch of a state = its residue mod 9 (2: retarded weight λ^{α−2};
8: advanced weight λ^{α−1}; 5: no branch); osc(fiber) = (max−min)/mean.

## 1. Measurements (k = 15..18)

M1 (tail mass). P(osc > t) decays geometrically in k at every threshold:
ratio ≈ 0.74–0.77 per level for t ∈ {0.2, 0.3}. Mean osc decays with ratio
0.910, 0.914, 0.916 (matching the γ-increment ratios via the exact
oscillation law of kl-limit-object.md, as it must).

M2 (genealogical coherence). The top-0.1% oscillating fibers at level k have
parents in the previous level's top-0.1% with probability 0.237, 0.249,
0.253 — a ~250× lift over base rate, rising. Note: this is coherence of
threshold sets of *different* eigenvectors across levels, not literal
nesting of cylinders; convergence to a closed subset of ℤ₃ is suggested,
not established.

M3 (finite-scale exponent — NOT yet a dimension). #{osc > 0.2} = 31703,
69337, 155338, 351539 at k = 15..18: cumulative exponent log₃(count)/(k−2)
= 0.726 (stable), but the more diagnostic consecutive slopes log₃ of the
count ratios are 0.712, 0.734, 0.743 — drifting upward. The tail-ratio
consistency (3^{d−1} ≈ measured 0.74–0.77) partly restates the same counts.
Whether the exponent converges below 1 is open.

M4 (localization). The maximal fiber at every level is exactly x = −1
(base-3 address all-2s), sup-osc = 0.594, 0.607, 0.614, 0.615. The top-30
list consists of 3-adic neighbors of −1 and of its backward ⟨4⟩-orbit
(−1/4 = (20)^∞, −1/16 = (2100)^∞ appear verbatim). Note −1 ≡ 8 (mod 9) and
R₈(−1) = (2(−1)−1)/3 = −1: **−1 is the fixed point of the advanced
refinement branch** — equivalently, the shadow of the negative fixed cycle
T̃(−1) = −1 of the accelerated Collatz map.

M5 (weighting). Eigenvector-mass-weighted mean oscillation exceeds the Haar
mean (0.0688 vs 0.0539 at k=18) — the eigenvector overweights the bad set —
but decays at the same geometric rate (ratios 0.919, 0.922, 0.924).

M6 (local renormalization at −1). The mean-normalized fiber profile of −1:
  k=15: (0.7010, 1.2953, 1.0036)   k=16: (1.3033, 0.6966, 1.0001)
  k=17: (0.6938, 1.3076, 0.9986)   k=18: (1.3077, 0.6927, 0.9996)
Convergence to a **period-2 cycle up to lift labeling**: profile →
(a, 2−a, 1) with a → 0.6925, the two non-(−1) lifts swapping each level,
−1 itself pinned at the mean. Caveat (external review): before treating this
as a dynamical 2-cycle, the lift-labeling action of the renormalization
across levels must be quotiented out — the invariant statement may be a
fixed unordered profile {a, 1, 2−a}; determining which is part of C2.
Hence sup-osc → 2(1−a) ≈ 0.615 (matches M4). The spike ratio
c(−1)/c(−4) = 194.8, 294.4, 438.4, 633.2 grows by ≈ λ^{α−1} ≈ 1.444 per
level: the advanced branch dominates transport at −1, with relative
suppression λ^{−2}/λ^{α−1} = λ^{−1−α} ≈ 0.20 per level (λ^{−2} ≈ 0.286
alone is the absolute transport weight).

M7 (corrected, mass-weighted diagnostics — the quantities the oscillation
law actually uses). With ν_k(r) = fiber-mean mass weights and
u_r = (mean−min)/mean: ν-weighted E[u] = 0.0407, 0.0375, 0.0347, 0.0321
(ratios 0.922, 0.924, 0.926); ν_k{o_r > 0.2} = 5.97e-2, 4.71e-2, 3.79e-2,
3.06e-2 (ratios 0.789, 0.805, 0.808); ν_k{o_r > 0.3} similar. The
eigenvector mass of the bad set vanishes empirically — faster than its Haar
measure — supporting λ_∞ = 2 through the corrected reduction below. The
upward ratio drift persists in these too.

## 2. Theorem (exact oscillation transport) — proved

**Theorem T2.** Let c be a positive exact eigenfunction of the level-k
KL operator (i.e. satisfying the eigen-equation with equality; certified
feasible points satisfy it only up to their slack, and the numerics below
reflect that margin). Let r ≡ 5 (mod 9) be a level-(k−1) state (k ≥ 4).
Then osc(fiber_k(r)) = osc(fiber_k(4r mod 3^{k−1})) exactly.

*Proof.* Children of r keep r's residue mod 9 (they differ by 3^{k−1}, k ≥ 4),
so each child m satisfies the branchless equation c(m) = λ^{−2} c(4m mod 3^k).
The map m ↦ 4m mod 3^k sends fiber_k(r) bijectively onto fiber_k(4r mod 3^{k−1})
preserving the lift index, since 4(r + j·3^{k−1}) = 4r + (3j + j)·3^{k−1}
≡ 4r + j·3^{k−1} (mod 3^k). Thus the fiber of r is the fiber of 4r scaled by
λ^{−2}, and osc is scale-invariant. ∎

(Verified on 10⁵ random fibers per level: value identity to 4×10⁻⁷ — the
λ_cert-vs-λ̂ margin — and osc equality to ≤ 4×10⁻⁴.)

Since x ↦ 4x cycles residues 5 → 2 → 8 → 5 (mod 9), every ⟨4⟩-orbit passes
through a pure-transport state every third step: oscillation is unchanged
through 5-branch states. (Whether 2-branch states can amplify normalized
oscillation is NOT settled by T2 — the min and the denominator interact;
that is part of Conjecture C3. The 8-branch, with weight > 1, is the natural
but unproven sole amplifier.)

## 3. The corrected reduction (v2 — after external review)

The oscillation law's δ_k is **eigenvector-mass weighted**: with
ν_k(r) = c̄_r/Σc̄_s and u_r = (c̄_r − min)/c̄_r, one has exactly
δ_k = (1/3)·Σ_r ν_k(r)·u_r. The original Proposition R bounded the *Haar*
mean of (max−min)/mean — the wrong measure and the wrong numerator. A set of
box dimension < 1 has vanishing Haar measure but can carry Θ(1) eigenvector
mass (in thermodynamic formalism a single periodic orbit can support the
maximizing measure), so dimension alone proves nothing here.

**Proposition R′ (corrected reduction).** If ν_k{r : o_r > t} → 0 for every
t > 0, then δ_k → 0; hence (under KL's hypotheses (H_k) along the tower)
λ_∞ = 2 and, conditional on the repaired KL Theorem 2.2/counting chain,
π_a(x) ≥ x^{1−ε}.

*Proof.* u_r ≤ min(o_r, 1), so δ_k ≤ (1/3)(t + ν_k{o_r > t}); let k → ∞,
then t → 0. The rest as before via the oscillation law and KL §6. ∎

**Conjecture C1′ (pressure/mass bound — the real open problem).** The
eigenvector mass of the high-oscillation set vanishes:
ν_k{o_r > t} → 0 for every t > 0. Equivalently (the theorem to aim for):
a restricted-pressure or Frostman-type inequality showing the
neighborhood of the backward ⟨4⟩-orbit of −1 carries eigenvector mass
→ 0 — the adversarial branch advantage at −1 is not worth enough pressure
to hold mass there. Empirical status: M7 (ratios ≈ 0.8/level, drifting up).

**Conjecture C1 (dimension bound — now auxiliary).** The finite-scale
exponent of {osc > t} stays bounded below 1. Insufficient for R′ by itself;
still the right combinatorial shadow, and an input a Frostman argument
would use.

## 4. The provable-looking local theory

**Conjecture C2 (renormalization at −1).** The mean-normalized fiber profile
of −1 converges to a period-2 cycle (a, 2−a, 1) ↔ (2−a, a, 1) with a the
solution of an explicit fixed-point equation for the telescoping local system
(structure: the level-k fiber of −1 references, through the min over lifts of
R₈(y_j) = −1 + 2j·3^{k−2}, the level-k fibers above the level-(k−1) fiber of
−1, plus ×4-transport terms from the fiber of −4 which are asymptotically
negligible by the measured λ^{−2}/λ^{α−1} ≈ 0.28 relative decay). In the
pure-branch limit at λ = 2 the system closes over 9 values; its fixed cycle
should give a in closed form (empirically a = 0.6925 ± 0.0003; candidate
closed forms to test: a = 2 − 2^{2−α} = 2 − 4/3 = 0.6667 ✗; a = 2(1 − 
2^{α−2})... to be determined by solving, not guessed).
Consequences if proved: sup-osc → 2(1−a) > 0 (the sup criterion is dead —
only measure-based criteria can decide λ_∞), and the local expansion of the
renormalization transversal to the −1 tower gives the local dimension of the
bad set — a first-principles derivation to test against d* ≈ 0.726.

**Conjecture C3 (contraction off the spine).** Through 2-branch and 5-branch
states, fiber oscillation does not grow (5: Theorem T2, exact; 2: the min
over lifts is 1-Lipschitz in each argument and the retarded weight
λ^{α−2} < 1 should give a strict average contraction); oscillation is
created only at 8-branch states, and persistent oscillation requires
asymptotically maximal 8-branch pull — confining the bad set to a
neighborhood of the grand backward orbit of the R₈-fixed point −1. C3 + a
counting argument for that orbit's neighborhood = the natural proof route
to C1.

## 5. Honest flags

- All measurements are k ≤ 18; the dimension estimate uses 4 levels.
- The oscillation-law route to λ_∞ = 2 needs KL's (H_k) hypotheses along the
  tower (verified numerically ≤ 12 by the limit-object note; unproved beyond).
- The decay-ratio drift (0.910 → 0.916, and 0.74 → 0.77 in tails) is real and
  unexplained; if the ratios drift to 1, C1 fails and λ_∞ < 2 — the data
  cannot yet exclude this. C2's local theory is the best tool to decide:
  the renormalization's transversal spectrum determines the drift.
