# Fiber geometry in KL finite feasible vectors: measurements, exact reductions, and open conjectures

**Current correction (2026-07-21).** The autonomous contraction conjecture C3
below is false. `CLEAN_LEAN/CleanLean/KL/Mixer.lean` gives an exact retarded-
branch counterexample: flat transport and individually flat referenced fibers
can have cross-fiber minima `(1,1,2)` and produce normalized oscillation `3/5`.
`MarginalObstruction.lean` separately checks the uncharged neutral co-spine
mode. Thus C1' is not equivalent to small mass near a backward orbit; that
would require a separate, time-aware localization theorem, and the full
backward `<4>` orbit modulo `3^J` is all states. The live replacement is a
non-autonomous mass genealogy (ultimately for a selected exact eigenvector) or
a direct primal feasible-sequence argument. A floating-only `k=20` scan still
has decreasing tails, but its
`0.2` and `0.3` tail ratios are about `0.824`, weakening the earlier
geometric-ratio extrapolation. Nothing here proves or disproves C1'.

**v2 — corrected after external review (GPT), same night.** The original
Proposition R mixed Haar weighting with the eigenvector-mass weighting that
the oscillation law actually uses; the corrected reduction (§3) requires a
*pressure/mass* bound, not a dimension bound. Dimension language, the T2
hypothesis, the transport-suppression rate, and the nesting/persistence
distinction are also corrected below. New measurement M7 added: the corrected
(mass-weighted) diagnostics. Their finite decrease is evidence to investigate,
not an asymptotic verdict.

2026-07-20 (late). Data: exact certified feasible subeigenvectors
`c≤F_λ(c)` at `k=15..18` (`experiments/kl/cert_k*_C.npy`), used as
near-critical numerical approximants rather than exact critical eigenvectors;
scripts `experiments/kl/osc_stats.py` and `experiments/kl/renorm_*.py`.
Notation as in `kl-limit-object.md`:
level-k states are residues m ≡ 2 (mod 3) mod 3^k; the fiber of a level-(k−1)
state r is its three level-k refinements {r + j·3^{k−1}}; α = log₂3;
branch of a state = its residue mod 9 (2: retarded weight λ^{α−2};
8: advanced weight λ^{α−1}; 5: no branch); osc(fiber) = (max−min)/mean.

## 1. Measurements (k = 15..18)

M1 (tail mass). Over `k=15..18`, P(osc > t) decreases with successive ratios
about 0.74–0.77 for t ∈ {0.2, 0.3}. Mean osc decreases with ratios 0.910,
0.914, 0.916. These short finite sequences do not establish geometric decay
or a nonzero asymptotic gap.

M2 (genealogical coherence). The top-0.1% oscillating fibers at level k have
parents in the previous level's top-0.1% with probability 0.237, 0.249,
0.253 — a ~250× lift over base rate, rising. Note: this is coherence of
threshold sets of *different feasible approximants* across levels, not literal
nesting of cylinders; convergence to a closed subset of ℤ₃ is suggested,
not established.

M3 (finite-scale exponent — NOT yet a dimension). #{osc > 0.2} = 31703,
69337, 155338, 351539 at k = 15..18: cumulative exponent log₃(count)/(k−2)
= 0.726 (stable), but the more diagnostic consecutive slopes log₃ of the
count ratios are 0.712, 0.734, 0.743 — drifting upward. The tail-ratio
consistency (3^{d−1} ≈ measured 0.74–0.77) partly restates the same counts.
Whether the exponent converges below 1 is open.

M4 (localization). The maximal fiber at every tested level is exactly x = −1
(base-3 address all-2s), sup-osc = 0.594, 0.607, 0.614, 0.615. The top-30
list consists of 3-adic neighbors of −1 and of its backward ⟨4⟩-orbit
(−1/4 = (20)^∞, −1/16 = (2100)^∞ appear verbatim). Note −1 ≡ 8 (mod 9) and
R₈(−1) = (2(−1)−1)/3 = −1: **−1 is the fixed point of the advanced
refinement branch** — equivalently, the shadow of the negative fixed cycle
T̃(−1) = −1 of the accelerated Collatz map.

M5 (weighting). Feasible-vector-mass-weighted mean oscillation exceeds the
Haar mean (0.0688 vs 0.0539 at k=18), so the tested vector overweights the bad
set. It decreases over the measured range with ratios 0.919, 0.922, 0.924;
this is not yet a geometric-decay theorem.

M6 (local renormalization at −1). The mean-normalized fiber profile of −1:
  k=15: (0.7010, 1.2953, 1.0036)   k=16: (1.3033, 0.6966, 1.0001)
  k=17: (0.6938, 1.3076, 0.9986)   k=18: (1.3077, 0.6927, 0.9996)
The later exact local calculation (`renormalization-at-minus-one.md`) shows
that the apparent period two is the depth-one doubling relabeling, not a
dynamical two-cycle. Under an exact eigenfunction premise the small lift obeys
`a_k = λ^(1−α) − λ^(−1−α)/σ_k`, where
`σ_k=c(−1)/c(−4)`; if `σ_k→∞` and `λ→2`, its min-normalized limit is exactly
`2/3`. The maximum lift and the empirical near-pinning `(a,2−a,1)` remain
globally selected, not consequences of the local equations. The spike ratio
c(−1)/c(−4) = 194.8, 294.4, 438.4, 633.2 grows by ≈ λ^{α−1} ≈ 1.444 per
level: the advanced branch dominates transport at −1, with relative
suppression λ^{−2}/λ^{α−1} = λ^{−1−α} ≈ 0.20 per level (λ^{−2} ≈ 0.286
alone is the absolute transport weight).

M7 (corrected, mass-weighted diagnostics — the quantities the oscillation
law actually uses). With ν_k(r) = fiber-mean mass weights and
u_r = (mean−min)/mean: ν-weighted E[u] = 0.0407, 0.0375, 0.0347, 0.0321
(ratios 0.922, 0.924, 0.926); ν_k{o_r > 0.2} = 5.97e-2, 4.71e-2, 3.79e-2,
3.06e-2 (ratios 0.789, 0.805, 0.808); ν_k{o_r > 0.3} similar. The tested
feasible-vector mass of the bad set decreases over this finite range. The
upward ratio drift persists, and the floating `k=20` point is slower still;
neither vanishing nor `λ_∞=2` follows from these measurements.

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
through 5-branch states. A 2-branch can amplify normalized oscillation:
`Mixer.retarded_mixer_counterexample` is an exact finite counterexample. The
8-branch is therefore not the sole possible amplifier.

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
λ_∞ = 2. The formerly conditional finite-feasibility-to-counting chain is
now kernel-checked generically, so a cofinal feasible sequence then gives
`π_a(x) ≥ x^{1−ε}` eventually for every fixed `ε>0` and admissible
target. Selecting the required exact critical eigenfunctions remains a
separate premise of this particular pressure route.

*Proof.* u_r ≤ min(o_r, 1), so δ_k ≤ (1/3)(t + ν_k{o_r > t}); let k → ∞,
then t → 0. The rest as before via the oscillation law and KL §6. ∎

**Conjecture C1′ (pressure/mass bound — the real open problem).** The
eigenvector mass of the high-oscillation set vanishes:
ν_k{o_r > t} → 0 for every t > 0. One possible route is a restricted-
pressure or Frostman-type inequality for a *depth-truncated, time-aware*
exceptional genealogy, together with a separately proved containment of the
high-oscillation set. This is not an equivalent reformulation: no such
localization theorem is known. Empirical status: the tails decrease through
the floating `k=20` candidate, but their ratios drift upward.

**Conjecture C1 (dimension bound — now auxiliary).** The finite-scale
exponent of {osc > t} stays bounded below 1. Insufficient for R′ by itself;
still the right combinatorial shadow, and an input a Frostman argument
would use.

## 4. Exact local law and the remaining selection problem

**C2, corrected.** For a positive exact eigenfunction, the local fiber-min law
is already exact:

`a_k = λ^(1−α) − λ^(−1−α)/σ_k`, with `σ_k=c(−1)/c(−4)`.

Thus `a_k→λ^(1−α)` if `σ_k→∞`, giving `2/3` at `λ=2`. The observed swap of
the two nonzero offsets is exactly multiplication by two modulo three. What
remains conjectural is global boundary selection: divergence of the relevant
spike ratio along an exact critical tower, pinning of the mean/max lift, and
control of the high-oscillation mass. The pure-branch local system has a
marginal family and cannot determine those data by itself.

**Conjecture C3 (contraction off the spine) — REFUTED.** The 5-branch
transport statement remains exact, but the claimed 2-branch nonexpansion is
false: coordinatewise minima taken from different referenced fibers can create
oscillation even when every individual input profile is flat. The exact
`Mixer.retarded_mixer_counterexample` produces oscillation `3/5`. Moreover,
the aligned co-spine has a neutral uncharged mode, so no policy/profile-uniform
autonomous contraction-or-charge theorem survives. Any replacement must use
global eigenvector selection, a non-autonomous mass genealogy with controlled
immigration, or a direct primal barrier.

## 5. Honest flags

- The tabulated measurements are `k≤18`; exact feasible records now reach
  `k=19`, and the additional `k=20` tail point is floating-only, sourced from
  a local untracked 8.7-GiB sidecar rather than a checked certificate. The
  dimension estimate still uses only four levels.
- The oscillation-law route to λ_∞ = 2 needs KL's (H_k) hypotheses along the
  tower (verified numerically ≤ 12 by the limit-object note; unproved beyond).
- The decay-ratio drift is real and unexplained. Ratios drifting toward one
  could signal subgeometric decay rather than failure of C1', so finite fits
  do not decide `λ_∞`. The exact neutral transversal mode explains why an
  autonomous geometric proof fails, but not what the global mass does.
