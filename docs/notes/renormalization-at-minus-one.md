# The local renormalization at −1: exact solution of the fiber law, the doubling relabeling, and the marginal transversal mode

2026-07-20 (later still). Resolves the solvable part of Conjecture C2 of
`fiber-geometry.md` (v2) and delimits exactly what is *not* locally solvable.
Data: exact certified feasible subeigenvectors `c≤F_λ(c)` at `k=15..19`
(`experiments/kl/cert_k{15..19}_C.npy`, exact integer vectors; λ the certified
rationals of `cert_k*_report.json`). They are near-critical approximants, not
exact critical eigenvectors.
Scripts: `experiments/kl/renorm_{common,extract,chains,window,annuli,limit_solve}.py`;
tables: `experiments/kl/renorm_{profiles,argmins,growth,chains,window,global,annuli,limit_table}.csv`.
Notation as in `kl-limit-object.md`: α = log₂3, level-k states [3^k] = {m mod 3^k :
m ≡ 2 (3)}, branch = residue mod 9, fiber of a level-(k−1) state r = {r + j·3^{k−1}}.

**Standing hypothesis (E).** c is a strictly positive *exact* eigenfunction of
the level-k operator, c = F_λ(c) (kl-limit-object.md §1.2), λ ∈ (1,2). The
certified vectors satisfy c ≤ F_λ(c) with relative slack ≤ 1.3×10⁻⁷ (and W₂,W₈
rational lower bounds for the weights), so every "exact" identity below is
verified on the data up to that margin; measured residuals are reported. All
k-asymptotics assume (H_k) along the tower, as elsewhere in this program.

Provenance: §§1–5 derived here and verified against the certified data; the
chain recursion (5) below was independently derived by the external model
gpt-5.6-sol from our brief (`renorm_sol_brief.txt`, reply
`renorm_sol_answer.md`), as were the two extremal constructions cited in
§6.3; sol's independent solution of the limit system agrees with ours on every
overlapping claim (min-constraint exact and unique; no pure-branch pinning;
transversal marginality). The heavy annulus/mass measurements were run by a
subagent (`renorm_annuli.py`); everything else run directly.

---

## 1. Exact local geometry at −1 (derived, not assumed)

Write −1 for the state 3^k − 1 ∈ [3^k]; −1 ≡ 8 (mod 9), and R₈(−1) =
(2(−1)−1)/3 = −1: −1 is the fixed point of the advanced branch.

**Lemma 1 (window geometry).** For 1 ≤ ν ≤ k−2 let B_ν := {−1 + u·3^{k−ν}
mod 3^k : u ∈ ℤ/3^ν} (the 3-adic ball of radius 3^{−(k−ν)} around −1 inside
[3^k]; B_ν ⊂ B_{ν+1}). Then:
(a) every x ∈ B_{k−2} satisfies x ≡ 8 (mod 9);
(b) for x = −1 + u·3^{k−ν} ∈ B_ν, R₈(x) = −1 + 2u·3^{k−ν−1} mod 3^{k−1},
and the three level-k lifts of R₈(x) are −1 + (2u + i·3^ν)·3^{k−ν−1}, i = 0,1,2
— elements of B_{ν+1};
(c) the transport reference 4x = −4 + 4u·3^{k−ν} lies in the corresponding
ball around −4, outside every B_μ (|−4−(−1)|₃ = 1/3).

*Proof.* (a) x ≡ −1 (mod 3^{k−ν}) and k−ν ≥ 2. (b) (2x−1)/3 =
(2u·3^{k−ν} − 3)/3; lifts add i·3^{k−1} = i·3^ν·3^{k−ν−1}. (c) immediate. ∎

**Offset coordinates.** Encode x = −1 + u·3^{k−ν} by q = u/3^ν in the Prüfer
group ℤ(3^∞) = ℤ[1/3]/ℤ (well-defined: (u, ν) and (3u, ν+1) give the same x).
Let ν(q) be the exact denominator exponent. By Lemma 1(b) the branch-min at q
is over the three solutions y of 3y = 2q — call them the **children** of q.
Every q has 0 as an iterated ancestor (the parent map q ↦ (3/2)q lowers ν(q) by
1), and **0 is its own child** (i = 0), the self-loop that anchors everything.
The fiber of the level-(k−1) state at offset q consists of the offsets
(q+i)/3, so **fibers = child-triples** (of q/2; ×2 is an automorphism).

The eigen-equation on the window, in these coordinates: with A := λ^{α−1} > 1,
t := λ^{−2}, and p(q) := c(−1 + q·3^k)/c(−1) (so p(0) = 1),

  (W)  p(q) = A · min{ p(y) : 3y = 2q } + t·c(4x_q)/c(−1),  q with ν(q) ≤ k−3.

## 2. Theorem 1: the exact fiber law at −1 and the closed form for a

Since R₈(−1) = −1 mod 3^{k−1}, the min in the eigen-equation *at* −1 is over
the fiber of −1 itself. This gives, with no approximation:

**Theorem 1 (fiber-min law).** Under (E), for every k ≥ 4:

  (I)  min_j c(−1 + j·3^{k−1}) / c(−1) = λ^{1−α} − λ^{−1−α} · c(−4)/c(−1).

In particular the min-normalized small lift is
a_k = λ^{1−α} − λ^{−1−α}/σ_k with σ_k := c(−1)/c(−4) the spike ratio, and
a_k → a* := **λ^{1−α}** whenever σ_k → ∞. At λ = 2, a* = 2^{1−α} = **2/3
exactly** (2^α = 3); at λ₁₈ = 1.8703245, a* = 0.693328.

*Proof.* The eigen-equation at m = −1 reads c(−1) = λ^{−2}c(−4) +
λ^{α−1}·min_j c(−1+j·3^{k−1}); solve for the min. ∎

**Verification** (renorm_limit_solve.py; full table renorm_limit_table.csv).
Residual of (I) on the certified vectors: ≤ 2.4×10⁻⁷ (= certificate slack,
correct sign). Both sides to 6 decimals:

| k | λ_k | RHS of (I) | measured min/c(−1) | a* = λ^{1−α} | mean-norm. a | c(−1)/mean |
|---|-----|-----------|--------------------|--------------|--------------|------------|
| 15 | 1.8419679 | 0.698494 | 0.698494 | 0.699552 | 0.701036 | 1.003640 |
| 16 | 1.8522343 | 0.696591 | 0.696591 | 0.697281 | 0.696643 | 1.000075 |
| 17 | 1.8616883 | 0.694750 | 0.694750 | 0.695208 | 0.693773 | 0.998593 |
| 18 | 1.8703245 | 0.693015 | 0.693015 | 0.693328 | 0.692709 | 0.999559 |
| 19 | 1.8783127 | 0.691395 | 0.691395 | 0.691602 | 0.689559 | 0.997344 |

The closed form matches the measured minimum to **six decimals** (it is an
identity); against C2's mean-normalized target a = 0.6925 ± 0.0003 it matches
through the third decimal, the residue being the pinning factor c(−1)/mean =
1 ± 0.004 (§5). Consequences: sup-osc of the −1 fiber = (max−min)/mean →
2(1−a*) if pinning holds (measured 0.594→0.624 vs predicted 0.601→0.617,
column suposc in the CSV); at λ = 2 the limit would be exactly 2/3.

## 3. Lemma 2: growth along the tower and transport suppression

**Lemma 2 (two-sided spike growth).** Under (E), for k ≥ 4:
(i) c(−1) ≥ λ^{(α−1)(k−2)} · min c;
(ii) c(−1) ≤ K(λ) · λ^{(α−1)(k−2)} · max c, with K(λ) = 1 + λ^{−2}/(1−λ^{1−α}).

*Proof.* Let m_ν := min_{B_ν} c, M_ν := max_{B_ν} c. Every x ∈ B_ν (ν ≤ k−3)
is 8-branch with children in B_{ν+1} (Lemma 1), so c(x) ≥ A·m_{ν+1} (transport
≥ 0), giving m_ν ≥ A·m_{ν+1}; iterate from ν = 0 ({−1}) to ν = k−2 and use
m_{k−2} ≥ min c. For (ii), c(x) ≤ t·max c + A·M_{ν+1} gives M_ν ≤
A^{k−2−ν}·max c + t·max c·Σ_{r≥0}A^{−r}·A^{k−2−ν}·… collapsing to (ii). ∎

So c(−1)/min c ≍ λ^{(α−1)k}: the dominant balance is the advanced branch, and
the per-level growth rate is **λ^{α−1}** (= 1.4423 at λ₁₈). Checks: measured
c(−1)/min c = 368.8, 553.7, 837.3, 1267.3, 1921.0 (k = 15..19), i.e. within
[bound, 3.7×bound] of (i) with stable ratio; growth ratios 1.501, 1.512,
1.514, 1.516. The spike σ_k = c(−1)/c(−4) = **194.8, 294.4, 438.4, 633.2**,
947.4 grows by 1.511, 1.489, 1.444, 1.496 per level — λ_k^{α−1} = 1.43–1.45
plus the λ_k-drift correction (λ_{k+1}/λ_k)^{(α−1)(k+1)} ≈ 1.05, which brackets
the measurements. (c(−4) tracks the global scale: σ_k ≈ 0.5·c(−1)/min c.)
The global maximum of c is itself in the window, at depth-4 offset
(orbit 58→35→70 under doubling), with max c = λ^{α−1}c(−1)(1 ± 0.005) — KL's
C^max_k is exactly the −1 spike.

**Corollary (transport suppression).** The relative transport at −1 is
t·c(−4)/c(−1) = λ^{−2}/σ_k: measured 1.51e−3, 9.90e−4, 6.58e−4, 4.52e−4,
2.99e−4 — per-level ratios 0.655, 0.665, 0.687, 0.662 ≈ **λ^{1−α} = 1/(spike
growth) ≈ 0.66–0.69 per level**. This corrects both earlier statements: the
v1 "0.28^k" and the review's "λ^{−1−α} ≈ 0.20 per level" — λ^{−1−α} is the
one-time weight ratio (transport weight λ^{−2} vs branch weight λ^{α−1});
the *rate* of relative suppression per level is λ^{1−α}. (0.67⁴ ≈ 0.20 over
four levels is the numerical coincidence that caused the conflation.)

Within one eigenvector, the same suppression appears per depth: along any
argmin chain x_0 = −1, x_{n+1} = argmin child, the eigen-equation gives the
exact recursion (in H_n := Aⁿ·c(x_n)/c(−1); derived independently by sol)

  (5)  H_{n+1} = H_n − t·Aⁿ·c(4x_n)/c(−1),

so H is constant along chains up to the accumulated transport forcing; the
measured H-drift per step equals the measured transport fraction to all
digits shown (renorm_chains.csv).

## 4. The closed limit system and its complete solution

**The system.** Dropping transport (Corollary above) and letting k → ∞ at
fixed λ, (W) becomes a min-plus eigenproblem on the Prüfer group:

  (P)  Π(q) = A · min{ Π(y) : 3y = 2q },  Π(0) = 1,  Π > 0,  q ∈ ℤ(3^∞).

This is the exact "pure-branch limit system" of C2. It closes over the value
towers {c(−1+u·3^{k−ν})}_k indexed by (which fiber, which lift) = the tree of
child-triples below the root; the finite-k fiber of −1 references, per C2's
structure, the fibers over the level-(k−1) fiber of −1 (children offsets
2j/3 → sibling fibers {2j+3i}/9) plus the ×4 transport to the −4 tower.

**Theorem 2 (solution of (P)).** Write Π(q) = A^{−ν(q)}·H(q). Then:
(a) (P) holds iff H(q) = min{H(y) : 3y = 2q} for all q ("min-harmonic on the
child tree") and H(0) = 1;
(b) every positive solution satisfies **min(Π(1/3), Π(2/3)) = A^{−1} =
λ^{1−α}** — the fiber of −1 has small lift exactly a* = λ^{1−α}, and this is
the ONLY constraint (P) places on the root fiber;
(c) the solution set is infinite-dimensional: for any C ≥ 1 there is a
solution with root profile (1, a*, b), b = A^{−1}C; in particular b is NOT
determined by (P). Existence: set H ≡ 1 on the subtree of one root child and
H ≡ C on the other, constant on each remaining subtree (min-harmonic by
construction).

*Proof.* (a) All three children of q ≠ 0 have depth ν(q)+1; substitute. At
q = 0 the self-loop gives 1 = A·min(1, Π(1/3), Π(2/3)) — since A > 1, the min
must be A^{−1} < 1, attained by a child of depth 1, i.e. (b). (c) The upward
constraints are exactly min-harmonicity; values off the argmin chains are
free above their parents' values. ∎

(b) is the theorem behind the empirical a: combined with Theorem 1 and
Lemma 2, **the small lift of the fiber of −1 converges to λ^{1−α}, = 2/3
exactly at λ = 2**, with finite-k correction −λ^{−1−α}/σ_k, verified to 1e−6.
The candidate closed forms floated in C2 (2 − 2^{2−α} etc.) are superseded:
the correct closed form is a = λ^{1−α}, whose numerical value at the
*certified finite-k* λ's (0.691–0.699) happens to sit near 0.6925, while its
λ→2 limit is 2/3 — the drift of a_k with k is real and tracks λ_k.

**The period-2 cycle is a relabeling, not a dynamical oscillation.**
R₈ doubles offsets (Lemma 1(b)): the level-k lift j of −1 min-references the
sibling fiber over offset 2j/3. Across levels the measured profiles satisfy

  p_{k+1}(u at depth ν) = p_k(2u mod 3^ν at depth ν) · (1 + O(0.005)),

verified for all offsets of depth ≤ 3 (≤ 4) for k = 15→16..18→19: mean
deviation 0.3–0.5% (max 1.2–2.3%), decreasing in k (renorm_extract.py §check).
The invariant object is a single function Π on ℤ(3^∞) modulo the ×2-action;
since ord(2 mod 3) = 2, the depth-1 shadow is the observed period-2 swap
(a, b) ↔ (b, a) with −1 fixed; at depth ν the labeled period is 2·3^{ν−1}
(verified at depth 2 through the 5 available levels). This answers the
review's point (2): the correct invariant statement is the unordered profile
{1, a, b} plus the exact doubling action on labels.

**Stability.** In log coordinates the cascade map T of (W) is
sup-norm-nonexpansive (a min of coordinate selections composed with the
common shift log A + transport); its linearization at any solution of (P) is
the argmin-selection operator: eigenvalue 0 in every direction that perturbs
only non-argmin children (strict margins: measured 0.44, 0.21, 0.06, 0.02,
0.05, 0.15, … along the spine — renorm_chains.csv), and eigenvalue exactly 1
along each chain-scale direction (one per chain family). So the labeled
2-cycle is stable but only *marginally* so in the co-spine direction; the
top-anchored (spine) components are asymptotically stable with the transport
lift: by (5), a perturbation of the spine scale is re-pinned to H = 1 at rate
1 − t/σ_k per level, while the co-spine scale C relaxes only through the
boundary. This is exactly the observed phenomenology: a_k converges cleanly
(identity-fast), b_k and the pinning factor wobble at ±0.4% with parity
structure and no monotone convergence through k = 19.

## 5. What is NOT determined locally: the pinning b = 2 − a

Empirically b_k ≈ 2 − a_k (equivalently c(−1) = fiber mean, "pinned at the
mean", profile (a, 2−a, 1)): measured b − (2−a) = −0.011, −0.000, +0.004,
+0.001, +0.008 (k = 15..19) — supported at the 1% level but with a
non-decaying parity wobble. Both our analysis and sol's independent solution
of (P) conclude: **no pure-branch mechanism forces b = 2 − a.** The co-spine
constant C = A·b is anchored at the deep boundary of the window (absolute
states: the co-spine chain passes through fixed absolute anchors, e.g. offset
54755·3^6, reached at every k ≥ 16 — renorm_chains.csv), i.e. inherited from
the global eigenvector; the transport feedback (the 2-branch states above
−1/4 reference the depth-2 ball of −1 with weight λ^{α−2}) selects C in the
full system but lies outside (P). Global mass balance (the oscillation law)
constrains only Σ_r min-fiber(r), not this fiber's mean. If pinning holds in
the limit, C → 2A − 1 (= 2 at λ = 2, profile (1, 2/3, 4/3)); measured
C_k = 1.845, 1.869, 1.884, 1.887, 1.904 vs 2A−1 = 1.859, 1.868, 1.877, 1.885,
1.892 — consistent to 1% but not settled. **Open**, and now precisely
located: pinning is a statement about the global selection of one
min-harmonic solution of (P), not about the local system.

## 6. Transversal analysis

### 6.1 Spectrum of the linearized renormalization

At the fixed structure of §4 the linearization of the cascade (log
coordinates) is the argmin-selection operator: **spectrum {0} ∪ {1}** — 0 on
all directions off the argmin chains, 1 (marginal) on the chain-scale
directions, one per chain family; there is no eigenvalue strictly between.
Strict argmin margins protect the selection pattern (top margins 0.44, 0.21,
0.06; but margins as small as 0.000–0.008 occur at steps ~10 deep —
renorm_chains.csv — so deep selections can switch between levels). Transport
lifts the marginal modes by O(t·Aⁿ·c(4x_n)/c(−1)) via (5). Consequently the
local theory has no autonomous transversal decay rate: transversal
observables converge only as fast as the boundary (global eigenvector)
converges, at the measured rates {λ^{1−α} ≈ 0.67 (transport), ≈ 0.93
(λ_k-drift/increment ratio)} per level.

### 6.2 What IS derivable: the mass profile around the spine

Since Π(q) ≍ A^{−ν(q)} (Theorem 2, H = O(1)), a fiber at 3-adic distance
3^{−j} from −1 has mean value ≍ c(−1)·A^{−(k−1−j)}·H, while the number of
such fibers is 2·3^{k−2−j}. Hence the eigenvector mass of the annulus
A_j = {r : |r−(−1)|₃ = 3^{−j}} decays, going inward (j → j+1), by

  **mass ratio per shell = λ^{α−1}/3**  (= 0.4808 at λ₁₈; = 1/2 exactly at λ = 2).

Measured (renorm_annuli.csv, k=18, j = 1..8): 0.516, 0.484, 0.475, 0.472,
0.466, 0.463, 0.460, 0.457 — matching to 1–5% with the residual drift
carrying the H-profile and boundary corrections. Total mass within distance
3^{−J} of −1 therefore vanishes like (λ^{α−1}/3)^J: **the spine itself
carries no Θ(1) eigenvector mass** — localization at −1 does not by itself
obstruct C1′ (mass of the bad set → 0). Mass enhancement over Haar per shell:
3·(λ^{α−1}/3) = λ^{α−1} ≈ 1.44/shell (measured 1.38–1.40).

### 6.3 Oscillation vs distance from the spine, and the local dimension

osc(fiber over q) equals the relative spread of H over the child-triple, so
the oscillation field is the H-spread field. Measured over the window shells
S_j (bases at distance 3^{−(k−1−j)}, j = 1 nearest — renorm_window.csv):
mean osc decays smoothly by ≈ 0.89/shell moving away from −1 (0.446, 0.277,
0.201, 0.174, 0.149, 0.139, 0.120, 0.108, 0.096 at k=18, j=1..9*, matching
the global per-level mean-osc ratio 0.91); the count of osc > 0.2 fibers
grows per shell by 2.0–2.2: local multiplier m = 2.12–2.15, **local dimension
log₃ m = 0.68–0.70** vs the global finite-scale exponent d* ≈ 0.726 (M3) —
the bad set near −1 reproduces the global exponent, consistent with C3's
picture that the global bad set is the closure of the spine's backward orbit
structure. (*shell 1 includes the base −1 itself.)

However — and this is the honest core of the transversal story — **the
multiplier is not derivable from (P)**: min-harmonicity permits both an
all-flat window (multiplier 0) and an all-oscillating window (multiplier 3,
dimension 1); constructions in renorm_sol_answer.md §Q2, matching our
boundary-inheritance analysis. The 2.1–2.2 is a property of the globally
selected solution. A proof of C1/C1′ therefore needs a *global* branching or
energy bound (e.g.: every high-osc fiber has ≤ B < 3 high-osc children up to
a geometric immigration term ⇒ dimension ≤ log₃ B), not a local RG argument.

### 6.4 Tail-ratio drift: transient or → 1?

The tracked k=19 point (`renorm_global.csv`) has
`ν_k{osc > 0.2}=2.4817e−2`; successive ratios through k19 are 0.789, 0.805,
0.808, 0.810. Haar count-fraction ratios are 0.729, 0.747, 0.754, 0.761
(counts 31703, 69337, 155338, 351539, 802383). We preregistered a k20
transient range `[0.810,0.813]` and a slow-decay discriminator `≥0.816`.
A full floating scan of the local, untracked 8.7-GiB k20 candidate instead
gave tail ratios about 0.824 at thresholds 0.2 and 0.3. Thus the preregistered
transient prediction failed. Absolute tail masses still decrease, so this one
floating point proves neither C1′ nor its failure; it removes the claimed
finite-data basis for a geometric limit near 0.81. The exact within-vector
multiscale genealogy audit is the next diagnostic.

## 7. Status of Conjecture C2, and honest gaps

Proved here (under (E), and (H_k) where k-limits are taken):
- Theorem 1: exact fiber-min law; a_k = λ^{1−α} − λ^{−1−α}/σ_k, exact.
- Lemma 2: two-sided spike growth at rate λ^{α−1} per level; transport
  suppression at rate λ^{1−α} per level (measured 0.66–0.69); checked against
  σ_k = 194.8 … 947.4.
- Theorem 2: complete solution of the pure-branch limit system (P): the small
  lift is a* = λ^{1−α} for EVERY positive solution (= 2/3 at λ = 2; 0.6933 at
  λ₁₈, matching the measured min-normalized 0.6930 and, through the pinning
  factor, the mean-normalized 0.6927); the rest of the profile is a free
  min-harmonic datum.
- The "period-2 cycle" is exactly the offset-doubling relabeling (order 2 at
  depth 1, 2·3^{ν−1} at depth ν); invariant object = Π mod ⟨×2⟩; verified at
  0.3–0.5% across k = 15..19.
- Transversal spectrum {0, 1}: marginal, no autonomous decay; mass law
  λ^{α−1}/3 per shell around the spine (verified 1–5%).

Not proved / corrected / open:
- **Pinning b = 2 − a is not a local theorem** (Theorem 2(c); sol concurs);
  measured to hold at ±1% with parity wobble. C2's "(a, 2−a, 1)" should be
  restated: min-lift = λ^{1−α} (proved-level), max-lift = boundary-selected,
  empirically ≈ 2 − a. Any proof must go through the global selection
  (transport feedback through the −1/4 tower; no standard vanishing-
  perturbation selection theorem applies as t = λ^{−2} does not vanish).
- The local dimension 0.68–0.70 (vs global 0.726) is measured, not derived;
  (P) alone permits [0, 1]. C1/C1′ need a global branching/energy estimate.
- σ_k → ∞ (spike divergence) is proved only relative to min c (Lemma 2(i));
  the step to c(−4) = O(global scale) is empirical (σ_k ≈ 0.5·c(−1)/min c).
- Certified vectors satisfy the equation with ≤ 1.3e−7 slack, not equality;
  all identities verified to that margin. (H_k) beyond k = 12 unproved.
- The relabeling covariance p_{k+1} = p_k∘(×2) + O(0.5%) is a measured
  regularity of the eigenvector tower, mechanism identified (chains anchored
  at absolute states; one cascade step inserted per level) but not proved.

## 8. Reproduction

- `python3 experiments/kl/renorm_extract.py` — profiles, argmins, growth
  (renorm_profiles/argmins/growth.csv; M6 check).
- `python3 experiments/kl/renorm_chains.py` — spine/co-spine chains, H,
  margins, transport fractions (renorm_chains.csv).
- `python3 experiments/kl/renorm_window.py` — window osc field, shell counts,
  identity residuals (renorm_window.csv).
- `python3 experiments/kl/renorm_annuli.py` — full-array global tails and
  annulus mass/osc, self-tested AP enumeration (renorm_global.csv,
  renorm_annuli.csv; reproduces M7 exactly; k = 19 new).
- `python3 experiments/kl/renorm_limit_solve.py` — sympy exact values, the
  verification table (renorm_limit_table.csv), mass-law and dimension checks.
- External consult: `experiments/kl/renorm_sol_brief.txt` and
  `experiments/kl/renorm_sol_answer.md`; all adopted claims re-verified
  against the certified data above.
