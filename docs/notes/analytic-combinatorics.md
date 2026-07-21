# Analytic combinatorics of the Collatz counting statistics: the KL exponent as a dominant singularity, and the BRW-front reading of λ∞→2

2026-07-20. Status: **scout report + reformulation proofs + one structural correction**.
Companion to `kl-limit-object.md` [LIM], `adversarial-operator.md`, and
`docs/smell/Branching-random-walks--additive-martingales.json` [BRW-smell].
Tags: [PROVED] proof/standard-cite; [PROVABLE] route clear; [SPEC] speculative;
[HEUR] a heuristic that AC *recovers but cannot prove* (the independence is the conjecture).

α := log₂3 = 1.5849625…; value(v) := log₂(v as integer); λ = 2^δ.

---

## 0. Summary

Flajolet–Sedgewick singularity analysis is essentially absent from the Collatz literature,
yet all three headline statistics — predecessor exponent, total-stopping mean, maximum
excursion — are *combinatorial parameters of trees/walks with a real-valued additive
weight*, hence live natively in the analytic-combinatorics (AC) frame. Findings:

1. **[PROVED, reformulation]** Our certified KL exponent γ_k *is* a singularity exponent:
   it is the **abscissa of convergence** of an explicit multitype Dirichlet generating
   function D(s) = (I − M(s))⁻¹𝟙 for the backward tree, equivalently the location of the
   **dominant singularity, which is a simple pole** of that resolvent. The Flajolet–Odlyzko
   transfer theorem then gives π_a(x) ~ C_k·x^{γ_k} **with no logarithmic factor** (the
   nonlattice condition log2/log3 ∉ ℚ), turning KL's difference-inequality exponent into a
   clean AC power law (§1). AC does **not** improve γ_k at fixed k — it is an exact
   reformulation; the improvement to 0.9033 came from more k, not from AC.
2. **[PROVED, reformulation]** The dichotomy λ∞ = 2 vs < 2 is a **confluence-of-singularities**
   statement: the quenched pole s = γ_k must migrate to the annealed pole s = 1 as k→∞
   (§2). The annealed pole sits at δ=1 for **all** k (the k-independent Perron root
   s(λ), [LIM] Lemma 1.3); the limit object is the resolvent of a transfer operator on
   C(ℤ₃), quenched = a *nonlinear* (min-type) resolvent.
3. **[PROVED, correction of BRW-smell]** γ_k is the **adversarial Biggins front / Legendre
   transform** (§4), and the annealed front is exactly the exponent-1 tilt. But the tilt
   δ=1 is a **transverse root** of the pressure (φ′(1) = 2·s′(2) ≈ −0.311 ≠ 0), i.e.
   *subcritical* — so the additive (Biggins) martingale is UI and the annealed count is a
   clean linear x with **no Seneta–Heyde / derivative-martingale polylog**. **Derivative
   martingales cannot move, and are not even relevant to, the predecessor exponent.** The
   genuine 0.9033→1 gap is a **quenched-vs-annealed (min-vs-mean) disorder** effect (a
   directed-polymer weak/strong-disorder question), not a front-correction effect. This
   downgrades the "hot-speculative" Seneta–Heyde hope in [BRW-smell].
4. **[PROVED for the walk model / HEUR for Collatz]** The forward mean-stopping constant
   6.952 and the maximum-excursion exponent 2 are recovered from the **same** two-step
   Syracuse walk {−1 w.p. ½, α−1 w.p. ½}: the mean is a LLN (1/|drift|), the excursion-2 is
   the **Lundberg root θ\* = 1** plus a record-over-N extreme-value count (§5). The forward
   Lundberg root θ\*=1 and the backward annealed pole δ=1 are the *same* "exponent-1"
   critical tilt — a single free-energy zero governs all three statistics (§5.3).
5. **[SPEC, data-backed — NEW 2026-07-20b]** The AC/BRW frame turns the open dichotomy into
   a **finite-size-scaling** question that the certified data can already be run against: the
   *rate* at which γ_k → γ_∞ is a cutoff diagnostic. A **spectral gap** (off-critical, λ∞<2)
   forces **exponential-in-k** convergence; a **critical/marginal** front (λ∞=2) forces the
   **algebraic Brunet–Derrida** law γ_∞−γ_k ≍ 1/(log N_k)² = 1/k² (N_k=3^{k−1}). Fitting the
   nine certified points k=11–19: geometric wins (γ_∞≈0.975–0.98, rms 1·10⁻⁴), the 1/k² form
   is **rejected** (30–200× worse), and the within-window signature is decisive — the
   increment ratios are **flat at ~0.92** (geometric) whereas a true 1/k² law would show them
   **rising 0.78→0.85** across this window. **Current evidence therefore points to λ∞ < 2, an
   intrinsic KL ceiling γ_∞ ≈ 0.975** (§8) — the first data-driven attack on [LIM] Problem 3.5.
   Caveat honestly flagged: a Brunet–Derrida crossover to critical scaling is notoriously
   delayed, so a clean geometric window can in principle be pre-asymptotic (§8.3).

---

## 1. The predecessor generating function and its dominant singularity [PROVED]

Fix precision k; work on the type set Y_k = {m≡2 (3) mod 3^k} of [LIM] §1. On the
backward tree rooted at a type m, each vertex carries value(v) = cumulative log₂-displacement
from the root, with edge displacements

  ×4 branch d = +2;  (4x−2)/3 branch d = 2−α;  (2x−1)/3 branch d = 1−α  (this one < 0).

Because value ranges over ℤ·log2 + ℤ·log3 (a dense, non-integer additive group), the correct
transform is a **Dirichlet series**, not an OGF/EGF in one integer variable. Put z = 2^{−s}
and define the vector GF

  **D_m(s) := Σ_{v in subtree of type m} 2^{−s·value(v)}.**

The tree recursion (a type-m root plus the subtrees of its deterministic children) gives the
linear functional equation

  **D(s) = 𝟙 + M(s)ᵀ D(s),  M(s)[m,m′] = Σ_{edges m→m′} 2^{−s·d}**,   ⇒  D(s) = (I − M(s)ᵀ)⁻¹𝟙.

M(s) is exactly the tilted matrix of [BRW-smell] and `kl_perron_solver.py` at δ = s:
entries λ^{−2}, λ^{α−2}, λ^{α−1} with λ = 2^s. Hence:

**Proposition 1.1 (γ_k is a singularity exponent).** The abscissa of convergence of D(s)
is s_c = γ_k, the unique s with ρ(M(s)) = 1; at s_c the resolvent (I − M(s))⁻¹ has a
**simple pole** (simple dominant Perron eigenvalue of the primitive core, [LIM] Lemma 1.3
bijections ⇒ primitivity on the coprime-to-3 core). *Proof.* ρ(M(s)) is continuous and
strictly decreasing in s (each entry 2^{−s·d} with the dominant mass on d>0 edges); the
Neumann series Σ M(s)ⁿ converges iff ρ<1 iff s>γ_k; Perron simplicity gives the simple
pole. ∎

**Corollary 1.2 (transfer theorem: no log correction).** For the mod-3^k approximant,
N_m(x) := #{v : value(v) ≤ log₂x} satisfies N_m(x) ~ C_k(m)·x^{γ_k}. The pole being simple
and the potential **nonlattice** (log2/log3 irrational ⇒ the displacement group is not
c·ℤ) rules out a lattice of poles on Re s = γ_k, hence **no oscillatory factor and no log
power**: a pure power law. [PROVED — this is the Flajolet–Odlyzko rational-singularity
transfer theorem, = Lalley's nonlattice renewal theorem [BRW-smell, Lalley 1989], with the
eventual-positivity hypothesis supplied by "no two consecutive ÷3 edges" ([BRW-smell]).]

This is the AC packaging of KL: **their λ_k is a Perron root = pole of a resolvent; their
spread C^max_k is the pole's eigenvector; their difference inequalities are the recursion
D = 𝟙 + M(s)ᵀD.** Contentless as new mathematics at fixed k, but it fixes vocabulary and
imports the transfer machinery.

---

## 2. λ∞ = 2 as confluence of singularities / radius of convergence of the limit GF

The finite GFs D_k(s) are rational (finite matrices) with dominant pole at γ_k. As k→∞
the object is the resolvent of the **transfer operator on C(Y), Y = 2+3ℤ₃** ([LIM] §1.4):

  (L_s c)(x) = 2^{−2s}c(4x) + 1_{Y₂}2^{(α−2)s}c(R₂x) + 1_{Y₈}2^{(α−1)s}c(R₈x),

  D_∞(s) "=" (I − L_s)⁻¹𝟙,  abscissa of convergence δ_∞ = {s : spec.radius L_s = 1}.

- **Annealed** (Haar-averaged lost digit) L_s is linear with k-independent Perron root
  s(λ)=λ^{−2}+(λ^{α−2}+λ^{α−1})/3; its pole is at **δ=1 for every k** ([LIM] Lemma 1.3,
  s(2)=1). So the annealed GF has radius of convergence exactly 1 at all precisions.
- **Quenched** (adversarial min over the lost 3-adic digit) the resolvent is **nonlinear**
  (min-of-linear), pole at γ_k < 1; the operator is the min-plus/topical F_λ^{(k)} of
  `adversarial-operator.md`.

**Reformulation of the dichotomy (AC form).** λ∞ = 2 ⟺ **the quenched dominant singularity
δ_k migrates up to the annealed one, δ_k ↑ 1** ⟺ the two GFs D^quench and D^ann acquire a
common radius of convergence in the limit. This is [LIM] Problem 3.5 verbatim, now phrased
as a **confluence of the quenched pole with the annealed pole** — the AC template for a
phase transition. The oscillation law s(λ_k)−1 = (λ_k^{α−2}+λ_k^{α−1})·δ_k ([LIM] Thm 3.2)
is exactly "distance of the quenched pole to the annealed pole = mean eigenvector
oscillation." No new leverage, but the target is now a standard AC quantity.

---

## 3. Lattice vs nonlattice: where the Collatz "wobble" would come from [PROVABLE]

Collatz sits on **two arithmetics at once**: the ×4/÷2 (base-2) part is *lattice*
(displacements in log2·ℤ), the ÷3 part is *nonlattice* relative to it (log3/log2 irrational).
For the full predecessor count the combined displacement group log2·ℤ + log3·ℤ is dense ⇒
**nonlattice ⇒ pure power law x^{γ}** (Cor 1.2). But any **sub-statistic that sees only the
2-adic structure** (e.g. counts filtered by a fixed 2-adic pattern / a Terras stopping-time
class) has displacements in log2·ℤ ⇒ **lattice ⇒ x^{γ} × (log₂x-periodic bounded function)**:
the Mellin poles line up on a vertical lattice Re s = γ + (2πi/log2)ℤ and the transfer
theorem returns an oscillatory prefactor. **Prediction:** empirical Collatz statistics
stratified by 2-adic data should exhibit log₂-periodic oscillation (a "wobble"), while the
unrestricted predecessor count should not — a concrete, cheap falsification test of the AC
picture and an explanation for periodicities seen in some Collatz density plots. [PROVABLE
via Wiener–Ikehara/Delange with the lattice term retained.]

---

## 4. The BRW front, and why derivative martingales are the wrong tool here

### 4.1 γ_k is the adversarial Biggins front [PROVED, = BRW-smell]
Define the pressure φ(δ) := log₂ ρ(M(δ)). The number of depth-n vertices with value ≈ nθ
grows like 2^{n·φ\*(θ)} (φ\* = concave conjugate); the count-below-V exponent is the Biggins
spreading-speed / level-set front, and solving φ(δ)=0 gives δ = γ_k. The **annealed** front
is the δ=1 root of φ_ann(δ)=log₂ s(2^δ). So:

  **γ_k = adversarial (min-type) Biggins front;  γ_∞ ≤ 1 = annealed Biggins front.**

### 4.2 The transverse-root correction: no Seneta–Heyde polylog [PROVED for the annealed model]
Is δ=1 the **critical/boundary tilt** (where derivative martingales and the (3/2)log n or
√n Seneta–Heyde corrections live)? No. Criticality requires the tilt to be the tangency
point, φ(δ)=δφ′(δ). Compute

  φ_ann′(1) = 2^δ s′(2^δ)/s(2^δ)·|_{δ=1} = 2·s′(2) = 2·(3(α−2)/8) = **3(α−2)/4 ≈ −0.311 ≠ 0.**

So δ=1 is a **transverse (simple, subcritical) root** of φ_ann. Consequences [PROVED for the
annealed multitype BRW; HEUR for the true tree]:
- The **additive (Biggins) martingale** W_n(1) = Σ_{|u|=n} 2^{−value(u)}·r_{type(u)}
  (r = right Perron eigenvector of M(1)) is uniformly integrable → strictly positive limit
  W_∞ (subcritical ⇒ Kesten–Stigum/Biggins L logL holds; offspring bounded ⇒ trivially).
- Hence the annealed predecessor count is a **clean N(x) ~ c·W_∞·x**, positive density,
  **no polylog factor** — matching the classical density heuristic π_a(x) ≍ x.
- **Derivative martingales / Aïdékon–Shi / Seneta–Heyde corrections are therefore
  irrelevant to predecessor counting**: they only act at the critical tilt, which δ=1 is
  not. This *corrects* the "hot-speculative" prediction in [BRW-smell] (that (A) would give
  x/(log x)^{3/2}); the honest prediction under (A) is π_a(x) = x^{1−o(1)} with the o(1)
  governed by the *disorder* rate, not by a universal ^{3/2} log power.

### 4.3 The real gap is disorder, not correction [SPEC — precise conjecture]
The min-over-lost-digit is a **zero-temperature quenched** relaxation; min ≤ mean gives
γ_k ≤ 1 always. λ∞ = 2 ⟺ the adversary's per-scale advantage vanishes ⟺ **weak-disorder /
disorder-irrelevance** for the directed polymer / BRW on the backward Collatz tree, where
the "environment" is the choice of lost 3-adic digit at each refinement. The clean new
object to study is the **true-tree additive martingale** W_n^{true}(1) = Σ_{depth n}
2^{−value(u)} r_{type(u)}: its uniform integrability / positivity is *equivalent* to
γ_∞ = 1 (exponent 1), and its degeneration would realize γ_∞ < 1. This is the AC/BRW twin
of [LIM]'s corrector-flattening criterion and of `adversarial-operator.md`'s "adversarial
Mather measure with Haar-singular marginal."

---

## 5. Forward statistics from one walk; the exponent-1 coincidence

The forward Syracuse map per accelerated T-step has log₂-increment
X = −1 (halving, prob ½) or X = α−1 = log₂(3/2) (the (3n+1)/2 step, prob ½), drift
E[X] = (α−2)/2 = −0.2075 < 0. [HEUR — the ½/½ i.i.d. parity is Terras's density-1 heuristic,
not a theorem; AC recovers the constants, it cannot prove them.]

### 5.1 Mean total stopping time [HEUR]
LLN: steps to descend log n = log n / |E[X] in nats| = log n / (½ log(4/3)) =
**(2/log(4/3))·log n = 6.9521·log n.** AC packaging: derivative at 0 of the stopping-time
Laplace transform (a saddle-point/moment extraction), = 1/|drift|. Recovered, not improved.

### 5.2 Maximum-excursion exponent 2 [HEUR, derived]
**Lundberg equation** E[2^{θX}] = 1: ½·2^{−θ} + ½·2^{θ(α−1)} = 1 has positive root
**θ\* = 1** (check: ¼ + ½·(3/2) = ¼ + ¾ = 1, using 2^{α−1}=3/2). Cramér–Lundberg:
P(sup_n S_n ≥ h) ≍ C·2^{−θ\*h} = C·2^{−h}, so for the running maximum M of the value process,
P(M ≥ n·t | start n) ≍ 1/t, i.e. P(M ≥ y | n) ≍ n/y. Taking the **record over all starts
n ≤ N** (E#{n ≤ N : M ≥ y} ≍ N²/(2y), = O(1) at y ≍ N²):

  **the largest excursion among starting values ≤ N scales like N² — excursion exponent 2 =
  the Lundberg root θ\* = 1.**

[Caveat, verified with gpt-5.6-sol: the record-over-N step uses a decorrelation/extreme-value
heuristic; true Collatz trajectories coalesce once merged, so this is a first-moment
prediction, not a theorem.]

### 5.3 The single free-energy zero [PROVED for the models]
The **same "exponent-1" critical tilt** governs all three: backward annealed pole δ=1
(⇔ λ=2, s(2)=1), forward Lundberg root θ\*=1, and the density heuristic π_a ≍ x. The
forward Lundberg polynomial ½·2^{−θ}+½·2^{θ(α−1)} and the backward annealed Perron root
λ^{−2}+(λ^{α−2}+λ^{α−1})/3 are different functions with the **same critical root at
exponent 1**, both expressing the identity 2^{α}=3, i.e. "one ÷3 exactly undoes log₂3 of
doubling." This is the cleanest thing the AC lens contributes: the excursion-2, the
mean-6.95, and the predecessor-1 exponents are three readings of one free-energy zero.

---

## 6. Does AC improve the constants? [Honest answer]

- **Predecessor exponent:** No improvement at fixed k (exact reformulation, §1). The value
  0.9033 is from computing k=18, unchanged by AC. AC's contribution is the transfer theorem
  (clean x^γ, no log), the confluence framing of λ∞ (§2), the lattice/nonlattice wobble
  prediction (§3), and the transverse-root correction that kills the derivative-martingale
  route and reframes the gap as disorder (§4).
- **Mean-stopping 6.95 and excursion-2:** Recovered exactly as LLN / Lundberg constants
  (§5); **not improved and not provable by AC** — the arithmetic increments are not
  independent, and that independence is precisely the open conjecture. AC gives the *shape*
  (why 6.95, why 2, why they share the exponent-1 zero), not a proof.

**Net:** AC does not crack anything, but it (i) certifies the endgame under (A) is a clean
linear law (no polylog), (ii) shows derivative-martingale theory is a dead end for the
exponent, redirecting effort to the quenched/annealed disorder martingale W^true(1), and
(iii) unifies the three folklore constants through 2^α = 3.

---

## 8. Finite-size scaling of γ_k: an AC/BRW cutoff diagnostic for the dichotomy [NEW, data-backed]

The dichotomy λ∞ = 2 vs < 2 has always been posed as a *limit* question ([LIM] Prob 3.5).
AC/BRW makes it a question about the **rate and functional form** of the approach γ_k → γ_∞,
and that form is *already legible in the certified data*. The precision-k system tracks
N_k = 3^{k−1} residue classes — a **finite population / truncation** of the tree. The
adversarial min is a directed-polymer/selection mechanism on that population. BRW front
theory then gives a sharp dichotomy for the finite-size correction:

- **Off-critical (spectral gap ⇒ λ∞ < 2):** the truncated front γ_k relaxes to γ_∞
  **exponentially**, γ_∞ − γ_k ≍ a·r^k, r = subdominant/dominant ratio of the level-tower
  refinement (a genuine gap).
- **Critical / marginal (λ∞ = 2):** the front is at its boundary tilt and the correction is
  the **Brunet–Derrida cutoff** γ_∞ − γ_k ≍ π²|ψ″|/(2 (log N_k)²). With log N_k = (k−1)log3
  this is an **algebraic 1/k²** law (up to a possible Bramson log(k)/k refinement).

### 8.1 The fits (`experiments/ac/`, 9 certified points k=11–19)
| model | γ_∞ | rms | verdict |
|---|---|---|---|
| geometric γ_∞−a·r^k (r=0.920) | 0.981 | 1.0·10⁻⁴ | best clean fit |
| repeated Aitken Δ² (model-free) | 0.974 | — | stable over 3 passes |
| force γ_∞=1, geometric | 1 | 3.4·10⁻⁴ | 3× worse |
| 1/k² (Brunet–Derrida) | 0.939 | 3.0·10⁻³ | 30× worse |
| force γ_∞=1, 1/k² | 1 | 2.1·10⁻² | **catastrophic (200×)** |

Data in `gamma_finite_size.csv`, fits in `fits_summary.csv`. The geometric law and the
algebraic law are cleanly separated: the geometric fit is 30–200× tighter.

### 8.2 The sharp within-window signature (does not need far extrapolation)
The consecutive **increment ratios** (γ_k−γ_{k−1})/(γ_{k−1}−γ_{k−2}) are the diagnostic that
avoids trusting the extrapolated intercept. A pure 1/k² law forces them to **rise**
monotonically: ((k−1)/k)³ climbs 0.78 → 0.85 across k=11→19. A geometric law forces them
**flat** at r. Observed (past the k=12 transient): **0.93, 0.91, 0.92, 0.91, 0.91, 0.92 —
flat at ~0.92, no rising trend.** This is the signature of a **gap**, not of criticality.

### 8.3 Reading and the honest caveat
Within k ≤ 19 the KL exponent behaves like an **off-critical, gapped** front converging to
**γ_∞ ≈ 0.975 < 1 ⇒ λ∞ < 2** — a concrete prediction that the KL difference-inequality
method has an **intrinsic ceiling** around x^{0.975}, *not* x^{1−ε}. This is the AC/BRW
instantiation of §4.3's "the gap is disorder" and of [LIM]'s corrector-non-flattening branch
(B). **Caveat [SPEC]:** Brunet–Derrida corrections are notoriously invisible until N is
astronomically large, so a clean geometric window (here N_k ≤ 3^18 ≈ 4·10⁸) *can* be a
pre-asymptotic transient that later crosses over to critical 1/k². What makes the reading
more than a curve-fit is §8.2: at true criticality the increment ratios must already be
**drifting upward** at these k, and they are not. **Pre-registered test:** k=20–22 (files
present, deprioritized). Off-critical predicts ratio stays ≈0.92 and γ_20≈0.9152,
γ_21≈0.9204, γ_22≈0.9251 (geometric fit); a *rise* in the ratio toward ~0.86 would be the
first fingerprint of a Brunet–Derrida crossover and would resurrect λ∞ = 2. This is a cheap,
decisive discriminator on data we already hold.

---

## 9. Two AC objects the scout missed [structural]

### 9.1 The Terras first-descent distribution as a kernel-method excursion GF [PROVABLE]
§5 treated the **total** stopping time (~6.95 log n). The **stopping time** σ(n) = min{m :
T^m(n) < n} (Terras) has instead a *proper limiting distribution* p_j = density{n : σ(n)=j},
independent of n. In the Terras parity-vector encoding, {σ(n)=j} is exactly a **first-passage
below 0** of the two-slope walk S_m = (#odd steps)·α − m; admissibility of a parity vector is
a ballot/Łukasiewicz positivity constraint on partial sums. That is precisely the domain of
the **Banderier–Flajolet kernel method** for directed lattice paths: the excursion/first-
passage GF P(z) = Σ p_j z^j is algebraic, obtained from the small roots of the step kernel,
and **singularity analysis of P(z) gives the geometric tail p_j ~ C·ρ^j** with ρ the dominant
singularity. This is the natural AC home of the stopping-time distribution and is absent from
the Collatz literature (which computes p_j by direct 2^k-enumeration). [Calibration: the
reduction to a lattice-path first-passage is structural/provable; the incommensurable slopes
{−1, α−1} put the *height* off-lattice, so the constant C, ρ come from a nonlattice
kernel/renewal variant — the same lattice/nonlattice split as §3.]

### 9.2 γ_k as the lowest zero of a truncated dynamical zeta [structural]
Prop 1.1's "ρ(M(s))=1" is literally **det(I − M(s)) = 0**: γ_k is the *largest real zero* of
the truncated **dynamical (Fredholm) determinant** d_k(s) = det(I − M_k(s)), and D_k(s) =
(I−Mᵀ)⁻¹𝟙 has its dominant pole there. So the AC dominant singularity **is** a dynamical-zeta
zero, and γ_∞ = lim (lowest zero of d_k). Note this is the **unsigned** transfer determinant
of the *predecessor* (backward, contracting) dynamics — a different object from
`solenoid-zeta.md`'s *signed cohomological* zeta Z_3 ≡ 1 (which is the traceless correspondence
statement). The two live on the same solenoid but carry opposite signs of the ÷3 branches:
the unsigned one *has* a zero (γ_∞), the signed one is identically 1. Reconciling them —
the unsigned lowest zero as a "temperature-0 limit" of the signed acyclicity — is the clean
bridge between this note and the zeta program.

---

## 7. Ledger and pointers

**[PROVED, reformulation]** §1 (γ_k = abscissa/simple pole of D(s)=(I−Mᵀ)⁻¹𝟙; transfer
theorem ⇒ x^{γ_k}, nonlattice ⇒ no log); §2 (λ∞ as pole confluence); §4.1 (Biggins front);
§4.2 transverse-root computation φ_ann′(1)=3(α−2)/4≠0 and its UI/no-polylog consequence for
the annealed model; §5.1–5.3 for the walk models (Lundberg θ\*=1, mean 6.95, exponent-1
coincidence).
**[PROVABLE]** §3 lattice-term/wobble via Wiener–Ikehara–Delange with retained oscillatory
poles.
**[SPEC / precise conjecture]** §4.3 λ∞=2 ⟺ weak disorder ⟺ UI of the true-tree additive
martingale W^true(1); the disorder-transition identity with `adversarial-operator.md` Conj 4.3.
**[SPEC, data-backed]** §8 finite-size scaling: geometric (gapped) fit ⇒ γ_∞≈0.975<1 ⇒ λ∞<2;
flat increment ratios ~0.92 reject the 1/k² Brunet–Derrida critical form; caveat = possible
delayed crossover, pre-registered k=20–22 test in §8.3.
**[PROVABLE / structural]** §9.1 Terras first-descent distribution = kernel-method excursion
GF (Banderier–Flajolet); §9.2 γ_k = lowest zero of the unsigned truncated dynamical zeta
det(I−M_k(s)), a signed-vs-unsigned bridge to `solenoid-zeta.md`.
**[HEUR]** §5 constants for the true (deterministic, correlated) dynamics.

**Sharpest new items.** (1) **Finite-size scaling discriminates the dichotomy on data we
already hold** (§8): the certified γ_k(k=11–19) converge *geometrically* (gap ⇒ λ∞<2, ceiling
γ_∞≈0.975), and the increment-ratio test (flat ~0.92, not rising 0.78→0.85) is a within-window
signature that does not rely on far extrapolation — pre-registered k=20–22 discriminator.
(2) **Derivative martingales are irrelevant to the predecessor exponent** (transverse root,
§4.2) — a correction to [BRW-smell]'s Seneta–Heyde hope; the right object is the additive
martingale W^true(1). (3) **One free-energy zero (2^α=3) yields all three exponents** (§5.3).
(4) **Terras first-descent distribution is a kernel-method excursion GF** (§9.1) and **γ_k is
a dynamical-zeta zero** (§9.2). (5) **Lattice/nonlattice wobble test** (§3): 2-adically
stratified counts should oscillate log₂-periodically; the full count should not.

**References.** P. Flajolet, R. Sedgewick, *Analytic Combinatorics*, CUP 2009 (Ch. IV–VIII,
singularity analysis, transfer theorems, saddle point). A. Odlyzko, *Asymptotic enumeration
methods*, Handbook of Combinatorics 1995 (Tauberian/Mellin machinery). S. Lalley, *Renewal
theorems in symbolic dynamics*, Acta Math. 163 (1989) [nonlattice renewal, saved via
BRW-smell]. J. Biggins, *Spreading speeds in reducible multitype BRW*, AAP 22 (2012),
arXiv:1003.4716 [`papers/biggins2012_reducible_multitype_spreading_speeds.pdf`]. Grama–
Mentemeier–Xiao, arXiv:2507.09737 [`papers/grama_mentemeier_xiao2025_matrix_BRW_spinal_derivative_martingale.pdf`]
(derivative martingale / Seneta–Heyde — shown here *not* to apply). Krasikov–Lagarias, Acta
Arith. 109 (2003). [LIM] `docs/notes/kl-limit-object.md`; solver `kl_perron_solver.py`.
