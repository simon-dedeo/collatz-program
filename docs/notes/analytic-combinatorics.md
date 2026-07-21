# Analytic-combinatorics scout for the Collatz counting statistics (corrected)

2026-07-20 (rev c). Status: **scout report with a load-bearing retraction**.
Rev c records the successor/Lean audit: the former §§1–2, §4.1 and §9.2
incorrectly identified the nonlinear KL min-over-fibers threshold with the pole
of a fixed linear backward-tree matrix. The claimed true-count asymptotic,
no-log conclusion, ordinary pole confluence, and dynamical-zeta zero at `γ_k`
are retracted. The annealed-model calculations, forward-walk heuristics,
finite-size data, and elementary increment-contraction criterion survive.
Companion to `kl-limit-object.md` [LIM], `adversarial-operator.md`, `solenoid-zeta.md`, and
`docs/smell/Branching-random-walks--additive-martingales.json` [BRW-smell].
Tags: [PROVED] proof/standard-cite; [RETRACTED] false as stated; [PROVABLE] route clear; [SPEC] speculative;
[HEUR] a heuristic that AC *recovers but cannot prove* (the independence is the conjecture).

α := log₂3 = 1.5849625…; value(v) := log₂(v as integer); λ = 2^δ.

---

## 0. Summary

Flajolet–Sedgewick singularity analysis is essentially absent from the Collatz literature,
yet all three headline statistics — predecessor exponent, total-stopping mean, maximum
excursion — are *combinatorial parameters of trees/walks with a real-valued additive
weight*, hence live natively in the analytic-combinatorics (AC) frame. Findings:

1. **[RETRACTED]** The certified KL exponent `γ_k` is *not established* as
   the abscissa/simple pole of the ordinary resolvent
   `D(s)=(I−M(s))⁻¹𝟙`. The KL solver applies a nonlinear minimum over three
   lifts in each fiber; the literal backward-tree series sums children with a
   fixed linear matrix. A locally selected policy matrix is not an exact
   counting recursion without a separate sandwich theorem. Consequently this
   note does not prove `π_a(x) ~ C_k x^{γ_k}` or a no-log conclusion (§1).
2. **[RETRACTED as an ordinary-pole statement]** `λ_∞=2` is equivalent to
   `γ_k→1`, but calling this confluence of a nonlinear "quenched pole" with
   the annealed linear pole is only an analogy until a nonlinear abscissa or an
   exact counting bridge is defined and proved (§2).
3. **[PROVED only for the annealed model; OPEN for nonlinear KL]** The
   annealed exponent-1 tilt is a **transverse root** of its pressure
   (φ′(1) = 2·s′(2) ≈ −0.311 ≠ 0), i.e.
   *subcritical* — so the additive (Biggins) martingale is UI and the annealed count is a
   clean linear x with **no Seneta–Heyde / derivative-martingale polylog**.
   This excludes such a correction for the annealed model only; it does not
   identify the nonlinear KL exponent or true predecessor asymptotic. The
   min-vs-mean gap remains a possible disorder analogy, not a proved directed-
   polymer equivalence.
4. **[PROVED for the walk model / HEUR for Collatz]** The forward mean-stopping constant
   6.952 and the maximum-excursion exponent 2 are recovered from the **same** two-step
   Syracuse walk {−1 w.p. ½, α−1 w.p. ½}: the mean is a LLN (1/|drift|), the excursion-2 is
   the **Lundberg root θ\* = 1** plus a record-over-N extreme-value count (§5). The forward
   Lundberg root θ\*=1 and the backward annealed pole δ=1 are the *same* "exponent-1"
   critical tilt — a single free-energy zero governs all three statistics (§5.3).
5. **[DATA + PROVABLE target — NEW 2026-07-20b, corrected]** The AC/BRW frame turns the open
   dichotomy into a **finite-size-scaling** question the certified data can be run against. On
   k=11–19 the certified γ_k converge in a **geometric (spectral-gap) shape, not** the
   **unshifted-marginal** 1/k² Brunet–Derrida shape (increment ratios flat ~0.92, not rising
   0.78→0.85; free-geom rms 1·10⁻⁴). **But — correcting an earlier draft claim (verified with
   gpt-5.6-sol) — geometric convergence does *not* decide λ∞: γ_k = 1 − a·r^k approaches
   exactly 1 and fits equally well (rms 3·10⁻⁴), so λ∞ = 2 stays fully compatible; nine
   deterministic points cannot separate γ_∞ = 1 from < 1** (only a mild, non-decisive tilt to
   ≈0.985 from out-of-sample prediction; Aitken unstable). The durable payoff is a **clean
   proof target**: since `γ_∞=γ_K+Σ_{j>K}d_j`, a *proved eventual contraction*
   `d_{k+1}≤q d_k` (`q<1`) together with
   `γ_K+d_{K+1}/(1−q)<1` is a sufficient certificate for `λ_∞<2`, plausibly
   obtainable from a spectral gap of the level-tower refinement. It is not an
   equivalence, and increment ratios alone do not decide the limit (§8).

---

## 1. The predecessor generating function and its dominant singularity [RETRACTED identification]

> **Audit correction.** A fixed linear matrix can encode a linear tree model,
> but it is not the nonlinear `kl_perron_solver.py` operator and its spectral
> root is not thereby `γ_k`. The former proposition and corollary in this section
> were invalid and are replaced by the distinction below.

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

The sentence in rev. b claiming that `M(s)` is exactly
`kl_perron_solver.py` was false. The code uses

`min(c[ref[:,0]], c[ref[:,1]], c[ref[:,2]])`,

so its map is nonlinear. Replacing that minimum by the sum/mean of all three
children gives the annealed linear relaxation; freezing minimizers gives a
policy matrix depending on the eigenvector. Neither operation proves an exact
recursion for the true predecessor count at exponent `γ_k`. A simple-pole and
nonlattice transfer theorem may apply to a separately defined irreducible
linear model after its hypotheses are checked, but no such theorem currently
transfers the KL lower-bound exponent to `π_a(x)`.

---

## 2. λ∞ = 2 and the annealed/nonlinear distinction [corrected]

The established facts are: the annealed linear calculation has the
`k`-independent root `s(2)=1`; the nonlinear KL thresholds satisfy
`γ_k=log₂ λ_k<1`; and `λ_∞=2` is equivalent to `γ_k→1`. It is
reasonable to seek a nonlinear-pressure or abscissa language for the
min-type operator, but this note has not defined one with an exact counting
interpretation. "Quenched pole," "common radius," and "pole confluence" are
therefore heuristic metaphors here, not reformulations or transfer theorems.

---

## 3. Lattice vs nonlattice: where a model "wobble" would come from [SPEC]

Collatz sits on **two arithmetics at once**: the ×4/÷2 (base-2) part is *lattice*
(displacements in log2·ℤ), the ÷3 part is *nonlattice* relative to it (log3/log2 irrational).
For a correctly specified irreducible linear renewal model, the combined displacement group
log2·ℤ + log3·ℤ is dense, which would give a nonlattice pure-power transfer law. No such
law has been proved here for the true predecessor count. A **sub-statistic that sees only the
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

### 4.1 Nonlinear-pressure analogy [OPEN]
The annealed matrix has the ordinary Biggins pressure
`φ_ann(δ)=log₂ s(2^δ)` and root `δ=1`. The nonlinear KL map has a
well-defined cone spectral radius, but rev. b did not prove that its threshold
is a Biggins front or the Legendre transform of a counting process. Any such
statement needs nonlinear thermodynamic formalism plus an exact interpretation;
it cannot be obtained by silently substituting a policy matrix for the min map.

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
  irrelevant to this annealed model**: they act at a critical tilt, which its
  `δ=1` root is not. Nothing here transfers that conclusion to the nonlinear
  KL threshold or proves the shape of the true predecessor count.

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

- **Predecessor exponent:** No improvement. The current certified value
  `0.9094372617` is from the KL difference inequalities at k=19, independently
  of this AC note. Rev. b's claimed exact AC reformulation and
  transfer theorem were wrong; the valid contribution is presently limited to
  annealed-model calculations, finite-size diagnostics, and possible nonlinear-
  pressure questions that still need an exact interpretation.
- **Mean-stopping 6.95 and excursion-2:** Recovered exactly as LLN / Lundberg constants
  (§5); **not improved and not provable by AC** — the arithmetic increments are not
  independent, and that independence is precisely the open conjecture. AC gives the *shape*
  (why 6.95, why 2, why they share the exponent-1 zero), not a proof.

**Net after audit:** AC does not currently yield a theorem about the true
predecessor count. It gives a correct transverse-root calculation for an
annealed model, useful finite-size plots, and heuristic connections among
folklore constants through `2^α=3`. A genuine advance requires a nonlinear
pressure theorem or a proved bridge to an exact linear counting object.

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

*Caveat carried throughout (flagged by gpt-5.6-sol, independently rechecked):* identifying
N_k = 3^{k−1} with a genuine BRW particle-cutoff needs a theorem, and "adversarial min" is
worst-case/min-plus control, not literally quenched disorder — so this is an analogy that
*organizes the data*, not a derivation. The results below are all `experiments/ac/`.

### 8.1 What the data robustly show [data]
The certified γ_k (k=11–19, `gamma_finite_size.csv`) converge in a **geometric / spectral-
gap shape, not** the **unshifted-marginal** 1/k² Brunet–Derrida shape. Two independent tells:
- **Fit quality.** Free geometric γ_∞−a·r^k: rms 1·10⁻⁴, and out-of-sample (fit k≤16, predict
  17–19) error only 4·10⁻⁵…4·10⁻⁴. Unshifted 1/k² forced to γ_∞=1: rms 2·10⁻² (excluded).
- **Increment ratios** d_k/d_{k−1} = (γ_k−γ_{k−1})/(γ_{k−1}−γ_{k−2}) are **flat at ~0.92**
  (0.93,0.91,0.92,0.91,0.91,0.92). A pure **unshifted** 1/k² law forces them to **rise**
  0.78→0.85 across this window; they do not. This is the robust content: the convergence is
  geometric-looking, and if criticality holds it has **not yet** entered its 1/k² regime
  (consistent with log N_k ≈ 20 being far from asymptotic).

### 8.2 What the data do NOT decide [correction of an earlier overclaim, verified w/ sol]
**Geometric convergence does *not* imply λ∞ < 2.** The sequence γ_k = 1 − a·r^k approaches
*exactly* 1 while being perfectly geometric; it fits the window at rms 3.3·10⁻⁴, and its
residuals e_k = 1−γ_k have flat ratios 0.928→0.936 — i.e. **λ∞ = 2 is fully compatible.** A
*shifted* critical law 1 − C/(k+a)² (a≈14) fits at rms 5.5·10⁻⁴ — also not excluded (only the
rigid unshifted form was). Nine deterministic points with 2–3 parameters **cannot separate
γ_∞ = 1 from γ_∞ < 1**; comparing rms without a noise model is not a statistical rejection.
This **retracts** the earlier draft's "λ∞ < 2, ceiling ≈0.975": that conclusion is not
supported. (No theorem gives exponential-in-k ⇒ λ∞ < 2; counterexample γ_k=1−cr^k.)

The only honest *tilt* is mild and non-decisive: (i) the free-limit fit predicts out-of-sample
~3× better than the forced-to-1 fit (γ_∞≈0.985); (ii) forced-limit residual ratios q_k(L) =
(L−γ_k)/(L−γ_{k−1}) are flattest near L≈0.975–0.98 and drift *upward* for L=1. Against this,
rolling 3-point Aitken estimates are **unstable** (0.93…1.08), which by itself warns against
reading any single extrapolated limit. Net: a whisker below 1, but inside the noise.

### 8.3 A sufficient increment-contraction certificate [PROVABLE target]
The value of this finite-size calculation is not a numerical verdict but a
clean sufficient proof target. Since `γ_k` is increasing and

`γ_∞ = γ_K + Σ_{j>K} d_j`,  where `d_j=γ_j−γ_{j−1}`,

an eventual bound `d_{k+1}≤q d_k` with `q<1`, together with
`γ_K+d_{K+1}/(1−q)<1`, would prove `λ_∞<2`. A spectral gap for the
level-tower refinement is one possible source of such a bound.

This certificate is **sufficient, not equivalent** to `λ_∞<2`, and its ratio
has no converse interpretation. For example, `γ_k=1−2^{-k}` has ratio `1/2`
but limit `1`, while `γ_k=L−1/k` with `L<1` has ratio tending to `1` but limit
below `1`. Thus the k=20–22 ratios can diagnose the local shape of the sequence,
but cannot by themselves favor either `λ_∞=2` or `λ_∞<2`. No general theorem
substitutes for a model-specific tail bound.

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

### 9.2 Truncated dynamical-zeta identification [RETRACTED]
The determinant identity belongs to a fixed linear matrix. The certified
`γ_k` belongs to the nonlinear min operator, so rev. b's equation
`det(I−M_k(γ_k))=0` was not established. No unsigned dynamical-zeta zero at
`γ_k`, nor a bridge from such a zero to the signed solenoid zeta, follows from
the present work.

---

## 7. Ledger and pointers

**[RETRACTED]** §1 (`γ_k` as an ordinary resolvent pole and the resulting
true-count/no-log transfer); §2 (ordinary pole confluence); §4.1 (nonlinear KL
threshold as a proved Biggins front); §9.2 (dynamical-zeta zero at `γ_k`).
**[PROVED for the annealed model]** §4.2 transverse-root computation φ_ann′(1)=3(α−2)/4≠0 and its UI/no-polylog consequence for
the annealed model; §5.1–5.3 for the walk models (Lundberg θ\*=1, mean 6.95, exponent-1
coincidence).
**[SPEC / model target]** §3 lattice-term/wobble after a valid linear
counting model and renewal hypotheses are supplied.
**[SPEC / precise conjecture]** §4.3 λ∞=2 ⟺ weak disorder ⟺ UI of the true-tree additive
martingale W^true(1); the disorder-transition identity with `adversarial-operator.md` Conj 4.3.
**[DATA + PROVABLE target]** §8 finite-size scaling: convergence is geometric-shaped, not
unshifted-1/k²; but this does NOT decide λ∞ (γ_k=1−a r^k fits too — verified w/ sol; earlier
"ceiling 0.975" retracted). An eventual increment contraction plus the displayed
strict tail bound is a **sufficient** certificate for `λ∞<2`, not an equivalence.
**[PROVABLE / structural]** §9.1 Terras first-descent distribution = kernel-method excursion
GF (Banderier–Flajolet), subject to its stated off-lattice qualification.
**[HEUR]** §5 constants for the true (deterministic, correlated) dynamics.

**Sharpest new items.** (1) **A sufficient increment-contraction certificate** (§8):
certified γ_k(k=11–19) converge *geometrically* (flat ratio ~0.92, not the rising 0.78→0.85 of
unshifted 1/k²), but that shape does NOT decide λ∞ (γ_k=1−a r^k fits too) — so the payoff is
that **a proved eventual contraction d_{k+1}≤q d_k with
γ_K+d_{K+1}/(1−q)<1 implies λ∞<2**. The converse is false; k=20–22 ratios
are shape diagnostics only.
(2) The **annealed** exponent-1 root is transverse (§4.2), so derivative-
martingale corrections do not apply to that model; no corresponding theorem for
the nonlinear KL threshold or true count is claimed. (3) The identity `2^α=3`
produces the same exponent-1 root in the stated heuristic walk models (§5.3).
(4) Terras first-descent has a kernel-method excursion formulation target
(§9.1). The former dynamical-zeta claim at `γ_k` is retracted (§9.2).
(5) The lattice/nonlattice wobble is a model prediction pending an exact
counting bridge (§3), not a proved property of the full predecessor count.

**References.** P. Flajolet, R. Sedgewick, *Analytic Combinatorics*, CUP 2009 (Ch. IV–VIII,
singularity analysis, transfer theorems, saddle point). A. Odlyzko, *Asymptotic enumeration
methods*, Handbook of Combinatorics 1995 (Tauberian/Mellin machinery). S. Lalley, *Renewal
theorems in symbolic dynamics*, Acta Math. 163 (1989) [nonlattice renewal, saved via
BRW-smell]. J. Biggins, *Spreading speeds in reducible multitype BRW*, AAP 22 (2012),
arXiv:1003.4716 [`papers/biggins2012_reducible_multitype_spreading_speeds.pdf`]. Grama–
Mentemeier–Xiao, arXiv:2507.09737 [`papers/grama_mentemeier_xiao2025_matrix_BRW_spinal_derivative_martingale.pdf`]
(derivative martingale / Seneta–Heyde — shown here *not* to apply). Krasikov–Lagarias, Acta
Arith. 109 (2003). C. Banderier, P. Flajolet, *Basic analytic combinatorics of directed
lattice paths*, TCS 281 (2002) [kernel method, §9.1]. J. Bérard, J.-B. Gouéré, *Brunet–Derrida
behavior of branching-selection particle systems on the line*, CMP 298 (2010) [the 1/(log N)²
law, §8]. R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976)
[first-descent distribution, §9.1]. [LIM] `docs/notes/kl-limit-object.md`; solver
`kl_perron_solver.py`; §8/§9 data `experiments/ac/*.csv`.
