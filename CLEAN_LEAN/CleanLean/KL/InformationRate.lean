/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ArgminFrustration

/-!
# Uniform cold-limit bounds for a ternary information rate

This is the scalar, Lean-ready statement from the information-geometric
defect calculation.  It proves a level-uniform `log 3 / beta` approximation
for the local cold escort rate.  It does not assert that the sum of these local
rates controls the global KL defect.
-/

namespace CleanLean.KL

open scoped BigOperators

/-- Three-term Boltzmann partition sum. -/
noncomputable def ternaryBoltzmannSum (β : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i, Real.exp (-β * v i)

theorem ternaryBoltzmannSum_pos (β : ℝ) (v : Fin 3 → ℝ) :
    0 < ternaryBoltzmannSum β v := by
  unfold ternaryBoltzmannSum
  positivity

/-- The partition sum lies between the largest Boltzmann term and three
copies of it. -/
theorem ternaryBoltzmannSum_bounds
    {β : ℝ} (hβ : 0 < β) (v : Fin 3 → ℝ) :
    Real.exp (-β * ternaryMin v) ≤ ternaryBoltzmannSum β v ∧
      ternaryBoltzmannSum β v ≤ 3 * Real.exp (-β * ternaryMin v) := by
  let i₀ := ternaryArgmin v
  have hi₀ : v i₀ = ternaryMin v := by
    apply le_antisymm
    · exact le_ternaryMin (ternaryArgmin_isArgmin v)
    · exact ternaryMin_le v i₀
  constructor
  · rw [← hi₀]
    unfold ternaryBoltzmannSum
    exact Finset.single_le_sum
      (fun i _ => (Real.exp_pos (-β * v i)).le) (Finset.mem_univ i₀)
  · unfold ternaryBoltzmannSum
    calc
      ∑ i : Fin 3, Real.exp (-β * v i) ≤
          ∑ _i : Fin 3, Real.exp (-β * ternaryMin v) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.exp_le_exp.mpr
        have hmin := ternaryMin_le v i
        nlinarith
      _ = 3 * Real.exp (-β * ternaryMin v) := by simp

/-- Logarithmic form of the three-term partition-sum estimate. -/
theorem log_ternaryBoltzmannSum_bounds
    {β : ℝ} (hβ : 0 < β) (v : Fin 3 → ℝ) :
    -β * ternaryMin v ≤ Real.log (ternaryBoltzmannSum β v) ∧
      Real.log (ternaryBoltzmannSum β v) ≤
        Real.log 3 - β * ternaryMin v := by
  obtain ⟨hlower, hupper⟩ := ternaryBoltzmannSum_bounds hβ v
  have hZ := ternaryBoltzmannSum_pos β v
  constructor
  · have hlog := Real.log_le_log (Real.exp_pos (-β * ternaryMin v)) hlower
    simpa using hlog
  · have hlog := Real.log_le_log hZ hupper
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.exp_ne_zero _)] at hlog
    simpa [sub_eq_add_neg] using hlog

/-- The cold two-profile Jensen information rate. -/
noncomputable def ternaryInformationRate
    (θ β : ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  let c := fun i => θ * x i + (1 - θ) * y i
  (-Real.log (ternaryBoltzmannSum β c) +
      θ * Real.log (ternaryBoltzmannSum β x) +
      (1 - θ) * Real.log (ternaryBoltzmannSum β y)) / β

/-- Uniform zero-temperature estimate.  Its error is independent of the
profiles and is exactly `log 3 / beta`. -/
theorem ternaryInformationRate_bounds
    {θ β : ℝ} (x y : Fin 3 → ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hβ : 0 < β)
    (hminx : ternaryMin x = 0) (hminy : ternaryMin y = 0) :
    let c := fun i => θ * x i + (1 - θ) * y i
    ternaryMin c - Real.log 3 / β ≤ ternaryInformationRate θ β x y ∧
      ternaryInformationRate θ β x y ≤ ternaryMin c + Real.log 3 / β := by
  dsimp only
  let c : Fin 3 → ℝ := fun i => θ * x i + (1 - θ) * y i
  obtain ⟨hcxLower, hcxUpper⟩ := log_ternaryBoltzmannSum_bounds hβ c
  obtain ⟨hxLower, hxUpper⟩ := log_ternaryBoltzmannSum_bounds hβ x
  obtain ⟨hyLower, hyUpper⟩ := log_ternaryBoltzmannSum_bounds hβ y
  rw [hminx, mul_zero] at hxLower hxUpper
  rw [hminy, mul_zero] at hyLower hyUpper
  simp only [sub_zero] at hxUpper hyUpper
  have hθ₀' : 0 ≤ θ := hθ₀.le
  have hθc : 0 ≤ 1 - θ := by linarith
  have hxWeightedLower : 0 ≤ θ * Real.log (ternaryBoltzmannSum β x) :=
    mul_nonneg hθ₀' hxLower
  have hyWeightedLower : 0 ≤ (1 - θ) * Real.log (ternaryBoltzmannSum β y) :=
    mul_nonneg hθc hyLower
  have hxWeightedUpper :
      θ * Real.log (ternaryBoltzmannSum β x) ≤ θ * Real.log 3 :=
    mul_le_mul_of_nonneg_left hxUpper hθ₀'
  have hyWeightedUpper :
      (1 - θ) * Real.log (ternaryBoltzmannSum β y) ≤
        (1 - θ) * Real.log 3 :=
    mul_le_mul_of_nonneg_left hyUpper hθc
  unfold ternaryInformationRate
  dsimp only
  constructor
  · apply (le_div_iff₀ hβ).2
    field_simp [hβ.ne']
    nlinarith
  · apply (div_le_iff₀ hβ).2
    field_simp [hβ.ne']
    nlinarith

/-- The cold information rate for a finite weighted family of ternary
profiles.  The weights are kept as data; normalization is a hypothesis of the
uniform bound below. -/
noncomputable def multiTernaryInformationRate
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) : ℝ :=
  let c := fun i => ∑ j, θ j * x j i
  (-Real.log (ternaryBoltzmannSum β c) +
      ∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j))) / β

/-- Multiway uniform zero-temperature estimate.  The error is still exactly
`log 3 / beta`, independently of the number of profiles, because the
partition-function errors are averaged by nonnegative weights summing to one.
This is the logarithmic form of equation (4.8) in the information-geometric
defect note. -/
theorem multiTernaryInformationRate_bounds
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) {β : ℝ} (x : ι → Fin 3 → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hθsum : ∑ j, θ j = 1) (hβ : 0 < β)
    (hmin : ∀ j, ternaryMin (x j) = 0) :
    let c := fun i => ∑ j, θ j * x j i
    ternaryMin c - Real.log 3 / β ≤
        multiTernaryInformationRate θ β x ∧
      multiTernaryInformationRate θ β x ≤
        ternaryMin c + Real.log 3 / β := by
  classical
  dsimp only
  let c : Fin 3 → ℝ := fun i => ∑ j, θ j * x j i
  obtain ⟨hcLower, hcUpper⟩ := log_ternaryBoltzmannSum_bounds hβ c
  have hxLower (j : ι) :
      0 ≤ Real.log (ternaryBoltzmannSum β (x j)) := by
    obtain ⟨hj, _⟩ := log_ternaryBoltzmannSum_bounds hβ (x j)
    rw [hmin j, mul_zero] at hj
    exact hj
  have hxUpper (j : ι) :
      Real.log (ternaryBoltzmannSum β (x j)) ≤ Real.log 3 := by
    obtain ⟨_, hj⟩ := log_ternaryBoltzmannSum_bounds hβ (x j)
    rw [hmin j, mul_zero, sub_zero] at hj
    exact hj
  have hweightedLower :
      0 ≤ ∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j)) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hθ j) (hxLower j)
  have hweightedUpper :
      (∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j))) ≤ Real.log 3 := by
    calc
      (∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j))) ≤
          ∑ j, θ j * Real.log 3 := by
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hxUpper j) (hθ j)
      _ = Real.log 3 := by rw [← Finset.sum_mul, hθsum, one_mul]
  unfold multiTernaryInformationRate
  dsimp only
  constructor
  · apply (le_div_iff₀ hβ).2
    field_simp [hβ.ne']
    nlinarith
  · apply (div_le_iff₀ hβ).2
    field_simp [hβ.ne']
    nlinarith

/-- The strictly positive Boltzmann probability of one ternary coordinate. -/
noncomputable def ternaryBoltzmannProbability
    (β : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  Real.exp (-β * v i) / ternaryBoltzmannSum β v

theorem ternaryBoltzmannProbability_pos
    (β : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) :
    0 < ternaryBoltzmannProbability β v i := by
  unfold ternaryBoltzmannProbability
  exact div_pos (Real.exp_pos _) (ternaryBoltzmannSum_pos β v)

theorem log_ternaryBoltzmannProbability
    (β : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) :
    Real.log (ternaryBoltzmannProbability β v i) =
      -β * v i - Real.log (ternaryBoltzmannSum β v) := by
  unfold ternaryBoltzmannProbability
  rw [Real.log_div (Real.exp_ne_zero _) (ternaryBoltzmannSum_pos β v).ne',
    Real.log_exp]

/-- Multiway overlap of positive Boltzmann laws, written in log coordinates.
For positive probabilities this is exactly
`sum_i product_j P_j(i) ^ theta_j`. -/
noncomputable def multiTernaryOverlap
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) : ℝ :=
  ∑ i, Real.exp
    (∑ j, θ j * Real.log (ternaryBoltzmannProbability β (x j) i))

/-- The same overlap in the literal weighted-geometric-mean notation used in
equation (4.8). -/
noncomputable def multiTernaryGeometricOverlap
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∏ j, (ternaryBoltzmannProbability β (x j) i) ^ (θ j)

theorem multiTernaryGeometricOverlap_eq_overlap
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) :
    multiTernaryGeometricOverlap θ β x = multiTernaryOverlap θ β x := by
  classical
  unfold multiTernaryGeometricOverlap multiTernaryOverlap
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [Real.rpow_def_of_pos
    (ternaryBoltzmannProbability_pos β (x _) i)]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

theorem multiTernaryOverlap_eq
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) :
    let c := fun i => ∑ j, θ j * x j i
    multiTernaryOverlap θ β x =
      Real.exp (-(∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j)))) *
        ternaryBoltzmannSum β c := by
  classical
  dsimp only
  let c : Fin 3 → ℝ := fun i => ∑ j, θ j * x j i
  let L : ℝ := ∑ j, θ j * Real.log (ternaryBoltzmannSum β (x j))
  have hexponent (i : Fin 3) :
      (∑ j, θ j * Real.log (ternaryBoltzmannProbability β (x j) i)) =
        -L + -β * c i := by
    simp_rw [log_ternaryBoltzmannProbability]
    change (∑ j, θ j * (-β * x j i -
      Real.log (ternaryBoltzmannSum β (x j)))) = -L + -β * c i
    dsimp only [L, c]
    have hdistrib :
        (∑ j, θ j * (-β * x j i -
          Real.log (ternaryBoltzmannSum β (x j)))) =
        ∑ j, (-β * (θ j * x j i) -
          θ j * Real.log (ternaryBoltzmannSum β (x j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hdistrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  unfold multiTernaryOverlap ternaryBoltzmannSum
  simp_rw [hexponent, Real.exp_add]
  rw [← Finset.mul_sum]
  dsimp only [L, c]
  simp only [ternaryBoltzmannSum]

theorem multiTernaryOverlap_pos
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (β : ℝ) (x : ι → Fin 3 → ℝ) :
    0 < multiTernaryOverlap θ β x := by
  unfold multiTernaryOverlap
  positivity

/-- Exact bridge from the literal overlap in (4.8) to the logarithmic rate
used above. -/
theorem neg_log_multiTernaryOverlap_div
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) {β : ℝ} (x : ι → Fin 3 → ℝ)
    (hβ : β ≠ 0) :
    -Real.log (multiTernaryOverlap θ β x) / β =
      multiTernaryInformationRate θ β x := by
  classical
  let c : Fin 3 → ℝ := fun i => ∑ j, θ j * x j i
  rw [multiTernaryOverlap_eq θ β x]
  rw [Real.log_mul (Real.exp_ne_zero _)
    (ternaryBoltzmannSum_pos β c).ne', Real.log_exp]
  unfold multiTernaryInformationRate
  dsimp only
  field_simp [hβ]
  ring

/-- Equation (4.8) itself: the literal multiway Boltzmann overlap has a
uniform cold-limit error `log 3 / beta`, independent of the finite number of
profiles. -/
theorem multiTernaryOverlap_cold_bound
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) {β : ℝ} (x : ι → Fin 3 → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hθsum : ∑ j, θ j = 1) (hβ : 0 < β)
    (hmin : ∀ j, ternaryMin (x j) = 0) :
    let c := fun i => ∑ j, θ j * x j i
    |(-Real.log (multiTernaryOverlap θ β x) / β) - ternaryMin c| ≤
      Real.log 3 / β := by
  dsimp only
  rw [neg_log_multiTernaryOverlap_div θ x hβ.ne']
  obtain ⟨hlower, hupper⟩ :=
    multiTernaryInformationRate_bounds θ x hθ hθsum hβ hmin
  rw [abs_le]
  constructor <;> linarith

/-- Literal weighted-geometric-mean form of equation (4.8). -/
theorem multiTernaryGeometricOverlap_cold_bound
    {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) {β : ℝ} (x : ι → Fin 3 → ℝ)
    (hθ : ∀ j, 0 ≤ θ j) (hθsum : ∑ j, θ j = 1) (hβ : 0 < β)
    (hmin : ∀ j, ternaryMin (x j) = 0) :
    let c := fun i => ∑ j, θ j * x j i
    |(-Real.log (multiTernaryGeometricOverlap θ β x) / β) -
        ternaryMin c| ≤ Real.log 3 / β := by
  rw [multiTernaryGeometricOverlap_eq_overlap]
  exact multiTernaryOverlap_cold_bound θ x hθ hθsum hβ hmin

end CleanLean.KL
