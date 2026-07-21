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

theorem ternaryMin_le (z : Fin 3 → ℝ) (d : Fin 3) : ternaryMin z ≤ z d := by
  fin_cases d <;> simp [ternaryMin]

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

end CleanLean.KL
