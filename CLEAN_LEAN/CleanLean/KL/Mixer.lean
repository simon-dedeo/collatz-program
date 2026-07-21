/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.LocalRenormalization

/-!
# Oscillation under a two-input branch mixer

Both KL branch equations have the form `p • transport + q • branchMinima`.
The absolute range of the output is bounded by the corresponding weighted
ranges.  Normalized oscillation therefore cannot exceed both complete input
oscillations, but it can increase relative to the transported fiber alone.
-/

namespace CleanLean.KL

noncomputable section

/-- Coordinatewise positive linear combination of two profiles. -/
def mix3 (p q : ℝ) (t b : Triple) : Triple := fun i => p * t i + q * b i

theorem pair_sub_le_range3 (x : Triple) (i j : Fin 3) :
    x i - x j ≤ max3 x - min3 x := by
  have hi : x i ≤ max3 x := by
    fin_cases i <;> simp [max3]
  have hj : min3 x ≤ x j := by
    fin_cases j <;> simp [min3]
  linarith

theorem range3_le_of_pair_bounds (x : Triple) (R : ℝ)
    (h : ∀ i j, x i - x j ≤ R) : max3 x - min3 x ≤ R := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h02 := h 0 2
  have h10 := h 1 0
  have h11 := h 1 1
  have h12 := h 1 2
  have h20 := h 2 0
  have h21 := h 2 1
  have h22 := h 2 2
  simp only [max3, min3, max_def, min_def]
  split <;> split <;> split <;> assumption

/-- Sharp absolute-range inequality for a positive two-input mixer. -/
theorem range_mix3_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (t b : Triple) :
    max3 (mix3 p q t b) - min3 (mix3 p q t b) ≤
      p * (max3 t - min3 t) + q * (max3 b - min3 b) := by
  apply range3_le_of_pair_bounds
  intro i j
  calc
    mix3 p q t b i - mix3 p q t b j =
        p * (t i - t j) + q * (b i - b j) := by simp [mix3]; ring
    _ ≤ p * (max3 t - min3 t) + q * (max3 b - min3 b) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pair_sub_le_range3 t i j) hp)
        (mul_le_mul_of_nonneg_left (pair_sub_le_range3 b i j) hq)

theorem mean3_mix3 (p q : ℝ) (t b : Triple) :
    mean3 (mix3 p q t b) = p * mean3 t + q * mean3 b := by
  simp [mean3, mix3]
  ring

/-- Flat transport profile used in the exact counterexample below. -/
def flatTriple : Triple := fun _ => 1

/-- Branch-minimum profile used in the exact counterexample below. -/
def branchCounterTriple : Triple := fun i => if i = 2 then 2 else 1

/-- Exact counterexample to the discarded claim that a retarded branch cannot
increase normalized oscillation relative to transport. -/
theorem retarded_mixer_counterexample :
    oscillation3 flatTriple = 0 ∧
      oscillation3 (mix3 (1 / 4) (3 / 4) flatTriple branchCounterTriple) = 3 / 5 ∧
      oscillation3 flatTriple <
        oscillation3 (mix3 (1 / 4) (3 / 4) flatTriple branchCounterTriple) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [oscillation3, mix3, max3, min3, mean3, flatTriple,
    branchCounterTriple, h02, h12]

end

end CleanLean.KL
