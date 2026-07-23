/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterGeometricMahler

/-!
# A rational outward-budget obstruction for KL words

The only positive Krasikov--Lagarias time increment is the class-8 chord.
The continued-fraction upper bound `log_2(3) < 65/41` therefore turns a
positive total increment into an exact integer branch-and-bound inequality.

This is only a necessary leading-multiplier condition.  It says nothing about
the affine constants, residue legality, or closure of a proposed word.
-/

namespace KontoroC
namespace KLWordBudget

/-- The certified power comparison gives the rational upper bound used by
the mixed-word budget. -/
theorem log_three_div_log_two_lt_sixtyFive_div_fortyOne :
    Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 41 < (2 : ℝ) ^ 65 := by
    exact_mod_cast
      EtherCounterAperiodic.TernaryCoreOrbit.three_pow_41_lt_two_pow_65
  have hlogpow : Real.log ((3 : ℝ) ^ 41) < Real.log ((2 : ℝ) ^ 65) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  norm_num at hlogpow
  apply (div_lt_iff₀ hlog2).2
  have h : Real.log 3 < (65 * Real.log 2) / 41 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 41)).2
    nlinarith
  calc
    Real.log 3 < (65 * Real.log 2) / 41 := h
    _ = (65 / 41) * Real.log 2 := by ring

/-- QM129: every KL predecessor word with positive total time shift uses
strictly more than `17*n2 + 82*ns` class-8 budget units. -/
theorem positive_shift_forces_classEight_budget
    (n8 n2 ns : ℕ)
    (hpositive :
      0 < ((n8 + n2 : ℕ) : ℝ) * (Real.log 3 / Real.log 2) -
        ((n8 + 2 * n2 + 2 * ns : ℕ) : ℝ)) :
    17 * n2 + 82 * ns < 24 * n8 := by
  have halpha := log_three_div_log_two_lt_sixtyFive_div_fortyOne
  have hsum_nonneg : (0 : ℝ) ≤ ((n8 + n2 : ℕ) : ℝ) := by positivity
  have hupper :
      ((n8 + n2 : ℕ) : ℝ) * (Real.log 3 / Real.log 2) ≤
        ((n8 + n2 : ℕ) : ℝ) * ((65 : ℝ) / 41) :=
    mul_le_mul_of_nonneg_left halpha.le hsum_nonneg
  have hreal :
      ((17 * n2 + 82 * ns : ℕ) : ℝ) < ((24 * n8 : ℕ) : ℝ) := by
    push_cast at hpositive hupper ⊢
    nlinarith
  exact_mod_cast hreal

end KLWordBudget
end KontoroC
