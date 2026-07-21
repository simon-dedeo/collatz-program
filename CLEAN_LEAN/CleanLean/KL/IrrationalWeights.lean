/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# The exact rational lower bound for `log₂ 3`

The large KL certificates store integers `P,Q` and require the checker to
recompute `2^P < 3^Q`.  This file proves that this finite integer inequality
really implies `P/Q < log₂ 3`.
-/

namespace CleanLean.KL

/-- The exponent `α = log₂ 3` used in the KL inequalities. -/
noncomputable def alpha : ℝ := Real.log 3 / Real.log 2

/-- Executable integer check for a proposed lower convergent to `α`. -/
def checkAlphaLower (P Q : ℕ) : Bool := decide (2 ^ P < 3 ^ Q)

/-- Executable integer check for a proposed upper convergent to `α`. -/
def checkAlphaUpper (P Q : ℕ) : Bool := decide (3 ^ Q < 2 ^ P)

theorem checkAlphaLower_eq_true_iff (P Q : ℕ) :
    checkAlphaLower P Q = true ↔ 2 ^ P < 3 ^ Q := by
  simp [checkAlphaLower]

theorem checkAlphaUpper_eq_true_iff (P Q : ℕ) :
    checkAlphaUpper P Q = true ↔ 3 ^ Q < 2 ^ P := by
  simp [checkAlphaUpper]

/-- The pure integer comparison used by the certificate format is sound. -/
theorem div_lt_alpha_of_pow_lt {P Q : ℕ} (hQ : 0 < Q)
    (hpow : 2 ^ P < 3 ^ Q) :
    (P : ℝ) / Q < alpha := by
  have hpowR : (2 : ℝ) ^ P < (3 : ℝ) ^ Q := by exact_mod_cast hpow
  have hlog : Real.log ((2 : ℝ) ^ P) < Real.log ((3 : ℝ) ^ Q) :=
    Real.strictMonoOn_log
      (by simpa only [Set.mem_Ioi] using pow_pos (by norm_num : (0 : ℝ) < 2) P)
      (by simpa only [Set.mem_Ioi] using pow_pos (by norm_num : (0 : ℝ) < 3) Q)
      hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold alpha
  rw [div_lt_div_iff₀ hQR hlog2]
  simpa [mul_comm] using hlog

theorem div_lt_alpha_of_check {P Q : ℕ} (hQ : 0 < Q)
    (hcheck : checkAlphaLower P Q = true) :
    (P : ℝ) / Q < alpha :=
  div_lt_alpha_of_pow_lt hQ ((checkAlphaLower_eq_true_iff P Q).1 hcheck)

/-- The reversed integer comparison gives the upper logarithmic bound used
by the portable tilted-pressure certificate. -/
theorem alpha_lt_div_of_pow_lt {P Q : ℕ} (hQ : 0 < Q)
    (hpow : 3 ^ Q < 2 ^ P) :
    alpha < (P : ℝ) / Q := by
  have hpowR : (3 : ℝ) ^ Q < (2 : ℝ) ^ P := by exact_mod_cast hpow
  have hlog : Real.log ((3 : ℝ) ^ Q) < Real.log ((2 : ℝ) ^ P) :=
    Real.strictMonoOn_log
      (by simpa only [Set.mem_Ioi] using pow_pos (by norm_num : (0 : ℝ) < 3) Q)
      (by simpa only [Set.mem_Ioi] using pow_pos (by norm_num : (0 : ℝ) < 2) P)
      hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold alpha
  rw [div_lt_div_iff₀ hlog2 hQR]
  simpa [mul_comm] using hlog

theorem alpha_lt_div_of_check {P Q : ℕ} (hQ : 0 < Q)
    (hcheck : checkAlphaUpper P Q = true) :
    alpha < (P : ℝ) / Q :=
  alpha_lt_div_of_pow_lt hQ ((checkAlphaUpper_eq_true_iff P Q).1 hcheck)

/-- Exact integer checks stored for the two irrational branch-weight lower
bounds.  The exponents use natural subtraction, so the range conditions are
included explicitly. -/
def checkBranchWeightLowerData
    (A scaleL B2 B8 scaleW P Q : ℕ) : Bool :=
  decide
    (Q ≤ P ∧ P ≤ 2 * Q ∧
      B2 ^ Q * A ^ (2 * Q - P) ≤ scaleW ^ Q * scaleL ^ (2 * Q - P) ∧
      B8 ^ Q * scaleL ^ (P - Q) ≤ A ^ (P - Q) * scaleW ^ Q)

theorem checkBranchWeightLowerData_eq_true_iff
    (A scaleL B2 B8 scaleW P Q : ℕ) :
    checkBranchWeightLowerData A scaleL B2 B8 scaleW P Q = true ↔
      Q ≤ P ∧ P ≤ 2 * Q ∧
        B2 ^ Q * A ^ (2 * Q - P) ≤ scaleW ^ Q * scaleL ^ (2 * Q - P) ∧
        B8 ^ Q * scaleL ^ (P - Q) ≤ A ^ (P - Q) * scaleW ^ Q := by
  simp [checkBranchWeightLowerData]

end CleanLean.KL
