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

/-- Taking a positive `Q`-th root converts the retarded branch's rational
power comparison into its fractional-exponent form. -/
theorem le_rpow_div_sub_two_of_pow_le
    {x lam : ℝ} {P Q : ℕ}
    (hx : 0 ≤ x) (hlam : 0 ≤ lam) (hQ : 0 < Q)
    (hpow : x ^ Q ≤ lam ^ ((P : ℝ) - 2 * Q)) :
    x ≤ lam ^ ((P : ℝ) / Q - 2) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  apply (Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hlam _) hQR).mp
  rw [Real.rpow_natCast]
  rw [← Real.rpow_mul hlam]
  convert hpow using 1
  field_simp

/-- The analogous positive-root lemma for the advanced branch. -/
theorem le_rpow_div_sub_one_of_pow_le
    {x lam : ℝ} {P Q : ℕ}
    (hx : 0 ≤ x) (hlam : 0 ≤ lam) (hQ : 0 < Q)
    (hpow : x ^ Q ≤ lam ^ ((P : ℝ) - Q)) :
    x ≤ lam ^ ((P : ℝ) / Q - 1) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  apply (Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hlam _) hQR).mp
  rw [Real.rpow_natCast]
  rw [← Real.rpow_mul hlam]
  convert hpow using 1
  field_simp

/-- Soundness of the exact cross-multiplied retarded-weight comparison before
the final replacement of `P/Q` by `alpha`. -/
theorem div_le_rpow_div_sub_two_of_crossmul
    {A scaleL B scaleW P Q : ℕ}
    (hA : 0 < A) (hL : 0 < scaleL) (hW : 0 < scaleW) (hQ : 0 < Q)
    (hP : P ≤ 2 * Q)
    (hcross : B ^ Q * A ^ (2 * Q - P) ≤
      scaleW ^ Q * scaleL ^ (2 * Q - P)) :
    (B : ℝ) / scaleW ≤
      ((A : ℝ) / scaleL) ^ ((P : ℝ) / Q - 2) := by
  apply le_rpow_div_sub_two_of_pow_le
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hQ
  have hcrossR :
      (B : ℝ) ^ Q * (A : ℝ) ^ (2 * Q - P) ≤
        (scaleW : ℝ) ^ Q * (scaleL : ℝ) ^ (2 * Q - P) := by
    exact_mod_cast hcross
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hLpos : (0 : ℝ) < scaleL := by exact_mod_cast hL
  have hWpos : (0 : ℝ) < scaleW := by exact_mod_cast hW
  have hE : ((2 * Q - P : ℕ) : ℝ) = 2 * (Q : ℝ) - P := by
    rw [Nat.cast_sub hP]
    norm_num
  rw [div_pow]
  rw [show (P : ℝ) - 2 * Q = -((2 * Q - P : ℕ) : ℝ) by
    rw [hE]; ring]
  rw [Real.rpow_neg (div_nonneg hApos.le hLpos.le)]
  rw [Real.rpow_natCast, div_pow, inv_div]
  rw [div_le_div_iff₀ (pow_pos hWpos Q) (pow_pos hApos (2 * Q - P))]
  simpa [mul_comm] using hcrossR

/-- Soundness of the exact cross-multiplied advanced-weight comparison before
the final replacement of `P/Q` by `alpha`. -/
theorem div_le_rpow_div_sub_one_of_crossmul
    {A scaleL B scaleW P Q : ℕ}
    (_hA : 0 < A) (hL : 0 < scaleL) (hW : 0 < scaleW) (hQ : 0 < Q)
    (hP : Q ≤ P)
    (hcross : B ^ Q * scaleL ^ (P - Q) ≤
      A ^ (P - Q) * scaleW ^ Q) :
    (B : ℝ) / scaleW ≤
      ((A : ℝ) / scaleL) ^ ((P : ℝ) / Q - 1) := by
  apply le_rpow_div_sub_one_of_pow_le
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hQ
  have hcrossR :
      (B : ℝ) ^ Q * (scaleL : ℝ) ^ (P - Q) ≤
        (A : ℝ) ^ (P - Q) * (scaleW : ℝ) ^ Q := by
    exact_mod_cast hcross
  have hLpos : (0 : ℝ) < scaleL := by exact_mod_cast hL
  have hWpos : (0 : ℝ) < scaleW := by exact_mod_cast hW
  have hE : ((P - Q : ℕ) : ℝ) = (P : ℝ) - Q := by
    rw [Nat.cast_sub hP]
  rw [div_pow]
  rw [show (P : ℝ) - Q = ((P - Q : ℕ) : ℝ) by rw [hE]]
  rw [Real.rpow_natCast, div_pow]
  rw [div_le_div_iff₀ (pow_pos hWpos Q) (pow_pos hLpos (P - Q))]
  simpa [mul_comm] using hcrossR

/-- End-to-end soundness of the two stored branch-weight lower bounds.  This
is the analytic bridge from the certificate's Boolean integer checks to the
true irrational KL coefficients. -/
theorem branchWeightLower_of_checks
    {A scaleL B2 B8 scaleW P Q : ℕ}
    (hL : 0 < scaleL) (hW : 0 < scaleW) (hQ : 0 < Q)
    (hlam : scaleL < A)
    (halpha : checkAlphaLower P Q = true)
    (hdata : checkBranchWeightLowerData
      A scaleL B2 B8 scaleW P Q = true) :
    (B2 : ℝ) / scaleW ≤
        ((A : ℝ) / scaleL) ^ (alpha - 2) ∧
      (B8 : ℝ) / scaleW ≤
        ((A : ℝ) / scaleL) ^ (alpha - 1) := by
  rcases (checkBranchWeightLowerData_eq_true_iff
    A scaleL B2 B8 scaleW P Q).1 hdata with
    ⟨hQP, hP2, hcross2, hcross8⟩
  have hA : 0 < A := lt_trans hL hlam
  have hlamR : (1 : ℝ) < (A : ℝ) / scaleL := by
    rw [one_lt_div (by exact_mod_cast hL : (0 : ℝ) < scaleL)]
    exact_mod_cast hlam
  have hpa : (P : ℝ) / Q < alpha :=
    div_lt_alpha_of_check hQ halpha
  constructor
  · exact (div_le_rpow_div_sub_two_of_crossmul
      hA hL hW hQ hP2 hcross2).trans
      (Real.rpow_le_rpow_of_exponent_le hlamR.le (by linarith))
  · exact (div_le_rpow_div_sub_one_of_crossmul
      hA hL hW hQ hQP hcross8).trans
      (Real.rpow_le_rpow_of_exponent_le hlamR.le (by linarith))

end CleanLean.KL
