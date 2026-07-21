/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.LocalRenormalization

/-!
# The ternary cold power mean

This file formalizes the dimension-free scalar sandwich used by the softened
KL route.  For `beta > 0`, the order-`-beta` mean of three positive numbers
lies between their minimum and `3^(1/beta)` times that minimum.
-/

namespace CleanLean.KL

noncomputable section

/-- The averaged negative moment entering the cold power mean. -/
def ternaryColdMoment (beta : ℝ) (x : Triple) : ℝ :=
  ((x 0) ^ (-beta) + (x 1) ^ (-beta) + (x 2) ^ (-beta)) / 3

/-- The normalized power mean of order `-beta` on three positive inputs. -/
def ternaryColdMean (beta : ℝ) (x : Triple) : ℝ :=
  (ternaryColdMoment beta x) ^ (-1 / beta)

private theorem min3_pos {x : Triple} (hx : ∀ i, 0 < x i) : 0 < min3 x := by
  simp only [min3]
  exact lt_min (hx 0) (lt_min (hx 1) (hx 2))

private theorem rpow_neg_beta_rpow_neg_inv_beta
    {m beta : ℝ} (hm : 0 < m) (hbeta : 0 < beta) :
    (m ^ (-beta)) ^ (-1 / beta) = m := by
  rw [← Real.rpow_mul hm.le]
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  convert Real.rpow_one m using 1
  field_simp

/-- A cold power mean is at least the minimum. -/
theorem min3_le_ternaryColdMean
    {beta : ℝ} {x : Triple} (hbeta : 0 < beta)
    (hx : ∀ i, 0 < x i) :
    min3 x ≤ ternaryColdMean beta x := by
  let m := min3 x
  let Z := ((x 0) ^ (-beta) + (x 1) ^ (-beta) +
    (x 2) ^ (-beta)) / 3
  have hm : 0 < m := min3_pos hx
  have hnegBeta : -beta ≤ 0 := by linarith
  have hm0 : m ≤ x 0 := min_le_left _ _
  have hm1 : m ≤ x 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hm2 : m ≤ x 2 := (min_le_right _ _).trans (min_le_right _ _)
  have h0 : (x 0) ^ (-beta) ≤ m ^ (-beta) :=
    Real.rpow_le_rpow_of_nonpos hm hm0 hnegBeta
  have h1 : (x 1) ^ (-beta) ≤ m ^ (-beta) :=
    Real.rpow_le_rpow_of_nonpos hm hm1 hnegBeta
  have h2 : (x 2) ^ (-beta) ≤ m ^ (-beta) :=
    Real.rpow_le_rpow_of_nonpos hm hm2 hnegBeta
  have hx0Pow : 0 < (x 0) ^ (-beta) := Real.rpow_pos_of_pos (hx 0) _
  have hx1Pow : 0 < (x 1) ^ (-beta) := Real.rpow_pos_of_pos (hx 1) _
  have hx2Pow : 0 < (x 2) ^ (-beta) := Real.rpow_pos_of_pos (hx 2) _
  have hZpos : 0 < Z := by
    dsimp only [Z]
    nlinarith
  have hZle : Z ≤ m ^ (-beta) := by
    dsimp only [Z]
    nlinarith
  have hq : -1 / beta ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hbeta.le
  have hpow : (m ^ (-beta)) ^ (-1 / beta) ≤ Z ^ (-1 / beta) :=
    Real.rpow_le_rpow_of_nonpos hZpos hZle hq
  rw [rpow_neg_beta_rpow_neg_inv_beta hm hbeta] at hpow
  simpa only [ternaryColdMean, ternaryColdMoment, Z] using hpow

/-- A cold power mean is at most `3^(1/beta)` times the minimum. -/
theorem ternaryColdMean_le_three_rpow_mul_min3
    {beta : ℝ} {x : Triple} (hbeta : 0 < beta)
    (hx : ∀ i, 0 < x i) :
    ternaryColdMean beta x ≤ 3 ^ (1 / beta) * min3 x := by
  let m := min3 x
  let Z := ((x 0) ^ (-beta) + (x 1) ^ (-beta) +
    (x 2) ^ (-beta)) / 3
  have hm : 0 < m := min3_pos hx
  have hmPow : 0 < m ^ (-beta) := Real.rpow_pos_of_pos hm _
  have hx0Pow : 0 < (x 0) ^ (-beta) := Real.rpow_pos_of_pos (hx 0) _
  have hx1Pow : 0 < (x 1) ^ (-beta) := Real.rpow_pos_of_pos (hx 1) _
  have hx2Pow : 0 < (x 2) ^ (-beta) := Real.rpow_pos_of_pos (hx 2) _
  have hZpos : 0 < Z := by
    dsimp only [Z]
    nlinarith
  have hminTerm : m ^ (-beta) ≤
      (x 0) ^ (-beta) + (x 1) ^ (-beta) + (x 2) ^ (-beta) := by
    rcases min_choice (x 0) (min (x 1) (x 2)) with h0 | h12
    · have hm0 : m = x 0 := h0
      rw [hm0]
      nlinarith
    · rcases min_choice (x 1) (x 2) with h1 | h2
      · have hm1 : m = x 1 := h12.trans h1
        rw [hm1]
        nlinarith
      · have hm2 : m = x 2 := h12.trans h2
        rw [hm2]
        nlinarith
  have hlower : m ^ (-beta) / 3 ≤ Z := by
    dsimp only [Z]
    linarith
  have hbase : 0 < m ^ (-beta) / 3 := div_pos hmPow (by norm_num)
  have hq : -1 / beta ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hbeta.le
  have hpow : Z ^ (-1 / beta) ≤
      (m ^ (-beta) / 3) ^ (-1 / beta) :=
    Real.rpow_le_rpow_of_nonpos hbase hlower hq
  have hcollapse : (m ^ (-beta) / 3) ^ (-1 / beta) =
      3 ^ (1 / beta) * m := by
    rw [Real.div_rpow hmPow.le (by norm_num : (0 : ℝ) ≤ 3)]
    rw [rpow_neg_beta_rpow_neg_inv_beta hm hbeta]
    rw [show (-1 / beta : ℝ) = -(1 / beta) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    have hthree : 0 < (3 : ℝ) ^ (1 / beta) :=
      Real.rpow_pos_of_pos (by norm_num) _
    field_simp [hthree.ne']
  rw [hcollapse] at hpow
  simpa only [ternaryColdMean, ternaryColdMoment, Z] using hpow

theorem ternaryColdMean_bounds
    {beta : ℝ} {x : Triple} (hbeta : 0 < beta)
    (hx : ∀ i, 0 < x i) :
    min3 x ≤ ternaryColdMean beta x ∧
      ternaryColdMean beta x ≤ 3 ^ (1 / beta) * min3 x :=
  ⟨min3_le_ternaryColdMean hbeta hx,
    ternaryColdMean_le_three_rpow_mul_min3 hbeta hx⟩

end

end CleanLean.KL
