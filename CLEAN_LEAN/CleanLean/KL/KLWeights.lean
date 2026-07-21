/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.IrrationalWeights
import CleanLean.KL.OscillationIdentity

/-!
# The concrete KL weights and annealed root
-/

namespace CleanLean.KL

/-- The three coefficients in the reduced KL operator. -/
noncomputable def klWeights (lam : ℝ) : Weights ℝ where
  transport := lam ^ (-2 : ℝ)
  retarded := lam ^ (alpha - 2)
  advanced := lam ^ (alpha - 1)

/-- The averaged (min replaced by mean) scalar value. -/
noncomputable def annealedKL (lam : ℝ) : ℝ :=
  FiniteSystem.annealedValue (klWeights lam)

theorem annealedKL_apply (lam : ℝ) :
    annealedKL lam = lam ^ (-2 : ℝ) +
      (lam ^ (alpha - 2) + lam ^ (alpha - 1)) / 3 := by
  rfl

theorem one_lt_alpha : (1 : ℝ) < alpha := by
  simpa using (div_lt_alpha_of_pow_lt (P := 1) (Q := 1) (by norm_num) (by norm_num))

theorem alpha_lt_two : alpha < (2 : ℝ) := by
  simpa using (alpha_lt_div_of_pow_lt (P := 2) (Q := 1) (by norm_num) (by norm_num))

/-- The identity `2^(log₂ 3)=3`, proved from the definition rather than
accepted as a floating-point fact. -/
theorem two_rpow_alpha : (2 : ℝ) ^ alpha = 3 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hmul : Real.log 2 * alpha = Real.log 3 := by
    unfold alpha
    field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem two_rpow_alpha_add_one : (2 : ℝ) ^ (alpha + 1) = 6 := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), two_rpow_alpha, Real.rpow_one]
  norm_num

theorem annealedKL_two : annealedKL 2 = 1 := by
  rw [annealedKL_apply]
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_neg h2.le]
  norm_num only [Real.rpow_natCast, pow_succ, pow_zero, mul_one]
  rw [Real.rpow_sub h2, Real.rpow_sub h2]
  rw [two_rpow_alpha]
  norm_num

theorem klBranchWeightSum_nonneg {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ (klWeights lam).retarded + (klWeights lam).advanced := by
  exact add_nonneg (Real.rpow_nonneg hlam _) (Real.rpow_nonneg hlam _)

/-- A uniform bound on the coefficient multiplying the normalized defect.
The crude constant `5/2` is sufficient for the limit argument. -/
theorem klBranchWeightSum_le {lam : ℝ} (hlam : lam ∈ Set.Icc (1 : ℝ) 2) :
    (klWeights lam).retarded + (klWeights lam).advanced ≤ 5 / 2 := by
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam.1
  have hlamPos : 0 < lam := lt_of_lt_of_le (by norm_num) hlam.1
  have hret : lam ^ (alpha - 2) ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos hlam.1 (by linarith [alpha_lt_two])
  have hadv : lam ^ (alpha - 1) ≤ (3 / 2 : ℝ) := by
    calc
      lam ^ (alpha - 1) ≤ (2 : ℝ) ^ (alpha - 1) :=
        Real.rpow_le_rpow hlam0 hlam.2 (by linarith [one_lt_alpha])
      _ = 3 / 2 := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), two_rpow_alpha,
          Real.rpow_one]
  change lam ^ (alpha - 2) + lam ^ (alpha - 1) ≤ 5 / 2
  linarith

theorem deriv_annealedKL {x : ℝ} (hx : 0 < x) :
    deriv annealedKL x =
      (-2) * x ^ (-3 : ℝ) +
        ((alpha - 2) * x ^ (alpha - 3) +
          (alpha - 1) * x ^ (alpha - 2)) / 3 := by
  have h0 := Real.differentiableAt_rpow_const_of_ne (-2 : ℝ) hx.ne'
  have h2 := Real.differentiableAt_rpow_const_of_ne (alpha - 2) hx.ne'
  have h8 := Real.differentiableAt_rpow_const_of_ne (alpha - 1) hx.ne'
  have e0 : (-2 : ℝ) - 1 = -3 := by norm_num
  have e2 : alpha - 2 - 1 = alpha - 3 := by ring
  have e8 : alpha - 1 - 1 = alpha - 2 := by ring
  change deriv
    ((fun y : ℝ => y ^ (-2 : ℝ)) +
      (fun y : ℝ => ((fun z : ℝ => z ^ (alpha - 2)) +
        (fun z : ℝ => z ^ (alpha - 1))) y / 3)) x = _
  rw [deriv_add h0 ((h2.add h8).div_const 3), deriv_div_const,
    deriv_add h2 h8, Real.deriv_rpow_const, Real.deriv_rpow_const,
    Real.deriv_rpow_const, e0, e2, e8]

/-- The concrete annealed scalar is strictly decreasing on the KL interval.
This supplies the root-separation premise in `LimitBridge.lean`. -/
theorem annealedKL_strictAntiOn :
    StrictAntiOn annealedKL (Set.Icc (1 : ℝ) 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 : ℝ) 2)
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
    change ContinuousWithinAt
      (fun y : ℝ => y ^ (-2 : ℝ) +
        (y ^ (alpha - 2) + y ^ (alpha - 1)) / 3) (Set.Icc 1 2) x
    exact ((Real.continuousAt_rpow_const x (-2) (Or.inl hx0)).add
      (((Real.continuousAt_rpow_const x (alpha - 2) (Or.inl hx0)).add
        (Real.continuousAt_rpow_const x (alpha - 1) (Or.inl hx0))).div_const 3)).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [deriv_annealedKL hx0]
    have hA0 : 0 < alpha := lt_trans (by norm_num) one_lt_alpha
    have hA1 : 0 ≤ alpha - 1 := by linarith [one_lt_alpha]
    have hxA : x ^ alpha ≤ (3 : ℝ) := by
      calc
        x ^ alpha ≤ (2 : ℝ) ^ alpha :=
          Real.rpow_le_rpow hx0.le hx.2.le hA0.le
        _ = 3 := two_rpow_alpha
    have hxA1 : x ^ (alpha + 1) ≤ (6 : ℝ) := by
      calc
        x ^ (alpha + 1) ≤ (2 : ℝ) ^ (alpha + 1) :=
          Real.rpow_le_rpow hx0.le hx.2.le (by linarith [one_lt_alpha])
        _ = 6 := two_rpow_alpha_add_one
    have hneg : (alpha - 2) * x ^ alpha ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [alpha_lt_two])
        (Real.rpow_pos_of_pos hx0 alpha).le
    have hadv : (alpha - 1) * x ^ (alpha + 1) ≤ (alpha - 1) * 6 :=
      mul_le_mul_of_nonneg_left hxA1 hA1
    have hbracket :
        -2 + ((alpha - 2) * x ^ alpha +
          (alpha - 1) * x ^ (alpha + 1)) / 3 < 0 := by
      nlinarith [alpha_lt_two]
    have hfactor : 0 < x ^ (-3 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hrewrite :
        (-2) * x ^ (-3 : ℝ) +
            ((alpha - 2) * x ^ (alpha - 3) +
              (alpha - 1) * x ^ (alpha - 2)) / 3 =
          x ^ (-3 : ℝ) *
            (-2 + ((alpha - 2) * x ^ alpha +
              (alpha - 1) * x ^ (alpha + 1)) / 3) := by
      have hpowA : x ^ (alpha - 3) = x ^ (-3 : ℝ) * x ^ alpha := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hpowA1 : x ^ (alpha - 2) = x ^ (-3 : ℝ) * x ^ (alpha + 1) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      rw [hpowA, hpowA1]
      ring
    rw [hrewrite]
    exact mul_neg_of_pos_of_neg hfactor hbracket

end CleanLean.KL
