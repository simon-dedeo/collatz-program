/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteLimit

/-!
# Quadratic defect growth implies the KL endpoint

This file isolates the exact scalar consequence of the selected iterated-
minimum conjecture.  It does not prove the conjectural quadratic inequality.
If a positive profile has `n` successive stages satisfying

`e (j+1) >= e j + (3/2) * (e j)^2`,

then its initial defect is at most `5 / (5 + 3*n)`.  Thus a family with an
unbounded number of such stages has vanishing initial defect, and the existing
oscillation identity forces its KL parameters to converge to two.
-/

namespace CleanLean.KL

/-- One quadratic-growth step drops the reciprocal by at least `3/5`.
The upper bound is needed only for the earlier defect. -/
theorem three_fifths_le_reciprocal_drop
    {e f : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hstep : e + (3 / 2 : ℝ) * e ^ 2 ≤ f) :
    (3 / 5 : ℝ) ≤ 1 / e - 1 / f := by
  have hf0 : 0 < f := by
    have hquad : 0 ≤ (3 / 2 : ℝ) * e ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg e)
    exact lt_of_lt_of_le he0 ((le_add_of_nonneg_right hquad).trans hstep)
  have hfactor : 0 ≤ 1 - (3 / 5 : ℝ) * e := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hstep hfactor
  have hcubic : 0 ≤ e ^ 2 * (1 - e) :=
    mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he1)
  have hcross : (3 / 5 : ℝ) * e * f ≤ f - e := by
    nlinarith
  rw [show 1 / e - 1 / f = (f - e) / (e * f) by
    field_simp [he0.ne', hf0.ne']]
  exact (le_div_iff₀ (mul_pos he0 hf0)).2 (by simpa [mul_assoc] using hcross)

/-- Reciprocal telescoping through `n` quadratic-growth steps. -/
theorem reciprocal_drop_sum
    (e : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j < n, e j ≤ 1)
    (hstep : ∀ j < n,
      e j + (3 / 2 : ℝ) * (e j) ^ 2 ≤ e (j + 1)) :
    (3 / 5 : ℝ) * n ≤ 1 / e 0 - 1 / e n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' : (3 / 5 : ℝ) * n ≤ 1 / e 0 - 1 / e n := by
        apply ih
        · intro j hj
          exact hpos j (by omega)
        · intro j hj
          exact hone j (by omega)
        · intro j hj
          exact hstep j (by omega)
      have hlast : (3 / 5 : ℝ) ≤ 1 / e n - 1 / e (n + 1) :=
        three_fifths_le_reciprocal_drop
          (hpos n (by omega)) (hone n (by omega)) (hstep n (by omega))
      rw [Nat.cast_succ]
      calc
        (3 / 5 : ℝ) * ((n : ℝ) + 1) =
            (3 / 5 : ℝ) * n + 3 / 5 := by ring
        _ ≤ (1 / e 0 - 1 / e n) +
            (1 / e n - 1 / e (n + 1)) := add_le_add ih' hlast
        _ = 1 / e 0 - 1 / e (n + 1) := by ring

/-- The finite bound obtained by reciprocal telescoping. -/
theorem initial_defect_le_of_quadratic_growth
    (e : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j ≤ n, e j ≤ 1)
    (hstep : ∀ j < n,
      e j + (3 / 2 : ℝ) * (e j) ^ 2 ≤ e (j + 1)) :
    e 0 ≤ 5 / (5 + 3 * n : ℝ) := by
  have htel := reciprocal_drop_sum e n hpos
    (fun j hj => hone j hj.le) hstep
  have hterminal : (1 : ℝ) ≤ 1 / e n := by
    rw [le_div_iff₀ (hpos n le_rfl)]
    simpa using hone n le_rfl
  have hrecip : (5 + 3 * n : ℝ) / 5 ≤ 1 / e 0 := by
    calc
      (5 + 3 * n : ℝ) / 5 = 1 + (3 / 5 : ℝ) * n := by ring
      _ ≤ 1 / e n + (3 / 5 : ℝ) * n :=
        add_le_add hterminal le_rfl
      _ ≤ 1 / e 0 := by linarith
  have he0 := hpos 0 (Nat.zero_le n)
  have hden : (0 : ℝ) < 5 + 3 * n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrecip he0.le
  have hcancel : e 0 * (1 / e 0) = 1 := by
    field_simp [he0.ne']
  rw [hcancel] at hmul
  apply (le_div_iff₀ hden).2
  nlinarith

/-- A triangular family with one more quadratic stage at each index has
vanishing initial defect. -/
theorem initial_defect_tendsto_zero_of_quadratic_growth
    (e : ℕ → ℕ → ℝ)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hstep : ∀ k j, j < k →
      e k j + (3 / 2 : ℝ) * (e k j) ^ 2 ≤ e k (j + 1)) :
    Filter.Tendsto (fun k => e k 0) Filter.atTop (nhds 0) := by
  have hbound : ∀ k, e k 0 ≤ 5 / (5 + 3 * k : ℝ) := by
    intro k
    exact initial_defect_le_of_quadratic_growth (e k) k
      (hpos k) (hone k) (hstep k)
  have hupper : Filter.Tendsto (fun k : ℕ => 5 / (5 + 3 * k : ℝ))
      Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun k : ℕ => (5 + 3 * k : ℝ))
        Filter.atTop Filter.atTop := by
      have hmul : Filter.Tendsto (fun k : ℕ => (3 : ℝ) * k)
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (r := (3 : ℝ)) (by norm_num)
          tendsto_natCast_atTop_atTop
      simpa [add_comm] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (5 : ℝ) hmul
    simpa using tendsto_const_nhds.div_atTop hden
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k => (hpos k 0 (Nat.zero_le k)).le
  · exact Filter.Eventually.of_forall hbound
  · exact hupper

/-- The selected iterated-minimum conjecture, expressed only through its
scalar defects, is sufficient for `lambda_k -> 2`.  The hypothesis `hidentity`
is the exact fixed-vector oscillation identity already proved elsewhere. -/
theorem klLambda_tendsto_two_of_quadratic_defect_growth
    (lam : ℕ → ℝ) (e : ℕ → ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hstep : ∀ k j, j < k →
      e k j + (3 / 2 : ℝ) * (e k j) ^ 2 ≤ e k (j + 1))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * e k 0) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  apply klLambda_tendsto_two_of_defect lam (fun k => e k 0) hlam
  · intro k
    exact (hpos k 0 (Nat.zero_le k)).le
  · exact initial_defect_tendsto_zero_of_quadratic_growth e hpos hone hstep
  · exact hidentity

end CleanLean.KL
