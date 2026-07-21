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

The coefficient `3/2` is not essential for the endpoint: this file also
proves the same conclusion from `e (j+1) ≥ e j + a * (e j)^2` for any fixed
`a > 0`.  This weaker interface is the one relevant to pressure arguments
that may not recover the empirically sharp constant.
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

/-- General form of the reciprocal-drop estimate.  Any fixed positive
quadratic coefficient gives a dimension-free reciprocal gain. -/
theorem coefficient_div_one_add_le_reciprocal_drop
    {a e f : ℝ} (ha : 0 < a) (he0 : 0 < e) (he1 : e ≤ 1)
    (hstep : e + a * e ^ 2 ≤ f) :
    a / (1 + a) ≤ 1 / e - 1 / f := by
  have hdena : 0 < 1 + a := by linarith
  have hc0 : 0 ≤ a / (1 + a) := (div_nonneg ha.le hdena.le)
  have hcle : a / (1 + a) ≤ 1 := by
    exact (div_le_one hdena).2 (by linarith)
  have hf0 : 0 < f := by
    have hquad : 0 ≤ a * e ^ 2 := mul_nonneg ha.le (sq_nonneg e)
    exact lt_of_lt_of_le he0 ((le_add_of_nonneg_right hquad).trans hstep)
  have hfactor : 0 ≤ 1 - (a / (1 + a)) * e := by
    have hmul : (a / (1 + a)) * e ≤ 1 * 1 :=
      mul_le_mul hcle he1 he0.le zero_le_one
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hstep hfactor
  have hratio : (a / (1 + a)) * (1 + a) = a := by
    field_simp [hdena.ne']
  have hdiff : a - a / (1 + a) = a * (a / (1 + a)) := by
    field_simp [hdena.ne']
    ring
  have hcubic : 0 ≤ e ^ 2 * (1 - e) :=
    mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he1)
  have hscaledCubic :
      0 ≤ (a * (a / (1 + a))) * (e ^ 2 * (1 - e)) :=
    mul_nonneg (mul_nonneg ha.le hc0) hcubic
  have hbase : e ≤ (e + a * e ^ 2) *
      (1 - (a / (1 + a)) * e) := by
    nlinarith
  have hthrough : e ≤ f * (1 - (a / (1 + a)) * e) :=
    hbase.trans hmul
  have hcross : (a / (1 + a)) * e * f ≤ f - e := by
    nlinarith
  rw [show 1 / e - 1 / f = (f - e) / (e * f) by
    field_simp [he0.ne', hf0.ne']]
  exact (le_div_iff₀ (mul_pos he0 hf0)).2 (by simpa [mul_assoc] using hcross)

/-- Reciprocal telescoping with an arbitrary positive quadratic
coefficient. -/
theorem reciprocal_drop_sum_with
    (a : ℝ) (e : ℕ → ℝ) (n : ℕ) (ha : 0 < a)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j < n, e j ≤ 1)
    (hstep : ∀ j < n, e j + a * (e j) ^ 2 ≤ e (j + 1)) :
    (a / (1 + a)) * n ≤ 1 / e 0 - 1 / e n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' : (a / (1 + a)) * n ≤ 1 / e 0 - 1 / e n := by
        apply ih
        · intro j hj
          exact hpos j (by omega)
        · intro j hj
          exact hone j (by omega)
        · intro j hj
          exact hstep j (by omega)
      have hlast : a / (1 + a) ≤ 1 / e n - 1 / e (n + 1) :=
        coefficient_div_one_add_le_reciprocal_drop ha
          (hpos n (by omega)) (hone n (by omega)) (hstep n (by omega))
      rw [Nat.cast_succ]
      calc
        (a / (1 + a)) * ((n : ℝ) + 1) =
            (a / (1 + a)) * n + a / (1 + a) := by ring
        _ ≤ (1 / e 0 - 1 / e n) +
            (1 / e n - 1 / e (n + 1)) := add_le_add ih' hlast
        _ = 1 / e 0 - 1 / e (n + 1) := by ring

/-- Finite initial-defect bound for any fixed positive quadratic gain. -/
theorem initial_defect_le_of_quadratic_growth_with
    (a : ℝ) (e : ℕ → ℝ) (n : ℕ) (ha : 0 < a)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j ≤ n, e j ≤ 1)
    (hstep : ∀ j < n, e j + a * (e j) ^ 2 ≤ e (j + 1)) :
    e 0 ≤ 1 / (1 + (a / (1 + a)) * n) := by
  have htel := reciprocal_drop_sum_with a e n ha hpos
    (fun j hj => hone j hj.le) hstep
  have hterminal : (1 : ℝ) ≤ 1 / e n := by
    rw [le_div_iff₀ (hpos n le_rfl)]
    simpa using hone n le_rfl
  have hrecip : 1 + (a / (1 + a)) * n ≤ 1 / e 0 := by
    linarith
  have hdena : 0 < 1 + a := by linarith
  have hc0 : 0 ≤ a / (1 + a) := div_nonneg ha.le hdena.le
  have hden : 0 < 1 + (a / (1 + a)) * n := by positivity
  have he0 := hpos 0 (Nat.zero_le n)
  apply (le_div_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hrecip he0.le
  have hcancel : e 0 * (1 / e 0) = 1 := by
    field_simp [he0.ne']
  nlinarith

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

/-- A triangular family with any fixed positive quadratic coefficient has
vanishing initial defect. -/
theorem initial_defect_tendsto_zero_of_quadratic_growth_with
    (a : ℝ) (e : ℕ → ℕ → ℝ) (ha : 0 < a)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hstep : ∀ k j, j < k →
      e k j + a * (e k j) ^ 2 ≤ e k (j + 1)) :
    Filter.Tendsto (fun k => e k 0) Filter.atTop (nhds 0) := by
  let c := a / (1 + a)
  have hdena : 0 < 1 + a := by linarith
  have hc : 0 < c := div_pos ha hdena
  have hbound : ∀ k, e k 0 ≤ 1 / (1 + c * k) := by
    intro k
    exact initial_defect_le_of_quadratic_growth_with a (e k) k ha
      (hpos k) (hone k) (hstep k)
  have hupper : Filter.Tendsto (fun k : ℕ => 1 / (1 + c * k : ℝ))
      Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun k : ℕ => (1 + c * k : ℝ))
        Filter.atTop Filter.atTop := by
      have hmul : Filter.Tendsto (fun k : ℕ => c * (k : ℝ))
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (r := c) hc
          tendsto_natCast_atTop_atTop
      simpa [add_comm] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) hmul
    have honeT : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    simpa [one_div] using honeT.div_atTop hden
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k => (hpos k 0 (Nat.zero_le k)).le
  · exact Filter.Eventually.of_forall hbound
  · exact hupper

/-- Stage-dependent quadratic gains are sufficient when they have a single
positive lower bound.  This is the natural interface for a pressure estimate
whose local constant varies with the level and coarse-minimum stage. -/
theorem initial_defect_tendsto_zero_of_uniform_quadratic_growth
    (a₀ : ℝ) (a : ℕ → ℕ → ℝ) (e : ℕ → ℕ → ℝ) (ha₀ : 0 < a₀)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hcoeff : ∀ k j, j < k → a₀ ≤ a k j)
    (hstep : ∀ k j, j < k →
      e k j + a k j * (e k j) ^ 2 ≤ e k (j + 1)) :
    Filter.Tendsto (fun k => e k 0) Filter.atTop (nhds 0) := by
  apply initial_defect_tendsto_zero_of_quadratic_growth_with
    a₀ e ha₀ hpos hone
  intro k j hj
  have hmul : a₀ * (e k j) ^ 2 ≤ a k j * (e k j) ^ 2 :=
    mul_le_mul_of_nonneg_right (hcoeff k j hj) (sq_nonneg (e k j))
  nlinarith [hstep k j hj]

/-- Reciprocal telescoping in the precision-indexed direction.  Here `e n`
is the finest defect and `e 0` the final coarse defect, so every coarse step
appears with the reverse inequality from the stage-indexed formulation. -/
theorem reverse_reciprocal_drop_sum_with
    (a : ℝ) (e : ℕ → ℝ) (n : ℕ) (ha : 0 < a)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j ≤ n, e j ≤ 1)
    (hstep : ∀ j < n, e (j + 1) + a * (e (j + 1)) ^ 2 ≤ e j) :
    (a / (1 + a)) * n ≤ 1 / e n - 1 / e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' : (a / (1 + a)) * n ≤ 1 / e n - 1 / e 0 := by
        apply ih
        · intro j hj
          exact hpos j (by omega)
        · intro j hj
          exact hone j (by omega)
        · intro j hj
          exact hstep j (by omega)
      have hlast : a / (1 + a) ≤ 1 / e (n + 1) - 1 / e n :=
        coefficient_div_one_add_le_reciprocal_drop ha
          (hpos (n + 1) (by omega)) (hone (n + 1) (by omega))
          (hstep n (by omega))
      rw [Nat.cast_succ]
      calc
        (a / (1 + a)) * ((n : ℝ) + 1) =
            (a / (1 + a)) * n + a / (1 + a) := by ring
        _ ≤ (1 / e n - 1 / e 0) +
            (1 / e (n + 1) - 1 / e n) := add_le_add ih' hlast
        _ = 1 / e (n + 1) - 1 / e 0 := by ring

/-- Finite bound in the natural precision indexing: the finest defect is at
index `n`, and repeated coarse-minimum gains force it to be `O(1/n)`. -/
theorem terminal_defect_le_of_reverse_quadratic_growth_with
    (a : ℝ) (e : ℕ → ℝ) (n : ℕ) (ha : 0 < a)
    (hpos : ∀ j ≤ n, 0 < e j)
    (hone : ∀ j ≤ n, e j ≤ 1)
    (hstep : ∀ j < n, e (j + 1) + a * (e (j + 1)) ^ 2 ≤ e j) :
    e n ≤ 1 / (1 + (a / (1 + a)) * n) := by
  have htel := reverse_reciprocal_drop_sum_with a e n ha hpos hone hstep
  have hcoarse : (1 : ℝ) ≤ 1 / e 0 := by
    rw [le_div_iff₀ (hpos 0 (Nat.zero_le n))]
    simpa using hone 0 (Nat.zero_le n)
  have hrecip : 1 + (a / (1 + a)) * n ≤ 1 / e n := by
    linarith
  have hdena : 0 < 1 + a := by linarith
  have hc0 : 0 ≤ a / (1 + a) := div_nonneg ha.le hdena.le
  have hden : 0 < 1 + (a / (1 + a)) * n := by positivity
  have hen := hpos n le_rfl
  apply (le_div_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hrecip hen.le
  have hcancel : e n * (1 / e n) = 1 := by
    field_simp [hen.ne']
  nlinarith

/-- A triangular precision-indexed family with uniformly positive, possibly
stage-dependent reverse quadratic gains has vanishing finest defect. -/
theorem terminal_defect_tendsto_zero_of_uniform_reverse_quadratic_growth
    (a₀ : ℝ) (a : ℕ → ℕ → ℝ) (e : ℕ → ℕ → ℝ) (ha₀ : 0 < a₀)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hcoeff : ∀ k j, j < k → a₀ ≤ a k j)
    (hstep : ∀ k j, j < k →
      e k (j + 1) + a k j * (e k (j + 1)) ^ 2 ≤ e k j) :
    Filter.Tendsto (fun k => e k k) Filter.atTop (nhds 0) := by
  let c := a₀ / (1 + a₀)
  have hdena : 0 < 1 + a₀ := by linarith
  have hc : 0 < c := div_pos ha₀ hdena
  have hbound : ∀ k, e k k ≤ 1 / (1 + c * k) := by
    intro k
    apply terminal_defect_le_of_reverse_quadratic_growth_with
      a₀ (e k) k ha₀ (hpos k) (hone k)
    intro j hj
    have hmul : a₀ * (e k (j + 1)) ^ 2 ≤
        a k j * (e k (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hcoeff k j hj)
        (sq_nonneg (e k (j + 1)))
    nlinarith [hstep k j hj]
  have hupper : Filter.Tendsto (fun k : ℕ => 1 / (1 + c * k : ℝ))
      Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun k : ℕ => (1 + c * k : ℝ))
        Filter.atTop Filter.atTop := by
      have hmul : Filter.Tendsto (fun k : ℕ => c * (k : ℝ))
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (r := c) hc
          tendsto_natCast_atTop_atTop
      simpa [add_comm] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) hmul
    have honeT : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    simpa [one_div] using honeT.div_atTop hden
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k => (hpos k k le_rfl).le
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

/-- The KL endpoint needs only some level-uniform positive quadratic gain,
not the conjecturally sharp coefficient `3/2`. -/
theorem klLambda_tendsto_two_of_quadratic_defect_growth_with
    (a : ℝ) (lam : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (ha : 0 < a)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hstep : ∀ k j, j < k →
      e k j + a * (e k j) ^ 2 ≤ e k (j + 1))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * e k 0) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  apply klLambda_tendsto_two_of_defect lam (fun k => e k 0) hlam
  · intro k
    exact (hpos k 0 (Nat.zero_le k)).le
  · exact initial_defect_tendsto_zero_of_quadratic_growth_with
      a e ha hpos hone hstep
  · exact hidentity

/-- The KL endpoint also accepts stage-dependent gains.  Only a uniform
positive lower bound on their coefficients is required. -/
theorem klLambda_tendsto_two_of_uniform_quadratic_defect_growth
    (a₀ : ℝ) (a : ℕ → ℕ → ℝ)
    (lam : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (ha₀ : 0 < a₀)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hcoeff : ∀ k j, j < k → a₀ ≤ a k j)
    (hstep : ∀ k j, j < k →
      e k j + a k j * (e k j) ^ 2 ≤ e k (j + 1))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * e k 0) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  apply klLambda_tendsto_two_of_defect lam (fun k => e k 0) hlam
  · intro k
    exact (hpos k 0 (Nat.zero_le k)).le
  · exact initial_defect_tendsto_zero_of_uniform_quadratic_growth
      a₀ a e ha₀ hpos hone hcoeff hstep
  · exact hidentity

/-- Precision-indexed concrete endpoint.  This matches a tower whose profile
at index `j+1` is replaced by its coarse minimum at index `j`; no reversal of
indices is left to an informal argument. -/
theorem klLambda_tendsto_two_of_uniform_reverse_quadratic_defect_growth
    (a₀ : ℝ) (a : ℕ → ℕ → ℝ)
    (lam : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (ha₀ : 0 < a₀)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hpos : ∀ k j, j ≤ k → 0 < e k j)
    (hone : ∀ k j, j ≤ k → e k j ≤ 1)
    (hcoeff : ∀ k j, j < k → a₀ ≤ a k j)
    (hstep : ∀ k j, j < k →
      e k (j + 1) + a k j * (e k (j + 1)) ^ 2 ≤ e k j)
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * e k k) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  apply klLambda_tendsto_two_of_defect lam (fun k => e k k) hlam
  · intro k
    exact (hpos k k le_rfl).le
  · exact terminal_defect_tendsto_zero_of_uniform_reverse_quadratic_growth
      a₀ a e ha₀ hpos hone hcoeff hstep
  · exact hidentity

end CleanLean.KL
