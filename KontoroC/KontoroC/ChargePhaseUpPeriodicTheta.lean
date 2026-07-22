/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePhaseUpTheta
import Mathlib.Analysis.SumOverResidueClass

/-!
# Periodic phase-up jump words split into finitely many theta series

This file starts the extension of the fixed-jump obstruction to a nonempty
finite word of positive jumps repeated forever.  It proves the exact
cycle-shift laws for the public-cofactor backward coefficients and the pure
algebra which splits the resulting series by positions in the period.

The final multi-value Väänänen--Wallisser linear-independence theorem remains
an external citation, just as in `ChargePhaseUpTheta`.
-/

namespace KontoroC

open Filter Topology MersennePacketRenewal

namespace PeriodicPhaseUp

/-! ## Exact range of the 1989 size hypothesis -/

noncomputable def gamma : ℝ :=
  1 - (23 : ℝ) * Real.log 2 / (17 * Real.log 3)

noncomputable def threshold (L : ℕ) : ℝ :=
  (2 * L + 1 - √(1 + 4 * (L : ℝ) ^ 2)) / (2 * L)

theorem gamma_lt_one_sixth : gamma < (1 : ℝ) / 6 := by
  have hratio : (5 : ℝ) / 8 < Real.log 2 / Real.log 3 := by
    have h :=
      NormalizedStandardPayloadStream.log_size_parameter_lt_three_eighths
    linarith
  have hscaled : (5 : ℝ) / 6 <
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) := by
    nlinarith
  rw [gamma]
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [show (23 : ℝ) * Real.log 2 / (17 * Real.log 3) =
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) by
    field_simp]
  linarith

theorem one_sixth_lt_threshold_two :
    (1 : ℝ) / 6 < threshold 2 := by
  have hsqrt_nonneg : 0 ≤ √(17 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(17 : ℝ)) ^ 2 = 17 := by norm_num
  have hsqrt_lt : √(17 : ℝ) < 13 / 3 := by nlinarith
  norm_num [threshold]
  nlinarith

theorem gamma_lt_threshold_two : gamma < threshold 2 :=
  gamma_lt_one_sixth.trans one_sixth_lt_threshold_two

theorem three_pow_29_lt_two_pow_46 : 3 ^ 29 < 2 ^ 46 := by
  norm_num

theorem gamma_lt_three_twentieths : gamma < (3 : ℝ) / 20 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 29 < (2 : ℝ) ^ 46 := by norm_num
  have hlogpow : Real.log ((3 : ℝ) ^ 29) < Real.log ((2 : ℝ) ^ 46) :=
    Real.strictMonoOn_log
      (show 0 < (3 : ℝ) ^ 29 by positivity)
      (show 0 < (2 : ℝ) ^ 46 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hratio : (29 : ℝ) / 46 < Real.log 2 / Real.log 3 := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 46) hlog3).2
    simpa [mul_comm] using hlogpow
  have hscaled : (17 : ℝ) / 20 <
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) := by
    nlinarith
  rw [gamma]
  rw [show (23 : ℝ) * Real.log 2 / (17 * Real.log 3) =
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) by
    field_simp]
  linarith

theorem three_twentieths_lt_threshold_three :
    (3 : ℝ) / 20 < threshold 3 := by
  have hsqrt_nonneg : 0 ≤ √(37 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(37 : ℝ)) ^ 2 = 37 := by norm_num
  have hsqrt_lt : √(37 : ℝ) < 61 / 10 := by nlinarith
  norm_num [threshold]
  nlinarith

theorem gamma_lt_threshold_three : gamma < threshold 3 :=
  gamma_lt_three_twentieths.trans three_twentieths_lt_threshold_three

theorem two_pow_184_lt_three_pow_119 : 2 ^ 184 < 3 ^ 119 := by
  norm_num

/-- The first failure of this particular sufficient criterion: the actual
gamma lies strictly above `1/8`. -/
theorem one_eighth_lt_gamma : (1 : ℝ) / 8 < gamma := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ 184 < (3 : ℝ) ^ 119 := by norm_num
  have hlogpow : Real.log ((2 : ℝ) ^ 184) < Real.log ((3 : ℝ) ^ 119) :=
    Real.strictMonoOn_log
      (show 0 < (2 : ℝ) ^ 184 by positivity)
      (show 0 < (3 : ℝ) ^ 119 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hratio : Real.log 2 / Real.log 3 < (119 : ℝ) / 184 := by
    apply (div_lt_div_iff₀ hlog3 (by norm_num : (0 : ℝ) < 184)).2
    simpa [mul_comm] using hlogpow
  have hscaled : ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) < 7 / 8 := by
    nlinarith
  rw [gamma]
  rw [show (23 : ℝ) * Real.log 2 / (17 * Real.log 3) =
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) by
    field_simp]
  linarith

theorem threshold_four_lt_one_eighth : threshold 4 < (1 : ℝ) / 8 := by
  have hsqrt_nonneg : 0 ≤ √(65 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(65 : ℝ)) ^ 2 = 65 := by norm_num
  have hsqrt_gt : 8 < √(65 : ℝ) := by nlinarith
  norm_num [threshold]
  linarith

theorem threshold_four_lt_gamma : threshold 4 < gamma :=
  threshold_four_lt_one_eighth.trans one_eighth_lt_gamma

/-- One nonempty finite word of positive jump sizes. -/
structure JumpWord where
  period : ℕ
  period_pos : 0 < period
  jump : Fin period → ℕ
  jump_pos : ∀ r, 0 < jump r

namespace JumpWord

private theorem finEquiv_val (n : ℕ) [NeZero n] (r : Fin n) :
    (ZMod.finEquiv n r).val = (r : ℕ) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

def cycleSum (W : JumpWord) : ℕ := ∑ r, W.jump r

def prefixSum (W : JumpWord) (r : Fin W.period) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin W.period => (i : ℕ) < r), W.jump i

theorem cycleSum_pos (W : JumpWord) : 0 < W.cycleSum := by
  let r : Fin W.period := ⟨0, W.period_pos⟩
  have hr := W.jump_pos r
  have hle : W.jump r ≤ W.cycleSum := by
    simp only [cycleSum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  omega

def phase (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  m₀ + 4 * (n * W.cycleSum + W.prefixSum r)

def targetPhase (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  W.phase m₀ n r + 4 * W.jump r

def recharge (W : JumpWord) (r : Fin W.period) : ℕ :=
  FixedJumpPhaseUp.recharge (W.jump r)

def binaryExponent (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  154 * W.recharge r + 23 * W.targetPhase m₀ n r

def ternaryExponent (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  114 * W.recharge r + 17 * W.phase m₀ n r

def backwardCoeff (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℚ :=
  (2 : ℚ) ^ W.binaryExponent m₀ n r /
    (3 : ℚ) ^ W.ternaryExponent m₀ n r

def backwardDefect (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℚ :=
  -(FixedJumpPhaseUp.gap (W.jump r) : ℚ) /
    (3 : ℚ) ^ W.ternaryExponent m₀ n r

def cycleRatio (W : JumpWord) : ℚ :=
  (2 : ℚ) ^ (92 * W.cycleSum) / (3 : ℚ) ^ (68 * W.cycleSum)

def defectRatio (W : JumpWord) : ℚ :=
  1 / (3 : ℚ) ^ (68 * W.cycleSum)

theorem phase_cycle_shift (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.phase m₀ (n + 1) r = W.phase m₀ n r + 4 * W.cycleSum := by
  simp only [phase]
  ring

theorem targetPhase_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.targetPhase m₀ (n + 1) r =
      W.targetPhase m₀ n r + 4 * W.cycleSum := by
  rw [targetPhase, targetPhase, W.phase_cycle_shift]
  ring

theorem binaryExponent_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.binaryExponent m₀ (n + 1) r =
      W.binaryExponent m₀ n r + 92 * W.cycleSum := by
  simp only [binaryExponent, W.targetPhase_cycle_shift]
  ring

theorem ternaryExponent_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.ternaryExponent m₀ (n + 1) r =
      W.ternaryExponent m₀ n r + 68 * W.cycleSum := by
  simp only [ternaryExponent, W.phase_cycle_shift]
  ring

/-- At a fixed position in the jump word, advancing one whole period
multiplies the backward coefficient by one common rational ratio. -/
theorem backwardCoeff_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ (n + 1) r =
      W.cycleRatio * W.backwardCoeff m₀ n r := by
  rw [backwardCoeff, backwardCoeff, W.binaryExponent_cycle_shift,
    W.ternaryExponent_cycle_shift]
  simp only [cycleRatio, pow_add]
  ring

/-- The signed defect has its own common cycle multiplier. -/
theorem backwardDefect_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ (n + 1) r =
      W.defectRatio * W.backwardDefect m₀ n r := by
  rw [backwardDefect, backwardDefect, W.ternaryExponent_cycle_shift]
  simp only [defectRatio, pow_add]
  ring

theorem backwardCoeff_cycle_closed
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ n r =
      W.cycleRatio ^ n * W.backwardCoeff m₀ 0 r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [W.backwardCoeff_cycle_shift m₀ n r, ih, pow_succ]
      ring

theorem backwardDefect_cycle_closed
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ n r =
      W.defectRatio ^ n * W.backwardDefect m₀ 0 r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [W.backwardDefect_cycle_shift m₀ n r, ih, pow_succ]
      ring

def cycleCoeff (W : JumpWord) (m₀ n : ℕ) : ℚ :=
  ∏ r, W.backwardCoeff m₀ n r

theorem cycleCoeff_closed (W : JumpWord) (m₀ n : ℕ) :
    W.cycleCoeff m₀ n =
      W.cycleRatio ^ (n * W.period) * W.cycleCoeff m₀ 0 := by
  simp only [cycleCoeff, W.backwardCoeff_cycle_closed m₀ n]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_fin, ← pow_mul]

theorem cycleRatio_ne_zero (W : JumpWord) : W.cycleRatio ≠ 0 := by
  apply div_ne_zero <;> positivity

theorem cycleRatio_pos (W : JumpWord) : 0 < W.cycleRatio := by
  simp only [cycleRatio]
  positivity

theorem cycle_rate_power_lt (W : JumpWord) :
    2 ^ (92 * W.cycleSum) < 3 ^ (68 * W.cycleSum) := by
  calc
    2 ^ (92 * W.cycleSum) = (2 ^ 23) ^ (4 * W.cycleSum) := by
      rw [← pow_mul]
      congr 1
      ring
    _ < (3 ^ 17) ^ (4 * W.cycleSum) :=
      Nat.pow_lt_pow_left FixedJumpPhaseUp.Ray.two_pow_23_lt_three_pow_17
        (Nat.ne_of_gt (Nat.mul_pos (by norm_num) W.cycleSum_pos))
    _ = 3 ^ (68 * W.cycleSum) := by
      rw [← pow_mul]
      congr 1
      ring

theorem cycleRatio_lt_one (W : JumpWord) : W.cycleRatio < 1 := by
  rw [cycleRatio]
  apply (div_lt_one (by positivity : (0 : ℚ) < 3 ^ (68 * W.cycleSum))).2
  exact_mod_cast W.cycle_rate_power_lt

theorem cycleRatio_ne_one (W : JumpWord) : W.cycleRatio ≠ 1 :=
  ne_of_lt W.cycleRatio_lt_one

theorem defectRatio_ne_zero (W : JumpWord) : W.defectRatio ≠ 0 := by
  simp [defectRatio]

theorem backwardCoeff_ne_zero
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ n r ≠ 0 := by
  apply div_ne_zero <;> positivity

theorem backwardDefect_ne_zero
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ n r ≠ 0 := by
  apply div_ne_zero
  · exact neg_ne_zero.mpr (by
      exact_mod_cast (FixedJumpPhaseUp.gap_pos (W.jump r)).ne')
  · positivity

theorem cycleCoeff_ne_zero (W : JumpWord) (m₀ n : ℕ) :
    W.cycleCoeff m₀ n ≠ 0 := by
  simp only [cycleCoeff, Finset.prod_ne_zero_iff]
  intro r _
  exact W.backwardCoeff_ne_zero m₀ n r

def flatCoeff (W : JumpWord) (m₀ i : ℕ) : ℚ :=
  W.backwardCoeff m₀ (i / W.period)
    ⟨i % W.period, Nat.mod_lt i W.period_pos⟩

def flatDefect (W : JumpWord) (m₀ i : ℕ) : ℚ :=
  W.backwardDefect m₀ (i / W.period)
    ⟨i % W.period, Nat.mod_lt i W.period_pos⟩

theorem flatCoeff_at (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.flatCoeff m₀ (W.period * n + r) = W.backwardCoeff m₀ n r := by
  simp only [flatCoeff, Nat.mul_add_div W.period_pos,
    Nat.div_eq_of_lt r.isLt, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt r.isLt]

theorem flatDefect_at (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.flatDefect m₀ (W.period * n + r) = W.backwardDefect m₀ n r := by
  simp only [flatDefect, Nat.mul_add_div W.period_pos,
    Nat.div_eq_of_lt r.isLt, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt r.isLt]

theorem binaryExponent_pos (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    0 < W.binaryExponent m₀ n r := by
  simp only [binaryExponent, recharge, FixedJumpPhaseUp.recharge]
  omega

theorem norm_backwardCoeff (W : JumpWord) (m₀ n : ℕ)
    (r : Fin W.period) :
    ‖(W.backwardCoeff m₀ n r : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ W.binaryExponent m₀ n r := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (W : JumpWord) (m₀ n : ℕ)
    (r : Fin W.period) :
    ‖(W.backwardCoeff m₀ n r : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [W.norm_backwardCoeff m₀ n r]
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
    (W.binaryExponent_pos m₀ n r).ne'
  rw [he, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ e ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) e]

theorem norm_flatCoeff_le_half (W : JumpWord) (m₀ i : ℕ) :
    ‖(W.flatCoeff m₀ i : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  exact W.norm_backwardCoeff_le_half m₀ (i / W.period)
    ⟨i % W.period, Nat.mod_lt i W.period_pos⟩

theorem norm_flatPrefix_le (W : JumpWord) (m₀ i : ℕ) :
    ‖(backwardPrefixProduct (W.flatCoeff m₀) i : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ i := by
  induction i with
  | zero => simp [backwardPrefixProduct]
  | succ i ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (W.norm_flatCoeff_le_half m₀ i)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one (W : JumpWord) (m₀ n : ℕ)
    (r : Fin W.period) :
    ‖(W.backwardDefect m₀ n r : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hgap :
      ‖(FixedJumpPhaseUp.gap (W.jump r) : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat (FixedJumpPhaseUp.gap (W.jump r)) : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one _
  rw [backwardDefect, Rat.cast_div, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, norm_div, norm_neg, norm_pow,
    hthree, one_pow, div_one]
  exact hgap

theorem norm_flatDefect_le_one (W : JumpWord) (m₀ i : ℕ) :
    ‖(W.flatDefect m₀ i : ℚ_[2])‖ ≤ 1 := by
  exact W.norm_backwardDefect_le_one m₀ (i / W.period)
    ⟨i % W.period, Nat.mod_lt i W.period_pos⟩

def residueCoeff (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℚ :=
  ∏ i : Fin r, W.backwardCoeff m₀ n
    ⟨i, lt_trans i.isLt r.isLt⟩

theorem residueCoeff_closed (W : JumpWord) (m₀ n : ℕ)
    (r : Fin W.period) :
    W.residueCoeff m₀ n r =
      W.cycleRatio ^ (n * (r : ℕ)) * W.residueCoeff m₀ 0 r := by
  simp only [residueCoeff, W.backwardCoeff_cycle_closed m₀ n]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_fin, ← pow_mul]

theorem backwardPrefixProduct_eq_prod_range (a : ℕ → ℚ) (n : ℕ) :
    backwardPrefixProduct a n = ∏ i ∈ Finset.range n, a i := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, ih, Finset.prod_range_succ]

theorem flat_block_product (W : JumpWord) (m₀ n : ℕ) :
    (∏ i ∈ Finset.range W.period,
      W.flatCoeff m₀ (W.period * n + i)) = W.cycleCoeff m₀ n := by
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => W.flatCoeff m₀ (W.period * n + i)) W.period]
  apply Finset.prod_congr rfl
  intro r _
  exact W.flatCoeff_at m₀ n r

theorem flat_cycle_prefix (W : JumpWord) (m₀ n : ℕ) :
    backwardPrefixProduct (W.flatCoeff m₀) (W.period * n) =
      W.cycleCoeff m₀ 0 ^ n *
        W.cycleRatio ^ (W.period * n.choose 2) := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct_eq_prod_range]
      rw [show W.period * (n + 1) = W.period * n + W.period by ring,
        Finset.prod_range_add]
      rw [← backwardPrefixProduct_eq_prod_range, ih,
        W.flat_block_product m₀ n, W.cycleCoeff_closed m₀ n]
      rw [show (n + 1).choose 2 = n.choose 2 + n by
        rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      simp only [pow_succ]
      ring

theorem flat_prefix_at (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    backwardPrefixProduct (W.flatCoeff m₀) (W.period * n + r) =
      W.cycleCoeff m₀ 0 ^ n *
        W.cycleRatio ^ (W.period * n.choose 2) *
        W.cycleRatio ^ (n * (r : ℕ)) * W.residueCoeff m₀ 0 r := by
  rw [backwardPrefixProduct_eq_prod_range, Finset.prod_range_add]
  rw [← backwardPrefixProduct_eq_prod_range, W.flat_cycle_prefix m₀ n]
  have hresidue :
      (∏ i ∈ Finset.range (r : ℕ),
        W.flatCoeff m₀ (W.period * n + i)) = W.residueCoeff m₀ n r := by
    rw [← Fin.prod_univ_eq_prod_range
      (fun i => W.flatCoeff m₀ (W.period * n + i)) (r : ℕ)]
    apply Finset.prod_congr rfl
    intro i _
    rw [W.flatCoeff_at m₀ n
      ⟨i, lt_trans i.isLt r.isLt⟩]
  rw [hresidue, W.residueCoeff_closed m₀ n r]
  ring

end JumpWord

/-! ## Pure residue-class theta decomposition -/

/-- Algebraic data left after splitting a periodic coefficient schedule by
positions in its period.  `ratio` is the common coefficient multiplier per
cycle, `defectRatio` is the common defect multiplier, and `cycleCoeff` is the
product of the coefficients in cycle zero. -/
structure ThetaResidueData (p : ℕ) where
  ratio : ℚ
  defectRatio : ℚ
  cycleCoeff : ℚ
  prefixScale : Fin p → ℚ

namespace ThetaResidueData

theorem rational_geometric_exponent_eq {R C : ℚ} (hRpos : 0 < R)
    (hRone : R ≠ 1) (hC : C ≠ 0) {p r s : ℕ} {z : ℤ}
    (h : (C * R ^ r) / (C * R ^ s) = ((R ^ p)⁻¹) ^ z) :
    (r : ℤ) - s = -(p : ℤ) * z := by
  apply (zpow_right_injective₀ hRpos hRone)
  calc
    R ^ ((r : ℤ) - s) = R ^ (r : ℤ) / R ^ (s : ℤ) :=
      zpow_sub₀ (ne_of_gt hRpos) _ _
    _ = (C * R ^ r) / (C * R ^ s) := by
      rw [zpow_natCast, zpow_natCast]
      field_simp
    _ = ((R ^ p)⁻¹) ^ z := h
    _ = (R ^ (-(p : ℤ))) ^ z := by
      rw [zpow_neg, zpow_natCast]
    _ = R ^ (-(p : ℤ) * z) := (zpow_mul R _ _).symm

def weightedTerm {p : ℕ} (D : ThetaResidueData p)
    (r : Fin p) (n : ℕ) : ℚ :=
  D.prefixScale r *
    (D.ratio ^ p) ^ n.choose 2 *
    (D.cycleCoeff * D.ratio ^ (r : ℕ) * D.defectRatio) ^ n

def parameterInverse {p : ℕ} (D : ThetaResidueData p) : ℚ :=
  D.ratio ^ p

def argument {p : ℕ} (D : ThetaResidueData p) (r : Fin p) : ℚ :=
  (D.cycleCoeff * D.ratio ^ (r : ℕ) * D.defectRatio) /
    D.parameterInverse

def argumentCommon {p : ℕ} (D : ThetaResidueData p) : ℚ :=
  D.cycleCoeff * D.defectRatio / D.parameterInverse

theorem argument_eq_common_mul {p : ℕ} (D : ThetaResidueData p)
    (r : Fin p) : D.argument r = D.argumentCommon * D.ratio ^ (r : ℕ) := by
  simp only [argument, argumentCommon, parameterInverse]
  ring

def vaananenExponent (n : ℕ) : ℕ := n.choose 2 + n

def vaananenTerm {p : ℕ} (D : ThetaResidueData p)
    (r : Fin p) (n : ℕ) : ℚ :=
  D.parameterInverse ^ vaananenExponent n * D.argument r ^ n

/-- Each residue-class subsequence is exactly one rational multiple of the
paper-normalized theta series, coefficient by coefficient. -/
theorem weightedTerm_eq_scaled_vaananenTerm {p : ℕ}
    (D : ThetaResidueData p) (hratio : D.ratio ≠ 0)
    (r : Fin p) (n : ℕ) :
    D.weightedTerm r n = D.prefixScale r * D.vaananenTerm r n := by
  simp only [weightedTerm, vaananenTerm, vaananenExponent, argument,
    parameterInverse, pow_add, div_pow]
  field_simp [pow_ne_zero _ hratio]

/-- The theta arguments at two period positions differ only by the
corresponding power of the common one-cycle ratio. -/
theorem argument_cross_ratio {p : ℕ} (D : ThetaResidueData p)
    (r s : Fin p) :
    D.argument r * D.ratio ^ (s : ℕ) =
      D.argument s * D.ratio ^ (r : ℕ) := by
  simp only [argument, parameterInverse]
  ring

theorem argument_ne_zero {p : ℕ} (D : ThetaResidueData p)
    (hratio : D.ratio ≠ 0) (hdefect : D.defectRatio ≠ 0)
    (hcycle : D.cycleCoeff ≠ 0) (r : Fin p) : D.argument r ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero hcycle (pow_ne_zero _ hratio)) hdefect
  · exact pow_ne_zero _ hratio

theorem argumentCommon_ne_zero {p : ℕ} (D : ThetaResidueData p)
    (hratio : D.ratio ≠ 0) (hdefect : D.defectRatio ≠ 0)
    (hcycle : D.cycleCoeff ≠ 0) : D.argumentCommon ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero hcycle hdefect
  · exact pow_ne_zero _ hratio

/-- Exact exponent forced by a forbidden paper-argument ratio. -/
theorem exponent_eq_of_argument_ratio {p : ℕ} (D : ThetaResidueData p)
    (hratioPos : 0 < D.ratio) (hratioOne : D.ratio ≠ 1)
    (hdefect : D.defectRatio ≠ 0) (hcycle : D.cycleCoeff ≠ 0)
    (r s : Fin p) (z : ℤ)
    (h : D.argument r / D.argument s = D.parameterInverse⁻¹ ^ z) :
    (r : ℤ) - s = -(p : ℤ) * z := by
  rw [D.argument_eq_common_mul r, D.argument_eq_common_mul s] at h
  exact rational_geometric_exponent_eq hratioPos hratioOne
    (D.argumentCommon_ne_zero (ne_of_gt hratioPos) hdefect hcycle) h

/-- For positions inside one nonempty period, the paper's forbidden
`alpha_r/alpha_s=q^z` relation forces the positions to be equal. -/
theorem eq_of_argument_ratio {p : ℕ}
    (D : ThetaResidueData p) (hratioPos : 0 < D.ratio)
    (hratioOne : D.ratio ≠ 1) (hdefect : D.defectRatio ≠ 0)
    (hcycle : D.cycleCoeff ≠ 0) (r s : Fin p) (z : ℤ)
    (h : D.argument r / D.argument s = D.parameterInverse⁻¹ ^ z) :
    r = s := by
  have he := D.exponent_eq_of_argument_ratio hratioPos hratioOne
    hdefect hcycle r s z h
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hrp : (r : ℤ) < p := by exact_mod_cast r.isLt
  have hsp : (s : ℤ) < p := by exact_mod_cast s.isLt
  by_cases hz0 : z = 0
  · subst z
    simp only [mul_zero] at he
    exact Fin.ext (by omega)
  · by_cases hz : 0 < z
    · have hz1 : (1 : ℤ) ≤ z := by omega
      have hpz : (p : ℤ) ≤ p * z := by nlinarith
      nlinarith
    · have hz1 : z ≤ -1 := by omega
      have hpz : p * z ≤ -(p : ℤ) := by nlinarith
      nlinarith

end ThetaResidueData

namespace JumpWord

def thetaData (W : JumpWord) (m₀ : ℕ) : ThetaResidueData W.period where
  ratio := W.cycleRatio
  defectRatio := W.defectRatio
  cycleCoeff := W.cycleCoeff m₀ 0
  prefixScale r := W.residueCoeff m₀ 0 r * W.backwardDefect m₀ 0 r

def flatWeightedTerm (W : JumpWord) (m₀ i : ℕ) : ℚ :=
  backwardPrefixProduct (W.flatCoeff m₀) i * W.flatDefect m₀ i

noncomputable def padicFlatWeightedTerm (W : JumpWord) (m₀ i : ℕ) : ℚ_[2] :=
  (W.flatWeightedTerm m₀ i : ℚ_[2])

theorem norm_padicFlatWeightedTerm_le (W : JumpWord) (m₀ i : ℕ) :
    ‖W.padicFlatWeightedTerm m₀ i‖ ≤ ((2 : ℝ)⁻¹) ^ i := by
  rw [padicFlatWeightedTerm, flatWeightedTerm, Rat.cast_mul, norm_mul]
  calc
    ‖(backwardPrefixProduct (W.flatCoeff m₀) i : ℚ_[2])‖ *
          ‖(W.flatDefect m₀ i : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct (W.flatCoeff m₀) i : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (W.norm_flatDefect_le_one m₀ i)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct (W.flatCoeff m₀) i : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ i := W.norm_flatPrefix_le m₀ i

theorem padicFlatWeightedTerm_tendsto_zero (W : JumpWord) (m₀ : ℕ) :
    Tendsto (W.padicFlatWeightedTerm m₀) atTop (𝓝 0) := by
  apply squeeze_zero_norm (W.norm_padicFlatWeightedTerm_le m₀)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicFlatWeightedTerm_summable (W : JumpWord) (m₀ : ℕ) :
    Summable (W.padicFlatWeightedTerm m₀) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using
    W.padicFlatWeightedTerm_tendsto_zero m₀

noncomputable def padicFlatSum (W : JumpWord) (m₀ : ℕ) : ℚ_[2] :=
  ∑' i, W.padicFlatWeightedTerm m₀ i

/-- The original flattened backward series, restricted to one residue class
modulo the jump-word period, has exactly the abstract theta weight. -/
theorem flatWeightedTerm_at (W : JumpWord) (m₀ n : ℕ)
    (r : Fin W.period) :
    W.flatWeightedTerm m₀ (W.period * n + r) =
      (W.thetaData m₀).weightedTerm r n := by
  rw [flatWeightedTerm, W.flat_prefix_at m₀ n r,
    W.flatDefect_at m₀ n r, W.backwardDefect_cycle_closed m₀ n r]
  simp only [thetaData, ThetaResidueData.weightedTerm]
  simp only [pow_mul, mul_pow]
  ring

/-- Complete coefficientwise splitter: each residue class of the actual PC4
series is a nonzero rational scale times one paper-normalized theta series. -/
theorem flatWeightedTerm_eq_scaled_vaananenTerm
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.flatWeightedTerm m₀ (W.period * n + r) =
      (W.thetaData m₀).prefixScale r *
        (W.thetaData m₀).vaananenTerm r n := by
  rw [W.flatWeightedTerm_at m₀ n r]
  exact (W.thetaData m₀).weightedTerm_eq_scaled_vaananenTerm
    W.cycleRatio_ne_zero r n

/-- Completed-series splitter.  The unique PC4 defect sum is the finite sum
of its period residue-class series; no conditional rearrangement is used. -/
theorem padicFlatSum_eq_sum_residues (W : JumpWord) (m₀ : ℕ) :
    W.padicFlatSum m₀ =
      ∑ r : Fin W.period,
        ∑' n : ℕ, W.padicFlatWeightedTerm m₀ (W.period * n + r) := by
  letI : NeZero W.period := ⟨W.period_pos.ne'⟩
  let f : ℕ → ℚ_[2] := W.padicFlatWeightedTerm m₀
  have hf : Summable f := W.padicFlatWeightedTerm_summable m₀
  calc
    W.padicFlatSum m₀ = ∑' i : ℕ, f i := rfl
    _ = ∑ j : ZMod W.period,
          ∑' n : ℕ, f (j.val + W.period * n) :=
      Nat.sumByResidueClasses hf W.period
    _ = ∑ r : Fin W.period,
          ∑' n : ℕ, f ((ZMod.finEquiv W.period r).val + W.period * n) := by
      exact (Equiv.sum_comp (ZMod.finEquiv W.period).toEquiv _).symm
    _ = ∑ r : Fin W.period,
          ∑' n : ℕ, W.padicFlatWeightedTerm m₀ (W.period * n + r) := by
      apply Fintype.sum_congr
      intro r
      have hval := finEquiv_val W.period r
      congr 1
      funext n
      simp only [f, hval]
      congr 1
      omega

theorem theta_prefixScale_ne_zero (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) : (W.thetaData m₀).prefixScale r ≠ 0 := by
  simp only [thetaData]
  apply mul_ne_zero
  · simp only [residueCoeff, Finset.prod_ne_zero_iff]
    intro i _
    exact W.backwardCoeff_ne_zero m₀ 0 _
  · exact W.backwardDefect_ne_zero m₀ 0 r

theorem theta_argument_ne_zero (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) : (W.thetaData m₀).argument r ≠ 0 := by
  exact (W.thetaData m₀).argument_ne_zero W.cycleRatio_ne_zero
    W.defectRatio_ne_zero (W.cycleCoeff_ne_zero m₀ 0) r

/-- The exact pairwise-argument hypothesis of the 1989 theorem.  Distinct
positions in one period cannot differ by any integer power of the common
paper parameter. -/
theorem theta_arguments_separated (W : JumpWord) (m₀ : ℕ)
    (r s : Fin W.period) (hrs : r ≠ s) (z : ℤ) :
    (W.thetaData m₀).argument r / (W.thetaData m₀).argument s ≠
      (W.thetaData m₀).parameterInverse⁻¹ ^ z := by
  intro h
  apply hrs
  exact (W.thetaData m₀).eq_of_argument_ratio W.cycleRatio_pos
    W.cycleRatio_ne_one W.defectRatio_ne_zero
    (W.cycleCoeff_ne_zero m₀ 0) r s z h

/-! ## The actual completed residue series -/

/-- The paper-normalized term belonging to one position of the periodic
jump word, embedded in `Q_2`. -/
noncomputable def padicVaananenTerm (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) (n : ℕ) : ℚ_[2] :=
  ((W.thetaData m₀).vaananenTerm r n : ℚ_[2])

/-- Exact coefficientwise identity in the completion.  This is the seam
that prevents replacing the public-cofactor series by a cleaner surrogate. -/
theorem padicFlatWeightedTerm_eq_scaled_vaananenTerm
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.padicFlatWeightedTerm m₀ (W.period * n + r) =
      ((W.thetaData m₀).prefixScale r : ℚ_[2]) *
        W.padicVaananenTerm m₀ r n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (W.flatWeightedTerm_eq_scaled_vaananenTerm m₀ n r)
  simpa [padicFlatWeightedTerm, padicVaananenTerm, Rat.cast_mul] using h

theorem padic_theta_prefixScale_ne_zero (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) :
    ((W.thetaData m₀).prefixScale r : ℚ_[2]) ≠ 0 := by
  exact_mod_cast W.theta_prefixScale_ne_zero m₀ r

/-- Every paper-normalized residue series converges 2-adically.  The proof
is derived from the original flattened PC4 series and a nonzero scale, so
it does not require a fresh analytic estimate. -/
theorem padicVaananenTerm_summable (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) : Summable (W.padicVaananenTerm m₀ r) := by
  let c : ℚ_[2] := ((W.thetaData m₀).prefixScale r : ℚ_[2])
  have hc : c ≠ 0 := W.padic_theta_prefixScale_ne_zero m₀ r
  have hzero : Tendsto
      (fun n => W.padicFlatWeightedTerm m₀ (W.period * n + r))
      atTop (nhds 0) := by
    have hindex : Tendsto (fun n : ℕ => W.period * n + (r : ℕ))
        atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with n hn
      calc
        b ≤ n := hn
        _ ≤ W.period * n := Nat.le_mul_of_pos_left n W.period_pos
        _ ≤ W.period * n + (r : ℕ) := Nat.le_add_right _ _
    exact (W.padicFlatWeightedTerm_tendsto_zero m₀).comp
      hindex
  have hs : Summable
      (fun n => W.padicFlatWeightedTerm m₀ (W.period * n + r)) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using hzero
  have hscaled := hs.mul_left c⁻¹
  refine hscaled.congr ?_
  intro n
  rw [W.padicFlatWeightedTerm_eq_scaled_vaananenTerm m₀ n r]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The exact `Q_2` value to which the multi-argument 1989 theorem applies
at residue `r`. -/
noncomputable def padicVaananenSum (W : JumpWord) (m₀ : ℕ)
    (r : Fin W.period) : ℚ_[2] :=
  ∑' n, W.padicVaananenTerm m₀ r n

/-- Completed equality for one residue class of the real recurrence. -/
theorem padicResidueSum_eq_scaled_vaananenSum
    (W : JumpWord) (m₀ : ℕ) (r : Fin W.period) :
    (∑' n, W.padicFlatWeightedTerm m₀ (W.period * n + r)) =
      ((W.thetaData m₀).prefixScale r : ℚ_[2]) *
        W.padicVaananenSum m₀ r := by
  have hv := (W.padicVaananenTerm_summable m₀ r).hasSum.mul_left
    ((W.thetaData m₀).prefixScale r : ℚ_[2])
  have hfun :
      (fun n => ((W.thetaData m₀).prefixScale r : ℚ_[2]) *
        W.padicVaananenTerm m₀ r n) =
      (fun n => W.padicFlatWeightedTerm m₀ (W.period * n + r)) := by
    funext n
    exact (W.padicFlatWeightedTerm_eq_scaled_vaananenTerm m₀ n r).symm
  rw [hfun] at hv
  simpa only [padicVaananenSum] using hv.tsum_eq

/-- The entire actual flattened PC4 defect sum is a finite rational linear
combination of the paper's theta values. -/
theorem padicFlatSum_eq_scaled_vaananenSums (W : JumpWord) (m₀ : ℕ) :
    W.padicFlatSum m₀ =
      ∑ r : Fin W.period,
        ((W.thetaData m₀).prefixScale r : ℚ_[2]) *
          W.padicVaananenSum m₀ r := by
  rw [W.padicFlatSum_eq_sum_residues]
  apply Fintype.sum_congr
  intro r
  exact W.padicResidueSum_eq_scaled_vaananenSum m₀ r

end JumpWord

end PeriodicPhaseUp

end KontoroC
