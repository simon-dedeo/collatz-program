/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerDecoder
import KontoroC.PadicMersenne

/-!
# The 2-adic candidate of a charge-bouncer schedule

Every accepted bouncer block has an affine-gain equation with a power of two
on the next state and a power of three on the current state.  Backward
iteration therefore selects one canonical 2-adic number from any prescribed
positive opcode schedule.  An ordinary infinite ray can exist only when that
candidate is an embedded positive natural.

This file proves the reduction.  It makes no claim that the candidate of any
particular aperiodic schedule avoids the natural numbers.
-/

namespace KontoroC

open Filter Topology MersennePacketRenewal

/-- A symbolic schedule of positive defect and recharge opcodes. -/
structure ChargeBouncerOpcodeSchedule where
  defect : ℕ → ℕ
  recharge : ℕ → ℕ
  defect_pos : ∀ t, 0 < defect t
  recharge_pos : ∀ t, 0 < recharge t

namespace ChargeBouncerOpcodeSchedule

def binaryExponent (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℕ :=
  23 * c.defect t + 154 * c.recharge t

def ternaryExponent (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℕ :=
  17 * c.defect t + 114 * c.recharge t

def gain (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℕ :=
  3 ^ (114 * c.recharge t) *
    (3 ^ (17 * c.defect t) - 2 ^ (23 * c.defect t))

def backwardCoeff (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ c.binaryExponent t / (3 : ℚ) ^ c.ternaryExponent t

def backwardDefect (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℚ :=
  c.gain t / (3 : ℚ) ^ c.ternaryExponent t

/-- The multiplicative digit factors into one defect weight and one recharge
weight.  This is the useful form for substitution recurrences. -/
theorem backwardCoeff_factor (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    c.backwardCoeff t =
      ((2 : ℚ) ^ 23 / (3 : ℚ) ^ 17) ^ c.defect t *
        ((2 : ℚ) ^ 154 / (3 : ℚ) ^ 114) ^ c.recharge t := by
  simp only [backwardCoeff, binaryExponent, ternaryExponent, pow_add,
    pow_mul, div_pow]
  ring

/-- The additive digit does not depend on the recharge opcode: its entire
`3^(114h)` factor cancels against the ternary denominator. -/
theorem backwardDefect_eq_one_sub (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    c.backwardDefect t =
      1 - ((2 : ℚ) ^ 23 / (3 : ℚ) ^ 17) ^ c.defect t := by
  have hbase : 2 ^ 23 ≤ 3 ^ 17 := by norm_num
  have hpow : 2 ^ (23 * c.defect t) ≤ 3 ^ (17 * c.defect t) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left hbase (c.defect t)
  rw [backwardDefect, gain, ternaryExponent, pow_add,
    Nat.cast_mul, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_pow]
  simp only [pow_mul, div_pow]
  field_simp
  ring

/-- The two symbolic weights have the exact determinant-four resonance
visible in the executable bouncer. -/
theorem weight_resonance :
    ((2 : ℚ) ^ 23 / (3 : ℚ) ^ 17) ^ 154 =
      3 ^ 4 * ((2 : ℚ) ^ 154 / (3 : ℚ) ^ 114) ^ 23 := by
  norm_num [div_pow]

theorem binaryExponent_pos (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    0 < c.binaryExponent t := by
  exact Nat.add_pos_left
    (Nat.mul_pos (by omega) (c.defect_pos t)) _

theorem norm_backwardCoeff (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    ‖(c.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ c.binaryExponent t := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half
    (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    ‖(c.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [c.norm_backwardCoeff]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (c.binaryExponent_pos t).ne'
  rw [hn, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_backwardPrefixProduct_le
    (c : ChargeBouncerOpcodeSchedule) (n : ℕ) :
    ‖(backwardPrefixProduct c.backwardCoeff n : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ n := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (c.norm_backwardCoeff_le_half n)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one
    (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    ‖(c.backwardDefect t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hgain : ‖(c.gain t : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (c.gain t))
  rw [backwardDefect, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, norm_div, norm_pow, hthree, one_pow, div_one]
  exact hgain

/-- The weighted defect term selected by the symbolic schedule. -/
noncomputable def padicDefectTerm
    (c : ChargeBouncerOpcodeSchedule) (t : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct c.backwardCoeff t * c.backwardDefect t : ℚ_[2])

theorem norm_padicDefectTerm_le
    (c : ChargeBouncerOpcodeSchedule) (t : ℕ) :
    ‖c.padicDefectTerm t‖ ≤ ((2 : ℝ)⁻¹) ^ t := by
  rw [padicDefectTerm, norm_mul]
  calc
    ‖(backwardPrefixProduct c.backwardCoeff t : ℚ_[2])‖ *
          ‖(c.backwardDefect t : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct c.backwardCoeff t : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (c.norm_backwardDefect_le_one t)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct c.backwardCoeff t : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ t := c.norm_backwardPrefixProduct_le t

theorem padicDefectTerm_tendsto_zero (c : ChargeBouncerOpcodeSchedule) :
    Tendsto c.padicDefectTerm atTop (𝓝 0) := by
  apply squeeze_zero_norm c.norm_padicDefectTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicDefectTerm_summable (c : ChargeBouncerOpcodeSchedule) :
    Summable c.padicDefectTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using c.padicDefectTerm_tendsto_zero

noncomputable def padicDefectSum (c : ChargeBouncerOpcodeSchedule) : ℚ_[2] :=
  ∑' t, c.padicDefectTerm t

/-- Sign-normalized candidate: an ordinary ray must make this a positive
natural, rather than making the raw defect sum a negative natural. -/
noncomputable def padicCandidate (c : ChargeBouncerOpcodeSchedule) : ℚ_[2] :=
  -c.padicDefectSum

noncomputable def padicDefectPartial
    (c : ChargeBouncerOpcodeSchedule) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect c.backwardCoeff c.backwardDefect n : ℚ_[2])

theorem padicDefectPartial_eq_sum
    (c : ChargeBouncerOpcodeSchedule) (n : ℕ) :
    c.padicDefectPartial n =
      ∑ t ∈ Finset.range n, c.padicDefectTerm t := by
  induction n with
  | zero => simp [padicDefectPartial, backwardPrefixDefect]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [padicDefectPartial, backwardPrefixDefect,
        padicDefectTerm, Rat.cast_add, Rat.cast_mul]

theorem padicDefectPartial_tendsto_sum (c : ChargeBouncerOpcodeSchedule) :
    Tendsto c.padicDefectPartial atTop (𝓝 c.padicDefectSum) := by
  have hsum := c.padicDefectTerm_summable.hasSum.tendsto_sum_nat
  have heq : c.padicDefectPartial = fun n =>
      ∑ t ∈ Finset.range n, c.padicDefectTerm t := by
    funext n
    exact c.padicDefectPartial_eq_sum n
  rw [heq]
  simpa only [padicDefectSum] using hsum

end ChargeBouncerOpcodeSchedule

/-- An infinite chain of accepted bouncer transitions. -/
structure InfiniteChargeBouncerRay where
  state : ℕ → ℕ
  stepData : ℕ → ChargeBouncerStep
  input_eq : ∀ t, (stepData t).input = state t
  output_eq : ∀ t, (stepData t).output = state (t + 1)

namespace InfiniteChargeBouncerRay

def schedule (g : InfiniteChargeBouncerRay) : ChargeBouncerOpcodeSchedule where
  defect t := (g.stepData t).defectOpcode
  recharge t := (g.stepData t).rechargeCount
  defect_pos t := (g.stepData t).defectOpcode_pos
  recharge_pos t := (g.stepData t).rechargeCount_pos

theorem state_pos (g : InfiniteChargeBouncerRay) (t : ℕ) :
    0 < g.state t := by
  rw [← g.input_eq t]
  exact (g.stepData t).input_pos

theorem recurrence (g : InfiniteChargeBouncerRay) (t : ℕ) :
    2 ^ (g.schedule.binaryExponent t) * g.state (t + 1) =
      3 ^ (g.schedule.ternaryExponent t) * g.state t +
        g.schedule.gain t := by
  simpa [schedule, ChargeBouncerOpcodeSchedule.binaryExponent,
    ChargeBouncerOpcodeSchedule.ternaryExponent,
    ChargeBouncerOpcodeSchedule.gain, g.input_eq t, g.output_eq t] using
      (g.stepData t).affine_balance

theorem step_backward (g : InfiniteChargeBouncerRay) (t : ℕ) :
    (g.state t : ℚ) =
      g.schedule.backwardCoeff t * g.state (t + 1) -
        g.schedule.backwardDefect t := by
  have h :
      (2 : ℚ) ^ g.schedule.binaryExponent t * g.state (t + 1) =
        (3 : ℚ) ^ g.schedule.ternaryExponent t * g.state t +
          g.schedule.gain t := by
    exact_mod_cast g.recurrence t
  dsimp [ChargeBouncerOpcodeSchedule.backwardCoeff,
    ChargeBouncerOpcodeSchedule.backwardDefect]
  have hthree : (3 : ℚ) ^ g.schedule.ternaryExponent t ≠ 0 := by positivity
  field_simp
  nlinarith

theorem finite_series (g : InfiniteChargeBouncerRay) (n : ℕ) :
    (g.state 0 : ℚ) =
      backwardPrefixProduct g.schedule.backwardCoeff n * g.state n -
        backwardPrefixDefect g.schedule.backwardCoeff
          g.schedule.backwardDefect n :=
  backward_affine_unroll (fun t => g.step_backward t) n

noncomputable def padicTerminal
    (g : InfiniteChargeBouncerRay) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.schedule.backwardCoeff n : ℚ_[2]) * g.state n

theorem norm_padicTerminal_le (g : InfiniteChargeBouncerRay) (n : ℕ) :
    ‖g.padicTerminal n‖ ≤ ((2 : ℝ)⁻¹) ^ n := by
  have hstate : ‖(g.state n : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.state n))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.schedule.backwardCoeff n : ℚ_[2])‖ *
          ‖(g.state n : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.schedule.backwardCoeff n : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hstate (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.schedule.backwardCoeff n : ℚ_[2])‖ :=
      mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ n := g.schedule.norm_backwardPrefixProduct_le n

theorem padicTerminal_tendsto_zero (g : InfiniteChargeBouncerRay) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : InfiniteChargeBouncerRay) (n : ℕ) :
    (g.state 0 : ℚ_[2]) =
      g.padicTerminal n - g.schedule.padicDefectPartial n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series n)
  simpa [padicTerminal, ChargeBouncerOpcodeSchedule.padicDefectPartial,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast] using h

/-- The independently prescribed candidate of the opcode schedule is the
embedded initial natural of every ordinary ray realizing that schedule. -/
theorem padicCandidate_eq_initial (g : InfiniteChargeBouncerRay) :
    g.schedule.padicCandidate = (g.state 0 : ℚ_[2]) := by
  have heq : g.schedule.padicDefectPartial = fun n =>
      g.padicTerminal n - (g.state 0 : ℚ_[2]) := by
    funext n
    have h := g.padic_finite_series n
    linear_combination h
  have hlim : Tendsto g.schedule.padicDefectPartial atTop
      (𝓝 (-(g.state 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.schedule.padicDefectSum = -(g.state 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.schedule.padicDefectPartial_tendsto_sum hlim
  rw [ChargeBouncerOpcodeSchedule.padicCandidate, hsum]
  simp

/-- Clean no-ray endpoint for one prescribed symbolic schedule. -/
theorem no_ray_of_candidate_avoids_positiveNaturals
    (c : ChargeBouncerOpcodeSchedule)
    (havoid : ∀ u : ℕ, 0 < u → c.padicCandidate ≠ (u : ℚ_[2])) :
    ¬∃ g : InfiniteChargeBouncerRay, g.schedule = c := by
  rintro ⟨g, hschedule⟩
  have heq := g.padicCandidate_eq_initial
  rw [hschedule] at heq
  exact havoid (g.state 0) (g.state_pos 0) heq

end InfiniteChargeBouncerRay

end KontoroC
