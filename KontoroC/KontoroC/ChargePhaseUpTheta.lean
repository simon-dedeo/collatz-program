/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.VaananenWallisserAudit
import KontoroC.ChargePublicCofactor

/-!
# The fixed-jump phase-up cofactor ray

The public-cofactor balance `PC4` for a phase-up cell is most safely written
over naturals without a truncated subtraction:

`2^P w' + (3^(114h) - 2^(154h)) = 3^Q w`.

Here `h = 391k+1`, the source opcode is `m₀+4kt`, and the target opcode is
the next source opcode.  This file proves the exact finite backward unrolling
and its canonical `Q_2` endpoint.  The eventual irrationality statement is
deliberately not asserted: its intended proof is the external
Väänänen--Wallisser partial-theta theorem.
-/

namespace KontoroC

open Filter Topology MersennePacketRenewal

namespace FixedJumpPhaseUp

def recharge (k : ℕ) : ℕ := 391 * k + 1

def phase (m₀ k t : ℕ) : ℕ := m₀ + 4 * k * t

def binaryExponent (m₀ k t : ℕ) : ℕ :=
  154 * recharge k + 23 * phase m₀ k (t + 1)

def ternaryExponent (m₀ k t : ℕ) : ℕ :=
  114 * recharge k + 17 * phase m₀ k t

def gap (k : ℕ) : ℕ :=
  3 ^ (114 * recharge k) - 2 ^ (154 * recharge k)

theorem recharge_pos (k : ℕ) : 0 < recharge k := by
  simp [recharge]

theorem two_pow_154_lt_three_pow_114 : 2 ^ 154 < 3 ^ 114 := by
  norm_num

theorem recharge_power_lt (k : ℕ) :
    2 ^ (154 * recharge k) < 3 ^ (114 * recharge k) := by
  rw [pow_mul, pow_mul]
  exact Nat.pow_lt_pow_left two_pow_154_lt_three_pow_114
    (Nat.ne_of_gt (recharge_pos k))

theorem gap_pos (k : ℕ) : 0 < gap k := by
  exact Nat.sub_pos_of_lt (recharge_power_lt k)

theorem binaryExponent_pos (m₀ k t : ℕ) :
    0 < binaryExponent m₀ k t := by
  simp only [binaryExponent]
  have hh := recharge_pos k
  omega

/-- A necessary arithmetic projection of an infinite chain of public
cofactor phase-up cells with one fixed positive jump size.  The oddness and
public-register conditions only restrict this structure further, so they are
not needed for the partial-theta obstruction. -/
structure Ray where
  initialPhase : ℕ
  jump : ℕ
  initialPhase_pos : 0 < initialPhase
  jump_pos : 0 < jump
  cofactor : ℕ → ℕ
  cofactor_pos : ∀ t, 0 < cofactor t
  balance : ∀ t,
    2 ^ binaryExponent initialPhase jump t * cofactor (t + 1) + gap jump =
      3 ^ ternaryExponent initialPhase jump t * cofactor t

namespace Ray

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ binaryExponent g.initialPhase g.jump t /
    (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t

/-- The generic affine-unrolling convention is `y_t=a_t*y_(t+1)-b_t`.
The phase-up natural gap is on the left of `PC4`, hence `b_t` is negative. -/
def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  -(gap g.jump : ℚ) /
    (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t

theorem step_backward (g : Ray) (t : ℕ) :
    (g.cofactor t : ℚ) =
      g.backwardCoeff t * g.cofactor (t + 1) - g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ binaryExponent g.initialPhase g.jump t *
            g.cofactor (t + 1) + gap g.jump =
        (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t *
            g.cofactor t := by
    exact_mod_cast g.balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree :
      (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t ≠ 0 := by
    positivity
  field_simp
  nlinarith

theorem finite_series (g : Ray) (n : ℕ) :
    (g.cofactor 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff n * g.cofactor n -
        backwardPrefixDefect g.backwardCoeff g.backwardDefect n :=
  backward_affine_unroll (fun t => g.step_backward t) n

theorem norm_backwardCoeff (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ binaryExponent g.initialPhase g.jump t := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [g.norm_backwardCoeff]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (binaryExponent_pos g.initialPhase g.jump t).ne'
  rw [hn, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_backwardPrefixProduct_le (g : Ray) (n : ℕ) :
    ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ n := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (g.norm_backwardCoeff_le_half n)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one (g : Ray) (t : ℕ) :
    ‖(g.backwardDefect t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hgap : ‖(gap g.jump : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat (gap g.jump) : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one (p := 2) (Int.ofNat (gap g.jump))
  rw [backwardDefect, Rat.cast_div, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, norm_div, norm_neg, norm_pow,
    hthree, one_pow, div_one]
  exact hgap

noncomputable def padicDefectTerm (g : Ray) (t : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t : ℚ_[2])

theorem norm_padicDefectTerm_le (g : Ray) (t : ℕ) :
    ‖g.padicDefectTerm t‖ ≤ ((2 : ℝ)⁻¹) ^ t := by
  rw [padicDefectTerm, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ *
          ‖(g.backwardDefect t : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (g.norm_backwardDefect_le_one t)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ t := g.norm_backwardPrefixProduct_le t

theorem padicDefectTerm_tendsto_zero (g : Ray) :
    Tendsto g.padicDefectTerm atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicDefectTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicDefectTerm_summable (g : Ray) : Summable g.padicDefectTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using g.padicDefectTerm_tendsto_zero

noncomputable def padicDefectSum (g : Ray) : ℚ_[2] :=
  ∑' t, g.padicDefectTerm t

noncomputable def padicCandidate (g : Ray) : ℚ_[2] := -g.padicDefectSum

noncomputable def padicDefectPartial (g : Ray) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect n : ℚ_[2])

theorem padicDefectPartial_eq_sum (g : Ray) (n : ℕ) :
    g.padicDefectPartial n =
      ∑ t ∈ Finset.range n, g.padicDefectTerm t := by
  induction n with
  | zero => simp [padicDefectPartial, backwardPrefixDefect]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [padicDefectPartial, backwardPrefixDefect,
        padicDefectTerm, Rat.cast_add, Rat.cast_mul]

theorem padicDefectPartial_tendsto_sum (g : Ray) :
    Tendsto g.padicDefectPartial atTop (𝓝 g.padicDefectSum) := by
  have hsum := g.padicDefectTerm_summable.hasSum.tendsto_sum_nat
  have heq : g.padicDefectPartial = fun n =>
      ∑ t ∈ Finset.range n, g.padicDefectTerm t := by
    funext n
    exact g.padicDefectPartial_eq_sum n
  rw [heq]
  simpa only [padicDefectSum] using hsum

noncomputable def padicTerminal (g : Ray) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff n : ℚ_[2]) * g.cofactor n

theorem norm_padicTerminal_le (g : Ray) (n : ℕ) :
    ‖g.padicTerminal n‖ ≤ ((2 : ℝ)⁻¹) ^ n := by
  have hcofactor : ‖(g.cofactor n : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.cofactor n))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ *
          ‖(g.cofactor n : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hcofactor (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ n := g.norm_backwardPrefixProduct_le n

theorem padicTerminal_tendsto_zero (g : Ray) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : Ray) (n : ℕ) :
    (g.cofactor 0 : ℚ_[2]) =
      g.padicTerminal n - g.padicDefectPartial n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series n)
  simpa [padicTerminal, padicDefectPartial, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast] using h

/-- The unique 2-adic candidate selected by the fixed-jump recurrence equals
the embedded initial ordinary cofactor of every such ray. -/
theorem padicCandidate_eq_initial (g : Ray) :
    g.padicCandidate = (g.cofactor 0 : ℚ_[2]) := by
  have heq : g.padicDefectPartial = fun n =>
      g.padicTerminal n - (g.cofactor 0 : ℚ_[2]) := by
    funext n
    have h := g.padic_finite_series n
    linear_combination h
  have hlim : Tendsto g.padicDefectPartial atTop
      (𝓝 (-(g.cofactor 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.padicDefectSum = -(g.cofactor 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.padicDefectPartial_tendsto_sum hlim
  rw [padicCandidate, hsum]
  simp

/-- Honest citation seam: irrationality of the explicit candidate rules out
the arithmetic ray.  A later theorem identifies this candidate with the
Väänänen--Wallisser partial-theta value. -/
theorem false_of_candidate_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicCandidate) : False := by
  exact hirr (g.cofactor 0) (g.padicCandidate_eq_initial)

end Ray

end FixedJumpPhaseUp

end KontoroC
