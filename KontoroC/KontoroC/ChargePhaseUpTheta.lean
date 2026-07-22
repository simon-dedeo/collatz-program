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

def initialBinaryExponent (g : Ray) : ℕ :=
  154 * recharge g.jump + 23 * g.initialPhase

def initialTernaryExponent (g : Ray) : ℕ :=
  114 * recharge g.jump + 17 * g.initialPhase

def binaryRate (g : Ray) : ℕ := 92 * g.jump

def ternaryRate (g : Ray) : ℕ := 68 * g.jump

theorem binaryExponent_eq (g : Ray) (t : ℕ) :
    binaryExponent g.initialPhase g.jump t =
      g.initialBinaryExponent + g.binaryRate * (t + 1) := by
  simp only [binaryExponent, phase, initialBinaryExponent, binaryRate]
  ring

theorem ternaryExponent_eq (g : Ray) (t : ℕ) :
    ternaryExponent g.initialPhase g.jump t =
      g.initialTernaryExponent + g.ternaryRate * t := by
  simp only [ternaryExponent, phase, initialTernaryExponent, ternaryRate]
  ring

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ binaryExponent g.initialPhase g.jump t /
    (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t

/-- The generic affine-unrolling convention is `y_t=a_t*y_(t+1)-b_t`.
The phase-up natural gap is on the left of `PC4`, hence `b_t` is negative. -/
def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  -(gap g.jump : ℚ) /
    (3 : ℚ) ^ ternaryExponent g.initialPhase g.jump t

def geometricRatio (g : Ray) : ℚ :=
  (2 : ℚ) ^ g.binaryRate / (3 : ℚ) ^ g.ternaryRate

def initialAlpha (g : Ray) : ℚ :=
  (2 : ℚ) ^ g.initialBinaryExponent /
    (3 : ℚ) ^ g.initialTernaryExponent

def firstCoefficient (g : Ray) : ℚ :=
  (2 : ℚ) ^ (g.initialBinaryExponent + g.binaryRate) /
    (3 : ℚ) ^ g.initialTernaryExponent

theorem backwardCoeff_eq_geometric (g : Ray) (t : ℕ) :
    g.backwardCoeff t =
      g.firstCoefficient * g.geometricRatio ^ t := by
  rw [backwardCoeff, g.binaryExponent_eq t, g.ternaryExponent_eq t]
  simp only [firstCoefficient, geometricRatio, pow_add,
    pow_mul, div_pow]
  ring

theorem backwardDefect_eq_scaled (g : Ray) (t : ℕ) :
    g.backwardDefect t =
      (-(gap g.jump : ℚ) / (3 : ℚ) ^ g.initialTernaryExponent) /
        (3 : ℚ) ^ (g.ternaryRate * t) := by
  rw [backwardDefect, g.ternaryExponent_eq t, pow_add]
  ring

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

theorem backwardPrefixProduct_eq_geometric (g : Ray) (n : ℕ) :
    backwardPrefixProduct g.backwardCoeff n =
      g.firstCoefficient ^ n * g.geometricRatio ^ n.choose 2 := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, ih, g.backwardCoeff_eq_geometric n]
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hchoose]
      simp only [pow_succ, pow_add]
      ring

/-- The Väänänen--Wallisser exponent `n(n+1)/2`, represented without
natural-number division. -/
def vaananenExponent (n : ℕ) : ℕ := n.choose 2 + n

/-- The exact term of `f_q(alpha)` in the convention
`q = 3^(68k)/2^(92k)`, so `q^-1 = geometricRatio`. -/
def vaananenTerm (g : Ray) (n : ℕ) : ℚ :=
  g.geometricRatio ^ vaananenExponent n * g.initialAlpha ^ n

def thetaScale (g : Ray) : ℚ :=
  gap g.jump / (3 : ℚ) ^ g.initialTernaryExponent

def vaananenParameter (g : Ray) : ℚ :=
  (3 : ℚ) ^ g.ternaryRate / (2 : ℚ) ^ g.binaryRate

theorem geometricRatio_eq_displayed (g : Ray) :
    g.geometricRatio =
      (2 : ℚ) ^ (92 * g.jump) / (3 : ℚ) ^ (68 * g.jump) := by
  rfl

theorem initialAlpha_eq_displayed (g : Ray) :
    g.initialAlpha =
      (2 : ℚ) ^ (23 * g.initialPhase + 154 * recharge g.jump) /
        (3 : ℚ) ^ (17 * g.initialPhase + 114 * recharge g.jump) := by
  simp only [initialAlpha, initialBinaryExponent, initialTernaryExponent]
  congr 2 <;> omega

theorem geometricRatio_eq_parameter_inverse (g : Ray) :
    g.geometricRatio = g.vaananenParameter⁻¹ := by
  simp only [geometricRatio, vaananenParameter]
  field_simp

theorem parameter_num_den_coprime (g : Ray) :
    (3 ^ g.ternaryRate).Coprime (2 ^ g.binaryRate) := by
  exact (by norm_num : Nat.Coprime 3 2).pow _ _

theorem two_pow_23_lt_three_pow_17 : 2 ^ 23 < 3 ^ 17 := by
  norm_num

theorem rate_power_lt (g : Ray) :
    2 ^ g.binaryRate < 3 ^ g.ternaryRate := by
  simp only [binaryRate, ternaryRate]
  calc
    2 ^ (92 * g.jump) = (2 ^ 23) ^ (4 * g.jump) := by
      rw [← pow_mul]
      congr 1
      ring
    _ < (3 ^ 17) ^ (4 * g.jump) :=
      Nat.pow_lt_pow_left two_pow_23_lt_three_pow_17
        (Nat.ne_of_gt
          (Nat.mul_pos (by norm_num : 0 < (4 : ℕ)) g.jump_pos))
    _ = 3 ^ (68 * g.jump) := by
      rw [← pow_mul]
      congr 1
      ring

theorem parameter_numerator_gt_one (g : Ray) :
    1 < 3 ^ g.ternaryRate := by
  apply one_lt_pow₀ (by norm_num : 1 < (3 : ℕ))
  simp only [ternaryRate]
  exact (Nat.mul_pos (by norm_num) g.jump_pos).ne'

theorem parameter_denominator_pos (g : Ray) :
    0 < 2 ^ g.binaryRate := by positivity

/-- Integer form of the uniform logarithmic-slope hypothesis in the cited
partial-theta theorem: `3*23 >= 4*17`. -/
theorem exponent_slope_condition : 4 * 17 ≤ 3 * 23 := by
  norm_num

/-- The exact `l=1, sigma=0, p=2` size inequality in the 1989 theorem,
after cancelling the common positive jump size from `log |s|_2 / log h`.
It is strictly easier than the already audited standard-schedule inequality. -/
theorem vaananenWallisser_size_condition :
    1 - (23 : ℝ) * Real.log 2 / (17 * Real.log 3) <
      (3 - √5) / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hratio : 0 < Real.log 2 / Real.log 3 := div_pos hlog2 hlog3
  have hscale : Real.log 2 / Real.log 3 <
      ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) := by
    nlinarith [mul_lt_mul_of_pos_right
      (by norm_num : (1 : ℝ) < 23 / 17) hratio]
  calc
    1 - (23 : ℝ) * Real.log 2 / (17 * Real.log 3) =
        1 - ((23 : ℝ) / 17) * (Real.log 2 / Real.log 3) := by
      field_simp
    _ < 1 - Real.log 2 / Real.log 3 := by linarith
    _ < (3 - √5) / 2 :=
      NormalizedStandardPayloadStream.vaananenWallisser_size_condition

/-- Coefficientwise conversion from the backward defect series to the
Väänänen--Wallisser partial-theta series.  This is the exact content of PT2,
including its sign and rational prefactor. -/
theorem weightedDefect_eq_scaled_vaananenTerm (g : Ray) (n : ℕ) :
    backwardPrefixProduct g.backwardCoeff n * g.backwardDefect n =
      -g.thetaScale * g.vaananenTerm n := by
  rw [g.backwardPrefixProduct_eq_geometric n,
    g.backwardDefect_eq_scaled n]
  simp only [firstCoefficient, geometricRatio, initialAlpha, vaananenTerm,
    vaananenExponent, thetaScale]
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  ring

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

/-- The paper-normalized partial-theta term embedded in `Q_2`. -/
noncomputable def padicVaananenTerm (g : Ray) (n : ℕ) : ℚ_[2] :=
  (g.vaananenTerm n : ℚ_[2])

theorem padicDefectTerm_eq_scaled_vaananenTerm (g : Ray) (n : ℕ) :
    g.padicDefectTerm n =
      -(g.thetaScale : ℚ_[2]) * g.padicVaananenTerm n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.weightedDefect_eq_scaled_vaananenTerm n)
  simpa [padicDefectTerm, padicVaananenTerm, Rat.cast_mul,
    Rat.cast_neg] using h

theorem thetaScale_ne_zero (g : Ray) : g.thetaScale ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast (gap_pos g.jump).ne'
  · positivity

theorem padic_thetaScale_ne_zero (g : Ray) :
    (g.thetaScale : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.thetaScale_ne_zero

theorem padicVaananenTerm_summable (g : Ray) :
    Summable g.padicVaananenTerm := by
  let c : ℚ_[2] := -(g.thetaScale : ℚ_[2])
  have hc : c ≠ 0 := neg_ne_zero.mpr g.padic_thetaScale_ne_zero
  have hs := g.padicDefectTerm_summable.mul_left c⁻¹
  refine hs.congr ?_
  intro n
  rw [g.padicDefectTerm_eq_scaled_vaananenTerm]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

noncomputable def padicVaananenSum (g : Ray) : ℚ_[2] :=
  ∑' n, g.padicVaananenTerm n

/-- Completed-series version of the coefficientwise PT2 conversion. -/
theorem padicDefectSum_eq_scaled_vaananenSum (g : Ray) :
    g.padicDefectSum =
      -(g.thetaScale : ℚ_[2]) * g.padicVaananenSum := by
  have hv := g.padicVaananenTerm_summable.hasSum.mul_left
    (-(g.thetaScale : ℚ_[2]))
  have hfun :
      (fun n => -(g.thetaScale : ℚ_[2]) * g.padicVaananenTerm n) =
        g.padicDefectTerm := by
    funext n
    exact (g.padicDefectTerm_eq_scaled_vaananenTerm n).symm
  rw [hfun] at hv
  exact g.padicDefectTerm_summable.hasSum.unique hv

theorem padicCandidate_eq_scaled_vaananenSum (g : Ray) :
    g.padicCandidate =
      (g.thetaScale : ℚ_[2]) * g.padicVaananenSum := by
  rw [padicCandidate, g.padicDefectSum_eq_scaled_vaananenSum]
  ring

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

theorem candidate_irrational_of_vaananenSum_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicVaananenSum) :
    NormalizedStandardPayloadStream.IsPadicIrrational g.padicCandidate := by
  intro q heq
  apply hirr (q / g.thetaScale)
  rw [Rat.cast_div]
  apply (eq_div_iff g.padic_thetaScale_ne_zero).2
  rw [g.padicCandidate_eq_scaled_vaananenSum] at heq
  linear_combination heq

/-- Exact final citation seam for fixed-jump phase-up: the published
irrationality statement for the displayed `f_q(alpha)` value rules out the
ray.  No irrationality theorem is postulated inside this project. -/
theorem false_of_vaananenSum_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicVaananenSum) : False :=
  g.false_of_candidate_irrational
    (g.candidate_irrational_of_vaananenSum_irrational hirr)

end Ray

/-- A genuinely linked chain of the exact public-cofactor `Step` surrogate,
restricted to the fixed-jump phase-up opcode policy. -/
structure PublicRay where
  initialPhase : ℕ
  jump : ℕ
  initialPhase_pos : 0 < initialPhase
  jump_pos : 0 < jump
  boundary : ℕ → ChargePublicCofactor.Boundary
  step : ℕ → ChargePublicCofactor.Step
  step_source : ∀ t, (step t).source = boundary t
  step_target : ∀ t, (step t).target = boundary (t + 1)
  step_recharge : ∀ t, (step t).recharge = recharge jump
  boundary_opcode : ∀ t, (boundary t).opcode = phase initialPhase jump t

namespace PublicRay

/-- Forget only the endpoint register/oddness data, retaining the exact PC4
cofactor recurrence used by the partial-theta obstruction. -/
def toRay (g : PublicRay) : Ray where
  initialPhase := g.initialPhase
  jump := g.jump
  initialPhase_pos := g.initialPhase_pos
  jump_pos := g.jump_pos
  cofactor t := (g.boundary t).cofactor
  cofactor_pos t := (g.boundary t).cofactor_pos
  balance t := by
    have h := (g.step t).cofactor_balance
    rw [g.step_source t, g.step_target t, g.step_recharge t,
      g.boundary_opcode t, g.boundary_opcode (t + 1)] at h
    have hB : ChargePublicCofactor.publicB ^ recharge g.jump =
        2 ^ (154 * recharge g.jump) := by
      rw [ChargePublicCofactor.publicB, ← pow_mul]
    have hD : ChargePublicCofactor.publicD ^
          phase g.initialPhase g.jump (t + 1) =
        2 ^ (23 * phase g.initialPhase g.jump (t + 1)) := by
      rw [ChargePublicCofactor.publicD, ← pow_mul]
    have hA : ChargePublicCofactor.publicA ^ recharge g.jump =
        3 ^ (114 * recharge g.jump) := by
      rw [ChargePublicCofactor.publicA, ← pow_mul]
    have hC : ChargePublicCofactor.publicC ^
          phase g.initialPhase g.jump t =
        3 ^ (17 * phase g.initialPhase g.jump t) := by
      rw [ChargePublicCofactor.publicC, ← pow_mul]
    rw [hB, hD, hA, hC] at h
    simpa only [binaryExponent, ternaryExponent, gap, pow_add, mul_assoc]
      using h

theorem false_of_vaananenSum_irrational (g : PublicRay)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.toRay.padicVaananenSum) : False :=
  g.toRay.false_of_vaananenSum_irrational hirr

end PublicRay

end FixedJumpPhaseUp

end KontoroC
