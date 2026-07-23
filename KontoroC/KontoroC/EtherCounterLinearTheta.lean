/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterAperiodic
import KontoroC.ChargePhaseUpTheta

/-!
# Arithmetic ether schedules and their partial-theta obstruction

For a one-based arithmetic branch schedule `n_t=n₀+k*t`, the normalized odd
part of the autonomous ether register obeys

`2^(8*n_(t+1)+15) h_(t+1) = 3^(6*n_t+11) h_t + 51`.

This file kernel-checks the exact finite backward identity, its conversion to
the Väänänen--Wallisser partial-theta normalization, and the `Q_2` limiting
argument.  The final nonexistence theorem is deliberately conditional on the
irrationality of one explicit Lean-defined p-adic sum: the cited 1989
irrationality theorem is not postulated or reproved here.
-/

namespace KontoroC
namespace EtherCounterLinearTheta

open Filter Topology MersennePacketRenewal

def branch (n₀ k t : ℕ) : ℕ := n₀ + k * t

def binaryExponent (n₀ k t : ℕ) : ℕ :=
  8 * branch n₀ k (t + 1) + 15

def ternaryExponent (n₀ k t : ℕ) : ℕ :=
  6 * branch n₀ k t + 11

/-- A necessary arithmetic projection of an infinite autonomous ether orbit
whose one-based branch numbers form a positive arithmetic progression. -/
structure Ray where
  initialBranch : ℕ
  jump : ℕ
  initialBranch_pos : 0 < initialBranch
  jump_pos : 0 < jump
  oddPart : ℕ → ℕ
  oddPart_pos : ∀ t, 0 < oddPart t
  balance : ∀ t,
    2 ^ binaryExponent initialBranch jump t * oddPart (t + 1) =
      3 ^ ternaryExponent initialBranch jump t * oddPart t + 51

namespace Ray

def initialBinaryExponent (g : Ray) : ℕ := 8 * g.initialBranch + 15
def initialTernaryExponent (g : Ray) : ℕ := 6 * g.initialBranch + 11
def binaryRate (g : Ray) : ℕ := 8 * g.jump
def ternaryRate (g : Ray) : ℕ := 6 * g.jump

theorem binaryExponent_eq (g : Ray) (t : ℕ) :
    binaryExponent g.initialBranch g.jump t =
      g.initialBinaryExponent + g.binaryRate * (t + 1) := by
  simp [binaryExponent, branch, initialBinaryExponent, binaryRate]
  ring

theorem ternaryExponent_eq (g : Ray) (t : ℕ) :
    ternaryExponent g.initialBranch g.jump t =
      g.initialTernaryExponent + g.ternaryRate * t := by
  simp [ternaryExponent, branch, initialTernaryExponent, ternaryRate]
  ring

theorem binaryExponent_pos (g : Ray) (t : ℕ) :
    0 < binaryExponent g.initialBranch g.jump t := by
  simp [binaryExponent, branch]

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ binaryExponent g.initialBranch g.jump t /
    (3 : ℚ) ^ ternaryExponent g.initialBranch g.jump t

def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  51 / (3 : ℚ) ^ ternaryExponent g.initialBranch g.jump t

def geometricRatio (g : Ray) : ℚ :=
  (2 : ℚ) ^ g.binaryRate / (3 : ℚ) ^ g.ternaryRate

def initialAlpha (g : Ray) : ℚ :=
  (2 : ℚ) ^ g.initialBinaryExponent /
    (3 : ℚ) ^ g.initialTernaryExponent

def firstCoefficient (g : Ray) : ℚ :=
  (2 : ℚ) ^ (g.initialBinaryExponent + g.binaryRate) /
    (3 : ℚ) ^ g.initialTernaryExponent

theorem step_backward (g : Ray) (t : ℕ) :
    (g.oddPart t : ℚ) =
      g.backwardCoeff t * g.oddPart (t + 1) - g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ binaryExponent g.initialBranch g.jump t *
          g.oddPart (t + 1) =
        (3 : ℚ) ^ ternaryExponent g.initialBranch g.jump t *
          g.oddPart t + 51 := by
    exact_mod_cast g.balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree :
      (3 : ℚ) ^ ternaryExponent g.initialBranch g.jump t ≠ 0 := by
    positivity
  field_simp
  nlinarith

/-- QM51 in the generic finite-affine notation already used elsewhere in the
project.  The accumulated defect is definitionally the finite displayed sum
of weighted `51/3^A` terms. -/
theorem finite_series (g : Ray) (N : ℕ) :
    (g.oddPart 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff N * g.oddPart N -
      backwardPrefixDefect g.backwardCoeff g.backwardDefect N :=
  backward_affine_unroll (fun t => g.step_backward t) N

theorem backwardPrefixDefect_eq_sum (g : Ray) (N : ℕ) :
    backwardPrefixDefect g.backwardCoeff g.backwardDefect N =
      ∑ t ∈ Finset.range N,
        backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect, Finset.sum_range_succ, ih]

/-- Expanded finite form of QM51. -/
theorem finite_series_sum (g : Ray) (N : ℕ) :
    (g.oddPart 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff N * g.oddPart N -
        ∑ t ∈ Finset.range N,
          backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t := by
  rw [g.finite_series N, g.backwardPrefixDefect_eq_sum N]

theorem backwardCoeff_eq_geometric (g : Ray) (t : ℕ) :
    g.backwardCoeff t =
      g.firstCoefficient * g.geometricRatio ^ t := by
  rw [backwardCoeff, g.binaryExponent_eq t, g.ternaryExponent_eq t]
  simp only [firstCoefficient, geometricRatio, pow_add, pow_mul, div_pow]
  ring

theorem backwardPrefixProduct_eq_geometric (g : Ray) (N : ℕ) :
    backwardPrefixProduct g.backwardCoeff N =
      g.firstCoefficient ^ N * g.geometricRatio ^ N.choose 2 := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, ih, g.backwardCoeff_eq_geometric N]
      have hchoose : (N + 1).choose 2 = N.choose 2 + N := by
        rw [show N + 1 = N.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hchoose]
      simp only [pow_succ, pow_add]
      ring

/-- Väänänen--Wallisser exponent `N(N+1)/2`, without natural division. -/
def vaananenExponent (N : ℕ) : ℕ := N.choose 2 + N

/-- The paper-normalized term with
`q=3^(6k)/2^(8k)` and
`alpha=2^(8n₀+15)/3^(6n₀+11)`. -/
def vaananenTerm (g : Ray) (N : ℕ) : ℚ :=
  g.geometricRatio ^ vaananenExponent N * g.initialAlpha ^ N

def thetaScale (g : Ray) : ℚ :=
  51 / (3 : ℚ) ^ g.initialTernaryExponent

def vaananenParameter (g : Ray) : ℚ :=
  (3 : ℚ) ^ g.ternaryRate / (2 : ℚ) ^ g.binaryRate

theorem geometricRatio_eq_displayed (g : Ray) :
    g.geometricRatio =
      (2 : ℚ) ^ (8 * g.jump) / (3 : ℚ) ^ (6 * g.jump) := rfl

theorem initialAlpha_eq_displayed (g : Ray) :
    g.initialAlpha =
      (2 : ℚ) ^ (8 * g.initialBranch + 15) /
        (3 : ℚ) ^ (6 * g.initialBranch + 11) := rfl

theorem vaananenParameter_eq_displayed (g : Ray) :
    g.vaananenParameter =
      (3 : ℚ) ^ (6 * g.jump) / (2 : ℚ) ^ (8 * g.jump) := rfl

theorem backwardDefect_eq_scaled (g : Ray) (t : ℕ) :
    g.backwardDefect t =
      (51 / (3 : ℚ) ^ g.initialTernaryExponent) /
        (3 : ℚ) ^ (g.ternaryRate * t) := by
  rw [backwardDefect, g.ternaryExponent_eq t, pow_add]
  ring

/-- Coefficientwise conversion of QM51 to QM52, including the exact rational
prefactor and sign convention. -/
theorem weightedDefect_eq_scaled_vaananenTerm (g : Ray) (N : ℕ) :
    backwardPrefixProduct g.backwardCoeff N * g.backwardDefect N =
      g.thetaScale * g.vaananenTerm N := by
  rw [g.backwardPrefixProduct_eq_geometric N,
    g.backwardDefect_eq_scaled N]
  simp only [firstCoefficient, geometricRatio, initialAlpha, vaananenTerm,
    vaananenExponent, thetaScale]
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  ring

theorem geometricRatio_eq_parameter_inverse (g : Ray) :
    g.geometricRatio = g.vaananenParameter⁻¹ := by
  simp [geometricRatio, vaananenParameter]

theorem parameter_num_den_coprime (g : Ray) :
    (3 ^ g.ternaryRate).Coprime (2 ^ g.binaryRate) :=
  (by norm_num : Nat.Coprime 3 2).pow _ _

theorem parameter_numerator_gt_one (g : Ray) :
    1 < 3 ^ g.ternaryRate := by
  apply Nat.one_lt_pow
  · simp [ternaryRate, g.jump_pos.ne']
  · norm_num

theorem parameter_denominator_pos (g : Ray) :
    0 < 2 ^ g.binaryRate := by positivity

theorem rate_power_lt (g : Ray) :
    2 ^ g.binaryRate < 3 ^ g.ternaryRate := by
  simp only [binaryRate, ternaryRate]
  calc
    2 ^ (8 * g.jump) = (2 ^ 8) ^ g.jump := by rw [pow_mul]
    _ < (3 ^ 6) ^ g.jump :=
      Nat.pow_lt_pow_left (by norm_num) g.jump_pos.ne'
    _ = 3 ^ (6 * g.jump) := by rw [pow_mul]

/-- Exact integer form of the exponent-slope hypothesis `3*8=4*6`. -/
theorem exponent_slope_condition : 4 * 6 ≤ 3 * 8 := by norm_num

/-- Exact elementary size audit for the one-argument, zero-derivative
Väänänen--Wallisser application. -/
theorem vaananenWallisser_size_condition :
    1 - (8 : ℝ) * Real.log 2 / (6 * Real.log 3) <
      (3 - √5) / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 8 := by norm_num
  have hlogpow : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
    Real.strictMonoOn_log
      (show 0 < (3 : ℝ) ^ 5 by positivity)
      (show 0 < (2 : ℝ) ^ 8 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hratio : (5 : ℝ) / 6 <
      8 * Real.log 2 / (6 * Real.log 3) := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 6)
      (mul_pos (by norm_num) hlog3)).2
    calc
      (5 : ℝ) * (6 * Real.log 3) =
          6 * (5 * Real.log 3) := by ring
      _ < 6 * (8 * Real.log 2) :=
        mul_lt_mul_of_pos_left hlogpow (by norm_num)
      _ = 8 * Real.log 2 * 6 := by ring
  have hsqrt_nonneg : 0 ≤ √(5 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(5 : ℝ)) ^ 2 = 5 := by norm_num
  have hsqrt_lt : √(5 : ℝ) < 8 / 3 := by
    nlinarith [show (45 : ℝ) < 64 by norm_num]
  nlinarith

/-! ## `Q_2` endpoint -/

noncomputable def padicDefectTerm (g : Ray) (t : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t : ℚ_[2])

theorem norm_backwardCoeff (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ binaryExponent g.initialBranch g.jump t := by
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
    (g.binaryExponent_pos t).ne'
  rw [hn, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_backwardPrefixProduct_le (g : Ray) (N : ℕ) :
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ N := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (g.norm_backwardCoeff_le_half N)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one (g : Ray) (t : ℕ) :
    ‖(g.backwardDefect t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖((3 : ℚ) : ℚ_[2])‖ = 1 := by
    have hp : ‖(3 : ℚ_[2])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    norm_num only [Rat.cast_ofNat]
    exact hp
  have h51 : ‖(51 : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat 51 : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one (p := 2) (Int.ofNat 51)
  rw [backwardDefect, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, norm_div, norm_pow, hthree, one_pow, div_one]
  exact h51

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

noncomputable def padicVaananenTerm (g : Ray) (N : ℕ) : ℚ_[2] :=
  (g.vaananenTerm N : ℚ_[2])

theorem padicDefectTerm_eq_scaled_vaananenTerm (g : Ray) (N : ℕ) :
    g.padicDefectTerm N =
      (g.thetaScale : ℚ_[2]) * g.padicVaananenTerm N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.weightedDefect_eq_scaled_vaananenTerm N)
  simpa [padicDefectTerm, padicVaananenTerm, Rat.cast_mul] using h

theorem thetaScale_ne_zero (g : Ray) : g.thetaScale ≠ 0 := by
  simp [thetaScale]

theorem padic_thetaScale_ne_zero (g : Ray) :
    (g.thetaScale : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.thetaScale_ne_zero

theorem padicVaananenTerm_summable (g : Ray) :
    Summable g.padicVaananenTerm := by
  let c : ℚ_[2] := (g.thetaScale : ℚ_[2])
  have hs := g.padicDefectTerm_summable.mul_left c⁻¹
  refine hs.congr ?_
  intro N
  rw [g.padicDefectTerm_eq_scaled_vaananenTerm]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ g.padic_thetaScale_ne_zero, one_mul]

noncomputable def padicVaananenSum (g : Ray) : ℚ_[2] :=
  ∑' N, g.padicVaananenTerm N

theorem padicDefectSum_eq_scaled_vaananenSum (g : Ray) :
    g.padicDefectSum =
      (g.thetaScale : ℚ_[2]) * g.padicVaananenSum := by
  have hv := g.padicVaananenTerm_summable.hasSum.mul_left
    (g.thetaScale : ℚ_[2])
  have hfun :
      (fun N => (g.thetaScale : ℚ_[2]) * g.padicVaananenTerm N) =
        g.padicDefectTerm := by
    funext N
    exact (g.padicDefectTerm_eq_scaled_vaananenTerm N).symm
  rw [hfun] at hv
  exact g.padicDefectTerm_summable.hasSum.unique hv

theorem padicCandidate_eq_scaled_vaananenSum (g : Ray) :
    g.padicCandidate =
      -(g.thetaScale : ℚ_[2]) * g.padicVaananenSum := by
  rw [padicCandidate, g.padicDefectSum_eq_scaled_vaananenSum]
  ring

noncomputable def padicDefectPartial (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect N : ℚ_[2])

theorem padicDefectPartial_eq_sum (g : Ray) (N : ℕ) :
    g.padicDefectPartial N =
      ∑ t ∈ Finset.range N, g.padicDefectTerm t := by
  induction N with
  | zero => simp [padicDefectPartial, backwardPrefixDefect]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [padicDefectPartial, backwardPrefixDefect,
        padicDefectTerm, Rat.cast_add, Rat.cast_mul]

theorem padicDefectPartial_tendsto_sum (g : Ray) :
    Tendsto g.padicDefectPartial atTop (𝓝 g.padicDefectSum) := by
  have hsum := g.padicDefectTerm_summable.hasSum.tendsto_sum_nat
  have heq : g.padicDefectPartial = fun N =>
      ∑ t ∈ Finset.range N, g.padicDefectTerm t := by
    funext N
    exact g.padicDefectPartial_eq_sum N
  rw [heq]
  simpa only [padicDefectSum] using hsum

noncomputable def padicTerminal (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff N : ℚ_[2]) * g.oddPart N

theorem norm_padicTerminal_le (g : Ray) (N : ℕ) :
    ‖g.padicTerminal N‖ ≤ ((2 : ℝ)⁻¹) ^ N := by
  have hodd : ‖(g.oddPart N : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.oddPart N))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ *
          ‖(g.oddPart N : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hodd (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ N := g.norm_backwardPrefixProduct_le N

theorem padicTerminal_tendsto_zero (g : Ray) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : Ray) (N : ℕ) :
    (g.oddPart 0 : ℚ_[2]) =
      g.padicTerminal N - g.padicDefectPartial N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series N)
  simpa [padicTerminal, padicDefectPartial, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast] using h

/-- Every ordinary arithmetic ray forces the 2-adic candidate to equal its
embedded initial odd part. -/
theorem padicCandidate_eq_initial (g : Ray) :
    g.padicCandidate = (g.oddPart 0 : ℚ_[2]) := by
  have heq : g.padicDefectPartial = fun N =>
      g.padicTerminal N - (g.oddPart 0 : ℚ_[2]) := by
    funext N
    have h := g.padic_finite_series N
    linear_combination h
  have hlim : Tendsto g.padicDefectPartial atTop
      (𝓝 (-(g.oddPart 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.padicDefectSum = -(g.oddPart 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.padicDefectPartial_tendsto_sum hlim
  rw [padicCandidate, hsum]
  simp

theorem candidate_irrational_of_vaananenSum_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicVaananenSum) :
    NormalizedStandardPayloadStream.IsPadicIrrational g.padicCandidate := by
  intro q heq
  apply hirr (-q / g.thetaScale)
  rw [Rat.cast_div, Rat.cast_neg]
  apply (eq_div_iff g.padic_thetaScale_ne_zero).2
  rw [g.padicCandidate_eq_scaled_vaananenSum] at heq
  linear_combination -heq

/-- Honest external-citation seam.  Irrationality of the explicit
paper-normalized p-adic theta value excludes the arithmetic ether ray. -/
theorem false_of_vaananenSum_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicVaananenSum) : False := by
  have hcand := g.candidate_irrational_of_vaananenSum_irrational hirr
  exact hcand (g.oddPart 0) g.padicCandidate_eq_initial

end Ray

end EtherCounterLinearTheta

/-! ## Connection to the executable ether normalization -/

open EtherCounterLinearTheta

namespace EtherCounterAperiodic.NormalizedOrbit

/-- QM50: a normalized autonomous ether orbit whose one-based level is the
arithmetic schedule produces exactly the `Ray` used above. -/
def toLinearThetaRay
    (o : EtherCounterAperiodic.NormalizedOrbit) (n₀ k : ℕ)
    (hn₀ : 0 < n₀) (hk : 0 < k)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterLinearTheta.branch n₀ k t) : EtherCounterLinearTheta.Ray where
  initialBranch := n₀
  jump := k
  initialBranch_pos := hn₀
  jump_pos := hk
  oddPart := o.oddPart
  oddPart_pos t := by
    have hvalue := o.value_pos t
    rw [o.factor t] at hvalue
    exact Nat.pos_of_mul_pos_left hvalue
  balance t := by
    have hstep := o.transition t
    have hB : EtherCounterLinearTheta.binaryExponent n₀ k t =
        8 * o.level (t + 1) + 23 := by
      simp only [EtherCounterLinearTheta.binaryExponent]
      rw [← hschedule (t + 1)]
      omega
    have hA : EtherCounterLinearTheta.ternaryExponent n₀ k t =
        6 * o.level t + 17 := by
      simp only [EtherCounterLinearTheta.ternaryExponent]
      rw [← hschedule t]
      omega
    rw [hB, hA]
    calc
      2 ^ (8 * o.level (t + 1) + 23) * o.oddPart (t + 1) =
          2 ^ 20 * o.value (t + 1) := by
        rw [o.factor (t + 1)]
        rw [show 8 * o.level (t + 1) + 23 =
          20 + (8 * o.level (t + 1) + 3) by omega, pow_add]
        ring
      _ = 3 ^ (6 * o.level t + 17) * o.oddPart t + 51 := hstep

theorem no_arithmetic_schedule_of_irrational
    (o : EtherCounterAperiodic.NormalizedOrbit) (n₀ k : ℕ)
    (hn₀ : 0 < n₀) (hk : 0 < k)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterLinearTheta.branch n₀ k t)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      (o.toLinearThetaRay n₀ k hn₀ hk hschedule).padicVaananenSum) : False :=
  (o.toLinearThetaRay n₀ k hn₀ hk hschedule).false_of_vaananenSum_irrational hirr

end EtherCounterAperiodic.NormalizedOrbit
end KontoroC
