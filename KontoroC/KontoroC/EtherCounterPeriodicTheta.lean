/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterLinearTheta
import KontoroC.ChargePhaseUpPeriodicTheta

/-!
# Period-two increment schedules for the ether core

This file treats the first genuinely nonconstant branch schedule left by the
autonomous ether no-go results.  A period-two increment word with positive
cycle sum `K` is expressed without signed-natural subtraction by the exact
law `branch (t+2)=branch t+K`.  This includes negative increments inside a
cycle while requiring every actual branch to remain positive.

The literal EC17 recurrence is split into its even and odd residue series and
identified coefficientwise with two Väänänen--Wallisser theta values.  The
final impossibility theorem is conditional on the external two-value p-adic
linear-independence statement.
-/

namespace KontoroC
namespace EtherCounterPeriodicTheta

open Filter Topology MersennePacketRenewal PeriodicPhaseUp

/-! ## Exact period-two EC17 ray -/

structure Ray where
  cycleGain : ℕ
  cycleGain_pos : 0 < cycleGain
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  branch_two_shift : ∀ t, branch (t + 2) = branch t + cycleGain
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  balance : ∀ t,
    2 ^ (8 * branch (t + 1) + 15) * core (t + 1) =
      3 ^ (6 * branch t + 11) * core t + 17

namespace Ray

def binaryExponent (g : Ray) (t : ℕ) : ℕ := 8 * g.branch (t + 1) + 15
def ternaryExponent (g : Ray) (t : ℕ) : ℕ := 6 * g.branch t + 11

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ g.binaryExponent t / (3 : ℚ) ^ g.ternaryExponent t

def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  17 / (3 : ℚ) ^ g.ternaryExponent t

def ratio (g : Ray) : ℚ :=
  (2 : ℚ) ^ (8 * g.cycleGain) / (3 : ℚ) ^ (6 * g.cycleGain)

def defectRatio (g : Ray) : ℚ :=
  1 / (3 : ℚ) ^ (6 * g.cycleGain)

theorem binaryExponent_two_shift (g : Ray) (t : ℕ) :
    g.binaryExponent (t + 2) = g.binaryExponent t + 8 * g.cycleGain := by
  simp only [binaryExponent]
  rw [show t + 2 + 1 = (t + 1) + 2 by omega, g.branch_two_shift (t + 1)]
  ring

theorem ternaryExponent_two_shift (g : Ray) (t : ℕ) :
    g.ternaryExponent (t + 2) = g.ternaryExponent t + 6 * g.cycleGain := by
  simp only [ternaryExponent, g.branch_two_shift t]
  ring

theorem backwardCoeff_two_shift (g : Ray) (t : ℕ) :
    g.backwardCoeff (t + 2) = g.ratio * g.backwardCoeff t := by
  rw [backwardCoeff, backwardCoeff, g.binaryExponent_two_shift,
    g.ternaryExponent_two_shift]
  simp only [ratio, pow_add]
  ring

theorem backwardDefect_two_shift (g : Ray) (t : ℕ) :
    g.backwardDefect (t + 2) = g.defectRatio * g.backwardDefect t := by
  rw [backwardDefect, backwardDefect, g.ternaryExponent_two_shift]
  simp only [defectRatio, pow_add]
  ring

theorem backwardCoeff_two_mul_add (g : Ray) (q r : ℕ) :
    g.backwardCoeff (2 * q + r) =
      g.ratio ^ q * g.backwardCoeff r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2 * (q + 1) + r = (2 * q + r) + 2 by ring,
        g.backwardCoeff_two_shift, ih, pow_succ]
      ring

theorem backwardDefect_two_mul_add (g : Ray) (q r : ℕ) :
    g.backwardDefect (2 * q + r) =
      g.defectRatio ^ q * g.backwardDefect r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2 * (q + 1) + r = (2 * q + r) + 2 by ring,
        g.backwardDefect_two_shift, ih, pow_succ]
      ring

def cycleCoeff (g : Ray) : ℚ := g.backwardCoeff 0 * g.backwardCoeff 1

theorem prefix_even (g : Ray) (q : ℕ) :
    backwardPrefixProduct g.backwardCoeff (2 * q) =
      g.cycleCoeff ^ q * g.ratio ^ (2 * q.choose 2) := by
  induction q with
  | zero => simp [backwardPrefixProduct]
  | succ q ih =>
      have hzero : g.backwardCoeff (2 * q) =
          g.ratio ^ q * g.backwardCoeff 0 := by
        simpa using g.backwardCoeff_two_mul_add q 0
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by ring,
        backwardPrefixProduct, backwardPrefixProduct, ih,
        hzero,
        g.backwardCoeff_two_mul_add q 1]
      rw [show (q + 1).choose 2 = q.choose 2 + q by
        rw [show q + 1 = q.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      simp only [cycleCoeff, pow_succ, pow_add]
      ring

theorem prefix_odd (g : Ray) (q : ℕ) :
    backwardPrefixProduct g.backwardCoeff (2 * q + 1) =
      g.cycleCoeff ^ q * g.ratio ^ (2 * q.choose 2) *
        g.ratio ^ q * g.backwardCoeff 0 := by
  have hzero : g.backwardCoeff (2 * q) =
      g.ratio ^ q * g.backwardCoeff 0 := by
    simpa using g.backwardCoeff_two_mul_add q 0
  rw [backwardPrefixProduct, g.prefix_even, hzero]
  ring

def thetaData (g : Ray) : PeriodicPhaseUp.ThetaResidueData 2 where
  ratio := g.ratio
  defectRatio := g.defectRatio
  cycleCoeff := g.cycleCoeff
  prefixScale r := if (r : ℕ) = 0 then g.backwardDefect 0
    else g.backwardCoeff 0 * g.backwardDefect 1

def weightedTerm (g : Ray) (t : ℕ) : ℚ :=
  backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t

/-- Literal EC17 coefficient at residue `r` equals the abstract theta weight;
this is the semantic seam preventing a free surrogate substitution. -/
theorem weightedTerm_at (g : Ray) (q : ℕ) (r : Fin 2) :
    g.weightedTerm (2 * q + r) = (g.thetaData).weightedTerm r q := by
  fin_cases r
  · change g.weightedTerm (2 * q) =
      (g.thetaData).weightedTerm (0 : Fin 2) q
    have hdefect : g.backwardDefect (2 * q) =
        g.defectRatio ^ q * g.backwardDefect 0 := by
      simpa using g.backwardDefect_two_mul_add q 0
    rw [weightedTerm, g.prefix_even, hdefect]
    simp [thetaData, PeriodicPhaseUp.ThetaResidueData.weightedTerm,
      pow_mul, mul_pow]
    ring
  · change g.weightedTerm (2 * q + 1) =
      (g.thetaData).weightedTerm (1 : Fin 2) q
    rw [weightedTerm, g.prefix_odd, g.backwardDefect_two_mul_add q 1]
    simp [thetaData, PeriodicPhaseUp.ThetaResidueData.weightedTerm,
      pow_mul, mul_pow]
    ring

theorem ratio_pos (g : Ray) : 0 < g.ratio := by simp [ratio]
theorem ratio_ne_zero (g : Ray) : g.ratio ≠ 0 := ne_of_gt g.ratio_pos
theorem defectRatio_ne_zero (g : Ray) : g.defectRatio ≠ 0 := by
  simp [defectRatio]
theorem cycleCoeff_ne_zero (g : Ray) : g.cycleCoeff ≠ 0 := by
  simp [cycleCoeff, backwardCoeff]

theorem ratio_lt_one (g : Ray) : g.ratio < 1 := by
  rw [ratio]
  apply (div_lt_one (by positivity : (0 : ℚ) < 3 ^ (6 * g.cycleGain))).2
  exact_mod_cast (show 2 ^ (8 * g.cycleGain) <
      3 ^ (6 * g.cycleGain) by
    calc
      2 ^ (8 * g.cycleGain) = (2 ^ 8) ^ g.cycleGain := by rw [pow_mul]
      _ < (3 ^ 6) ^ g.cycleGain :=
        Nat.pow_lt_pow_left (by norm_num) g.cycleGain_pos.ne'
      _ = 3 ^ (6 * g.cycleGain) := by rw [pow_mul])

theorem theta_arguments_separated (g : Ray) (r s : Fin 2)
    (hrs : r ≠ s) (z : ℤ) :
    (g.thetaData).argument r / (g.thetaData).argument s ≠
      (g.thetaData).parameterInverse⁻¹ ^ z := by
  intro h
  apply hrs
  exact (g.thetaData).eq_of_argument_ratio g.ratio_pos
    (ne_of_lt g.ratio_lt_one) g.defectRatio_ne_zero
    g.cycleCoeff_ne_zero r s z h

theorem step_backward (g : Ray) (t : ℕ) :
    (g.core t : ℚ) =
      g.backwardCoeff t * g.core (t + 1) - g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ g.binaryExponent t * g.core (t + 1) =
        (3 : ℚ) ^ g.ternaryExponent t * g.core t + 17 := by
    exact_mod_cast g.balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree : (3 : ℚ) ^ g.ternaryExponent t ≠ 0 := by positivity
  field_simp
  nlinarith

theorem finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff N * g.core N -
        backwardPrefixDefect g.backwardCoeff g.backwardDefect N :=
  backward_affine_unroll (fun t => g.step_backward t) N

/-! ## The actual completed two-residue series -/

theorem binaryExponent_pos (g : Ray) (t : ℕ) :
    0 < g.binaryExponent t := by simp [binaryExponent]

noncomputable def padicWeightedTerm (g : Ray) (t : ℕ) : ℚ_[2] :=
  (g.weightedTerm t : ℚ_[2])

theorem norm_backwardCoeff (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ g.binaryExponent t := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [g.norm_backwardCoeff]
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
    (g.binaryExponent_pos t).ne'
  rw [he, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ e ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) e]

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
  have h17 : ‖(17 : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat 17 : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one _
  rw [backwardDefect, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    norm_div, norm_pow, hthree, one_pow, div_one]
  exact h17

theorem norm_padicWeightedTerm_le (g : Ray) (t : ℕ) :
    ‖g.padicWeightedTerm t‖ ≤ ((2 : ℝ)⁻¹) ^ t := by
  rw [padicWeightedTerm, weightedTerm, Rat.cast_mul, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ *
          ‖(g.backwardDefect t : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (g.norm_backwardDefect_le_one t)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff t : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ t := g.norm_backwardPrefixProduct_le t

theorem padicWeightedTerm_tendsto_zero (g : Ray) :
    Tendsto g.padicWeightedTerm atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicWeightedTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicWeightedTerm_summable (g : Ray) :
    Summable g.padicWeightedTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using g.padicWeightedTerm_tendsto_zero

noncomputable def padicWeightedSum (g : Ray) : ℚ_[2] :=
  ∑' t, g.padicWeightedTerm t

noncomputable def padicCandidate (g : Ray) : ℚ_[2] := -g.padicWeightedSum

noncomputable def padicPartial (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect N : ℚ_[2])

theorem padicPartial_eq_sum (g : Ray) (N : ℕ) :
    g.padicPartial N = ∑ t ∈ Finset.range N, g.padicWeightedTerm t := by
  induction N with
  | zero => simp [padicPartial, backwardPrefixDefect]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [padicPartial, backwardPrefixDefect, padicWeightedTerm,
        weightedTerm, Rat.cast_add, Rat.cast_mul]

theorem padicPartial_tendsto_sum (g : Ray) :
    Tendsto g.padicPartial atTop (𝓝 g.padicWeightedSum) := by
  have hs := g.padicWeightedTerm_summable.hasSum.tendsto_sum_nat
  have heq : g.padicPartial = fun N =>
      ∑ t ∈ Finset.range N, g.padicWeightedTerm t := by
    funext N
    exact g.padicPartial_eq_sum N
  rw [heq]
  simpa only [padicWeightedSum] using hs

noncomputable def padicTerminal (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff N : ℚ_[2]) * g.core N

theorem norm_padicTerminal_le (g : Ray) (N : ℕ) :
    ‖g.padicTerminal N‖ ≤ ((2 : ℝ)⁻¹) ^ N := by
  have hcore : ‖(g.core N : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.core N))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ *
          ‖(g.core N : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hcore (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ N := g.norm_backwardPrefixProduct_le N

theorem padicTerminal_tendsto_zero (g : Ray) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ_[2]) = g.padicTerminal N - g.padicPartial N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series N)
  simpa [padicTerminal, padicPartial, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast] using h

/-- Every ordinary EC17 ray makes the completed candidate rational: it is
exactly the embedded initial positive core. -/
theorem padicCandidate_eq_initial (g : Ray) :
    g.padicCandidate = (g.core 0 : ℚ_[2]) := by
  have heq : g.padicPartial = fun N =>
      g.padicTerminal N - (g.core 0 : ℚ_[2]) := by
    funext N
    have h := g.padic_finite_series N
    linear_combination h
  have hlim : Tendsto g.padicPartial atTop
      (𝓝 (-(g.core 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.padicWeightedSum = -(g.core 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.padicPartial_tendsto_sum hlim
  rw [padicCandidate, hsum]
  simp

private theorem finEquiv_val (n : ℕ) [NeZero n] (r : Fin n) :
    (ZMod.finEquiv n r).val = (r : ℕ) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The actual EC17 sum splits into its even and odd subsequences. -/
theorem padicWeightedSum_eq_sum_residues (g : Ray) :
    g.padicWeightedSum =
      ∑ r : Fin 2, ∑' q : ℕ, g.padicWeightedTerm (2 * q + r) := by
  let f : ℕ → ℚ_[2] := g.padicWeightedTerm
  have hf : Summable f := g.padicWeightedTerm_summable
  calc
    g.padicWeightedSum = ∑' i : ℕ, f i := rfl
    _ = ∑ j : ZMod 2, ∑' q : ℕ, f (j.val + 2 * q) :=
      Nat.sumByResidueClasses hf 2
    _ = ∑ r : Fin 2,
        ∑' q : ℕ, f ((ZMod.finEquiv 2 r).val + 2 * q) := by
      exact (Equiv.sum_comp (ZMod.finEquiv 2).toEquiv _).symm
    _ = ∑ r : Fin 2,
        ∑' q : ℕ, g.padicWeightedTerm (2 * q + r) := by
      apply Fintype.sum_congr
      intro r
      have hval := finEquiv_val 2 r
      congr 1
      funext q
      simp only [f, hval]
      congr 1
      omega

noncomputable def padicVaananenTerm (g : Ray) (r : Fin 2)
    (q : ℕ) : ℚ_[2] := ((g.thetaData).vaananenTerm r q : ℚ_[2])

noncomputable def padicVaananenSum (g : Ray) (r : Fin 2) : ℚ_[2] :=
  ∑' q, g.padicVaananenTerm r q

theorem theta_prefixScale_ne_zero (g : Ray) (r : Fin 2) :
    (g.thetaData).prefixScale r ≠ 0 := by
  fin_cases r <;> simp [thetaData, backwardCoeff, backwardDefect]

theorem padic_theta_prefixScale_ne_zero (g : Ray) (r : Fin 2) :
    ((g.thetaData).prefixScale r : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.theta_prefixScale_ne_zero r

theorem padicWeightedTerm_eq_scaled_vaananenTerm
    (g : Ray) (q : ℕ) (r : Fin 2) :
    g.padicWeightedTerm (2 * q + r) =
      ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenTerm r q := by
  have h := congrArg (fun x : ℚ => (x : ℚ_[2]))
    ((g.weightedTerm_at q r).trans
      ((g.thetaData).weightedTerm_eq_scaled_vaananenTerm
        g.ratio_ne_zero r q))
  simpa [padicWeightedTerm, padicVaananenTerm, Rat.cast_mul] using h

theorem padicVaananenTerm_summable (g : Ray) (r : Fin 2) :
    Summable (g.padicVaananenTerm r) := by
  let c : ℚ_[2] := ((g.thetaData).prefixScale r : ℚ_[2])
  have hc : c ≠ 0 := g.padic_theta_prefixScale_ne_zero r
  have hzero : Tendsto
      (fun q => g.padicWeightedTerm (2 * q + r)) atTop (𝓝 0) := by
    have hindex : Tendsto (fun q : ℕ => 2 * q + (r : ℕ))
        atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with q hq
      omega
    exact g.padicWeightedTerm_tendsto_zero.comp hindex
  have hs : Summable (fun q => g.padicWeightedTerm (2 * q + r)) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using hzero
  have hscaled := hs.mul_left c⁻¹
  refine hscaled.congr ?_
  intro q
  rw [g.padicWeightedTerm_eq_scaled_vaananenTerm q r]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem padicResidueSum_eq_scaled_vaananenSum (g : Ray) (r : Fin 2) :
    (∑' q, g.padicWeightedTerm (2 * q + r)) =
      ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenSum r := by
  have hv := (g.padicVaananenTerm_summable r).hasSum.mul_left
    ((g.thetaData).prefixScale r : ℚ_[2])
  have hfun :
      (fun q => ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenTerm r q) =
      (fun q => g.padicWeightedTerm (2 * q + r)) := by
    funext q
    exact (g.padicWeightedTerm_eq_scaled_vaananenTerm q r).symm
  rw [hfun] at hv
  simpa only [padicVaananenSum] using hv.tsum_eq

theorem padicWeightedSum_eq_scaled_vaananenSums (g : Ray) :
    g.padicWeightedSum =
      ∑ r : Fin 2, ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenSum r := by
  rw [g.padicWeightedSum_eq_sum_residues]
  apply Fintype.sum_congr
  intro r
  exact g.padicResidueSum_eq_scaled_vaananenSum r

/-- The exact external statement needed from Väänänen--Wallisser at
`ell=2, sigma=0, p=2`: `1` and the two residue theta values are linearly
independent over `ℚ`. -/
def ThetaIndependent (g : Ray) : Prop :=
  ∀ (a₀ : ℚ) (a : Fin 2 → ℚ),
    (a₀ ≠ 0 ∨ ∃ r, a r ≠ 0) →
    (a₀ : ℚ_[2]) + ∑ r : Fin 2,
      (a r : ℚ_[2]) * g.padicVaananenSum r ≠ 0

/-- Honest citation seam.  The exact two-value linear independence statement
contradicts the positive rational core forced by every period-two EC17 ray. -/
theorem false_of_thetaIndependent (g : Ray)
    (hind : g.ThetaIndependent) : False := by
  have hrelation :
      (g.core 0 : ℚ_[2]) + ∑ r : Fin 2,
        ((g.thetaData).prefixScale r : ℚ_[2]) *
          g.padicVaananenSum r = 0 := by
    have hcand := g.padicCandidate_eq_initial
    rw [padicCandidate, g.padicWeightedSum_eq_scaled_vaananenSums] at hcand
    linear_combination -hcand
  have hcore : (g.core 0 : ℚ) ≠ 0 := by
    exact_mod_cast (g.core_pos 0).ne'
  exact hind (g.core 0) (g.thetaData).prefixScale (Or.inl hcore) hrelation

end Ray

/-! ## Exact size boundary -/

noncomputable def gamma : ℝ :=
  1 - (8 : ℝ) * Real.log 2 / (6 * Real.log 3)

noncomputable def threshold (L : ℕ) : ℝ :=
  (2 * L + 1 - √(1 + 4 * (L : ℝ) ^ 2)) / (2 * L)

/-- QM73: the exact all-derivative threshold printed in the 1989 theorem.
It depends only on the combined parameter `ell * (sigma+1)`. -/
noncomputable def derivativeThreshold (ell sigma : ℕ) : ℝ :=
  threshold (ell * (sigma + 1))

theorem derivativeThreshold_eq (ell sigma : ℕ) :
    derivativeThreshold ell sigma =
      (2 * ell * (sigma + 1) + 1 -
        √(1 + 4 * ((ell * (sigma + 1) : ℕ) : ℝ) ^ 2)) /
        (2 * ell * (sigma + 1)) := by
  simp [derivativeThreshold, threshold]
  ring

theorem derivativeThreshold_zero (ell : ℕ) :
    derivativeThreshold ell 0 = threshold ell := by
  simp [derivativeThreshold]

theorem gamma_lt_one_sixth : gamma < (1 : ℝ) / 6 := by
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
      (5 : ℝ) * (6 * Real.log 3) = 6 * (5 * Real.log 3) := by ring
      _ < 6 * (8 * Real.log 2) :=
        mul_lt_mul_of_pos_left hlogpow (by norm_num)
      _ = 8 * Real.log 2 * 6 := by ring
  rw [gamma]
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

theorem five_thirtyseconds_lt_gamma : (5 : ℝ) / 32 < gamma := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ 128 < (3 : ℝ) ^ 81 := by norm_num
  have hlogpow : Real.log ((2 : ℝ) ^ 128) < Real.log ((3 : ℝ) ^ 81) :=
    Real.strictMonoOn_log
      (show 0 < (2 : ℝ) ^ 128 by positivity)
      (show 0 < (3 : ℝ) ^ 81 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hratio : Real.log 2 / Real.log 3 < (81 : ℝ) / 128 := by
    apply (div_lt_div_iff₀ hlog3 (by norm_num : (0 : ℝ) < 128)).2
    simpa [mul_comm] using hlogpow
  rw [gamma]
  have heq : (8 : ℝ) * Real.log 2 / (6 * Real.log 3) =
      (4 / 3) * (Real.log 2 / Real.log 3) := by
    field_simp [ne_of_gt hlog3]
    norm_num
  rw [heq]
  nlinarith

theorem threshold_three_lt_five_thirtyseconds :
    threshold 3 < (5 : ℝ) / 32 := by
  have hsqrt_nonneg : 0 ≤ √(37 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(37 : ℝ)) ^ 2 = 37 := by norm_num
  have hsqrt_gt : (97 : ℝ) / 16 < √37 := by
    nlinarith [show (97 : ℝ) ^ 2 < 37 * 16 ^ 2 by norm_num]
  norm_num [threshold]
  nlinarith

theorem threshold_three_lt_gamma : threshold 3 < gamma :=
  threshold_three_lt_five_thirtyseconds.trans five_thirtyseconds_lt_gamma

/-- QM74: positive derivative order cannot rescue the three-phase EC17
endpoint.  Its sufficient threshold is already below the proven lower bound
for `gamma`. -/
theorem derivativeThreshold_three_lt_gamma (sigma : ℕ) (hsigma : 1 ≤ sigma) :
    derivativeThreshold 3 sigma < gamma := by
  let m : ℕ := 3 * (sigma + 1)
  have hm_nat : 6 ≤ m := by simp [m]; omega
  have hm : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm_nat)
  have hsqrt_nonneg : 0 ≤ √(1 + 4 * (m : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(1 + 4 * (m : ℝ) ^ 2)) ^ 2 =
      1 + 4 * (m : ℝ) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_gt : 2 * (m : ℝ) < √(1 + 4 * (m : ℝ) ^ 2) := by
    nlinarith
  have hthreshold : derivativeThreshold 3 sigma < 1 / (2 * (m : ℝ)) := by
    rw [derivativeThreshold, threshold]
    change (2 * (m : ℝ) + 1 - √(1 + 4 * (m : ℝ) ^ 2)) /
      (2 * (m : ℝ)) < 1 / (2 * (m : ℝ))
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hrecip : 1 / (2 * (m : ℝ)) ≤ (1 : ℝ) / 12 := by
    have hm_real : (6 : ℝ) ≤ m := by exact_mod_cast hm_nat
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  calc
    derivativeThreshold 3 sigma < 1 / (2 * (m : ℝ)) := hthreshold
    _ ≤ (1 : ℝ) / 12 := hrecip
    _ < (5 : ℝ) / 32 := by norm_num
    _ < gamma := five_thirtyseconds_lt_gamma

end EtherCounterPeriodicTheta
end KontoroC
