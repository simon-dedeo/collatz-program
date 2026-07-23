/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodThree
import KontoroC.ChargePhaseUpPeriodicTheta

/-!
# The literal period-three EC17 ray as three p-adic theta values

This file supplies the semantic seam missing from the active period-three
construction.  It splits the actual one-step EC17 backward series into three
residue classes and identifies each coefficient with the paper-normalized
Väänänen--Wallisser theta term.  The eventual linear-independence input is
kept explicit: the 1989 sufficient size criterion does not prove it at this
three-value parameter.
-/

namespace KontoroC
namespace EtherCounterPeriodThreeTheta

open Filter Topology MersennePacketRenewal PeriodicPhaseUp

abbrev Ray := EtherCounterPeriodThree.Ray

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

/-- The three displayed affine phase laws really do give one global
three-step shift law. -/
theorem branch_three_shift (g : Ray) (t : ℕ) :
    g.branch (t + 3) = g.branch t + g.cycleGain := by
  generalize hq : t / 3 = q
  generalize hr : t % 3 = r
  have hrlt : r < 3 := by
    rw [← hr]
    exact Nat.mod_lt t (by omega)
  have ht : 3 * q + r = t := by
    have h := Nat.div_add_mod t 3
    rw [hq, hr] at h
    omega
  interval_cases r
  · have ht0 : t = 3 * q := by omega
    rw [ht0, show 3 * q + 3 = 3 * (q + 1) by ring,
      g.branch_zero, g.branch_zero]
    ring
  · have ht1 : t = 3 * q + 1 := by omega
    rw [ht1, show 3 * q + 1 + 3 = 3 * (q + 1) + 1 by ring,
      g.branch_one, g.branch_one]
    ring
  · have ht2 : t = 3 * q + 2 := by omega
    rw [ht2, show 3 * q + 2 + 3 = 3 * (q + 1) + 2 by ring,
      g.branch_two, g.branch_two]
    ring

theorem binaryExponent_three_shift (g : Ray) (t : ℕ) :
    g.binaryExponent (t + 3) =
      g.binaryExponent t + 8 * g.cycleGain := by
  simp only [binaryExponent]
  rw [show t + 3 + 1 = (t + 1) + 3 by omega,
    g.branch_three_shift (t + 1)]
  ring

theorem ternaryExponent_three_shift (g : Ray) (t : ℕ) :
    g.ternaryExponent (t + 3) =
      g.ternaryExponent t + 6 * g.cycleGain := by
  simp only [ternaryExponent, g.branch_three_shift t]
  ring

theorem backwardCoeff_three_shift (g : Ray) (t : ℕ) :
    g.backwardCoeff (t + 3) = g.ratio * g.backwardCoeff t := by
  rw [backwardCoeff, backwardCoeff, g.binaryExponent_three_shift,
    g.ternaryExponent_three_shift]
  simp only [ratio, pow_add]
  ring

theorem backwardDefect_three_shift (g : Ray) (t : ℕ) :
    g.backwardDefect (t + 3) = g.defectRatio * g.backwardDefect t := by
  rw [backwardDefect, backwardDefect, g.ternaryExponent_three_shift]
  simp only [defectRatio, pow_add]
  ring

theorem backwardCoeff_three_mul_add (g : Ray) (q r : ℕ) :
    g.backwardCoeff (3 * q + r) =
      g.ratio ^ q * g.backwardCoeff r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 3 * (q + 1) + r = (3 * q + r) + 3 by ring,
        g.backwardCoeff_three_shift, ih, pow_succ]
      ring

theorem backwardDefect_three_mul_add (g : Ray) (q r : ℕ) :
    g.backwardDefect (3 * q + r) =
      g.defectRatio ^ q * g.backwardDefect r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 3 * (q + 1) + r = (3 * q + r) + 3 by ring,
        g.backwardDefect_three_shift, ih, pow_succ]
      ring

def cycleCoeff (g : Ray) : ℚ :=
  g.backwardCoeff 0 * g.backwardCoeff 1 * g.backwardCoeff 2

theorem prefix_cycle (g : Ray) (q : ℕ) :
    backwardPrefixProduct g.backwardCoeff (3 * q) =
      g.cycleCoeff ^ q * g.ratio ^ (3 * q.choose 2) := by
  induction q with
  | zero => simp [backwardPrefixProduct]
  | succ q ih =>
      have hc0 : g.backwardCoeff (3 * q) =
          g.ratio ^ q * g.backwardCoeff 0 := by
        simpa using g.backwardCoeff_three_mul_add q 0
      rw [show 3 * (q + 1) = (3 * q + 2) + 1 by ring,
        backwardPrefixProduct, backwardPrefixProduct, backwardPrefixProduct,
        ih, hc0,
        g.backwardCoeff_three_mul_add q 1,
        g.backwardCoeff_three_mul_add q 2]
      rw [show (q + 1).choose 2 = q.choose 2 + q by
        rw [show q + 1 = q.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      simp only [cycleCoeff, pow_succ]
      ring

theorem prefix_phase_one (g : Ray) (q : ℕ) :
    backwardPrefixProduct g.backwardCoeff (3 * q + 1) =
      g.cycleCoeff ^ q * g.ratio ^ (3 * q.choose 2) *
        g.ratio ^ q * g.backwardCoeff 0 := by
  have hc0 : g.backwardCoeff (3 * q) =
      g.ratio ^ q * g.backwardCoeff 0 := by
    simpa using g.backwardCoeff_three_mul_add q 0
  rw [backwardPrefixProduct, g.prefix_cycle, hc0]
  ring

theorem prefix_phase_two (g : Ray) (q : ℕ) :
    backwardPrefixProduct g.backwardCoeff (3 * q + 2) =
      g.cycleCoeff ^ q * g.ratio ^ (3 * q.choose 2) *
        g.ratio ^ (2 * q) *
          (g.backwardCoeff 0 * g.backwardCoeff 1) := by
  rw [backwardPrefixProduct, g.prefix_phase_one,
    g.backwardCoeff_three_mul_add q 1]
  rw [pow_mul]
  ring

def thetaData (g : Ray) : PeriodicPhaseUp.ThetaResidueData 3 where
  ratio := g.ratio
  defectRatio := g.defectRatio
  cycleCoeff := g.cycleCoeff
  prefixScale r :=
    if (r : ℕ) = 0 then g.backwardDefect 0
    else if (r : ℕ) = 1 then
      g.backwardCoeff 0 * g.backwardDefect 1
    else
      g.backwardCoeff 0 * g.backwardCoeff 1 * g.backwardDefect 2

def weightedTerm (g : Ray) (t : ℕ) : ℚ :=
  backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t

/-- The literal period-three EC17 coefficient at phase `r` is exactly the
corresponding abstract theta weight. -/
theorem weightedTerm_at (g : Ray) (q : ℕ) (r : Fin 3) :
    g.weightedTerm (3 * q + r) = (g.thetaData).weightedTerm r q := by
  fin_cases r
  · change g.weightedTerm (3 * q) =
      (g.thetaData).weightedTerm (0 : Fin 3) q
    have hd0 : g.backwardDefect (3 * q) =
        g.defectRatio ^ q * g.backwardDefect 0 := by
      simpa using g.backwardDefect_three_mul_add q 0
    rw [weightedTerm, g.prefix_cycle, hd0]
    simp [thetaData, PeriodicPhaseUp.ThetaResidueData.weightedTerm,
      pow_mul, mul_pow]
    ring
  · change g.weightedTerm (3 * q + 1) =
      (g.thetaData).weightedTerm (1 : Fin 3) q
    rw [weightedTerm, g.prefix_phase_one,
      g.backwardDefect_three_mul_add q 1]
    simp [thetaData, PeriodicPhaseUp.ThetaResidueData.weightedTerm,
      pow_mul, mul_pow]
    ring
  · change g.weightedTerm (3 * q + 2) =
      (g.thetaData).weightedTerm (2 : Fin 3) q
    rw [weightedTerm, g.prefix_phase_two,
      g.backwardDefect_three_mul_add q 2]
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

/-- The three paper arguments are pairwise separated modulo powers of the
theta parameter; this is one of the exact hypotheses in a future
linear-independence application. -/
theorem theta_arguments_separated (g : Ray) (r s : Fin 3)
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

/-! ## Completion in `Q_2` -/

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

/-- The completed three-residue theta candidate is not a surrogate: every
ordinary ray identifies it with its actual positive initial core. -/
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

/-- The actual EC17 sum splits into its three literal phase subsequences. -/
theorem padicWeightedSum_eq_sum_residues (g : Ray) :
    g.padicWeightedSum =
      ∑ r : Fin 3, ∑' q : ℕ, g.padicWeightedTerm (3 * q + r) := by
  let f : ℕ → ℚ_[2] := g.padicWeightedTerm
  have hf : Summable f := g.padicWeightedTerm_summable
  calc
    g.padicWeightedSum = ∑' i : ℕ, f i := rfl
    _ = ∑ j : ZMod 3, ∑' q : ℕ, f (j.val + 3 * q) :=
      Nat.sumByResidueClasses hf 3
    _ = ∑ r : Fin 3,
        ∑' q : ℕ, f ((ZMod.finEquiv 3 r).val + 3 * q) := by
      exact (Equiv.sum_comp (ZMod.finEquiv 3).toEquiv _).symm
    _ = ∑ r : Fin 3,
        ∑' q : ℕ, g.padicWeightedTerm (3 * q + r) := by
      apply Fintype.sum_congr
      intro r
      have hval := finEquiv_val 3 r
      congr 1
      funext q
      simp only [f, hval]
      congr 1
      omega

noncomputable def padicVaananenTerm (g : Ray) (r : Fin 3)
    (q : ℕ) : ℚ_[2] := ((g.thetaData).vaananenTerm r q : ℚ_[2])

noncomputable def padicVaananenSum (g : Ray) (r : Fin 3) : ℚ_[2] :=
  ∑' q, g.padicVaananenTerm r q

theorem theta_prefixScale_ne_zero (g : Ray) (r : Fin 3) :
    (g.thetaData).prefixScale r ≠ 0 := by
  fin_cases r <;> simp [thetaData, backwardCoeff, backwardDefect]

theorem padic_theta_prefixScale_ne_zero (g : Ray) (r : Fin 3) :
    ((g.thetaData).prefixScale r : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.theta_prefixScale_ne_zero r

theorem padicWeightedTerm_eq_scaled_vaananenTerm
    (g : Ray) (q : ℕ) (r : Fin 3) :
    g.padicWeightedTerm (3 * q + r) =
      ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenTerm r q := by
  have h := congrArg (fun x : ℚ => (x : ℚ_[2]))
    ((g.weightedTerm_at q r).trans
      ((g.thetaData).weightedTerm_eq_scaled_vaananenTerm
        g.ratio_ne_zero r q))
  simpa [padicWeightedTerm, padicVaananenTerm, Rat.cast_mul] using h

theorem padicVaananenTerm_summable (g : Ray) (r : Fin 3) :
    Summable (g.padicVaananenTerm r) := by
  let c : ℚ_[2] := ((g.thetaData).prefixScale r : ℚ_[2])
  have hc : c ≠ 0 := g.padic_theta_prefixScale_ne_zero r
  have hzero : Tendsto
      (fun q => g.padicWeightedTerm (3 * q + r)) atTop (𝓝 0) := by
    have hindex : Tendsto (fun q : ℕ => 3 * q + (r : ℕ))
        atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with q hq
      omega
    exact g.padicWeightedTerm_tendsto_zero.comp hindex
  have hs : Summable (fun q => g.padicWeightedTerm (3 * q + r)) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using hzero
  have hscaled := hs.mul_left c⁻¹
  refine hscaled.congr ?_
  intro q
  rw [g.padicWeightedTerm_eq_scaled_vaananenTerm q r]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem padicResidueSum_eq_scaled_vaananenSum (g : Ray) (r : Fin 3) :
    (∑' q, g.padicWeightedTerm (3 * q + r)) =
      ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenSum r := by
  have hv := (g.padicVaananenTerm_summable r).hasSum.mul_left
    ((g.thetaData).prefixScale r : ℚ_[2])
  have hfun :
      (fun q => ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenTerm r q) =
      (fun q => g.padicWeightedTerm (3 * q + r)) := by
    funext q
    exact (g.padicWeightedTerm_eq_scaled_vaananenTerm q r).symm
  rw [hfun] at hv
  simpa only [padicVaananenSum] using hv.tsum_eq

theorem padicWeightedSum_eq_scaled_vaananenSums (g : Ray) :
    g.padicWeightedSum =
      ∑ r : Fin 3, ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenSum r := by
  rw [g.padicWeightedSum_eq_sum_residues]
  apply Fintype.sum_congr
  intro r
  exact g.padicResidueSum_eq_scaled_vaananenSum r

/-- The precise missing theorem is independence of `1` and the three actual
theta values.  This is deliberately a proposition, not an axiom. -/
def ThetaIndependent (g : Ray) : Prop :=
  ∀ (a₀ : ℚ) (a : Fin 3 → ℚ),
    (a₀ ≠ 0 ∨ ∃ r, a r ≠ 0) →
    (a₀ : ℚ_[2]) + ∑ r : Fin 3,
      (a r : ℚ_[2]) * g.padicVaananenSum r ≠ 0

/-- Any proof of the exact four-value independence statement rules out the
literal period-three EC17 ray. -/
theorem false_of_thetaIndependent (g : Ray)
    (hind : g.ThetaIndependent) : False := by
  have hrelation :
      (g.core 0 : ℚ_[2]) + ∑ r : Fin 3,
        ((g.thetaData).prefixScale r : ℚ_[2]) *
          g.padicVaananenSum r = 0 := by
    have hcand := g.padicCandidate_eq_initial
    rw [padicCandidate, g.padicWeightedSum_eq_scaled_vaananenSums] at hcand
    linear_combination -hcand
  have hcore : (g.core 0 : ℚ) ≠ 0 := by
    exact_mod_cast (g.core_pos 0).ne'
  exact hind (g.core 0) (g.thetaData).prefixScale (Or.inl hcore) hrelation

/-- Citation-boundary audit.  The desired relation has four values in total,
but the 1989 parameter `ell` counts the three theta values (not the additional
constant `1`).  Its sufficient threshold is already strictly below the EC17
height parameter at `ell=3`. -/
theorem published_threshold_three_lt_gamma :
    EtherCounterPeriodicTheta.threshold 3 <
      EtherCounterPeriodicTheta.gamma :=
  EtherCounterPeriodicTheta.threshold_three_lt_gamma

end Ray
end EtherCounterPeriodThreeTheta
end KontoroC
