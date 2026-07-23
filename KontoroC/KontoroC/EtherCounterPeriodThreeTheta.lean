/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodThree
import KontoroC.ChargePhaseUpPeriodicTheta
import KontoroC.VaananenWallisserCore
import KontoroC.GeometricVandermonde
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Multiplicity

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

theorem theta_argument_injective (g : Ray) :
    Function.Injective g.thetaData.argument := by
  intro r s hrs
  by_contra hne
  have hs0 : g.thetaData.argument s ≠ 0 :=
    g.thetaData.argument_ne_zero g.ratio_ne_zero
      g.defectRatio_ne_zero g.cycleCoeff_ne_zero s
  have hquot : g.thetaData.argument r / g.thetaData.argument s = 1 := by
    rw [hrs, div_self hs0]
  exact g.theta_arguments_separated r s hne 0 (by simpa using hquot)

/-- The special consecutive-argument geometry has a nonzero rational
Vandermonde determinant.  This is the algebraic separation input for a
three-value Skolem--Hermite construction; the still-missing work is the
sharper valuation/height estimate. -/
theorem theta_argument_vandermonde_ne_zero (g : Ray) :
    (Matrix.vandermonde g.thetaData.argument).det ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr g.theta_argument_injective

/-- Exact determinant of the consecutive geometric argument triple.  Unlike
generic separation, this displays the precise extra factor paid by the
three-value geometry. -/
theorem theta_argument_vandermonde_formula (g : Ray) :
    (Matrix.vandermonde g.thetaData.argument).det =
      g.thetaData.argumentCommon ^ 3 * g.ratio *
        (g.ratio - 1) ^ 3 * (g.ratio + 1) := by
  rw [Matrix.det_vandermonde]
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
  simp [PeriodicPhaseUp.ThetaResidueData.argument_eq_common_mul, thetaData]
  ring

theorem norm_padic_ratio (g : Ray) :
    ‖(g.ratio : ℚ_[2])‖ = ((2 : ℝ)⁻¹) ^ (8 * g.cycleGain) := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [ratio, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_padic_ratio_lt_one (g : Ray) : ‖(g.ratio : ℚ_[2])‖ < 1 := by
  rw [g.norm_padic_ratio]
  apply pow_lt_one₀ (by positivity) (by norm_num)
  exact Nat.mul_ne_zero (by norm_num) g.cycleGain_pos.ne'

theorem norm_padic_ratio_sub_one (g : Ray) :
    ‖(g.ratio : ℚ_[2]) - 1‖ = 1 := by
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne]
  · simp only [norm_neg, norm_one]
    exact max_eq_right g.norm_padic_ratio_lt_one.le
  · simp only [norm_neg, norm_one]
    exact ne_of_lt g.norm_padic_ratio_lt_one

theorem norm_padic_ratio_add_one (g : Ray) :
    ‖(g.ratio : ℚ_[2]) + 1‖ = 1 := by
  rw [Padic.add_eq_max_of_ne]
  · simp only [norm_one]
    exact max_eq_right g.norm_padic_ratio_lt_one.le
  · simp only [norm_one]
    exact ne_of_lt g.norm_padic_ratio_lt_one

/-- Exact `2`-adic cost of the geometric Vandermonde: apart from the common
argument scale, only the single ratio factor contributes. -/
theorem norm_padic_theta_argument_vandermonde (g : Ray) :
    ‖((Matrix.vandermonde g.thetaData.argument).det : ℚ_[2])‖ =
      ‖(g.thetaData.argumentCommon : ℚ_[2])‖ ^ 3 *
        ((2 : ℝ)⁻¹) ^ (8 * g.cycleGain) := by
  rw [g.theta_argument_vandermonde_formula]
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_add,
    Rat.cast_one, norm_mul, norm_pow]
  rw [g.norm_padic_ratio, g.norm_padic_ratio_sub_one,
    g.norm_padic_ratio_add_one]
  ring

/-! ## What the fixed Vandermonde cost cannot do

The exact norm above is useful local arithmetic, but the Väänänen--Wallisser
threshold is obtained after dividing logarithmic estimates by a quadratic
Hermite parameter.  For a fixed ray, the logarithm of this `3 x 3`
determinant is a constant, hence disappears on that scale.  Consequently the
bare Vandermonde saving cannot by itself repair the failed `ell = 3`
criterion.  Any successful special-geometry refinement must improve a family
of auxiliary forms at quadratic order, rather than only their fixed initial
separation determinant.
-/

/-- Every fixed real cost is negligible after quadratic Hermite
normalization. -/
theorem fixed_cost_div_sq_tendsto_zero (C : ℝ) :
    Tendsto (fun ν : ℕ => C / (ν : ℝ) ^ 2) atTop (𝓝 0) := by
  have hC : Tendsto (fun ν : ℕ => C / (ν : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hOne : Tendsto (fun ν : ℕ => (1 : ℝ) / (ν : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h := hC.mul hOne
  simp only [zero_mul] at h
  convert h using 1
  funext ν
  simp only [div_eq_mul_inv]
  ring

/-- In particular, the logarithmic cost of the literal active
Vandermonde determinant is subquadratic in the auxiliary Hermite parameter.
This is a no-go for the determinant-only proposed repair, not for every
possible specialized three-theta argument. -/
theorem theta_argument_vandermonde_log_cost_subquadratic (g : Ray) :
    Tendsto
      (fun ν : ℕ =>
        Real.log ‖((Matrix.vandermonde g.thetaData.argument).det : ℚ_[2])‖ /
          (ν : ℝ) ^ 2)
      atTop (𝓝 0) :=
  fixed_cost_div_sq_tendsto_zero _

/-! ## The full consecutive Hermite root grid

The three arguments are not merely a geometric triple.  Since the paper
parameter is the inverse cube of `ratio`, the three length-`ν` root strings
interlace into one consecutive length-`3ν` geometric grid.  Unlike the fixed
three-point determinant, this geometry persists with quadratic multiplicity
as the auxiliary degree grows.
-/

/-- Exact natural-exponent normalization of one point in the interlaced
three-phase Skolem root grid (QM123a). -/
theorem scaled_theta_root_eq_consecutive_grid (g : Ray) (ν a : ℕ)
    (ha : a < ν) (r : Fin 3) :
    g.ratio ^ (3 * (ν - 1)) *
          (g.thetaData.parameterInverse⁻¹) ^ a * g.thetaData.argument r =
      g.thetaData.argumentCommon *
        g.ratio ^ (3 * (ν - 1 - a) + (r : ℕ)) := by
  rw [g.thetaData.argument_eq_common_mul]
  simp only [thetaData, PeriodicPhaseUp.ThetaResidueData.parameterInverse]
  have hsplit : 3 * (ν - 1) = 3 * a + 3 * (ν - 1 - a) := by omega
  rw [hsplit, pow_add, inv_pow, pow_mul]
  have hratio : g.ratio ≠ 0 := g.ratio_ne_zero
  rw [pow_add]
  field_simp [pow_ne_zero _ hratio]

/-- Address map from the three phasewise root strings to the single
consecutive grid.  The first coordinate is reversed because the natural
normalization clears the largest negative exponent. -/
def rootGridIndex (ν : ℕ) (ar : Fin ν × Fin 3) : Fin (3 * ν) :=
  ⟨3 * (ν - 1 - (ar.1 : ℕ)) + (ar.2 : ℕ), by
    have ha := ar.1.isLt
    have hr := ar.2.isLt
    omega⟩

theorem rootGridIndex_injective (ν : ℕ) :
    Function.Injective (rootGridIndex ν) := by
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  have hv := congrArg Fin.val h
  change 3 * (ν - 1 - (a : ℕ)) + (r : ℕ) =
    3 * (ν - 1 - (b : ℕ)) + (s : ℕ) at hv
  have ha := a.isLt
  have hb := b.isLt
  have hr := r.isLt
  have hs := s.isLt
  have hab : (a : ℕ) = (b : ℕ) := by omega
  have hrs : (r : ℕ) = (s : ℕ) := by omega
  have hab' : a = b := Fin.ext hab
  have hrs' : r = s := Fin.ext hrs
  subst b
  subst s
  rfl

/-- The interlacing address is a bijection onto all `3 * ν` consecutive
exponents, so no root is omitted or repeated. -/
theorem rootGridIndex_bijective (ν : ℕ) :
    Function.Bijective (rootGridIndex ν) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact rootGridIndex_injective ν
  · simp [Nat.mul_comm]

/-- Exact determinant of the complete `3 * ν` consecutive root grid.  The
gap of distance `d` occurs with multiplicity `3 * ν - d`, exposing the
quadratic-order arithmetic absent from the fixed three-point determinant. -/
theorem full_root_grid_vandermonde_formula (g : Ray) (ν : ℕ) :
    (Matrix.vandermonde
      (fun i : Fin (3 * ν) =>
        g.thetaData.argumentCommon * g.ratio ^ (i : ℕ))).det =
      g.thetaData.argumentCommon ^ ((3 * ν).choose 2) *
        g.ratio ^ ((3 * ν).choose 3) *
          GeometricVandermonde.gapProductSub g.ratio (3 * ν) :=
  GeometricVandermonde.det_geometric _ _ _

def ratioNumerator (g : Ray) : ℕ := 2 ^ (8 * g.cycleGain)
def ratioDenominator (g : Ray) : ℕ := 3 ^ (6 * g.cycleGain)

theorem ratio_eq_numerator_div_denominator (g : Ray) :
    g.ratio = (g.ratioNumerator : ℚ) / g.ratioDenominator := by
  simp [ratio, ratioNumerator, ratioDenominator]

theorem ratioNumerator_le_ratioDenominator (g : Ray) :
    g.ratioNumerator ≤ g.ratioDenominator := by
  rw [ratioNumerator, ratioDenominator]
  calc
    2 ^ (8 * g.cycleGain) = (2 ^ 8) ^ g.cycleGain := by rw [pow_mul]
    _ ≤ (3 ^ 6) ^ g.cycleGain :=
      Nat.pow_le_pow_left (by norm_num) g.cycleGain
    _ = 3 ^ (6 * g.cycleGain) := by rw [pow_mul]

theorem ratioNumerator_lt_ratioDenominator (g : Ray) :
    g.ratioNumerator < g.ratioDenominator := by
  rw [ratioNumerator, ratioDenominator]
  calc
    2 ^ (8 * g.cycleGain) = (2 ^ 8) ^ g.cycleGain := by rw [pow_mul]
    _ < (3 ^ 6) ^ g.cycleGain :=
      Nat.pow_lt_pow_left (by norm_num) g.cycleGain_pos.ne'
    _ = 3 ^ (6 * g.cycleGain) := by rw [pow_mul]

/-- The first auxiliary prime in `3^6 - 2^8 = 473 = 11 * 43`
divides the active base gap at every positive cycle gain. -/
theorem eleven_dvd_ratio_base_gap (g : Ray) :
    11 ∣ g.ratioDenominator - g.ratioNumerator := by
  have hbase : 2 ^ 8 ≡ 3 ^ 6 [MOD 11] := by norm_num [Nat.ModEq]
  have hpow := hbase.pow g.cycleGain
  rw [← pow_mul, ← pow_mul] at hpow
  exact (Nat.modEq_iff_dvd' g.ratioNumerator_le_ratioDenominator).1 hpow

/-- The second auxiliary prime in the same base gap. -/
theorem fortyThree_dvd_ratio_base_gap (g : Ray) :
    43 ∣ g.ratioDenominator - g.ratioNumerator := by
  have hbase : 2 ^ 8 ≡ 3 ^ 6 [MOD 43] := by norm_num [Nat.ModEq]
  have hpow := hbase.pow g.cycleGain
  rw [← pow_mul, ← pow_mul] at hpow
  exact (Nat.modEq_iff_dvd' g.ratioNumerator_le_ratioDenominator).1 hpow

/-- Exact LTE valuation of the active base gap at `11`. -/
theorem padicValNat_eleven_ratio_base_gap (g : Ray) :
    padicValNat 11 (g.ratioDenominator - g.ratioNumerator) =
      1 + padicValNat 11 g.cycleGain := by
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [ratioDenominator, ratioNumerator]
  rw [show 3 ^ (6 * g.cycleGain) = (3 ^ 6) ^ g.cycleGain by rw [pow_mul],
    show 2 ^ (8 * g.cycleGain) = (2 ^ 8) ^ g.cycleGain by rw [pow_mul]]
  rw [padicValNat.pow_sub_pow (p := 11) (x := 3 ^ 6) (y := 2 ^ 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      g.cycleGain_pos.ne']
  have hbase : padicValNat 11 (3 ^ 6 - 2 ^ 8) = 1 := by
    norm_num only [Nat.reducePow, Nat.reduceSub]
    rw [show 473 = 11 * 43 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hbase]

/-- Exact LTE valuation of the same gap at `43`. -/
theorem padicValNat_fortyThree_ratio_base_gap (g : Ray) :
    padicValNat 43 (g.ratioDenominator - g.ratioNumerator) =
      1 + padicValNat 43 g.cycleGain := by
  letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  rw [ratioDenominator, ratioNumerator]
  rw [show 3 ^ (6 * g.cycleGain) = (3 ^ 6) ^ g.cycleGain by rw [pow_mul],
    show 2 ^ (8 * g.cycleGain) = (2 ^ 8) ^ g.cycleGain by rw [pow_mul]]
  rw [padicValNat.pow_sub_pow (p := 43) (x := 3 ^ 6) (y := 2 ^ 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      g.cycleGain_pos.ne']
  have hbase : padicValNat 43 (3 ^ 6 - 2 ^ 8) = 1 := by
    norm_num only [Nat.reducePow, Nat.reduceSub]
    rw [show 473 = 11 * 43 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hbase]

/-- After clearing the powers of `2` and `3`, the full root-grid gap
numerator contains at least one factor `11` per unordered pair. -/
theorem eleven_pow_choose_two_dvd_full_grid_gapNumerator
    (g : Ray) (ν : ℕ) :
    11 ^ ((3 * ν).choose 2) ∣
      GeometricVandermonde.gapNumerator
        g.ratioNumerator g.ratioDenominator (3 * ν) :=
  GeometricVandermonde.pow_choose_two_dvd_gapNumerator
    g.ratioNumerator_le_ratioDenominator g.eleven_dvd_ratio_base_gap

/-- The identical quadratic lower bound at the independent auxiliary prime
`43`. -/
theorem fortyThree_pow_choose_two_dvd_full_grid_gapNumerator
    (g : Ray) (ν : ℕ) :
    43 ^ ((3 * ν).choose 2) ∣
      GeometricVandermonde.gapNumerator
        g.ratioNumerator g.ratioDenominator (3 * ν) :=
  GeometricVandermonde.pow_choose_two_dvd_gapNumerator
    g.ratioNumerator_le_ratioDenominator g.fortyThree_dvd_ratio_base_gap

/-- Exact auxiliary-prime valuation of the complete cleared grid numerator
at `11` (QM123d). -/
theorem padicValNat_eleven_full_grid_gapNumerator (g : Ray) (ν : ℕ) :
    padicValNat 11
        (GeometricVandermonde.gapNumerator
          g.ratioNumerator g.ratioDenominator (3 * ν)) =
      ((3 * ν).choose 2) * (1 + padicValNat 11 g.cycleGain) +
        ∑ d ∈ Finset.Ico 1 (3 * ν),
          (3 * ν - d) * padicValNat 11 d := by
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [GeometricVandermonde.padicValNat_gapNumerator_of_lte
    (p := 11) (by norm_num) g.ratioNumerator_lt_ratioDenominator
    g.eleven_dvd_ratio_base_gap]
  · rw [g.padicValNat_eleven_ratio_base_gap]
  · intro hdiv
    have := (show Nat.Prime 11 by norm_num).dvd_of_dvd_pow hdiv
    norm_num [ratioDenominator] at this

/-- Exact companion formula at `43`. -/
theorem padicValNat_fortyThree_full_grid_gapNumerator (g : Ray) (ν : ℕ) :
    padicValNat 43
        (GeometricVandermonde.gapNumerator
          g.ratioNumerator g.ratioDenominator (3 * ν)) =
      ((3 * ν).choose 2) * (1 + padicValNat 43 g.cycleGain) +
        ∑ d ∈ Finset.Ico 1 (3 * ν),
          (3 * ν - d) * padicValNat 43 d := by
  letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  rw [GeometricVandermonde.padicValNat_gapNumerator_of_lte
    (p := 43) (by norm_num) g.ratioNumerator_lt_ratioDenominator
    g.fortyThree_dvd_ratio_base_gap]
  · rw [g.padicValNat_fortyThree_ratio_base_gap]
  · intro hdiv
    have := (show Nat.Prime 43 by norm_num).dvd_of_dvd_pow hdiv
    norm_num [ratioDenominator] at this

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

/-- Exact normalization seam to the independently defined 1989 theta term.
The paper's parameter is the inverse of `parameterInverse`; recording this
orientation avoids silently applying a theorem at `q⁻¹`. -/
theorem padicVaananenTerm_eq_thetaTerm (g : Ray) (r : Fin 3) (n : ℕ) :
    g.padicVaananenTerm r n =
      VaananenWallisser.thetaTerm
        (((g.thetaData).parameterInverse : ℚ_[2])⁻¹)
        ((g.thetaData).argument r : ℚ_[2]) n := by
  simp [padicVaananenTerm, PeriodicPhaseUp.ThetaResidueData.vaananenTerm,
    PeriodicPhaseUp.ThetaResidueData.vaananenExponent,
    VaananenWallisser.thetaTerm, VaananenWallisser.exponent,
    Rat.cast_pow]

/-- The completed EC17 residue value is literally the paper's completed
theta function, not merely a coefficientwise analogue. -/
theorem padicVaananenSum_eq_thetaSum (g : Ray) (r : Fin 3) :
    g.padicVaananenSum r =
      VaananenWallisser.thetaSum
        (((g.thetaData).parameterInverse : ℚ_[2])⁻¹)
        ((g.thetaData).argument r : ℚ_[2]) := by
  rw [padicVaananenSum, VaananenWallisser.thetaSum]
  apply tsum_congr
  intro n
  exact g.padicVaananenTerm_eq_thetaTerm r n

/-- Exact paper functional equation at each of the three actual arguments. -/
theorem padicVaananen_functional (g : Ray) (r : Fin 3) :
    let q : ℚ_[2] := ((g.thetaData).parameterInverse : ℚ_[2])⁻¹
    let x : ℚ_[2] := ((g.thetaData).argument r : ℚ_[2])
    VaananenWallisser.thetaSum q (q * x) =
      1 + x * g.padicVaananenSum r := by
  dsimp only
  have hparameter :
      ((g.thetaData).parameterInverse : ℚ_[2]) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 3 g.ratio_ne_zero)
  have hq :
      (((g.thetaData).parameterInverse : ℚ_[2])⁻¹) ≠ 0 :=
    inv_ne_zero hparameter
  have hs : Summable (VaananenWallisser.thetaTerm
      (((g.thetaData).parameterInverse : ℚ_[2])⁻¹)
      ((g.thetaData).argument r : ℚ_[2])) := by
    exact (g.padicVaananenTerm_summable r).congr
      (fun n => g.padicVaananenTerm_eq_thetaTerm r n)
  rw [g.padicVaananenSum_eq_thetaSum r]
  exact VaananenWallisser.thetaSum_functional _ _ hq hs

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

/-- The concrete full-support rational relation forced by a hypothetical
ordinary period-three ray. -/
theorem actual_theta_relation (g : Ray) :
    (g.core 0 : ℚ_[2]) + ∑ r : Fin 3,
      ((g.thetaData).prefixScale r : ℚ_[2]) *
        g.padicVaananenSum r = 0 := by
  have hcand := g.padicCandidate_eq_initial
  rw [padicCandidate, g.padicWeightedSum_eq_scaled_vaananenSums] at hcand
  linear_combination -hcand

/-- Every coefficient in the ray-forced four-term relation is nonzero. -/
theorem actual_theta_relation_full_support (g : Ray) :
    (g.core 0 : ℚ) ≠ 0 ∧
      ∀ r : Fin 3, (g.thetaData).prefixScale r ≠ 0 := by
  constructor
  · exact_mod_cast (g.core_pos 0).ne'
  · exact g.theta_prefixScale_ne_zero

/-- Any proof of the exact four-value independence statement rules out the
literal period-three EC17 ray. -/
theorem false_of_thetaIndependent (g : Ray)
    (hind : g.ThetaIndependent) : False := by
  exact hind (g.core 0) (g.thetaData).prefixScale
    (Or.inl g.actual_theta_relation_full_support.1) g.actual_theta_relation

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
