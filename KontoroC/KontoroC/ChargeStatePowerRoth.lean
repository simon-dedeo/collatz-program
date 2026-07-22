/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeStatePowerQuine

/-!
# Elementary bridge from public-state quines to Roth approximation

This file contains only the elementary algebra and inequalities preceding an
application of Roth's theorem.  Roth's theorem itself is not assumed as an
axiom here.
-/

namespace KontoroC

namespace ChargeStatePowerRoth

/-- The public-state equation when the recharge is `23 * ell`. -/
abbrev GeneralStateEquation (m ell s t : ℕ) : Prop :=
  (3 ^ 17) ^ m * (s ^ 23 + 1) =
    (2 ^ 23) ^ m * (1 + ((2 ^ 154) ^ ell * t) ^ 23)

/-- The exact additive normalization underlying the Roth gap equation. -/
theorem general_state_equation_normalizes
    {m ell s t : ℕ} (heq : GeneralStateEquation m ell s t) :
    let a := 17 * m / 23
    let e := 17 * m % 23
    let X := 3 ^ a * s
    let Y := 2 ^ m * (2 ^ 154) ^ ell * t
    Y ^ 23 + (2 ^ 23) ^ m = 3 ^ e * X ^ 23 + (3 ^ 17) ^ m := by
  dsimp only
  have hm : 17 * m % 23 + 23 * (17 * m / 23) = 17 * m :=
    Nat.mod_add_div _ _
  have hC : (3 ^ 17) ^ m =
      3 ^ (17 * m % 23) * (3 ^ (17 * m / 23)) ^ 23 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hD : (2 ^ 23) ^ m = (2 ^ m) ^ 23 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hY : (2 ^ m * (2 ^ 154) ^ ell * t) ^ 23 =
      (2 ^ m) ^ 23 * (((2 ^ 154) ^ ell * t) ^ 23) := by
    rw [mul_assoc, mul_pow]
  have hX : 3 ^ (17 * m % 23) *
      (3 ^ (17 * m / 23) * s) ^ 23 =
      (3 ^ (17 * m % 23) * (3 ^ (17 * m / 23)) ^ 23) * s ^ 23 := by
    rw [mul_pow]
    ring
  change (3 ^ 17) ^ m * (s ^ 23 + 1) =
    (2 ^ 23) ^ m * (1 + ((2 ^ 154) ^ ell * t) ^ 23) at heq
  rw [hC, hD] at heq
  rw [hY, hD, hC, hX]
  rw [mul_add, mul_add] at heq
  omega

/-- Integer-subtraction form of the normalized equation. -/
theorem general_state_equation_gap
    {m ell s t : ℕ} (heq : GeneralStateEquation m ell s t) :
    let a := 17 * m / 23
    let e := 17 * m % 23
    let X : ℕ := 3 ^ a * s
    let Y : ℕ := 2 ^ m * (2 ^ 154) ^ ell * t
    (Y : ℤ) ^ 23 - (3 : ℤ) ^ e * (X : ℤ) ^ 23 =
      (↑((3 ^ 17) ^ m) : ℤ) - ↑((2 ^ 23) ^ m) := by
  dsimp only
  have h := general_state_equation_normalizes heq
  dsimp only at h
  have hz := congrArg (fun n : ℕ ↦ (n : ℤ)) h
  norm_num at hz ⊢
  linarith

/-- The normalized gap is positive for every positive defect count. -/
theorem general_state_gap_pos {m : ℕ} (hm : 0 < m) :
    (0 : ℤ) < (↑((3 ^ 17) ^ m) : ℤ) - ↑((2 ^ 23) ^ m) := by
  have hbase : (2 : ℕ) ^ 23 < 3 ^ 17 := by norm_num
  have hp := Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hm)
  have hpz : (↑((2 ^ 23) ^ m) : ℤ) < ↑((3 ^ 17) ^ m) := by
    exact_mod_cast hp
  linarith

/-- The gap is smaller than the ternary complete-power packet. -/
theorem general_state_gap_lt_scale (m : ℕ) :
    let e := 17 * m % 23
    let U := 3 ^ (17 * m / 23)
    (↑((3 ^ 17) ^ m) : ℝ) - ↑((2 ^ 23) ^ m) <
      (3 : ℝ) ^ e * (U : ℝ) ^ 23 := by
  dsimp only
  have hC : (3 ^ 17) ^ m =
      3 ^ (17 * m % 23) * (3 ^ (17 * m / 23)) ^ 23 := by
    have hm : 17 * m % 23 + 23 * (17 * m / 23) = 17 * m :=
      Nat.mod_add_div _ _
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hCR : (↑((3 ^ 17) ^ m) : ℝ) =
      (3 : ℝ) ^ (17 * m % 23) * (↑(3 ^ (17 * m / 23)) : ℝ) ^ 23 := by
    exact_mod_cast hC
  rw [← hCR]
  exact sub_lt_self _ (by positivity)

/-- GSPQ forces the collision root to be strictly larger than the input
root. -/
theorem collision_root_strictly_grows
    {m ell s t : ℕ} (hm : 0 < m)
    (heq : GeneralStateEquation m ell s t) :
    s < (2 ^ 154) ^ ell * t := by
  let z := (2 ^ 154) ^ ell * t
  have hbase : (2 : ℕ) ^ 23 < 3 ^ 17 := by norm_num
  have hcoeff : (2 ^ 23) ^ m < (3 ^ 17) ^ m :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hm)
  have hfactor : 0 < s ^ 23 + 1 := by positivity
  have hscaled : (2 ^ 23) ^ m * (s ^ 23 + 1) <
      (3 ^ 17) ^ m * (s ^ 23 + 1) :=
    Nat.mul_lt_mul_of_pos_right hcoeff hfactor
  rw [heq] at hscaled
  have hcoeffPos : 0 < (2 ^ 23) ^ m := by positivity
  have hsums : s ^ 23 + 1 < 1 + z ^ 23 := by
    exact (Nat.mul_lt_mul_left hcoeffPos).mp (by simpa [z] using hscaled)
  have hpows : s ^ 23 < z ^ 23 := by omega
  exact (Nat.pow_lt_pow_iff_left (by omega : 23 ≠ 0)).mp hpows

/-- Since the output uses `A^ell` rather than `B^ell`, the reproduced state
root grows strictly as well. -/
theorem output_root_strictly_grows
    {m ell s t : ℕ} (hm : 0 < m) (hell : 0 < ell) (ht : 0 < t)
    (heq : GeneralStateEquation m ell s t) :
    s < (3 ^ 114) ^ ell * t := by
  have hcollision := collision_root_strictly_grows hm heq
  have hbase : (2 : ℕ) ^ 154 < 3 ^ 114 := by norm_num
  have hpowers : (2 ^ 154) ^ ell < (3 ^ 114) ^ ell :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hell)
  have hmul : (2 ^ 154) ^ ell * t < (3 ^ 114) ^ ell * t :=
    Nat.mul_lt_mul_of_pos_right hpowers ht
  exact hcollision.trans hmul

/-- Exact valuation divisibility makes the complete ternary factor smaller
than the input root; consequently the approximation denominator `X` is below
`s^2`. -/
theorem valuation_forces_scale_bounds
    {m s : ℕ} (hm : 0 < m) (hval : 2 ^ (23 * m) ∣ s + 1) :
    let U := 3 ^ (17 * m / 23)
    U < s ∧ U * s < s ^ 2 := by
  dsimp only
  have ha : 17 * m / 23 < m := by
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 23)).mpr (by omega)
  have h34 : 3 ^ (17 * m / 23) < 4 ^ m := by
    calc
      3 ^ (17 * m / 23) ≤ 4 ^ (17 * m / 23) :=
        Nat.pow_le_pow_left (by omega) _
      _ < 4 ^ m := (Nat.pow_lt_pow_iff_right (by omega : 1 < 4)).mpr ha
  have hUtwo : 3 ^ (17 * m / 23) < 2 ^ (2 * m) := by
    have hfour : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rwa [hfour] at h34
  have hExp : 2 * m < 23 * m := by omega
  have hPow : 2 ^ (2 * m) + 1 ≤ 2 ^ (23 * m) :=
    Nat.lt_iff_add_one_le.mp
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hExp)
  have hDiv : 2 ^ (23 * m) ≤ s + 1 :=
    Nat.le_of_dvd (by positivity) hval
  have hTwoS : 2 ^ (2 * m) ≤ s := by omega
  have hUs : 3 ^ (17 * m / 23) < s := hUtwo.trans_le hTwoS
  have hsPos : 0 < s := (by positivity : 0 < 2 ^ (2 * m)).trans_le hTwoS
  refine ⟨hUs, ?_⟩
  simpa [pow_two] using Nat.mul_lt_mul_of_pos_right hUs hsPos

private theorem real_power_gap_lower
    {q y : ℝ} (hq : 0 ≤ q) (hqy : q ≤ y) :
    (y - q) * q ^ 22 ≤ y ^ 23 - q ^ 23 := by
  have hy : 0 ≤ y := hq.trans hqy
  have hp : q ^ 22 ≤ y ^ 22 := by gcongr
  have hmul : y * q ^ 22 ≤ y * y ^ 22 :=
    mul_le_mul_of_nonneg_left hp hy
  rw [show y ^ 23 = y * y ^ 22 by rw [pow_succ'],
    show q ^ 23 = q * q ^ 22 by rw [pow_succ']]
  nlinarith

/-- The real approximation inequality used before invoking Roth.  It is
stated abstractly so the eventual number-theoretic consumer need only supply
the exact normalized gap and its elementary upper bound. -/
theorem real_roth_gap_bound
    {alpha U s X Y Δ : ℝ}
    (halpha : 0 < alpha) (hU : 0 < U) (hs : 0 < s)
    (hX : X = U * s)
    (hgap : Y ^ 23 - alpha ^ 23 * X ^ 23 = Δ)
    (hΔpos : 0 < Δ) (hΔupper : Δ < alpha ^ 23 * U ^ 23) :
    0 < Y / X - alpha ∧ Y / X - alpha < alpha / s ^ 23 := by
  let q := alpha * X
  have hXpos : 0 < X := by rw [hX]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqpow : q ^ 23 = alpha ^ 23 * X ^ 23 := by
    simp [q, mul_pow]
  have hgapq : Y ^ 23 - q ^ 23 = Δ := by rwa [hqpow]
  have hpowlt : q ^ 23 < Y ^ 23 := by linarith
  have hqY : q < Y :=
    (Odd.pow_lt_pow (by decide : Odd 23)).mp hpowlt
  have hratio : Y / X - alpha = (Y - q) / X := by
    dsimp [q]
    field_simp [ne_of_gt hXpos]
  constructor
  · rw [hratio]
    exact div_pos (sub_pos.mpr hqY) hXpos
  · have hgapLower : (Y - q) * q ^ 22 ≤ Y ^ 23 - q ^ 23 :=
      real_power_gap_lower hqpos.le hqY.le
    have hprod : (Y - q) * q ^ 22 < alpha ^ 23 * U ^ 23 := by
      calc
        (Y - q) * q ^ 22 ≤ Y ^ 23 - q ^ 23 := hgapLower
        _ = Δ := hgapq
        _ < alpha ^ 23 * U ^ 23 := hΔupper
    have hquot : alpha ^ 23 * U ^ 23 / q ^ 22 =
        alpha * U / s ^ 22 := by
      dsimp [q]
      rw [hX]
      field_simp [ne_of_gt halpha, ne_of_gt hU, ne_of_gt hs]
    have hdelta : Y - q < alpha * U / s ^ 22 := by
      have := (lt_div_iff₀ (pow_pos hqpos 22)).mpr hprod
      rwa [hquot] at this
    have hrhs : alpha / s ^ 23 * X = alpha * U / s ^ 22 := by
      rw [hX]
      field_simp [ne_of_gt hs]
    rw [hratio]
    apply (div_lt_iff₀ hXpos).mpr
    rw [hrhs]
    exact hdelta

/-- RB1 with `alpha^23 = 3^e` implies the advertised one-sided Roth
approximation bound. -/
theorem rb1_implies_rb2
    {e : ℕ} {alpha U s X Y Δ : ℝ}
    (halpha : 0 < alpha) (hU : 0 < U) (hs : 0 < s)
    (halphaPow : alpha ^ 23 = (3 : ℝ) ^ e)
    (hX : X = U * s)
    (hgap : Y ^ 23 - (3 : ℝ) ^ e * X ^ 23 = Δ)
    (hΔpos : 0 < Δ) (hΔupper : Δ < (3 : ℝ) ^ e * U ^ 23) :
    0 < Y / X - alpha ∧ Y / X - alpha < alpha / s ^ 23 := by
  rw [← halphaPow] at hgap hΔupper
  exact real_roth_gap_bound halpha hU hs hX hgap hΔpos hΔupper

/-- A positive GSPQ transition directly supplies the RB2 approximation. -/
theorem general_state_equation_roth_bound
    {m ell s t : ℕ} (hm : 0 < m) (hsNat : 0 < s)
    (heq : GeneralStateEquation m ell s t)
    {alpha : ℝ} (halpha : 0 < alpha)
    (halphaPow : alpha ^ 23 = (3 : ℝ) ^ (17 * m % 23)) :
    let X : ℕ := 3 ^ (17 * m / 23) * s
    let Y : ℕ := 2 ^ m * (2 ^ 154) ^ ell * t
    0 < (Y : ℝ) / X - alpha ∧
      (Y : ℝ) / X - alpha < alpha / (s : ℝ) ^ 23 := by
  dsimp only
  let U : ℕ := 3 ^ (17 * m / 23)
  let X : ℕ := U * s
  let Y : ℕ := 2 ^ m * (2 ^ 154) ^ ell * t
  let Δ : ℝ := (↑((3 ^ 17) ^ m) : ℝ) - ↑((2 ^ 23) ^ m)
  have hgapZ := general_state_equation_gap heq
  dsimp only at hgapZ
  have hgapR := congrArg (fun z : ℤ ↦ (z : ℝ)) hgapZ
  norm_num at hgapR
  have hgap : (Y : ℝ) ^ 23 - (3 : ℝ) ^ (17 * m % 23) *
      (X : ℝ) ^ 23 = Δ := by
    norm_num [X, Y, U, Δ] at hgapR ⊢
    exact hgapR
  have hΔpos : 0 < Δ := by
    have hbase : (2 : ℕ) ^ 23 < 3 ^ 17 := by norm_num
    have hpNat : (2 ^ 23) ^ m < (3 ^ 17) ^ m :=
      Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hm)
    have hpReal : (↑((2 ^ 23) ^ m) : ℝ) < ↑((3 ^ 17) ^ m) := by
      exact_mod_cast hpNat
    dsimp [Δ]
    linarith
  have hΔupper : Δ < (3 : ℝ) ^ (17 * m % 23) * (U : ℝ) ^ 23 := by
    simpa [U, Δ] using general_state_gap_lt_scale m
  have hX : (X : ℝ) = (U : ℝ) * (s : ℝ) := by
    simp [X]
  have hresult := rb1_implies_rb2 halpha (by positivity : (0 : ℝ) < U)
    (by exact_mod_cast hsNat : (0 : ℝ) < s) halphaPow hX hgap hΔpos hΔupper
  simpa [X, Y, U] using hresult

/-- Because 17 is invertible modulo 23, the zero residual class is exactly
the already-excluded class `23 ∣ m`. -/
theorem residual_eq_zero_iff (m : ℕ) :
    17 * m % 23 = 0 ↔ m % 23 = 0 := by
  omega

theorem residual_eq_zero_iff_dvd (m : ℕ) :
    17 * m % 23 = 0 ↔ 23 ∣ m := by
  rw [residual_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

/-- The explicit eventual-constant step from RB2 to a Roth exponent of 11.
The hypothesis `alpha < s` is essential; exponent arithmetic alone does not
remove this constant. -/
theorem rb2_implies_exponent_eleven
    {alpha error : ℝ} {q s : ℕ}
    (hq : 0 < q) (hs : 0 < s) (halphaS : alpha < s)
    (hqS : q < s ^ 2) (herror : error < alpha / (s : ℝ) ^ 23) :
    error < 1 / (q : ℝ) ^ 11 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have halphaSR : alpha < (s : ℝ) := by exact_mod_cast halphaS
  have hfirst : alpha / (s : ℝ) ^ 23 < 1 / (s : ℝ) ^ 22 := by
    have hdiv := div_lt_div_of_pos_right halphaSR (pow_pos hsR 23)
    have hid : (s : ℝ) / (s : ℝ) ^ 23 = 1 / (s : ℝ) ^ 22 := by
      field_simp [ne_of_gt hsR]
    rwa [hid] at hdiv
  have hpowNat : q ^ 11 < s ^ 22 := by
    have hp := Nat.pow_lt_pow_left hqS (by omega : 11 ≠ 0)
    have hsPow : (s ^ 2) ^ 11 = s ^ 22 := by rw [← pow_mul]
    rwa [hsPow] at hp
  have hpowR : (q : ℝ) ^ 11 < (s : ℝ) ^ 22 := by
    exact_mod_cast hpowNat
  have hsecond : 1 / (s : ℝ) ^ 22 < 1 / (q : ℝ) ^ 11 :=
    one_div_lt_one_div_of_lt (pow_pos hqR 11) hpowR
  exact herror.trans (hfirst.trans hsecond)

end ChargeStatePowerRoth

end KontoroC
