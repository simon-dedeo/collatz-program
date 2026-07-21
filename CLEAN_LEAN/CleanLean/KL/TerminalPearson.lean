/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.LocalRenormalization
import CleanLean.KL.OscillationIdentity

/-!
# Sharp Pearson bounds for a ternary refinement fiber

This file proves the local algebra used by the terminal-localization program.
For a ternary probability vector `p`, its loss from replacing the average by
the minimum controls its Pearson energy with sharp quadratic constants.
-/

namespace CleanLean.KL

noncomputable section

/-- Average-minus-minimum defect of a ternary probability profile. -/
def ternaryDefect (p : Triple) : ℝ := 1 / 3 - min3 p

/-- Pearson energy of a ternary probability profile relative to the uniform
law. -/
def ternaryPearson (p : Triple) : ℝ :=
  3 * ((p 0 - 1 / 3) ^ 2 + (p 1 - 1 / 3) ^ 2 +
    (p 2 - 1 / 3) ^ 2)

/-- Unnormalized `L¹` variation around the mean of a ternary profile. -/
def ternaryVariation (p : Triple) : ℝ :=
  |p 0 - mean3 p| + |p 1 - mean3 p| + |p 2 - mean3 p|

/-- Mean-minus-minimum defect for an arbitrary (not necessarily normalized)
ternary profile. -/
def ternaryMeanDefect (p : Triple) : ℝ := mean3 p - min3 p

private theorem variation_bounds_when_first_is_min
    (x y z : ℝ) (hxy : x ≤ y) (hxz : x ≤ z) :
    let mu := (x + y + z) / 3
    let a := mu - x
    let variation := |x - mu| + |y - mu| + |z - mu|
    0 ≤ a ∧ 2 * a ≤ variation ∧ variation ≤ 4 * a := by
  dsimp
  let mu : ℝ := (x + y + z) / 3
  let a : ℝ := mu - x
  let t : ℝ := y - mu
  have ha0 : 0 ≤ a := by
    dsimp [a, mu]
    linarith
  have htLower : -a ≤ t := by
    dsimp [a, t]
    linarith
  have htUpper : t ≤ 2 * a := by
    dsimp [a, t, mu]
    linarith
  have hxdev : x - mu = -a := by simp [a]
  have hzdev : z - mu = a - t := by
    dsimp [a, t, mu]
    ring
  rw [hxdev, hzdev, abs_neg, abs_of_nonneg ha0]
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
    by_cases hat : 0 ≤ a - t
    · rw [abs_of_nonneg hat]
      constructor
      · exact ha0
      constructor <;> linarith
    · have hat' : a - t ≤ 0 := le_of_not_ge hat
      rw [abs_of_nonpos hat']
      constructor
      · exact ha0
      constructor <;> linarith
  · have ht0' : t ≤ 0 := le_of_not_ge ht0
    have hat : 0 ≤ a - t := by linarith
    rw [abs_of_nonpos ht0', abs_of_nonneg hat]
    constructor
    · exact ha0
    constructor <;> linarith

/-- The terminal `L¹` variation of a ternary fiber is between twice and four
times its average-minus-minimum defect. -/
theorem ternaryVariation_bounds (p : Triple) :
    0 ≤ ternaryMeanDefect p ∧
      2 * ternaryMeanDefect p ≤ ternaryVariation p ∧
      ternaryVariation p ≤ 4 * ternaryMeanDefect p := by
  by_cases h01 : p 0 ≤ p 1
  · by_cases h02 : p 0 ≤ p 2
    · have h := variation_bounds_when_first_is_min
          (p 0) (p 1) (p 2) h01 h02
      simpa [ternaryMeanDefect, ternaryVariation, mean3, min3,
        min_eq_left (le_min h01 h02)] using h
    · have h20 : p 2 ≤ p 0 := le_of_not_ge h02
      have h21 : p 2 ≤ p 1 := h20.trans h01
      have h := variation_bounds_when_first_is_min
          (p 2) (p 0) (p 1) h20 h21
      simpa [ternaryMeanDefect, ternaryVariation, mean3, min3,
        min_eq_right h20, min_eq_right h21, add_comm, add_left_comm,
        add_assoc] using h
  · have h10 : p 1 ≤ p 0 := le_of_not_ge h01
    by_cases h12 : p 1 ≤ p 2
    · have h := variation_bounds_when_first_is_min
          (p 1) (p 0) (p 2) h10 h12
      simpa [ternaryMeanDefect, ternaryVariation, mean3, min3,
        min_eq_right h10, min_eq_left h12, add_comm, add_left_comm,
        add_assoc] using h
    · have h21 : p 2 ≤ p 1 := le_of_not_ge h12
      have h20 : p 2 ≤ p 0 := h21.trans h10
      have h := variation_bounds_when_first_is_min
          (p 2) (p 0) (p 1) h20 h21
      simpa [ternaryMeanDefect, ternaryVariation, mean3, min3,
        min_eq_right h20, min_eq_right h21, add_comm, add_left_comm,
        add_assoc] using h

private theorem pearson_bounds_when_first_is_min
    (x y z : ℝ)
    (hsum : x + y + z = 1)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    let a := 1 / 3 - x
    let chi := 3 * ((x - 1 / 3) ^ 2 + (y - 1 / 3) ^ 2 +
      (z - 1 / 3) ^ 2)
    0 ≤ a ∧ a ≤ 1 / 3 ∧
      (9 / 2) * a ^ 2 ≤ chi ∧ chi ≤ 18 * a ^ 2 ∧
        18 * a ^ 2 ≤ 6 * a := by
  dsimp
  let a : ℝ := 1 / 3 - x
  let t : ℝ := y - 1 / 3
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have ha13 : a ≤ 1 / 3 := by
    dsimp [a]
    linarith
  have htLower : -a ≤ t := by
    dsimp [a, t]
    linarith
  have htUpper : t ≤ 2 * a := by
    dsimp [a, t]
    linarith
  have hfactor : 0 ≤ (2 * a - t) * (a + t) :=
    mul_nonneg (sub_nonneg.mpr htUpper) (by linarith)
  have hlower :
      (9 / 2 : ℝ) * a ^ 2 ≤
        3 * ((x - 1 / 3) ^ 2 + (y - 1 / 3) ^ 2 +
          (z - 1 / 3) ^ 2) := by
    have hsquare : 0 ≤ (t - a / 2) ^ 2 := sq_nonneg _
    dsimp [a, t] at hsquare ⊢
    nlinarith [hsum]
  have hupper :
      3 * ((x - 1 / 3) ^ 2 + (y - 1 / 3) ^ 2 +
        (z - 1 / 3) ^ 2) ≤ 18 * a ^ 2 := by
    dsimp [a, t] at hfactor ⊢
    nlinarith [hsum]
  have hlinear : 18 * a ^ 2 ≤ 6 * a := by
    have hprod : 0 ≤ a * (1 - 3 * a) :=
      mul_nonneg ha0 (by linarith)
    nlinarith
  exact ⟨ha0, ha13, hlower, hupper, hlinear⟩

/-- Sharp pointwise comparison between terminal min-defect and Pearson
energy.  The constants are exact:

`(9/2) a^2 ≤ chi ≤ 18 a^2 ≤ 6a`.
-/
theorem ternaryPearson_bounds
    (p : Triple)
    (hsum : p 0 + p 1 + p 2 = 1)
    (hnonneg : ∀ i, 0 ≤ p i) :
    0 ≤ ternaryDefect p ∧ ternaryDefect p ≤ 1 / 3 ∧
      (9 / 2) * (ternaryDefect p) ^ 2 ≤ ternaryPearson p ∧
      ternaryPearson p ≤ 18 * (ternaryDefect p) ^ 2 ∧
      18 * (ternaryDefect p) ^ 2 ≤ 6 * ternaryDefect p := by
  by_cases h01 : p 0 ≤ p 1
  · by_cases h02 : p 0 ≤ p 2
    · have h := pearson_bounds_when_first_is_min
          (p 0) (p 1) (p 2) hsum (hnonneg 0) h01 h02
      simpa [ternaryDefect, ternaryPearson, min3,
        min_eq_left (le_min h01 h02)] using h
    · have h20 : p 2 ≤ p 0 := le_of_not_ge h02
      have h21 : p 2 ≤ p 1 := h20.trans h01
      have h := pearson_bounds_when_first_is_min
          (p 2) (p 0) (p 1) (by linarith [hsum]) (hnonneg 2) h20 h21
      simpa [ternaryDefect, ternaryPearson, min3,
        min_eq_right h20, min_eq_right h21, add_comm, add_left_comm,
        add_assoc] using h
  · have h10 : p 1 ≤ p 0 := le_of_not_ge h01
    by_cases h12 : p 1 ≤ p 2
    · have h := pearson_bounds_when_first_is_min
          (p 1) (p 0) (p 2) (by linarith [hsum]) (hnonneg 1) h10 h12
      simpa [ternaryDefect, ternaryPearson, min3,
        min_eq_right h10, min_eq_left h12, add_comm, add_left_comm,
        add_assoc] using h
    · have h21 : p 2 ≤ p 1 := le_of_not_ge h12
      have h20 : p 2 ≤ p 0 := h21.trans h10
      have h := pearson_bounds_when_first_is_min
          (p 2) (p 0) (p 1) (by linarith [hsum]) (hnonneg 2) h20 h21
      simpa [ternaryDefect, ternaryPearson, min3,
        min_eq_right h20, min_eq_right h21, add_comm, add_left_comm,
        add_assoc] using h

theorem ternaryPearson_lower
    (p : Triple) (hsum : p 0 + p 1 + p 2 = 1)
    (hnonneg : ∀ i, 0 ≤ p i) :
    (9 / 2) * (ternaryDefect p) ^ 2 ≤ ternaryPearson p :=
  (ternaryPearson_bounds p hsum hnonneg).2.2.1

theorem ternaryPearson_upper
    (p : Triple) (hsum : p 0 + p 1 + p 2 = 1)
    (hnonneg : ∀ i, 0 ≤ p i) :
    ternaryPearson p ≤ 6 * ternaryDefect p :=
  (ternaryPearson_bounds p hsum hnonneg).2.2.2.1.trans
    (ternaryPearson_bounds p hsum hnonneg).2.2.2.2

/-- Parent-mass-weighted mean terminal defect. -/
def weightedTernaryDefect {ι : Type} [Fintype ι]
    (nu : ι → ℝ) (p : ι → Triple) : ℝ :=
  ∑ i, nu i * ternaryDefect (p i)

/-- Parent-mass-weighted terminal Pearson energy. -/
def weightedTernaryPearson {ι : Type} [Fintype ι]
    (nu : ι → ℝ) (p : ι → Triple) : ℝ :=
  ∑ i, nu i * ternaryPearson (p i)

private theorem weighted_square_mean_le {ι : Type} [Fintype ι]
    (nu a : ι → ℝ) (hnu : ∀ i, 0 ≤ nu i)
    (hprob : ∑ i, nu i = 1) :
    (∑ i, nu i * a i) ^ 2 ≤ ∑ i, nu i * (a i) ^ 2 := by
  let d : ℝ := ∑ i, nu i * a i
  have hvar : 0 ≤ ∑ i, nu i * (a i - d) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hnu i) (sq_nonneg _)
  have hexpand :
      (∑ i, nu i * (a i - d) ^ 2) =
        (∑ i, nu i * (a i) ^ 2) - d ^ 2 := by
    calc
      (∑ i, nu i * (a i - d) ^ 2) =
          ∑ i, (nu i * (a i) ^ 2 - 2 * d * (nu i * a i) +
            d ^ 2 * nu i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, nu i * (a i) ^ 2) -
          2 * d * (∑ i, nu i * a i) + d ^ 2 * (∑ i, nu i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
      _ = (∑ i, nu i * (a i) ^ 2) - d ^ 2 := by
        rw [hprob]
        change (∑ i, nu i * (a i) ^ 2) - 2 * d * d + d ^ 2 * 1 = _
        ring
  rw [hexpand] at hvar
  change d ^ 2 ≤ _
  linarith

/-- Weighted Jensen version of the sharp ternary Pearson comparison:

`(9/2) delta^2 ≤ chi ≤ 18 E[a^2] ≤ 6 delta`.
-/
theorem weightedTernaryPearson_bounds {ι : Type} [Fintype ι]
    (nu : ι → ℝ) (p : ι → Triple)
    (hnu : ∀ i, 0 ≤ nu i) (hprob : ∑ i, nu i = 1)
    (hprofileSum : ∀ i, p i 0 + p i 1 + p i 2 = 1)
    (hprofileNonneg : ∀ i j, 0 ≤ p i j) :
    (9 / 2) * (weightedTernaryDefect nu p) ^ 2 ≤
        weightedTernaryPearson nu p ∧
      weightedTernaryPearson nu p ≤
        18 * (∑ i, nu i * (ternaryDefect (p i)) ^ 2) ∧
      18 * (∑ i, nu i * (ternaryDefect (p i)) ^ 2) ≤
        6 * weightedTernaryDefect nu p := by
  let a : ι → ℝ := fun i => ternaryDefect (p i)
  have hjensen : (∑ i, nu i * a i) ^ 2 ≤ ∑ i, nu i * (a i) ^ 2 :=
    weighted_square_mean_le nu a hnu hprob
  have hlowerLocal :
      (∑ i, nu i * ((9 / 2 : ℝ) * (a i) ^ 2)) ≤
        ∑ i, nu i * ternaryPearson (p i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (ternaryPearson_lower (p i) (hprofileSum i) (hprofileNonneg i)) (hnu i)
  have hupperLocal :
      (∑ i, nu i * ternaryPearson (p i)) ≤
        ∑ i, nu i * (18 * (a i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (ternaryPearson_bounds (p i) (hprofileSum i)
        (hprofileNonneg i)).2.2.2.1 (hnu i)
  have hlinearLocal :
      (∑ i, nu i * (18 * (a i) ^ 2)) ≤
        ∑ i, nu i * (6 * a i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (ternaryPearson_bounds (p i) (hprofileSum i)
        (hprofileNonneg i)).2.2.2.2 (hnu i)
  dsimp [weightedTernaryDefect, weightedTernaryPearson]
  dsimp [a] at hjensen hlowerLocal hupperLocal hlinearLocal ⊢
  constructor
  · calc
      (9 / 2 : ℝ) * (∑ i, nu i * ternaryDefect (p i)) ^ 2 ≤
          (9 / 2) * (∑ i, nu i * (ternaryDefect (p i)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hjensen (by norm_num)
      _ = ∑ i, nu i * ((9 / 2) * (ternaryDefect (p i)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, nu i * ternaryPearson (p i) := hlowerLocal
  constructor
  · calc
      (∑ i, nu i * ternaryPearson (p i)) ≤
          ∑ i, nu i * (18 * (ternaryDefect (p i)) ^ 2) := hupperLocal
      _ = 18 * (∑ i, nu i * (ternaryDefect (p i)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · calc
      18 * (∑ i, nu i * (ternaryDefect (p i)) ^ 2) =
          ∑ i, nu i * (18 * (ternaryDefect (p i)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, nu i * (6 * ternaryDefect (p i)) := hlinearLocal
      _ = 6 * (∑ i, nu i * ternaryDefect (p i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

namespace FiniteSystem

variable (S : FiniteSystem)

/-- The three values over one coarse KL state, viewed as a ternary profile. -/
def fiberProfile (c : S.State → ℝ) (r : S.Coarse) : Triple :=
  fun j => c (S.fiber r j)

@[simp] theorem ternaryMeanDefect_fiberProfile
    (c : S.State → ℝ) (r : S.Coarse) :
    ternaryMeanDefect (S.fiberProfile c r) = S.fiberDefect c r := by
  simp [ternaryMeanDefect, mean3, min3, fiberProfile,
    fiberDefect, fiberSum, fiberMin]

/-- Total terminal `L¹` variation across all three-point refinement fibers. -/
def terminalVariationMass (c : S.State → ℝ) : ℝ :=
  ∑ r, ternaryVariation (S.fiberProfile c r)

/-- Terminal `L¹` variation normalized by total fine-state mass. -/
def normalizedTerminalVariation (c : S.State → ℝ) : ℝ :=
  S.terminalVariationMass c / S.totalMass c

/-- Exact global comparison `2 defect ≤ terminal variation ≤ 4 defect`. -/
theorem terminalVariationMass_bounds (c : S.State → ℝ) :
    2 * S.defectMass c ≤ S.terminalVariationMass c ∧
      S.terminalVariationMass c ≤ 4 * S.defectMass c := by
  constructor
  · calc
      2 * S.defectMass c =
          ∑ r, 2 * ternaryMeanDefect (S.fiberProfile c r) := by
        simp only [defectMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [S.ternaryMeanDefect_fiberProfile]
      _ ≤ ∑ r, ternaryVariation (S.fiberProfile c r) := by
        apply Finset.sum_le_sum
        intro r _
        exact (ternaryVariation_bounds (S.fiberProfile c r)).2.1
      _ = S.terminalVariationMass c := rfl
  · calc
      S.terminalVariationMass c =
          ∑ r, ternaryVariation (S.fiberProfile c r) := rfl
      _ ≤ ∑ r, 4 * ternaryMeanDefect (S.fiberProfile c r) := by
        apply Finset.sum_le_sum
        intro r _
        exact (ternaryVariation_bounds (S.fiberProfile c r)).2.2
      _ = 4 * S.defectMass c := by
        simp only [defectMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [S.ternaryMeanDefect_fiberProfile]

/-- After normalization by positive total mass, terminal localization is
equivalent up to the exact constants two and four to vanishing mean min-loss.
This is the finite `2 delta ≤ Delta ≤ 4 delta` obstruction. -/
theorem normalizedTerminalVariation_bounds (c : S.State → ℝ)
    (hmass : 0 < S.totalMass c) :
    2 * S.normalizedDefect c ≤ S.normalizedTerminalVariation c ∧
      S.normalizedTerminalVariation c ≤ 4 * S.normalizedDefect c := by
  have hbounds := S.terminalVariationMass_bounds c
  constructor
  · simp only [normalizedDefect, normalizedTerminalVariation]
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hmass).2 hbounds.1
  · simp only [normalizedDefect, normalizedTerminalVariation]
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hmass).2 hbounds.2

end FiniteSystem

end

end CleanLean.KL
