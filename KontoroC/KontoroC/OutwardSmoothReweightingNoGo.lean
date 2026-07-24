/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardIteratedKraftGap

/-!
# Smooth reweighting cannot defeat iterated Kraft rarity

At a common Boolean residue depth, the fair law is uniform.  If another
finite law is pointwise at most `density` times the fair law, its mass on the
depth-`n` first-passage survivor cylinders is at most
`density * (17 / 20)^n`.  Consequently, retaining a fixed positive survivor
mass requires an exponentially growing pointwise density ratio.

The argument is finite summation over exact residue cylinders.  No
Radon--Nikodym derivative, limiting measure, atom, or ordinary seed is
asserted.
-/

namespace KontoroC
namespace OutwardSmoothReweightingNoGo

noncomputable section

open scoped BigOperators
open ShortcutParityPeriodicNoGo PrefixKraft OutwardCodeCompactness OutwardOddSlice
  OutwardStrictKraftGap OutwardIteratedKraftGap
  OutwardFiniteStateKraftGap.FirstPassageGrammar

/-- Mass assigned by a real-valued weight to a finite set. -/
def finiteMass {α : Type*} (weight : α → ℝ) (s : Finset α) : ℝ :=
  ∑ x ∈ s, weight x

/-- The singleton mass of the fair law on length-`L` Boolean words. -/
def fairDyadicAtom (L : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ L

/-- Fair mass of a finite collection of length-`L` residue words. -/
def fairResidueMass (L : ℕ) (s : Finset (List Bool)) : ℝ :=
  finiteMass (fun _ => fairDyadicAtom L) s

theorem finiteMass_le_density_mul
    {α : Type*} (s : Finset α) (μ ν : α → ℝ) (density : ℝ)
    (hcap : ∀ x ∈ s, μ x ≤ density * ν x) :
    finiteMass μ s ≤ density * finiteMass ν s := by
  rw [finiteMass, finiteMass, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hcap x hx

theorem fairResidueMass_eq
    (L : ℕ) (s : Finset (List Bool)) :
    fairResidueMass L s = (s.card : ℝ) / (2 : ℝ) ^ L := by
  simp [fairResidueMass, finiteMass, fairDyadicAtom,
    div_eq_mul_inv]

/-- The existing integer cylinder bound expressed as fair probability mass. -/
theorem finite_nMacro_fairResidueMass_le
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length ≤ L) :
    fairResidueMass L
        (coveredAtDepth (flattenedSchedules schedules) L) ≤
      ((17 : ℝ) / 20) ^ n := by
  let survivors := coveredAtDepth (flattenedSchedules schedules) L
  have hcard := finite_nMacro_coveredAtDepth_card_bound
    schedules n L hwords hmacroLength hbitLength
  have hcardReal :
      (20 : ℝ) ^ n * (survivors.card : ℝ) ≤
        (17 : ℝ) ^ n * (2 : ℝ) ^ L := by
    exact_mod_cast hcard
  rw [fairResidueMass_eq]
  have hratio :
      (survivors.card : ℝ) / (2 : ℝ) ^ L ≤
        (17 : ℝ) ^ n / (20 : ℝ) ^ n := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa [mul_comm] using hcardReal
  simpa [div_pow] using hratio

/-- Cross-multiplied fair-mass form, convenient for exact density lower
bounds. -/
theorem finite_nMacro_fairResidueMass_scaled_le
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length ≤ L) :
    (20 : ℝ) ^ n * fairResidueMass L
        (coveredAtDepth (flattenedSchedules schedules) L) ≤
      (17 : ℝ) ^ n := by
  have hmass := finite_nMacro_fairResidueMass_le
    schedules n L hwords hmacroLength hbitLength
  have hmul := mul_le_mul_of_nonneg_left hmass
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 20) n)
  calc
    (20 : ℝ) ^ n * fairResidueMass L
        (coveredAtDepth (flattenedSchedules schedules) L) ≤
      (20 : ℝ) ^ n * ((17 : ℝ) / 20) ^ n := hmul
    _ = (17 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num

/-- QM171a: a pointwise density cap against the fair residue law transfers
the iterated `17/20` Kraft bound to the reweighted survivor mass. -/
theorem finite_nMacro_smooth_reweighting_mass_le
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (μ : List Bool → ℝ) (density : ℝ) (hdensity : 0 ≤ density)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length ≤ L)
    (hcap : ∀ x ∈ binaryWords L,
      μ x ≤ density * fairDyadicAtom L) :
    finiteMass μ (coveredAtDepth (flattenedSchedules schedules) L) ≤
      density * ((17 : ℝ) / 20) ^ n := by
  let survivors := coveredAtDepth (flattenedSchedules schedules) L
  have hClength : ∀ w ∈ flattenedSchedules schedules, w.length ≤ L := by
    intro w hw
    rcases mem_flattenedSchedules_iff.mp hw with
      ⟨words, hmem, hflat⟩
    rw [← hflat]
    exact hbitLength words hmem
  have hsubset : survivors ⊆ binaryWords L :=
    coveredAtDepth_subset_binaryWords _ L hClength
  have hsmooth : finiteMass μ survivors ≤
      density * fairResidueMass L survivors := by
    apply finiteMass_le_density_mul
    intro x hx
    exact hcap x (hsubset hx)
  exact hsmooth.trans (mul_le_mul_of_nonneg_left
    (finite_nMacro_fairResidueMass_le
      schedules n L hwords hmacroLength hbitLength) hdensity)

/-- Scaled form of QM171a. -/
theorem finite_nMacro_smooth_reweighting_mass_scaled_le
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (μ : List Bool → ℝ) (density : ℝ) (hdensity : 0 ≤ density)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length ≤ L)
    (hcap : ∀ x ∈ binaryWords L,
      μ x ≤ density * fairDyadicAtom L) :
    (20 : ℝ) ^ n *
        finiteMass μ (coveredAtDepth (flattenedSchedules schedules) L) ≤
      density * (17 : ℝ) ^ n := by
  let survivors := coveredAtDepth (flattenedSchedules schedules) L
  have hClength : ∀ w ∈ flattenedSchedules schedules, w.length ≤ L := by
    intro w hw
    rcases mem_flattenedSchedules_iff.mp hw with
      ⟨words, hmem, hflat⟩
    rw [← hflat]
    exact hbitLength words hmem
  have hsubset : survivors ⊆ binaryWords L :=
    coveredAtDepth_subset_binaryWords _ L hClength
  have hsmooth : finiteMass μ survivors ≤
      density * fairResidueMass L survivors := by
    apply finiteMass_le_density_mul
    intro x hx
    exact hcap x (hsubset hx)
  calc
    (20 : ℝ) ^ n * finiteMass μ survivors ≤
        (20 : ℝ) ^ n * (density * fairResidueMass L survivors) :=
      mul_le_mul_of_nonneg_left hsmooth (pow_nonneg (by norm_num) n)
    _ = density *
        ((20 : ℝ) ^ n * fairResidueMass L survivors) := by ring
    _ ≤ density * (17 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left
        (finite_nMacro_fairResidueMass_scaled_le
          schedules n L hwords hmacroLength hbitLength) hdensity

/-- QM171b: retaining survivor mass `delta` forces an exponentially large
pointwise density ratio. -/
theorem finite_nMacro_density_growth_lower_bound
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (μ : List Bool → ℝ) (density delta : ℝ) (hdensity : 0 ≤ density)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length ≤ L)
    (hcap : ∀ x ∈ binaryWords L,
      μ x ≤ density * fairDyadicAtom L)
    (hretained : delta ≤
      finiteMass μ (coveredAtDepth (flattenedSchedules schedules) L)) :
    delta * (20 : ℝ) ^ n ≤ density * (17 : ℝ) ^ n := by
  calc
    delta * (20 : ℝ) ^ n = (20 : ℝ) ^ n * delta := by ring
    _ ≤ (20 : ℝ) ^ n *
        finiteMass μ (coveredAtDepth (flattenedSchedules schedules) L) :=
      mul_le_mul_of_nonneg_left hretained (pow_nonneg (by norm_num) n)
    _ ≤ density * (17 : ℝ) ^ n :=
      finite_nMacro_smooth_reweighting_mass_scaled_le
        schedules n L μ density hdensity hwords hmacroLength hbitLength hcap

end
end OutwardSmoothReweightingNoGo
end KontoroC
