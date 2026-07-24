/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardOddSlice
import KontoroC.OutwardCodeCounterexample
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Non-escape compactness for outward first-passage survivors

A family of measures carried by the depth-`n` survivor sets can produce an
ordinary all-depth seed only if some fixed finite natural window retains
positive mass at every depth.  For nested predicates that condition is also
sufficient: finite additivity finds a survivor inside the window at each
depth, and finite-window compactness finds one survivor common to all depths.

The main equivalence shows that carried uniformly nonescaping measures are
not a relaxation of the ordinary-root problem.  The probability corollaries
translate the standard uniform-tail condition into this exact gate and then
reuse the audited outward-code bridge to Syracuse and Collatz.
-/

namespace KontoroC
namespace OutwardNonEscapeCompactness

open MeasureTheory Set
open OutwardCodeCompactness OutwardCodeCounterexample OutwardOddSlice
open ShortcutParityPeriodicNoGo CleanLean.Collatz

/-- Every atom of `μ` is a witness to `P`. -/
def CarriedBy (P : ℕ → Prop) (μ : Measure ℕ) : Prop :=
  ∀ x, μ {x} ≠ 0 → P x

/-- One fixed finite natural window has positive mass at every depth. -/
def UniformlyNonEscaping (μ : ℕ → Measure ℕ) : Prop :=
  ∃ B, ∀ n, 0 < μ n (Finset.range (B + 1) : Set ℕ)

/-- Positive mass in a finite window carried by `P` supplies a bounded point
witnessing `P`. -/
theorem exists_bounded_point_of_positive_window
    {P : ℕ → Prop} {μ : Measure ℕ} {B : ℕ}
    (hcarried : CarriedBy P μ)
    (hwindow : 0 < μ (Finset.range (B + 1) : Set ℕ)) :
    ∃ x, x ≤ B ∧ P x := by
  have hsum : ∑ x ∈ Finset.range (B + 1), μ {x} ≠ 0 := by
    rw [sum_measure_singleton]
    exact ne_of_gt hwindow
  obtain ⟨x, hxmem, hxmass⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨x, by simpa using hxmem, hcarried x hxmass⟩

theorem exists_all_of_carriedBy_uniformlyNonEscaping
    (P : ℕ → ℕ → Prop)
    (hnested : ∀ n x, P (n + 1) x → P n x)
    (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n, CarriedBy (P n) (μ n))
    (hnonescape : UniformlyNonEscaping μ) :
    ∃ x, ∀ n, P n x := by
  obtain ⟨B, hB⟩ := hnonescape
  obtain ⟨x, _, hx⟩ := finiteWindow_nested P hnested B (fun n =>
    exists_bounded_point_of_positive_window (hcarried n) (hB n))
  exact ⟨x, hx⟩

/-- For nested predicates, a uniformly nonescaping family of measures carried
by the finite-depth witnesses exists exactly when one ordinary point survives
all depths. -/
theorem exists_all_iff_exists_carriedBy_uniformlyNonEscaping
    (P : ℕ → ℕ → Prop)
    (hnested : ∀ n x, P (n + 1) x → P n x) :
    (∃ x, ∀ n, P n x) ↔
      ∃ μ : ℕ → Measure ℕ,
        (∀ n, CarriedBy (P n) (μ n)) ∧ UniformlyNonEscaping μ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun _ => Measure.dirac x, ?_, ?_⟩
    · intro n y hymass
      by_cases hxy : x = y
      · simpa [hxy] using hx n
      · exact (hymass (by simp [hxy])).elim
    · refine ⟨x, fun _ => ?_⟩
      simp
  · rintro ⟨μ, hcarried, hnonescape⟩
    exact exists_all_of_carriedBy_uniformlyNonEscaping
      P hnested μ hcarried hnonescape

/-- There is one finite cutoff whose escaping tail has mass below one at
every depth.  For probability measures this already forces non-escape. -/
def UniformTailBelowOne (μ : ℕ → Measure ℕ) : Prop :=
  ∃ B, ∀ n, μ n {x | B < x} < 1

/-- Elementary discrete uniform tightness, stated directly through natural
tails. -/
def UniformlyTightOnNat (μ : ℕ → Measure ℕ) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ B, ∀ n, μ n {x | B < x} < ε

theorem uniformTailBelowOne_of_uniformlyTightOnNat
    {μ : ℕ → Measure ℕ} (htight : UniformlyTightOnNat μ) :
    UniformTailBelowOne μ := by
  obtain ⟨B, hB⟩ := htight 1 (by norm_num)
  exact ⟨B, hB⟩

theorem uniformlyNonEscaping_of_probability_tailBelowOne
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (htail : UniformTailBelowOne μ) :
    UniformlyNonEscaping μ := by
  obtain ⟨B, hB⟩ := htail
  refine ⟨B, fun n => ?_⟩
  by_contra hnot
  have hzero : μ n (Finset.range (B + 1) : Set ℕ) = 0 :=
    not_lt.mp hnot |> nonpos_iff_eq_zero.mp
  have hpartition := measure_add_measure_compl
    (μ := μ n) (s := (Finset.range (B + 1) : Set ℕ))
    MeasurableSet.of_discrete
  rw [hzero, zero_add, measure_univ] at hpartition
  have hcompl : ((Finset.range (B + 1) : Set ℕ))ᶜ = {x | B < x} := by
    ext x
    simp
  rw [hcompl] at hpartition
  exact (hB n).ne hpartition

theorem uniformlyNonEscaping_of_probability_uniformlyTightOnNat
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (htight : UniformlyTightOnNat μ) :
    UniformlyNonEscaping μ :=
  uniformlyNonEscaping_of_probability_tailBelowOne μ
    (uniformTailBelowOne_of_uniformlyTightOnNat htight)

theorem exists_infiniteExecution_of_carriedBy_uniformlyNonEscaping
    (C : Set (List Bool)) (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n, CarriedBy (RealizesDepth C n) (μ n))
    (hnonescape : UniformlyNonEscaping μ) :
    ∃ start, InfiniteExecution C start :=
  exists_all_of_carriedBy_uniformlyNonEscaping
    (RealizesDepth C) (realizesDepth_nested C) μ hcarried hnonescape

theorem exists_infiniteExecution_iff_exists_carriedBy_uniformlyNonEscaping
    (C : Set (List Bool)) :
    (∃ start, InfiniteExecution C start) ↔
      ∃ μ : ℕ → Measure ℕ,
        (∀ n, CarriedBy (RealizesDepth C n) (μ n)) ∧
          UniformlyNonEscaping μ :=
  exists_all_iff_exists_carriedBy_uniformlyNonEscaping
    (RealizesDepth C) (realizesDepth_nested C)

/-- If no ordinary point survives every depth, then any carried measure
family must lose all mass from each fixed finite window at some depth. -/
theorem finiteWindow_mass_zero_of_no_infiniteExecution
    (C : Set (List Bool)) (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n, CarriedBy (RealizesDepth C n) (μ n))
    (hnone : ¬ ∃ start, InfiniteExecution C start) :
    ∀ B, ∃ n, μ n (Finset.range (B + 1) : Set ℕ) = 0 := by
  intro B
  by_contra hzero
  push Not at hzero
  have hpositive : ∀ n,
      0 < μ n (Finset.range (B + 1) : Set ℕ) := fun n =>
    (pos_iff_ne_zero.mpr (hzero n))
  exact hnone (exists_infiniteExecution_of_carriedBy_uniformlyNonEscaping
    C μ hcarried ⟨B, hpositive⟩)

theorem exists_not_syracuseReachesOne_of_nonEscaping_firstPassage_measures
    (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hnonescape : UniformlyNonEscaping μ) :
    ∃ start, ¬ SyracuseReachesOne start := by
  obtain ⟨start, hinfinite⟩ :=
    exists_infiniteExecution_of_carriedBy_uniformlyNonEscaping
      FirstPassageCode μ hcarried hnonescape
  exact ⟨start, not_syracuseReachesOne_of_infiniteExecution
    (C := FirstPassageCode)
    (fun w hw => OutwardFirstPassage.firstPassage_outward
      (by simpa [FirstPassageCode] using hw))
    hinfinite⟩

theorem not_collatz_of_nonEscaping_firstPassage_measures
    (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hnonescape : UniformlyNonEscaping μ) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    exists_infiniteExecution_of_carriedBy_uniformlyNonEscaping
      FirstPassageCode μ hcarried hnonescape
  exact not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
    (fun w hw => OutwardFirstPassage.firstPassage_outward
      (by simpa [FirstPassageCode] using hw))
    hinfinite

theorem not_collatz_of_tight_firstPassage_probability_measures
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (htight : UniformlyTightOnNat μ) :
    ¬ CleanLean.Collatz.Conjecture :=
  not_collatz_of_nonEscaping_firstPassage_measures μ hcarried
    (uniformlyNonEscaping_of_probability_uniformlyTightOnNat μ htight)

theorem not_collatz_of_tailBelowOne_firstPassage_probability_measures
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (htail : UniformTailBelowOne μ) :
    ¬ CleanLean.Collatz.Conjecture :=
  not_collatz_of_nonEscaping_firstPassage_measures μ hcarried
    (uniformlyNonEscaping_of_probability_tailBelowOne μ htail)

/-- Conditional on Collatz, every family of measures carried by the finite
first-passage survivors completely leaves each fixed finite window at some
depth.  This is the exact no-free-lunch converse to the tightness bridge. -/
theorem firstPassage_carried_measures_escape_of_collatz
    (μ : ℕ → Measure ℕ)
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hcollatz : CleanLean.Collatz.Conjecture) :
    ∀ B, ∃ n, μ n (Finset.range (B + 1) : Set ℕ) = 0 := by
  apply finiteWindow_mass_zero_of_no_infiniteExecution
    FirstPassageCode μ hcarried
  rintro ⟨start, hinfinite⟩
  exact not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
    (fun w hw => OutwardFirstPassage.firstPassage_outward
      (by simpa [FirstPassageCode] using hw))
    hinfinite hcollatz

/-- For carried probability measures, the previous zero-window conclusion
is equivalent to placing all mass beyond the cutoff. -/
theorem firstPassage_probability_tail_eq_one_of_collatz
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hcollatz : CleanLean.Collatz.Conjecture) :
    ∀ B, ∃ n, μ n {x | B < x} = 1 := by
  intro B
  obtain ⟨n, hzero⟩ :=
    firstPassage_carried_measures_escape_of_collatz μ hcarried hcollatz B
  refine ⟨n, ?_⟩
  have hpartition := measure_add_measure_compl
    (μ := μ n) (s := (Finset.range (B + 1) : Set ℕ))
    MeasurableSet.of_discrete
  rw [hzero, zero_add, measure_univ] at hpartition
  have hcompl : ((Finset.range (B + 1) : Set ℕ))ᶜ = {x | B < x} := by
    ext x
    simp
  rw [hcompl] at hpartition
  exact hpartition

end OutwardNonEscapeCompactness
end KontoroC
