/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardOddSlice
import KontoroC.OutwardResourceTightness

/-!
# Least-survivor resource extremality and the triadic tax

For the maximal outward first-passage code, let `leastSurvivor d` be the
least positive ordinary seed executing `d` blocks.  This file proves that no
probability reweighting carried by the depth-`d` survivor set can lower the
expected resource `(x+1)/2` below the value at `leastSurvivor d`; the Dirac
mass at that least survivor attains equality.

The residue-two scalar slice then gives an exact nonnegative increment.  Its
`triadicTax d` is the difference between consecutive least-survivor resource
levels.  Bounded resource, bounded tax partial sums, eventual zero tax,
eventual stabilization of the least survivor, and one ordinary all-depth
seed are equivalent.  No boundedness or eventual vanishing is asserted.
-/

namespace KontoroC
namespace OutwardLeastSurvivorResource

open MeasureTheory Set
open OutwardCodeCompactness OutwardNonEscapeCompactness OutwardOddSlice
open ShortcutParityPeriodicNoGo OutwardFirstPassage

noncomputable section

/-- The one-letter first-passage word makes the maximal code nonempty. -/
theorem firstPassageCode_nonempty : FirstPassageCode.Nonempty := by
  refine ⟨[true], ?_⟩
  constructor
  · norm_num [WordOutward]
  · intro u hu
    have hlen := properPrefix_length_lt hu
    have huNil : u = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst u
    norm_num [WordOutward]

/-- The least positive ordinary seed executing exactly `d` first-passage
blocks. -/
def leastSurvivor (d : ℕ) : ℕ :=
  canonicalMinimumStart FirstPassageCode firstPassageCode_nonempty d

theorem leastSurvivor_realizes (d : ℕ) :
    RealizesFirstPassageDepth d (leastSurvivor d) := by
  exact leastWitness_spec
    (RealizesDepth FirstPassageCode)
    (finiteDepth_of_nonempty firstPassageCode_nonempty) d

theorem leastSurvivor_le {d x : ℕ}
    (hx : RealizesFirstPassageDepth d x) :
    leastSurvivor d ≤ x := by
  exact leastWitness_le
    (RealizesDepth FirstPassageCode)
    (finiteDepth_of_nonempty firstPassageCode_nonempty) hx

theorem leastSurvivor_odd (d : ℕ) : Odd (leastSurvivor d) :=
  least_realizer_odd (leastSurvivor_realizes d)
    (fun _ hx ↦ leastSurvivor_le hx)

theorem leastSurvivor_mono : Monotone leastSurvivor := by
  exact canonicalMinimumStart_mono FirstPassageCode
    firstPassageCode_nonempty

/-- The ordinary Archimedean resource used in QM172. -/
def resource (x : ℕ) : ℕ := (x + 1) / 2

/-- Resource of the least depth-`d` survivor. -/
def leastResource (d : ℕ) : ℕ := resource (leastSurvivor d)

theorem resource_mono : Monotone resource := by
  intro x y hxy
  exact Nat.div_le_div_right (Nat.add_le_add_right hxy 1)

theorem leastResource_mono : Monotone leastResource :=
  resource_mono.comp leastSurvivor_mono

/-- The lower bound is pointwise on every atom carried by the survivor set. -/
theorem leastResource_le_of_realizes {d x : ℕ}
    (hx : RealizesFirstPassageDepth d x) :
    leastResource d ≤ resource x :=
  resource_mono (leastSurvivor_le hx)

/-- The ENNReal resource moment of a measure on ordinary seeds. -/
def resourceMoment (μ : Measure ℕ) : ENNReal :=
  ∫⁻ x, (resource x : ENNReal) ∂μ

/-- A carried measure sees the least-survivor resource lower bound almost
everywhere.  The only subtlety is that `CarriedBy` is stated atomwise; on the
countable space `ℕ`, the union of all exceptional zero-mass atoms is null. -/
theorem ae_le_resource_of_carried
    {d : ℕ} {μ : Measure ℕ}
    (hcarried : CarriedBy (RealizesFirstPassageDepth d) μ) :
    ∀ᵐ x ∂μ, (leastResource d : ENNReal) ≤ (resource x : ENNReal) := by
  rw [MeasureTheory.ae_iff]
  let bad : Set ℕ :=
    {x | ¬(leastResource d : ENNReal) ≤ (resource x : ENNReal)}
  have hbad :
      bad = ⋃ x : {x // x ∈ bad}, ({x.1} : Set ℕ) := by
    ext x
    simp [bad]
  change μ bad = 0
  rw [hbad]
  apply MeasureTheory.measure_iUnion_null
  intro x
  by_contra hmass
  have hxDepth : RealizesFirstPassageDepth d x.1 :=
    hcarried x.1 hmass
  have hxLe : (leastResource d : ENNReal) ≤
      (resource x.1 : ENNReal) := by
    exact_mod_cast leastResource_le_of_realizes hxDepth
  exact x.2 hxLe

/-- QM172a: every probability measure carried by the depth-`d` survivors has
resource moment at least the resource of their least member. -/
theorem leastResource_le_resourceMoment
    {d : ℕ} (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hcarried : CarriedBy (RealizesFirstPassageDepth d) μ) :
    (leastResource d : ENNReal) ≤ resourceMoment μ := by
  calc
    (leastResource d : ENNReal) =
        ∫⁻ _x : ℕ, (leastResource d : ENNReal) ∂μ := by
      simp [MeasureTheory.lintegral_const]
    _ ≤ resourceMoment μ :=
      MeasureTheory.lintegral_mono_ae
        (ae_le_resource_of_carried hcarried)

/-- The Dirac mass at the least survivor is carried by the correct finite
depth survivor set. -/
theorem carriedBy_dirac_leastSurvivor (d : ℕ) :
    CarriedBy (RealizesFirstPassageDepth d)
      (Measure.dirac (leastSurvivor d)) := by
  intro x hmass
  by_cases hx : leastSurvivor d = x
  · simpa [← hx] using leastSurvivor_realizes d
  · exact (hmass (by simp [hx])).elim

/-- Dirac mass attains the lower bound exactly. -/
@[simp] theorem resourceMoment_dirac_leastSurvivor (d : ℕ) :
    resourceMoment (Measure.dirac (leastSurvivor d)) =
      (leastResource d : ENNReal) := by
  simp [resourceMoment, leastResource]

/-- The possible resource moments of carried probability measures. -/
def carriedResourceMoments (d : ℕ) : Set ENNReal :=
  {value | ∃ μ : Measure ℕ,
    IsProbabilityMeasure μ ∧
    CarriedBy (RealizesFirstPassageDepth d) μ ∧
    resourceMoment μ = value}

/-- The least-survivor resource is an attained minimum, not merely an
infimum. -/
theorem leastResource_isLeast_carriedResourceMoments (d : ℕ) :
    IsLeast (carriedResourceMoments d) (leastResource d : ENNReal) := by
  constructor
  · refine ⟨Measure.dirac (leastSurvivor d), inferInstance,
      carriedBy_dirac_leastSurvivor d, ?_⟩
    exact resourceMoment_dirac_leastSurvivor d
  · intro value hvalue
    obtain ⟨μ, hprob, hcarried, rfl⟩ := hvalue
    letI : IsProbabilityMeasure μ := hprob
    exact leastResource_le_resourceMoment μ hcarried

/-- Exact infimum formulation of QM172a. -/
theorem sInf_carriedResourceMoments (d : ℕ) :
    sInf (carriedResourceMoments d) = (leastResource d : ENNReal) :=
  (leastResource_isLeast_carriedResourceMoments d).csInf_eq

/-- Existence of one depth-indexed family of carried probability measures
whose resource moments share a finite upper bound. -/
def HasUniformCarriedResourceMoment : Prop :=
  ∃ μ : ℕ → Measure ℕ,
    (∀ d, IsProbabilityMeasure (μ d)) ∧
    (∀ d, CarriedBy (RealizesFirstPassageDepth d) (μ d)) ∧
    ∃ bound : ENNReal, bound ≠ ⊤ ∧
      ∀ d, resourceMoment (μ d) ≤ bound

/-- Reweighting cannot improve the uniform boundedness question: such a
carried probability family exists exactly when the least-survivor resource
sequence itself is bounded. -/
theorem hasUniformCarriedResourceMoment_iff_bounded_leastResource :
    HasUniformCarriedResourceMoment ↔ BoundedRange leastResource := by
  constructor
  · rintro ⟨μ, hprob, hcarried, bound, hboundTop, hbound⟩
    letI : ∀ d, IsProbabilityMeasure (μ d) := hprob
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hboundTop
    refine ⟨N, fun d ↦ ?_⟩
    have hlower : (leastResource d : ENNReal) ≤
        resourceMoment (μ d) :=
      leastResource_le_resourceMoment (μ d) (hcarried d)
    have hcast : (leastResource d : ENNReal) < (N : ENNReal) :=
      (hlower.trans (hbound d)).trans_lt hN
    have hnat : leastResource d < N := by
      exact_mod_cast hcast
    omega
  · rintro ⟨B, hB⟩
    let μ : ℕ → Measure ℕ :=
      fun d ↦ Measure.dirac (leastSurvivor d)
    refine ⟨μ, ?_, ?_, (B : ENNReal), ENNReal.natCast_ne_top B, ?_⟩
    · intro d
      dsimp only [μ]
      infer_instance
    · intro d
      dsimp only [μ]
      exact carriedBy_dirac_leastSurvivor d
    · intro d
      dsimp only [μ]
      rw [resourceMoment_dirac_leastSurvivor]
      exact_mod_cast hB d

/-! ## The residue-two tax -/

/-- Depth-`d` survivors in residue class two modulo three. -/
def ResidueTwoSurvivor (d x : ℕ) : Prop :=
  RealizesFirstPassageDepth d x ∧ x % 3 = 2

/-- The residue-two slice is nonempty at every finite depth: delete the
forced initial `[true]` block from the least survivor one level deeper. -/
theorem residueTwoSurvivor_nonempty (d : ℕ) :
    ∃ x, ResidueTwoSurvivor d x := by
  obtain ⟨x, hxDepth, hxMod, _⟩ :=
    odd_successor_to_residueTwo (leastSurvivor_odd (d + 1))
      (leastSurvivor_realizes (d + 1))
  exact ⟨x, hxDepth, hxMod⟩

/-- Least depth-`d` survivor lying in residue class two modulo three. -/
def leastResidueTwoSurvivor (d : ℕ) : ℕ :=
  leastWitness ResidueTwoSurvivor residueTwoSurvivor_nonempty d

theorem leastResidueTwoSurvivor_spec (d : ℕ) :
    ResidueTwoSurvivor d (leastResidueTwoSurvivor d) :=
  leastWitness_spec ResidueTwoSurvivor residueTwoSurvivor_nonempty d

theorem leastResidueTwoSurvivor_le {d x : ℕ}
    (hx : ResidueTwoSurvivor d x) :
    leastResidueTwoSurvivor d ≤ x :=
  leastWitness_le ResidueTwoSurvivor residueTwoSurvivor_nonempty hx

/-- The exact scalar slice formula from the existing odd-source theorem. -/
theorem leastSurvivor_succ_eq_residueTwo_slice (d : ℕ) :
    leastSurvivor (d + 1) =
      (2 * leastResidueTwoSurvivor d - 1) / 3 := by
  exact least_successor_eq_residueTwo_slice_unconditional
    (leastSurvivor_realizes (d + 1))
    (fun _ hx ↦ leastSurvivor_le hx)
    (leastResidueTwoSurvivor_spec d).1
    (leastResidueTwoSurvivor_spec d).2
    (fun _ hy hyMod ↦ leastResidueTwoSurvivor_le ⟨hy, hyMod⟩)

/-- Division-free form of the scalar slice identity. -/
theorem two_mul_leastResidueTwoSurvivor (d : ℕ) :
    2 * leastResidueTwoSurvivor d =
      3 * leastSurvivor (d + 1) + 1 := by
  have hm := (leastResidueTwoSurvivor_spec d).2
  have hdiv : 3 ∣ 2 * leastResidueTwoSurvivor d - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hmul :
      3 * ((2 * leastResidueTwoSurvivor d - 1) / 3) =
        2 * leastResidueTwoSurvivor d - 1 :=
    Nat.mul_div_cancel' hdiv
  rw [← leastSurvivor_succ_eq_residueTwo_slice d] at hmul
  omega

/-- Numerator of the nonnegative residue-two selection tax. -/
def triadicTaxNumerator (d : ℕ) : ℕ :=
  2 * leastResidueTwoSurvivor d - 3 * leastSurvivor d - 1

/-- The selected residue-two tax.  Divisibility by six is proved below. -/
def triadicTax (d : ℕ) : ℕ := triadicTaxNumerator d / 6

/-- Exact resource increment law, QM172b. -/
theorem leastResource_succ_eq_add_triadicTax (d : ℕ) :
    leastResource (d + 1) = leastResource d + triadicTax d := by
  obtain ⟨u, hu⟩ := leastSurvivor_odd d
  obtain ⟨v, hv⟩ := leastSurvivor_odd (d + 1)
  have huv : u ≤ v := by
    have hmono := leastSurvivor_mono (Nat.le_succ d)
    rw [hu, hv] at hmono
    omega
  have hm := two_mul_leastResidueTwoSurvivor d
  rw [hv] at hm
  simp only [leastResource, resource, triadicTax,
    triadicTaxNumerator]
  rw [hu, hv]
  omega

/-- The displayed tax numerator is genuinely divisible by six. -/
theorem six_dvd_triadicTaxNumerator (d : ℕ) :
    6 ∣ triadicTaxNumerator d := by
  obtain ⟨u, hu⟩ := leastSurvivor_odd d
  obtain ⟨v, hv⟩ := leastSurvivor_odd (d + 1)
  have huv : u ≤ v := by
    have hmono := leastSurvivor_mono (Nat.le_succ d)
    rw [hu, hv] at hmono
    omega
  have hm := two_mul_leastResidueTwoSurvivor d
  rw [hv] at hm
  refine ⟨v - u, ?_⟩
  simp only [triadicTaxNumerator]
  rw [hu]
  omega

theorem six_mul_triadicTax_eq_numerator (d : ℕ) :
    6 * triadicTax d = triadicTaxNumerator d := by
  exact Nat.mul_div_cancel' (six_dvd_triadicTaxNumerator d)

/-! ## Equivalent forms of vanishing accumulated tax -/

/-- Accumulated selected-residue tax before depth `d`. -/
def taxPartialSum (d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, triadicTax i

@[simp] theorem taxPartialSum_zero : taxPartialSum 0 = 0 := by
  simp [taxPartialSum]

theorem taxPartialSum_succ (d : ℕ) :
    taxPartialSum (d + 1) = taxPartialSum d + triadicTax d := by
  simp [taxPartialSum, Finset.sum_range_succ]

theorem leastSurvivor_zero : leastSurvivor 0 = 1 := by
  apply le_antisymm
  · apply leastSurvivor_le
    exact ⟨by omega, [], rfl, by simp [WordsIn],
      by simp [ExecutesBlocks]⟩
  · exact (leastSurvivor_realizes 0).1

@[simp] theorem leastResource_zero : leastResource 0 = 1 := by
  simp [leastResource, resource, leastSurvivor_zero]

/-- Telescoping form of QM172b. -/
theorem leastResource_eq_one_add_taxPartialSum (d : ℕ) :
    leastResource d = 1 + taxPartialSum d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [leastResource_succ_eq_add_triadicTax, ih,
        taxPartialSum_succ]
      omega

/-- Bounded least-survivor resource is exactly bounded accumulated tax. -/
theorem bounded_leastResource_iff_bounded_taxPartialSum :
    BoundedRange leastResource ↔ BoundedRange taxPartialSum := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun d ↦ ?_⟩
    have hEq := leastResource_eq_one_add_taxPartialSum d
    have h := hB d
    omega
  · rintro ⟨B, hB⟩
    refine ⟨B + 1, fun d ↦ ?_⟩
    rw [leastResource_eq_one_add_taxPartialSum]
    have h := hB d
    omega

/-- Eventual zero for a natural-valued increment sequence. -/
def EventuallyZero (f : ℕ → ℕ) : Prop :=
  ∃ N, ∀ d, N ≤ d → f d = 0

theorem taxPartialSum_mono : Monotone taxPartialSum := by
  apply monotone_nat_of_le_succ
  intro d
  rw [taxPartialSum_succ]
  omega

/-- A bounded nonnegative accumulated tax has only finitely many nonzero
increments, and conversely. -/
theorem bounded_taxPartialSum_iff_eventuallyZero_triadicTax :
    BoundedRange taxPartialSum ↔ EventuallyZero triadicTax := by
  rw [← eventuallyConstant_iff_boundedRange_of_monotone taxPartialSum_mono]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun d hd ↦ ?_⟩
    have hcur := hN d hd
    have hnext := hN (d + 1) (by omega)
    rw [taxPartialSum_succ] at hnext
    omega
  · rintro ⟨N, hzero⟩
    refine ⟨N, ?_⟩
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => rfl
    | succ d hd ih =>
        rw [taxPartialSum_succ, hzero d hd, Nat.add_zero, ih]

/-- For an odd least survivor, its resource remembers it exactly. -/
theorem two_mul_leastResource (d : ℕ) :
    2 * leastResource d = leastSurvivor d + 1 := by
  obtain ⟨u, hu⟩ := leastSurvivor_odd d
  simp only [leastResource, resource, hu]
  omega

/-- Eventual zero tax is equivalent to eventual stabilization of the least
resource level. -/
theorem eventuallyZero_triadicTax_iff_eventuallyConstant_leastResource :
    EventuallyZero triadicTax ↔ EventuallyConstant leastResource := by
  constructor
  · rintro ⟨N, hzero⟩
    refine ⟨N, ?_⟩
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => rfl
    | succ d hd ih =>
        rw [leastResource_succ_eq_add_triadicTax,
          hzero d hd, Nat.add_zero, ih]
  · rintro ⟨N, hN⟩
    refine ⟨N, fun d hd ↦ ?_⟩
    have hcur := hN d hd
    have hnext := hN (d + 1) (by omega)
    rw [leastResource_succ_eq_add_triadicTax] at hnext
    omega

/-- Because every least survivor is odd, stabilizing its halved resource is
equivalent to stabilizing the survivor itself. -/
theorem eventuallyConstant_leastResource_iff_leastSurvivor :
    EventuallyConstant leastResource ↔ EventuallyConstant leastSurvivor := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun d hd ↦ ?_⟩
    have hdEq := hN d hd
    have htwoD := two_mul_leastResource d
    have htwoN := two_mul_leastResource N
    omega
  · rintro ⟨N, hN⟩
    refine ⟨N, fun d hd ↦ ?_⟩
    simp only [leastResource, hN d hd]

/-- Stabilization of the least finite-depth seeds is exactly the existence of
one ordinary seed realizing every finite depth. -/
theorem eventuallyConstant_leastSurvivor_iff_exists_allDepth :
    EventuallyConstant leastSurvivor ↔
      ∃ x, ∀ d, RealizesFirstPassageDepth d x := by
  change
    EventuallyConstant
        (canonicalMinimumStart FirstPassageCode
          firstPassageCode_nonempty) ↔
      ∃ x, ∀ d, RealizesDepth FirstPassageCode d x
  exact (infiniteExecution_iff_eventuallyConstant_canonicalMinimum
    FirstPassageCode firstPassageCode_nonempty).symm

/-- QM172c, exposed as the four adjacent equivalences so no implication is
hidden by a bundled proposition. -/
theorem leastSurvivor_triadicTax_equivalences :
    (BoundedRange leastResource ↔ BoundedRange taxPartialSum) ∧
    (BoundedRange taxPartialSum ↔ EventuallyZero triadicTax) ∧
    (EventuallyZero triadicTax ↔ EventuallyConstant leastSurvivor) ∧
    (EventuallyConstant leastSurvivor ↔
      ∃ x, ∀ d, RealizesFirstPassageDepth d x) := by
  exact ⟨bounded_leastResource_iff_bounded_taxPartialSum,
    bounded_taxPartialSum_iff_eventuallyZero_triadicTax,
    eventuallyZero_triadicTax_iff_eventuallyConstant_leastResource.trans
      eventuallyConstant_leastResource_iff_leastSurvivor,
    eventuallyConstant_leastSurvivor_iff_exists_allDepth⟩

end

end OutwardLeastSurvivorResource
end KontoroC
