/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardLeastSurvivorResource

/-!
# Compactness for arbitrary coercive resource minima

A bounded sublevel census replaces ordinary height by a resource
`resource : ℕ → ℕ`.  If every resource sublevel lies in a finite ordinary
window, then this is only a change of coordinates in the compactness gate:
the depthwise minimum resource is bounded exactly when one ordinary natural
survives every depth.

Equivalently, absence of an all-depth survivor says that every fixed resource
sublevel is eventually empty.  A computation at one cutoff certifies only
that any all-depth survivor must lie above that cutoff; proving the statement
for every cutoff is the full ordinary-root obstruction.
-/

namespace KontoroC
namespace OutwardResourceMinimumCompactness

open OutwardCodeCompactness OutwardOddSlice
open OutwardLeastSurvivorResource

noncomputable section

/-- Every resource sublevel is contained in some finite ordinary window. -/
def BoundedSublevels (resource : ℕ → ℕ) : Prop :=
  ∀ B, ∃ X, ∀ x, resource x ≤ B → x ≤ X

/-- A resource value actually attained by a depth-`d` witness. -/
def ResourceRealized
    (P : ℕ → ℕ → Prop) (resource : ℕ → ℕ)
    (d value : ℕ) : Prop :=
  ∃ x, P d x ∧ resource x = value

theorem resourceRealized_nonempty
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (resource : ℕ → ℕ) (d : ℕ) :
    ∃ value, ResourceRealized P resource d value := by
  obtain ⟨x, hx⟩ := h_nonempty d
  exact ⟨resource x, x, hx, rfl⟩

/-- Least resource value among the depth-`d` witnesses. -/
def minimumResource
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (resource : ℕ → ℕ) (d : ℕ) : ℕ :=
  leastWitness (ResourceRealized P resource)
    (resourceRealized_nonempty P h_nonempty resource) d

theorem minimumResource_spec
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (resource : ℕ → ℕ) (d : ℕ) :
    ResourceRealized P resource d
      (minimumResource P h_nonempty resource d) :=
  leastWitness_spec (ResourceRealized P resource)
    (resourceRealized_nonempty P h_nonempty resource) d

theorem minimumResource_le
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (resource : ℕ → ℕ) {d x : ℕ} (hx : P d x) :
    minimumResource P h_nonempty resource d ≤ resource x := by
  apply leastWitness_le (ResourceRealized P resource)
    (resourceRealized_nonempty P h_nonempty resource)
  exact ⟨x, hx, rfl⟩

/-- Nested witness sets make their minimum resource nondecreasing, even when
the resource itself is not monotone in the ordinary seed. -/
theorem minimumResource_mono
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (h_nested : ∀ d x, P (d + 1) x → P d x)
    (resource : ℕ → ℕ) :
    Monotone (minimumResource P h_nonempty resource) := by
  apply leastWitness_mono (ResourceRealized P resource)
    (resourceRealized_nonempty P h_nonempty resource)
  intro d value hvalue
  obtain ⟨x, hx, hresource⟩ := hvalue
  exact ⟨x, h_nested d x hx, hresource⟩

/-- Main compactness theorem: for a resource with bounded sublevels, bounded
depthwise minima are exactly one ordinary all-depth witness. -/
theorem exists_all_iff_bounded_minimumResource
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (h_nested : ∀ d x, P (d + 1) x → P d x)
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource) :
    (∃ x, ∀ d, P d x) ↔
      BoundedRange (minimumResource P h_nonempty resource) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨resource x, fun d ↦
      minimumResource_le P h_nonempty resource (hx d)⟩
  · rintro ⟨B, hB⟩
    obtain ⟨X, hX⟩ := hsublevels B
    obtain ⟨x, _, hx⟩ := finiteWindow_nested P h_nested X (fun d ↦ by
      obtain ⟨y, hy, hresource⟩ :=
        minimumResource_spec P h_nonempty resource d
      refine ⟨y, hX y ?_, hy⟩
      rw [hresource]
      exact hB d)
    exact ⟨x, hx⟩

/-- Since the minimum-resource sequence is monotone, boundedness is also
equivalent to eventual stabilization of the numerical minimum.  Coercive
sublevels are still needed to turn that scalar stabilization into one common
ordinary witness. -/
theorem exists_all_iff_eventuallyConstant_minimumResource
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (h_nested : ∀ d x, P (d + 1) x → P d x)
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource) :
    (∃ x, ∀ d, P d x) ↔
      EventuallyConstant (minimumResource P h_nonempty resource) := by
  rw [eventuallyConstant_iff_boundedRange_of_monotone
    (minimumResource_mono P h_nonempty h_nested resource)]
  exact exists_all_iff_bounded_minimumResource
    P h_nonempty h_nested resource hsublevels

/-- Every fixed resource cutoff is eventually excluded from the nested
witness sets. -/
def ResourceEscapes
    (P : ℕ → ℕ → Prop) (resource : ℕ → ℕ) : Prop :=
  ∀ B, ∃ d, ∀ x, P d x → B < resource x

/-- A single empty depth-`d` sublevel rules out every all-depth witness whose
resource is at most that cutoff. -/
theorem allDepth_resource_gt_of_empty_sublevel
    {P : ℕ → ℕ → Prop} {resource : ℕ → ℕ} {B d x : ℕ}
    (hempty : ∀ y, P d y → B < resource y)
    (hx : ∀ n, P n x) :
    B < resource x :=
  hempty x (hx d)

/-- With bounded sublevels, escape of every cutoff is exactly nonexistence of
one ordinary all-depth witness. -/
theorem not_exists_all_iff_resourceEscapes
    (P : ℕ → ℕ → Prop)
    (h_nested : ∀ d x, P (d + 1) x → P d x)
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource) :
    (¬ ∃ x, ∀ d, P d x) ↔ ResourceEscapes P resource := by
  constructor
  · intro hnone B
    obtain ⟨X, hX⟩ := hsublevels B
    by_contra hnot
    push Not at hnot
    have hwindow : ∀ d, ∃ x, x ≤ X ∧ P d x := by
      intro d
      obtain ⟨x, hx, hxresource⟩ := hnot d
      exact ⟨x, hX x hxresource, hx⟩
    obtain ⟨x, _, hx⟩ := finiteWindow_nested P h_nested X hwindow
    exact hnone ⟨x, hx⟩
  · intro hescape
    rintro ⟨x, hx⟩
    obtain ⟨d, hd⟩ := hescape (resource x)
    exact (Nat.lt_irrefl (resource x)) (hd x (hx d))

/-- Resource escape is equivalently unboundedness of the depthwise exact
minimum.  This direction does not need bounded sublevels; it is pure minimum
arithmetic. -/
theorem resourceEscapes_iff_not_bounded_minimumResource
    (P : ℕ → ℕ → Prop) (h_nonempty : ∀ d, ∃ x, P d x)
    (resource : ℕ → ℕ) :
    ResourceEscapes P resource ↔
      ¬BoundedRange (minimumResource P h_nonempty resource) := by
  constructor
  · intro hescape
    rintro ⟨B, hB⟩
    obtain ⟨d, hd⟩ := hescape B
    obtain ⟨x, hx, hresource⟩ :=
      minimumResource_spec P h_nonempty resource d
    have hgt := hd x hx
    rw [hresource] at hgt
    exact (Nat.not_lt_of_ge (hB d)) hgt
  · intro hunbounded B
    have hexists : ∃ d,
        B < minimumResource P h_nonempty resource d := by
      by_contra hnot
      push Not at hnot
      exact hunbounded ⟨B, hnot⟩
    obtain ⟨d, hd⟩ := hexists
    refine ⟨d, fun x hx ↦ ?_⟩
    exact hd.trans_le (minimumResource_le P h_nonempty resource hx)

/-! ## First-passage specialization -/

def firstPassageResourceMinimum (resource : ℕ → ℕ) (d : ℕ) : ℕ :=
  minimumResource RealizesFirstPassageDepth
    (finiteDepth_of_nonempty firstPassageCode_nonempty) resource d

theorem firstPassage_exists_allDepth_iff_bounded_resourceMinimum
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource) :
    (∃ x, ∀ d, RealizesFirstPassageDepth d x) ↔
      BoundedRange (firstPassageResourceMinimum resource) := by
  exact exists_all_iff_bounded_minimumResource
    RealizesFirstPassageDepth
    (finiteDepth_of_nonempty firstPassageCode_nonempty)
    (realizesDepth_nested FirstPassageCode)
    resource hsublevels

theorem firstPassage_not_exists_allDepth_iff_resourceEscapes
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource) :
    (¬ ∃ x, ∀ d, RealizesFirstPassageDepth d x) ↔
      ResourceEscapes RealizesFirstPassageDepth resource := by
  exact not_exists_all_iff_resourceEscapes
    RealizesFirstPassageDepth
    (realizesDepth_nested FirstPassageCode)
    resource hsublevels

/-- A bounded resource-minimum sequence reaches the existing standard
Collatz counterexample endpoint.  No such bound is asserted. -/
theorem not_collatz_of_bounded_firstPassage_resourceMinimum
    (resource : ℕ → ℕ) (hsublevels : BoundedSublevels resource)
    (hbounded : BoundedRange (firstPassageResourceMinimum resource)) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    (firstPassage_exists_allDepth_iff_bounded_resourceMinimum
      resource hsublevels).mpr hbounded
  exact OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
    (fun _ hw ↦ hw.1) hinfinite

/-! ## The worker's mixed-base resource -/

/-- Exponent of two in `x+1`. -/
def mixedBaseTwoExponent (x : ℕ) : ℕ :=
  padicValNat 2 (x + 1)

/-- Quotient after removing the maximal power of two from `x+1`. -/
def mixedBaseAfterTwo (x : ℕ) : ℕ :=
  (x + 1).divMaxPow 2

/-- Exponent of three after the two-primary part has been removed. -/
def mixedBaseThreeExponent (x : ℕ) : ℕ :=
  padicValNat 3 (mixedBaseAfterTwo x)

/-- Primitive factor after removing the maximal powers of two and three. -/
def mixedBaseUnit (x : ℕ) : ℕ :=
  (mixedBaseAfterTwo x).divMaxPow 3

/-- The exact coercive resource enumerated by
`outward_resource_sublevel.py`. -/
def mixedBaseResource (x : ℕ) : ℕ :=
  mixedBaseTwoExponent x + mixedBaseThreeExponent x + mixedBaseUnit x

/-- Exact factorization underlying the resource definition. -/
theorem mixedBase_decomposition (x : ℕ) :
    x + 1 =
      2 ^ mixedBaseTwoExponent x *
        3 ^ mixedBaseThreeExponent x * mixedBaseUnit x := by
  have htwo :
      2 ^ mixedBaseTwoExponent x * mixedBaseAfterTwo x = x + 1 := by
    exact Nat.pow_padicValNat_mul_divMaxPow 2 (x + 1)
  have hthree :
      3 ^ mixedBaseThreeExponent x * mixedBaseUnit x =
        mixedBaseAfterTwo x := by
    exact Nat.pow_padicValNat_mul_divMaxPow 3 (mixedBaseAfterTwo x)
  calc
    x + 1 = 2 ^ mixedBaseTwoExponent x * mixedBaseAfterTwo x :=
      htwo.symm
    _ = 2 ^ mixedBaseTwoExponent x *
        (3 ^ mixedBaseThreeExponent x * mixedBaseUnit x) := by
      rw [hthree]
    _ = 2 ^ mixedBaseTwoExponent x *
        3 ^ mixedBaseThreeExponent x * mixedBaseUnit x := by
      ring

/-- The worker's displayed coercivity estimate:
`mixedBaseResource x ≤ B` forces `x+1 ≤ B*6^B`. -/
theorem add_one_le_resource_mul_six_pow
    {x B : ℕ} (hresource : mixedBaseResource x ≤ B) :
    x + 1 ≤ B * 6 ^ B := by
  have htwoExp : mixedBaseTwoExponent x ≤ B := by
    dsimp [mixedBaseResource] at hresource
    omega
  have hthreeExp : mixedBaseThreeExponent x ≤ B := by
    dsimp [mixedBaseResource] at hresource
    omega
  have hunit : mixedBaseUnit x ≤ B := by
    dsimp [mixedBaseResource] at hresource
    omega
  have htwoPow : 2 ^ mixedBaseTwoExponent x ≤ 2 ^ B :=
    Nat.pow_le_pow_right (by omega) htwoExp
  have hthreePow : 3 ^ mixedBaseThreeExponent x ≤ 3 ^ B :=
    Nat.pow_le_pow_right (by omega) hthreeExp
  calc
    x + 1 =
        (2 ^ mixedBaseTwoExponent x *
          3 ^ mixedBaseThreeExponent x) * mixedBaseUnit x := by
      rw [mixedBase_decomposition]
    _ ≤ (2 ^ B * 3 ^ B) * B :=
      Nat.mul_le_mul (Nat.mul_le_mul htwoPow hthreePow) hunit
    _ = B * 6 ^ B := by
      rw [← mul_pow]
      ring

/-- Hence every mixed-base resource sublevel is an explicitly bounded finite
ordinary window. -/
theorem mixedBaseResource_boundedSublevels :
    BoundedSublevels mixedBaseResource := by
  intro B
  refine ⟨B * 6 ^ B, fun x hx ↦ ?_⟩
  have h := add_one_le_resource_mul_six_pow hx
  omega

def mixedBaseFirstPassageMinimum : ℕ → ℕ :=
  firstPassageResourceMinimum mixedBaseResource

/-- Exact infinite interpretation of the resource-sublevel census.  A
uniform bound on its depthwise exact minima would already produce one
ordinary all-depth first-passage seed. -/
theorem firstPassage_exists_allDepth_iff_bounded_mixedBaseMinimum :
    (∃ x, ∀ d, RealizesFirstPassageDepth d x) ↔
      BoundedRange mixedBaseFirstPassageMinimum :=
  firstPassage_exists_allDepth_iff_bounded_resourceMinimum
    mixedBaseResource mixedBaseResource_boundedSublevels

/-- Conversely, excluding every fixed mixed-base sublevel is exactly
nonexistence of an ordinary all-depth first-passage seed. -/
theorem firstPassage_not_exists_allDepth_iff_mixedBaseResourceEscapes :
    (¬ ∃ x, ∀ d, RealizesFirstPassageDepth d x) ↔
      ResourceEscapes RealizesFirstPassageDepth mixedBaseResource :=
  firstPassage_not_exists_allDepth_iff_resourceEscapes
    mixedBaseResource mixedBaseResource_boundedSublevels

/-- The exact scope of one finite sublevel audit such as `B=128`: an
all-depth seed, if one exists, must have resource above the excluded cutoff. -/
theorem allDepth_mixedBaseResource_gt_of_empty_sublevel
    {B d x : ℕ}
    (hempty : ∀ y, RealizesFirstPassageDepth d y →
      B < mixedBaseResource y)
    (hx : ∀ n, RealizesFirstPassageDepth n x) :
    B < mixedBaseResource x :=
  allDepth_resource_gt_of_empty_sublevel hempty hx

end

end OutwardResourceMinimumCompactness
end KontoroC
