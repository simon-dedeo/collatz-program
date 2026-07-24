/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSemanticAliasNoGo

/-!
# Exact indistinguishability witnesses for finite selector architectures

On a complete finite state set, a proposed target can be selected from the
current feature signature only if feature-indistinguishable states always
have the same target.  Failure yields an exact pair of states, suitable for a
CEGIS refinement loop.  Success is equivalent to existence of a decoder on
that finite state set.

This is a bounded architecture theorem.  Independently synthesized decoders
at growing precisions do not constitute one uniform unbounded selector.
-/

namespace KontoroC
namespace OutwardSelectorIndistinguishability

variable {State Feature Target : Type*}

/-- The target is a function of the observed feature on the specified exact
finite state set. -/
def FunctionalOn (states : Finset State)
    (feature : State → Feature) (target : State → Target) : Prop :=
  ∀ x ∈ states, ∀ y ∈ states,
    feature x = feature y → target x = target y

/-- One exact obstruction pair: the current architecture cannot distinguish
the states, but the required targets differ. -/
def IsIndistinguishableWitness
    (feature : State → Feature) (target : State → Target)
    (x y : State) : Prop :=
  feature x = feature y ∧ target x ≠ target y

section Decidable

variable [DecidableEq State] [DecidableEq Feature] [DecidableEq Target]

/-- Executable set of all exact obstruction pairs inside `states`. -/
def witnessPairs (states : Finset State)
    (feature : State → Feature) (target : State → Target) :
    Finset (State × State) :=
  (states.product states).filter fun pair =>
    feature pair.1 = feature pair.2 ∧ target pair.1 ≠ target pair.2

omit [DecidableEq State] in
@[simp] theorem mem_witnessPairs_iff
    {states : Finset State} {feature : State → Feature}
    {target : State → Target} {x y : State} :
    (x, y) ∈ witnessPairs states feature target ↔
      x ∈ states ∧ y ∈ states ∧
        IsIndistinguishableWitness feature target x y := by
  simp [witnessPairs, IsIndistinguishableWitness, and_assoc]

omit [DecidableEq State] [DecidableEq Feature] [DecidableEq Target] in
/-- Failure of functionality is exactly the existence of an obstruction
pair, not merely a failed fit score. -/
theorem not_functionalOn_iff_exists_witness
    (states : Finset State) (feature : State → Feature)
    (target : State → Target) :
    ¬FunctionalOn states feature target ↔
      ∃ x ∈ states, ∃ y ∈ states,
        IsIndistinguishableWitness feature target x y := by
  simp only [FunctionalOn, IsIndistinguishableWitness]
  push Not
  rfl

omit [DecidableEq State] in
/-- The executable obstruction-pair set is nonempty exactly when the current
feature architecture fails. -/
theorem witnessPairs_nonempty_iff_not_functionalOn
    (states : Finset State) (feature : State → Feature)
    (target : State → Target) :
    (witnessPairs states feature target).Nonempty ↔
      ¬FunctionalOn states feature target := by
  rw [not_functionalOn_iff_exists_witness]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    rcases mem_witnessPairs_iff.mp hxy with ⟨hx, hy, hwitness⟩
    exact ⟨x, hx, y, hy, hwitness⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨(x, y), mem_witnessPairs_iff.mpr ⟨hx, hy, hxy⟩⟩

omit [DecidableEq State] in
/-- Empty output from the exact checker is equivalent to functionality. -/
theorem witnessPairs_eq_empty_iff_functionalOn
    (states : Finset State) (feature : State → Feature)
    (target : State → Target) :
    witnessPairs states feature target = ∅ ↔
      FunctionalOn states feature target := by
  rw [← Finset.not_nonempty_iff_eq_empty,
    witnessPairs_nonempty_iff_not_functionalOn]
  simp

end Decidable

/-- Functionality is equivalent to the existence of an actual decoder on the
finite state set.  Values on feature signatures absent from `states` are
irrelevant and filled arbitrarily. -/
theorem functionalOn_iff_exists_decoder
    [Nonempty Target]
    (states : Finset State) (feature : State → Feature)
    (target : State → Target) :
    FunctionalOn states feature target ↔
      ∃ decode : Feature → Target,
        ∀ x ∈ states, target x = decode (feature x) := by
  constructor
  · intro hfunctional
    let Restricted := {x : State // x ∈ states}
    let restrictedFeature : Restricted → Feature := fun x => feature x
    let restrictedTarget : Restricted → Target := fun x => target x
    have hfactors : restrictedTarget.FactorsThrough restrictedFeature := by
      intro x y hxy
      exact hfunctional x x.property y y.property hxy
    obtain ⟨decode, hdecode⟩ :=
      (Function.factorsThrough_iff restrictedTarget).mp hfactors
    refine ⟨decode, fun x hx => ?_⟩
    have hpoint := congrFun hdecode (⟨x, hx⟩ : Restricted)
    simpa [restrictedFeature, restrictedTarget] using hpoint
  · rintro ⟨decode, hdecode⟩
    intro x hx y hy hxy
    rw [hdecode x hx, hdecode y hy, hxy]

/-- Adding information preserves functionality: if every coarse feature is
recoverable from the refined feature, a coarse decoder is also a refined
decoder. -/
theorem FunctionalOn.of_refinement
    (states : Finset State)
    (coarse : State → Feature) (fine : State → Target)
    {Output : Type*} (required : State → Output)
    (hcoarse : ∀ x ∈ states, ∀ y ∈ states,
      fine x = fine y → coarse x = coarse y)
    (hfunctional : FunctionalOn states coarse required) :
    FunctionalOn states fine required := by
  intro x hx y hy hxy
  exact hfunctional x hx y hy (hcoarse x hx y hy hxy)

/-- Conversely, an old obstruction pair survives every proposed refinement
which still assigns that pair the same new signature. -/
theorem witness_survives_unseparating_refinement
    (coarse : State → Feature) (fine : State → Target)
    {Output : Type*} (required : State → Output)
    {x y : State}
    (hwitness : IsIndistinguishableWitness coarse required x y)
    (hfine : fine x = fine y) :
    IsIndistinguishableWitness fine required x y :=
  ⟨hfine, hwitness.2⟩

end OutwardSelectorIndistinguishability
end KontoroC
