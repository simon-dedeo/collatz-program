/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeMatching
import KontoroC.OutwardSelectorIndistinguishability

/-!
# Exact feature-fiber obstructions to finite recharge policies

A bounded selector architecture sees a state only through a proposed feature
map.  It therefore needs one common legal move on every observed feature
fiber.  Pointwise viability is not enough: different states in the same fiber
may require incompatible moves.

This file gives the exact finite alternative.  Either a policy depending only
on the feature exists, or (assuming every state is individually viable) one
observed fiber is a replayable obstruction: all its states have some legal
move, but no single move works for the whole fiber.  Executable finite tables
of common moves and bad features are provided for CEGIS.

The final theorem records the first-passage semantic boundary.  On a finite
nonempty same-layer state space of actual charges, even a successful feature
policy cannot consist entirely of literal recharge edges, since every such
edge strictly raises the charge.
-/

namespace KontoroC
namespace OutwardFeaturePolicyGap

open OutwardDirectedPathExpansion OutwardRechargeMatching

variable {State Feature Move : Type*}

/-- Every state in the exact table has at least one legal move. -/
def PointwiseViable (states : Finset State)
    (safe : State → Move → Prop) : Prop :=
  ∀ state ∈ states, ∃ move, safe state move

/-- A selector depending only on the proposed feature is legal throughout
the exact finite state table. -/
def FeaturePolicyOn (states : Finset State)
    (feature : State → Feature) (safe : State → Move → Prop) : Prop :=
  ∃ policy : Feature → Move,
    ∀ state ∈ states, safe state (policy (feature state))

/-- One move works simultaneously for every table state in a given feature
fiber.  Empty fibers satisfy this whenever the move type is nonempty; the
main equivalence quantifies only over observed fibers. -/
def CommonMoveOnFiber (states : Finset State)
    (feature : State → Feature) (safe : State → Move → Prop)
    (fiber : Feature) : Prop :=
  ∃ move, ∀ state ∈ states,
    feature state = fiber → safe state move

/-- An exact architecture obstruction.  The feature is observed, every state
in its fiber is individually viable, but the whole fiber has no common legal
move. -/
def IsFeatureGap (states : Finset State)
    (feature : State → Feature) (safe : State → Move → Prop)
    (fiber : Feature) : Prop :=
  (∃ state ∈ states, feature state = fiber) ∧
  (∀ state ∈ states, feature state = fiber →
    ∃ move, safe state move) ∧
  ¬ CommonMoveOnFiber states feature safe fiber

/-- A feature-based policy exists exactly when every observed feature fiber
has a common legal move. -/
theorem featurePolicyOn_iff_commonMoveOn_observed
    [Nonempty Move]
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) :
    FeaturePolicyOn states feature safe ↔
      ∀ fiber, (∃ state ∈ states, feature state = fiber) →
        CommonMoveOnFiber states feature safe fiber := by
  classical
  constructor
  · rintro ⟨policy, hpolicy⟩ fiber _
    refine ⟨policy fiber, ?_⟩
    intro state hstate hfeature
    simpa [hfeature] using hpolicy state hstate
  · intro hcommon
    let default : Move := Classical.choice inferInstance
    let policy : Feature → Move := fun fiber ↦
      if hfiber : ∃ state ∈ states, feature state = fiber then
        Classical.choose (hcommon fiber hfiber)
      else default
    refine ⟨policy, ?_⟩
    intro state hstate
    have hfiber : ∃ source ∈ states, feature source = feature state :=
      ⟨state, hstate, rfl⟩
    have hchosen := Classical.choose_spec
      (hcommon (feature state) hfiber)
    have hpolicyValue : policy (feature state) =
        Classical.choose (hcommon (feature state) hfiber) := by
      simp only [policy, dif_pos hfiber]
    rw [hpolicyValue]
    exact hchosen state hstate rfl

/-- Under pointwise viability, failure of the proposed feature architecture
is exactly the existence of an observed incompatible fiber. -/
theorem not_featurePolicyOn_iff_exists_featureGap
    [Nonempty Move]
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop)
    (hviable : PointwiseViable states safe) :
    ¬ FeaturePolicyOn states feature safe ↔
      ∃ fiber, IsFeatureGap states feature safe fiber := by
  constructor
  · intro hnot
    have hnotCommon : ¬ ∀ fiber,
        (∃ state ∈ states, feature state = fiber) →
        CommonMoveOnFiber states feature safe fiber := by
      intro hcommon
      exact hnot ((featurePolicyOn_iff_commonMoveOn_observed
        states feature safe).mpr hcommon)
    push Not at hnotCommon
    obtain ⟨fiber, hfiber, hnoCommon⟩ := hnotCommon
    refine ⟨fiber, hfiber, ?_, hnoCommon⟩
    intro state hstate _
    exact hviable state hstate
  · rintro ⟨fiber, hfiber, _, hnoCommon⟩ hpolicy
    have hcommon := (featurePolicyOn_iff_commonMoveOn_observed
      states feature safe).mp hpolicy
    exact hnoCommon (hcommon fiber hfiber)

/-- The exact finite selector alternative in directly consumable form. -/
theorem featurePolicyOn_or_featureGap
    [Nonempty Move]
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop)
    (hviable : PointwiseViable states safe) :
    FeaturePolicyOn states feature safe ∨
      ∃ fiber, IsFeatureGap states feature safe fiber := by
  by_cases hpolicy : FeaturePolicyOn states feature safe
  · exact Or.inl hpolicy
  · exact Or.inr
      ((not_featurePolicyOn_iff_exists_featureGap
        states feature safe hviable).mp hpolicy)

/-- A feature that separates all table states loses no policy information:
pointwise legal moves can then be assembled into a feature policy. -/
theorem featurePolicyOn_of_injectiveOn
    [Nonempty Move]
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop)
    (hviable : PointwiseViable states safe)
    (hinjective : ∀ x ∈ states, ∀ y ∈ states,
      feature x = feature y → x = y) :
    FeaturePolicyOn states feature safe := by
  apply (featurePolicyOn_iff_commonMoveOn_observed
    states feature safe).mpr
  rintro fiber ⟨source, hsource, hsourceFeature⟩
  obtain ⟨move, hmove⟩ := hviable source hsource
  refine ⟨move, ?_⟩
  intro state hstate hstateFeature
  have heq : state = source := hinjective state hstate source hsource
    (hstateFeature.trans hsourceFeature.symm)
  simpa [heq] using hmove

section Executable

variable [DecidableEq State] [DecidableEq Feature]
variable [Fintype Move] [DecidableEq Move] [Nonempty Move]

/-- Exact intersection of all legal-move sets on one feature fiber. -/
def commonMoves (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) [DecidableRel safe]
    (fiber : Feature) : Finset Move :=
  Finset.univ.filter fun move ↦
    ∀ state ∈ states, feature state = fiber → safe state move

omit [DecidableEq State] [DecidableEq Move] [Nonempty Move] in
@[simp] theorem mem_commonMoves_iff
    {states : Finset State} {feature : State → Feature}
    {safe : State → Move → Prop} [DecidableRel safe]
    {fiber : Feature} {move : Move} :
    move ∈ commonMoves states feature safe fiber ↔
      ∀ state ∈ states, feature state = fiber → safe state move := by
  simp [commonMoves]

omit [DecidableEq State] [DecidableEq Move] [Nonempty Move] in
theorem commonMoves_nonempty_iff
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) [DecidableRel safe]
    (fiber : Feature) :
    (commonMoves states feature safe fiber).Nonempty ↔
      CommonMoveOnFiber states feature safe fiber := by
  constructor
  · rintro ⟨move, hmove⟩
    exact ⟨move, mem_commonMoves_iff.mp hmove⟩
  · rintro ⟨move, hmove⟩
    exact ⟨move, mem_commonMoves_iff.mpr hmove⟩

/-- Exact list of observed feature signatures having no common legal move. -/
def badFeatures (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) [DecidableRel safe] : Finset Feature :=
  (states.image feature).filter fun fiber ↦
    commonMoves states feature safe fiber = ∅

omit [DecidableEq State] [Nonempty Move] in
@[simp] theorem mem_badFeatures_iff
    {states : Finset State} {feature : State → Feature}
    {safe : State → Move → Prop} [DecidableRel safe]
    {fiber : Feature} :
    fiber ∈ badFeatures states feature safe ↔
      fiber ∈ states.image feature ∧
        ¬ CommonMoveOnFiber states feature safe fiber := by
  rw [badFeatures, Finset.mem_filter]
  rw [← Finset.not_nonempty_iff_eq_empty, commonMoves_nonempty_iff]

omit [DecidableEq State] in
/-- Empty output from the exact bad-feature checker is equivalent to an
actual policy on the complete finite table. -/
theorem badFeatures_eq_empty_iff_featurePolicyOn
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) [DecidableRel safe] :
    badFeatures states feature safe = ∅ ↔
      FeaturePolicyOn states feature safe := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  constructor
  · intro hnoBad
    apply (featurePolicyOn_iff_commonMoveOn_observed
      states feature safe).mpr
    intro fiber hfiber
    by_contra hnoCommon
    exact hnoBad ⟨fiber,
      mem_badFeatures_iff.mpr
        ⟨Finset.mem_image.mpr hfiber, hnoCommon⟩⟩
  · intro hpolicy
    rintro ⟨fiber, hbad⟩
    obtain ⟨hfiber, hnoCommon⟩ := mem_badFeatures_iff.mp hbad
    exact hnoCommon
      ((featurePolicyOn_iff_commonMoveOn_observed
        states feature safe).mp hpolicy fiber
          (Finset.mem_image.mp hfiber))

omit [DecidableEq State] [Nonempty Move] in
/-- With a pointwise-viable complete table, nonempty checker output is
exactly existence of a feature-gap certificate. -/
theorem badFeatures_nonempty_iff_exists_featureGap
    (states : Finset State) (feature : State → Feature)
    (safe : State → Move → Prop) [DecidableRel safe]
    (hviable : PointwiseViable states safe) :
    (badFeatures states feature safe).Nonempty ↔
      ∃ fiber, IsFeatureGap states feature safe fiber := by
  constructor
  · rintro ⟨fiber, hfiber⟩
    obtain ⟨hobserved, hnoCommon⟩ := mem_badFeatures_iff.mp hfiber
    refine ⟨fiber, Finset.mem_image.mp hobserved, ?_, hnoCommon⟩
    intro state hstate _
    exact hviable state hstate
  · rintro ⟨fiber, hobserved, _, hnoCommon⟩
    exact ⟨fiber, mem_badFeatures_iff.mpr
      ⟨Finset.mem_image.mpr hobserved, hnoCommon⟩⟩

end Executable

/-- No feature map can make a finite nonempty same-layer table into a total
literal recharge policy.  The obstruction is semantic, not a failure to find
the right finite signature. -/
theorem no_featurePolicy_sameLayer_literalRecharge
    [Fintype State] [Nonempty State]
    (charge : State → ℕ) (feature : State → Feature)
    (edge : State → State → Prop)
    (hsound : ∀ source target, edge source target →
      RechargeEdge (charge source) (charge target)) :
    ¬ FeaturePolicyOn Finset.univ feature edge := by
  rintro ⟨policy, hpolicy⟩
  apply no_total_sameLayer_literalRecharge charge edge hsound
  exact ⟨fun state ↦ policy (feature state), fun state ↦
    hpolicy state (Finset.mem_univ state)⟩

end OutwardFeaturePolicyGap
end KontoroC
