/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Combinatorics.Hall.Finite
import KontoroC.OutwardDirectedPathExpansion
import KontoroC.OutwardChartRankNoGo

/-!
# Hall certificates for layered first-passage recharge routers

At one exact finite precision, a collision-free router is an injective choice
of one accepted target for every source.  Mathlib's finite Hall theorem gives
the exact dichotomy: either such a router exists, or a concrete source subset
has fewer joint targets than sources.

For literal positive recharge edges there is an additional sharp boundary.
A finite same-layer graph on actual charges cannot even have one outgoing
edge from every state, because every recharge strictly increases the charge.
Consequently every such same-layer table has a Hall-deficient subset.  A live
router must therefore be genuinely cross-layer (or use lifted states whose
source and target charge interpretations differ).
-/

namespace KontoroC
namespace OutwardRechargeMatching

open OutwardDirectedPathExpansion OutwardChartRankNoGo

variable {Source Target State : Type*}

section FiniteRouter

variable [Fintype Source] [DecidableEq Source]
variable [Fintype Target] [DecidableEq Target]

/-- Exact accepted targets of one source in a finite decidable edge table. -/
def acceptedTargets (edge : Source → Target → Prop) [DecidableRel edge]
    (source : Source) : Finset Target :=
  Finset.univ.filter (edge source)

/-- One exact Hall obstruction. -/
def HallDeficient (edge : Source → Target → Prop) [DecidableRel edge]
    (sources : Finset Source) : Prop :=
  (sources.biUnion (acceptedTargets edge)).card < sources.card

/-- A collision-free router chooses an accepted, distinct target for every
source. -/
def CollisionFreeRouter (edge : Source → Target → Prop) : Prop :=
  ∃ route : Source → Target,
    Function.Injective route ∧ ∀ source, edge source (route source)

/-- The executable list of every Hall-deficient source family. -/
def hallDeficientSets (edge : Source → Target → Prop)
    [DecidableRel edge] : Finset (Finset Source) :=
  Finset.univ.powerset.filter fun sources ↦
    (sources.biUnion (acceptedTargets edge)).card < sources.card

omit [Fintype Source] [DecidableEq Source] [DecidableEq Target] in
@[simp] theorem mem_acceptedTargets_iff
    {edge : Source → Target → Prop} [DecidableRel edge]
    {source : Source} {target : Target} :
    target ∈ acceptedTargets edge source ↔ edge source target := by
  simp [acceptedTargets]

omit [DecidableEq Source] in
@[simp] theorem mem_hallDeficientSets_iff
    {edge : Source → Target → Prop} [DecidableRel edge]
    {sources : Finset Source} :
    sources ∈ hallDeficientSets edge ↔ HallDeficient edge sources := by
  simp [hallDeficientSets, HallDeficient]

omit [DecidableEq Source] in
/-- Hall's theorem in the exact form used by the finite router checker. -/
theorem hallCondition_iff_collisionFreeRouter
    (edge : Source → Target → Prop) [DecidableRel edge] :
    (∀ sources : Finset Source,
      sources.card ≤ (sources.biUnion (acceptedTargets edge)).card) ↔
      CollisionFreeRouter edge := by
  simpa [CollisionFreeRouter, acceptedTargets] using
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (acceptedTargets edge))

omit [DecidableEq Source] in
/-- Exact finite routing dichotomy: success is an injective accepted router;
failure is a replayable deficient source subset. -/
theorem collisionFreeRouter_or_hallDeficient
    (edge : Source → Target → Prop) [DecidableRel edge] :
    CollisionFreeRouter edge ∨
      ∃ sources : Finset Source, HallDeficient edge sources := by
  by_cases hhall : ∀ sources : Finset Source,
      sources.card ≤ (sources.biUnion (acceptedTargets edge)).card
  · exact Or.inl ((hallCondition_iff_collisionFreeRouter edge).mp hhall)
  · push Not at hhall
    obtain ⟨sources, hsources⟩ := hhall
    exact Or.inr ⟨sources, hsources⟩

omit [DecidableEq Source] in
/-- Empty output from the executable deficient-set checker is equivalent to
an actual collision-free router. -/
theorem hallDeficientSets_eq_empty_iff_collisionFreeRouter
    (edge : Source → Target → Prop) [DecidableRel edge] :
    hallDeficientSets edge = ∅ ↔ CollisionFreeRouter edge := by
  constructor
  · intro hempty
    rcases collisionFreeRouter_or_hallDeficient edge with hrouter | ⟨sources, hsources⟩
    · exact hrouter
    · have : sources ∈ hallDeficientSets edge :=
        mem_hallDeficientSets_iff.mpr hsources
      rw [hempty] at this
      simp at this
  · intro hrouter
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨sources, hsources⟩
    have hdeficient := mem_hallDeficientSets_iff.mp hsources
    have hhall := (hallCondition_iff_collisionFreeRouter edge).mpr hrouter
    exact (Nat.not_lt_of_ge (hhall sources)) hdeficient

end FiniteRouter

/-! ## Literal recharge soundness and the same-layer no-go -/

/-- Any total self-map whose every selected edge is a literal recharge is
impossible on a nonempty finite state type.  Injectivity is not needed. -/
theorem no_total_sameLayer_literalRecharge
    [Fintype State] [Nonempty State]
    (charge : State → ℕ) (edge : State → State → Prop)
    (hsound : ∀ source target, edge source target →
      RechargeEdge (charge source) (charge target)) :
    ¬∃ route : State → State, ∀ source, edge source (route source) := by
  rintro ⟨route, hroute⟩
  apply no_finite_total_strict_descent
      (fun state ↦ -((charge state : ℕ) : ℤ)) edge
  · intro source
    exact ⟨route source, hroute source⟩
  · intro source target hedge
    have hlt := (hsound source target hedge).lt
    omega

/-- In particular a collision-free same-layer literal recharge router cannot
exist. -/
theorem no_collisionFreeRouter_sameLayer_literalRecharge
    [Fintype State] [Nonempty State]
    (charge : State → ℕ) (edge : State → State → Prop)
    (hsound : ∀ source target, edge source target →
      RechargeEdge (charge source) (charge target)) :
    ¬CollisionFreeRouter edge := by
  rintro ⟨route, _, hroute⟩
  exact no_total_sameLayer_literalRecharge charge edge hsound
    ⟨route, hroute⟩

/-- Every finite nonempty same-layer literal recharge table has a concrete
Hall-deficient source family. -/
theorem exists_hallDeficient_sameLayer_literalRecharge
    [Fintype State] [DecidableEq State] [Nonempty State]
    (charge : State → ℕ) (edge : State → State → Prop)
    [DecidableRel edge]
    (hsound : ∀ source target, edge source target →
      RechargeEdge (charge source) (charge target)) :
    ∃ sources : Finset State, HallDeficient edge sources := by
  rcases collisionFreeRouter_or_hallDeficient edge with hrouter | hdeficient
  · exact (no_collisionFreeRouter_sameLayer_literalRecharge
      charge edge hsound hrouter).elim
  · exact hdeficient

/-! ## Cross-layer literal adapter -/

/-- For a genuinely layered table, Hall returns either an injective router
whose every edge has a literal recharge witness, or an exact deficient source
family. -/
theorem certifiedRechargeRouter_or_hallDeficient
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (sourceCharge : Source → ℕ) (targetCharge : Target → ℕ)
    (edge : Source → Target → Prop) [DecidableRel edge]
    (hsound : ∀ source target, edge source target →
      RechargeEdge (sourceCharge source) (targetCharge target)) :
    (∃ route : Source → Target,
      Function.Injective route ∧
      ∀ source, edge source (route source) ∧
        RechargeEdge (sourceCharge source) (targetCharge (route source))) ∨
      ∃ sources : Finset Source, HallDeficient edge sources := by
  rcases collisionFreeRouter_or_hallDeficient edge with hrouter | hdeficient
  · obtain ⟨route, hinjective, hroute⟩ := hrouter
    exact Or.inl ⟨route, hinjective, fun source ↦
      ⟨hroute source, hsound source (route source) (hroute source)⟩⟩
  · exact Or.inr hdeficient

end OutwardRechargeMatching
end KontoroC
