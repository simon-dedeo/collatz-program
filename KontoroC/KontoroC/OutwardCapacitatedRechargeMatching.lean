/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardPolicyLiftCohomology
import KontoroC.OutwardRechargeMatching

/-!
# Capacitated Hall certificates for finite tower completion

A target top with capacity `c` is replaced by `c` distinct slots.  Ordinary
Hall matching on the slot type then gives the exact capacitated dichotomy:
either every uncovered source is assigned injectively to a reachable slot, or
a concrete source family sees fewer total reachable slots than sources.

Every accepted cross-layer edge may additionally carry a literal recharge
witness.  As in the uncapacitated case, a finite same-layer table on fixed
ordinary charges is impossible even with repeated slots: capacity can absorb
collisions but cannot create an outgoing positive-recharge edge from a state
of maximal charge.
-/

namespace KontoroC
namespace OutwardCapacitatedRechargeMatching

open OutwardDirectedPathExpansion OutwardRechargeMatching

variable {Source Target State : Type*}

/-- Distinct capacity slots over each target. -/
abbrev CapacitySlot (capacity : Target → ℕ) :=
  Σ target : Target, Fin (capacity target)

/-- A source reaches a slot exactly when it reaches the slot's underlying
target. -/
def reachesSlot (capacity : Target → ℕ)
    (edge : Source → Target → Prop)
    (source : Source) (slot : CapacitySlot capacity) : Prop :=
  edge source slot.1

instance reachesSlot_decidableRel
    (capacity : Target → ℕ) (edge : Source → Target → Prop)
    [DecidableRel edge] : DecidableRel (reachesSlot capacity edge) :=
  fun source slot ↦ inferInstanceAs (Decidable (edge source slot.1))

/-- Every source receives a distinct reachable capacity slot. -/
def CapacitatedRouter
    (capacity : Target → ℕ) (edge : Source → Target → Prop) : Prop :=
  CollisionFreeRouter (reachesSlot capacity edge)

/-- A source family has insufficient total reachable target capacity. -/
def CapacitatedHallDeficient
    [Fintype Target] [DecidableEq Target]
    (capacity : Target → ℕ) (edge : Source → Target → Prop)
    [DecidableRel edge] (sources : Finset Source) : Prop :=
  HallDeficient (reachesSlot capacity edge) sources

section Finite

variable [Fintype Source] [DecidableEq Source]
variable [Fintype Target] [DecidableEq Target]

omit [DecidableEq Source] in
/-- Exact capacitated Hall dichotomy by expansion into distinct target slots. -/
theorem capacitatedRouter_or_hallDeficient
    (capacity : Target → ℕ) (edge : Source → Target → Prop)
    [DecidableRel edge] :
    CapacitatedRouter capacity edge ∨
      ∃ sources : Finset Source,
        CapacitatedHallDeficient capacity edge sources :=
  by
    simpa [CapacitatedRouter, CapacitatedHallDeficient] using
      (collisionFreeRouter_or_hallDeficient (reachesSlot capacity edge))

omit [DecidableEq Source] in
/-- Cross-layer literal specialization: a successful slot assignment retains
a literal recharge witness for every selected underlying target. -/
theorem certifiedCapacitatedRechargeRouter_or_hallDeficient
    (capacity : Target → ℕ)
    (sourceCharge : Source → ℕ) (targetCharge : Target → ℕ)
    (edge : Source → Target → Prop) [DecidableRel edge]
    (hsound : ∀ source target, edge source target →
      RechargeEdge (sourceCharge source) (targetCharge target)) :
    (∃ route : Source → CapacitySlot capacity,
      Function.Injective route ∧
      ∀ source,
        edge source (route source).1 ∧
        RechargeEdge (sourceCharge source)
          (targetCharge (route source).1)) ∨
      ∃ sources : Finset Source,
        CapacitatedHallDeficient capacity edge sources := by
  rcases capacitatedRouter_or_hallDeficient capacity edge with
      hrouter | hdeficient
  · obtain ⟨route, hinjective, hroute⟩ := hrouter
    exact Or.inl ⟨route, hinjective, fun source ↦
      ⟨hroute source,
        hsound source (route source).1 (hroute source)⟩⟩
  · exact Or.inr hdeficient

end Finite

/-! ## Same-layer capacity cannot defeat strict outwardness -/

/-- Even with arbitrary target capacities, a nonempty finite same-layer
literal recharge table has a capacitated Hall-deficient source family. -/
theorem exists_capacitatedHallDeficient_sameLayer_literalRecharge
    [Fintype State] [DecidableEq State] [Nonempty State]
    (capacity : State → ℕ) (charge : State → ℕ)
    (edge : State → State → Prop) [DecidableRel edge]
    (hsound : ∀ source target, edge source target →
      RechargeEdge (charge source) (charge target)) :
    ∃ sources : Finset State,
      CapacitatedHallDeficient capacity edge sources := by
  rcases capacitatedRouter_or_hallDeficient capacity edge with
      hrouter | hdeficient
  · obtain ⟨route, _, hroute⟩ := hrouter
    exact (no_total_sameLayer_literalRecharge charge edge hsound
      ⟨fun source ↦ (route source).1, fun source ↦ hroute source⟩).elim
  · exact hdeficient

end OutwardCapacitatedRechargeMatching
end KontoroC
