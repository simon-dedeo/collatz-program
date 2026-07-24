/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardBinaryRepairCokernel

/-!
# One-level selector lifts as exact carry cohomology

Fix a finite branch chart at one precision.  Changing the chosen lift of each
state by a bit `u` changes an edge defect by the affine coboundary

`(δu)(e) = u(target(e)) - gain(e) * u(source(e))`.

This file packages that expression as a linear map and applies the exact
repair-or-cokernel theorem.  Over `F_2`, either a state correction solves the
one-level lift equation, or a dual cocycle annihilates every coboundary and
detects the replayed carry defect.

Only the finite cochain equation is certified.  The caller must separately
prove that the chart, gains, and defects come from literal first-passage
replay and that corrections chosen at successive precisions are compatible.
-/

namespace KontoroC
namespace OutwardPolicyLiftCohomology

open OutwardBinaryRepairCokernel

variable {FieldType State Edge : Type*}

/-- The one-level state-lift coboundary on a directed branch chart. -/
def liftCoboundary
    [Field FieldType]
    (source target : Edge → State) (gain : Edge → FieldType) :
    (State → FieldType) →ₗ[FieldType] (Edge → FieldType) where
  toFun correction edge :=
    correction (target edge) - gain edge * correction (source edge)
  map_add' left right := by
    funext edge
    simp only [Pi.add_apply]
    ring
  map_smul' scalar correction := by
    funext edge
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

@[simp] theorem liftCoboundary_apply
    [Field FieldType]
    (source target : Edge → State) (gain : Edge → FieldType)
    (correction : State → FieldType) (edge : Edge) :
    liftCoboundary source target gain correction edge =
      correction (target edge) - gain edge * correction (source edge) :=
  rfl

/-- Generic one-level lift dichotomy over a field. -/
theorem policyLift_or_cocycleObstruction
    [Field FieldType]
    (source target : Edge → State) (gain : Edge → FieldType)
    (defect : Edge → FieldType) :
    (∃ correction : State → FieldType,
      ∀ edge,
        correction (target edge) - gain edge * correction (source edge) =
          defect edge) ∨
      ∃ cocycle : (Edge → FieldType) →ₗ[FieldType] FieldType,
        (∀ correction : State → FieldType,
          cocycle (fun edge ↦
            correction (target edge) -
              gain edge * correction (source edge)) = 0) ∧
        cocycle defect ≠ 0 := by
  rcases linearRepair_or_cokernelWitness
      (liftCoboundary source target gain) defect with
      hcorrection | ⟨cocycle, hannihilates, hdetects⟩
  · obtain ⟨correction, hcorrection⟩ := hcorrection
    exact Or.inl ⟨correction, fun edge ↦ congrFun hcorrection edge⟩
  · exact Or.inr ⟨cocycle, hannihilates, hdetects⟩

/-- Explicit binary form for a selector lift from precision `2^k` to
`2^(k+1)`. -/
theorem binaryPolicyLift_or_cocycleObstruction
    (source target : Edge → State) (gain : Edge → ZMod 2)
    (defect : Edge → ZMod 2) :
    (∃ correction : State → ZMod 2,
      ∀ edge,
        correction (target edge) - gain edge * correction (source edge) =
          defect edge) ∨
      ∃ cocycle : (Edge → ZMod 2) →ₗ[ZMod 2] ZMod 2,
        (∀ correction : State → ZMod 2,
          cocycle (fun edge ↦
            correction (target edge) -
              gain edge * correction (source edge)) = 0) ∧
        cocycle defect ≠ 0 :=
  policyLift_or_cocycleObstruction source target gain defect

/-- A checked dual cocycle refutes every state-bit lift correction. -/
theorem no_policyLift_of_cocycleObstruction
    [Field FieldType]
    (source target : Edge → State) (gain : Edge → FieldType)
    (defect : Edge → FieldType)
    (cocycle : (Edge → FieldType) →ₗ[FieldType] FieldType)
    (hannihilates : ∀ correction : State → FieldType,
      cocycle (fun edge ↦
        correction (target edge) - gain edge * correction (source edge)) = 0)
    (hdetects : cocycle defect ≠ 0) :
    ¬∃ correction : State → FieldType,
      ∀ edge,
        correction (target edge) - gain edge * correction (source edge) =
          defect edge := by
  rintro ⟨correction, hcorrection⟩
  apply hdetects
  have hfunctions :
      (fun edge ↦ correction (target edge) -
        gain edge * correction (source edge)) = defect := by
    funext edge
    exact hcorrection edge
  rw [← hfunctions]
  exact hannihilates correction

end OutwardPolicyLiftCohomology
end KontoroC
