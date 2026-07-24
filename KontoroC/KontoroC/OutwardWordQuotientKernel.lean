/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCoherentSeedTower
import KontoroC.OutwardSemanticAliasNoGo
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exact kernel gate for linearized word quotients

A shuffle, bracket, or rewriting relation may compress a finite aggregate
calculation only after every proposed relation is proved to lie in the kernel
of the exact linearized evaluator.  This file provides that gate for a finite
list of relations in the free module on words.

Sound generators span a submodule contained in the evaluator kernel, so the
evaluator descends canonically to the quotient.  Failure returns an explicit
generator with nonzero evaluated effect.  This validates only the aggregate
linear quotient: literal first-passage words, their order, legality, carries,
and seed replay are not quotient objects.  In particular, the existing
semantic-alias theorem still governs executable macros.
-/

namespace KontoroC
namespace OutwardWordQuotientKernel

variable {RingType Word Effect : Type*}
variable [Ring RingType] [AddCommGroup Effect] [Module RingType Effect]

/-- Every proposed finite relation is killed by the exact evaluator. -/
def RelationsSound
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType)) : Prop :=
  ∀ relation ∈ relations, evaluator relation = 0

/-- Soundness of the finite generating table is exactly containment of its
linear span in the evaluator kernel. -/
theorem span_relations_le_ker_iff
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType)) :
    Submodule.span RingType (relations : Set (Word →₀ RingType)) ≤
        LinearMap.ker evaluator ↔
      RelationsSound evaluator relations := by
  rw [Submodule.span_le]
  constructor
  · intro h relation hrelation
    exact LinearMap.mem_ker.mp (h hrelation)
  · intro h relation hrelation
    exact LinearMap.mem_ker.mpr (h relation hrelation)

/-- The evaluator induced on the quotient by a certified sound relation
table. -/
noncomputable def quotientEvaluator
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType))
    (hsound : RelationsSound evaluator relations) :
    ((Word →₀ RingType) ⧸
      Submodule.span RingType (relations : Set (Word →₀ RingType)))
        →ₗ[RingType] Effect :=
  (Submodule.span RingType (relations : Set (Word →₀ RingType))).liftQ
    evaluator ((span_relations_le_ker_iff evaluator relations).mpr hsound)

/-- Descending to the quotient preserves the exact evaluation of every
aggregate word combination. -/
@[simp] theorem quotientEvaluator_mkQ
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType))
    (hsound : RelationsSound evaluator relations)
    (combination : Word →₀ RingType) :
    quotientEvaluator evaluator relations hsound
        ((Submodule.span RingType
          (relations : Set (Word →₀ RingType))).mkQ combination) =
      evaluator combination := by
  rfl

section Decidable

variable [DecidableEq (Word →₀ RingType)] [DecidableEq Effect]

/-- Exact finite table of proposed relations whose evaluated effect is
nonzero.  A concrete decidable evaluator may compute the same filter
externally and replay its entries through the theorems below. -/
noncomputable def relationFailures
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType)) :
    Finset (Word →₀ RingType) :=
  relations.filter fun relation ↦ evaluator relation ≠ 0

omit [DecidableEq (Word →₀ RingType)] in
@[simp] theorem mem_relationFailures_iff
    {evaluator : (Word →₀ RingType) →ₗ[RingType] Effect}
    {relations : Finset (Word →₀ RingType)}
    {relation : Word →₀ RingType} :
    relation ∈ relationFailures evaluator relations ↔
      relation ∈ relations ∧ evaluator relation ≠ 0 := by
  simp [relationFailures]

omit [DecidableEq (Word →₀ RingType)] in
/-- Empty checker output is equivalent to exact soundness of the proposed
finite quotient. -/
theorem relationFailures_eq_empty_iff_sound
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
    (relations : Finset (Word →₀ RingType)) :
    relationFailures evaluator relations = ∅ ↔
      RelationsSound evaluator relations := by
  simp [relationFailures, RelationsSound]

omit [DecidableEq (Word →₀ RingType)] in
/-- Failure of quotient soundness produces one exact nonzero evaluated
relation, suitable for a CEGIS refinement. -/
theorem exists_failed_relation_of_not_sound
    (evaluator : (Word →₀ RingType) →ₗ[RingType] Effect)
  (relations : Finset (Word →₀ RingType))
    (hnot : ¬RelationsSound evaluator relations) :
    ∃ relation ∈ relationFailures evaluator relations,
      evaluator relation ≠ 0 := by
  rw [RelationsSound] at hnot
  push Not at hnot
  obtain ⟨relation, hrelation, hnonzero⟩ := hnot
  exact ⟨relation,
    mem_relationFailures_iff.mpr ⟨hrelation, hnonzero⟩, hnonzero⟩

end Decidable

end OutwardWordQuotientKernel
end KontoroC
