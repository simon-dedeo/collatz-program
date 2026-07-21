/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteElimination
import CleanLean.KL.DeletionInvariant

/-!
# Pointwise soundness of the pruning phase

The proposed repair performs every split while global `LocallyValid` is still
available, and only then prunes dead alternatives.  This file packages the
inductive invariant needed by the second phase.  A deletion is justified by
absence from every critical assignment satisfying the principal bounds.  If
all pre-deletion critical assignments satisfy those bounds, this conditional
deadness becomes the unconditional `NoCriticalUse` premise of the existing
functional and lifting theorems.
-/

namespace CleanLean.KL

namespace EliminationTree

variable {ι : Type}

/-- The assignment-specific KL invariant holds for every critical assignment
of a fixed tree at one evaluation point. -/
def AllCriticalRespect (tree : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ A : Assignment tree, A.IsCritical φ y → A.RespectsPrincipalBounds φ y

/-- A left minimum occurrence is dead relative to the whole surrounding tree,
conditional on the principal-bound invariant. -/
def LeftDead (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ bigA : Assignment (K.fill (.inf left right)),
    bigA.IsCritical φ y → bigA.RespectsPrincipalBounds φ y →
      ∀ leftA : Assignment left,
        ¬Assignment.SelectedSubassignment
          (.infLeft (right := right) leftA) bigA

/-- Symmetric deadness for a right minimum occurrence. -/
def RightDead (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ bigA : Assignment (K.fill (.inf left right)),
    bigA.IsCritical φ y → bigA.RespectsPrincipalBounds φ y →
      ∀ rightA : Assignment right,
        ¬Assignment.SelectedSubassignment
          (.infRight (left := left) rightA) bigA

theorem allCriticalRespect_of_locallyValid
    {tree : EliminationTree ι} (φ : ι → ℝ → ℝ) (y : ℝ)
    (hvalid : tree.LocallyValid φ y) : tree.AllCriticalRespect φ y := by
  intro A hA
  exact A.respectsPrincipalBounds_of_locallyValid φ y hA hvalid

/-- A tree satisfying the invariant has a critical assignment satisfying it,
so a dead marker cannot propagate through the root. -/
theorem exists_critical_respecting
    {tree : EliminationTree ι} (φ : ι → ℝ → ℝ) (y : ℝ)
    (hrespect : tree.AllCriticalRespect φ y) :
    ∃ A : Assignment tree,
      A.IsCritical φ y ∧ A.RespectsPrincipalBounds φ y := by
  obtain ⟨A, hA⟩ := Assignment.exists_isCritical tree φ y
  exact ⟨A, hA, hrespect A hA⟩

/-- One sound left-pruning step: functional value is unchanged and the
principal-bound invariant survives. -/
theorem prune_dead_left
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hrespect : (K.fill (.inf left right)).AllCriticalRespect φ y)
    (hdead : LeftDead K left right φ y) :
    (K.fill (.inf left right)).eval φ y = (K.fill right).eval φ y ∧
      (K.fill right).AllCriticalRespect φ y := by
  have havoid : ∀ oldA : Assignment (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ leftA : Assignment left,
        ¬Assignment.SelectedSubassignment
          (.infLeft (right := right) leftA) oldA := by
    intro oldA hold leftA
    exact hdead oldA hold (hrespect oldA hold) leftA
  exact ⟨Assignment.eval_delete_left_of_noCriticalUse K left right φ y havoid,
    Assignment.respectsPrincipalBounds_delete_left K left right φ y
      havoid hrespect⟩

/-- Symmetric right-pruning step. -/
theorem prune_dead_right
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hrespect : (K.fill (.inf left right)).AllCriticalRespect φ y)
    (hdead : RightDead K left right φ y) :
    (K.fill (.inf left right)).eval φ y = (K.fill left).eval φ y ∧
      (K.fill left).AllCriticalRespect φ y := by
  have havoid : ∀ oldA : Assignment (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ rightA : Assignment right,
        ¬Assignment.SelectedSubassignment
          (.infRight (left := left) rightA) oldA := by
    intro oldA hold rightA
    exact hdead oldA hold (hrespect oldA hold) rightA
  exact ⟨Assignment.eval_delete_right_of_noCriticalUse K left right φ y havoid,
    Assignment.respectsPrincipalBounds_delete_right K left right φ y
      havoid hrespect⟩

end EliminationTree

namespace ConcreteElimination

variable {ι : Type}

/-- LP coefficient evaluation moves in the correct direction during the same
left-pruning step, independently of the functional data. -/
theorem prune_dead_left_coeff
    (K : EliminationTree.Context ι) (left right : EliminationTree ι)
    (c : ι → ℝ) (lam : ℝ) :
    (eraseToRetarded (K.fill (.inf left right))).coeffEval c lam ≤
      (eraseToRetarded (K.fill right)).coeffEval c lam :=
  coeff_delete_left_le K left right c lam

/-- Symmetric coefficient monotonicity for right pruning. -/
theorem prune_dead_right_coeff
    (K : EliminationTree.Context ι) (left right : EliminationTree ι)
    (c : ι → ℝ) (lam : ℝ) :
    (eraseToRetarded (K.fill (.inf left right))).coeffEval c lam ≤
      (eraseToRetarded (K.fill left)).coeffEval c lam :=
  coeff_delete_right_le K left right c lam

end ConcreteElimination

end CleanLean.KL
