/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.EliminationTree

/-!
# Critical-assignment lifting across safe deletion

Deleting a globally non-critical minimum alternative can expose new ties at
outer minima.  Equality of the numerical tree value alone does not show that
KL's assignment-specific principal bound survives those ties.  This file
proves the stronger fact: every critical assignment after a globally safe
deletion lifts to a critical assignment before deletion with the same selected
leaf sum, and the two assignments satisfy exactly the same principal bounds.
-/

namespace CleanLean.KL

namespace EliminationTree.Assignment

variable {ι : Type}

/-- Critical assignments lift backward across deletion of a globally unused
left alternative.  This is the missing invariant-preservation statement:
newly exposed critical ties cannot escape the pre-deletion `(3.4)` bounds. -/
theorem exists_critical_lift_delete_left
    (K : EliminationTree.Context ι)
    (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
        ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA)
    (newA : EliminationTree.Assignment (K.fill right))
    (hnew : newA.IsCritical φ y) :
    ∃ oldA : EliminationTree.Assignment (K.fill (.inf left right)),
      oldA.IsCritical φ y ∧
      oldA.selectedEval φ y = newA.selectedEval φ y ∧
      (oldA.RespectsPrincipalBounds φ y ↔
        newA.RespectsPrincipalBounds φ y) := by
  induction K with
  | hole =>
      have hright : right.eval φ y ≤ left.eval φ y := by
        by_contra hnot
        have hleft : left.eval φ y ≤ right.eval φ y := le_of_not_ge hnot
        obtain ⟨leftA, hleftA⟩ := exists_isCritical left φ y
        exact (havoid (.infLeft leftA) ⟨hleft, hleftA⟩ leftA)
          (.refl (.infLeft leftA))
      refine ⟨.infRight newA, ⟨hright, hnew⟩, rfl, ?_⟩
      rfl
  | principal label K ih =>
      cases newA with
      | principalNode child =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
            intro oldA hold leftA hsub
            exact (havoid (.principalNode oldA) hold leftA) (.principal hsub)
          obtain ⟨oldChild, holdCritical, hselected, hrespect⟩ :=
            ih hinner child hnew
          refine ⟨.principalNode oldChild, holdCritical, hselected, ?_⟩
          constructor
          · intro hold
            exact ⟨hselected ▸ hold.1, hrespect.mp hold.2⟩
          · intro hnewRespect
            exact ⟨hselected.symm ▸ hnewRespect.1, hrespect.mpr hnewRespect.2⟩
  | addLeft K sibling ih =>
      cases newA with
      | add innerNew siblingA =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
            intro oldA hold leftA hsub
            exact (havoid (.add oldA siblingA) ⟨hold, hnew.2⟩ leftA)
              (.addLeft hsub siblingA)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.1
          refine ⟨.add oldInner siblingA, ⟨holdCritical, hnew.2⟩, ?_, ?_⟩
          · simp only [selectedEval, hselected]
          · simp only [RespectsPrincipalBounds, hrespect]
  | addRight sibling K ih =>
      cases newA with
      | add siblingA innerNew =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
            intro oldA hold leftA hsub
            exact (havoid (.add siblingA oldA) ⟨hnew.1, hold⟩ leftA)
              (.addRight siblingA hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.add siblingA oldInner, ⟨hnew.1, holdCritical⟩, ?_, ?_⟩
          · simp only [selectedEval, hselected]
          · simp only [RespectsPrincipalBounds, hrespect]
  | infLeft K sibling ih =>
      cases newA with
      | infLeft innerNew =>
          have hmono : (K.fill (.inf left right)).eval φ y ≤
              (K.fill right).eval φ y :=
            eval_delete_left_le K left right φ y
          have holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y := hmono.trans hnew.1
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
            intro oldA hold leftA hsub
            exact (havoid (.infLeft oldA) ⟨holdChosen, hold⟩ leftA)
              (.infLeft hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.infLeft oldInner, ⟨holdChosen, holdCritical⟩,
            hselected, hrespect⟩
      | infRight siblingA =>
          by_cases holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y
          · have hinner : ∀ oldA : EliminationTree.Assignment
                  (K.fill (.inf left right)),
                oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                  ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
              intro oldA hold leftA hsub
              exact (havoid (.infLeft oldA) ⟨holdChosen, hold⟩ leftA)
                (.infLeft hsub)
            have heq := eval_delete_left_of_noCriticalUse K left right φ y hinner
            have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := by
              rw [heq]
              exact hnew.1
            exact ⟨.infRight siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
          · have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := le_of_not_ge holdChosen
            exact ⟨.infRight siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
  | infRight sibling K ih =>
      cases newA with
      | infLeft siblingA =>
          by_cases holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y
          · have hinner : ∀ oldA : EliminationTree.Assignment
                  (K.fill (.inf left right)),
                oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                  ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
              intro oldA hold leftA hsub
              exact (havoid (.infRight oldA) ⟨holdChosen, hold⟩ leftA)
                (.infRight hsub)
            have heq := eval_delete_left_of_noCriticalUse K left right φ y hinner
            have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := by
              rw [heq]
              exact hnew.1
            exact ⟨.infLeft siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
          · have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := le_of_not_ge holdChosen
            exact ⟨.infLeft siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
      | infRight innerNew =>
          have hmono : (K.fill (.inf left right)).eval φ y ≤
              (K.fill right).eval φ y :=
            eval_delete_left_le K left right φ y
          have holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y := hmono.trans hnew.1
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
                ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA := by
            intro oldA hold leftA hsub
            exact (havoid (.infRight oldA) ⟨holdChosen, hold⟩ leftA)
              (.infRight hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.infRight oldInner, ⟨holdChosen, holdCritical⟩,
            hselected, hrespect⟩

/-- If every pre-deletion critical assignment satisfies the KL principal
bounds, then every post-deletion critical assignment does too. -/
theorem respectsPrincipalBounds_delete_left
    (K : EliminationTree.Context ι)
    (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ leftA : EliminationTree.Assignment left,
        ¬SelectedSubassignment (.infLeft (right := right) leftA) oldA)
    (hbefore : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → oldA.RespectsPrincipalBounds φ y) :
    ∀ newA : EliminationTree.Assignment (K.fill right),
      newA.IsCritical φ y → newA.RespectsPrincipalBounds φ y := by
  intro newA hnew
  obtain ⟨oldA, holdCritical, _, hrespect⟩ :=
    exists_critical_lift_delete_left K left right φ y havoid newA hnew
  exact hrespect.mp (hbefore oldA holdCritical)

/-- Symmetric lifting theorem for deletion of a globally unused right
alternative. -/
theorem exists_critical_lift_delete_right
    (K : EliminationTree.Context ι)
    (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
        ¬SelectedSubassignment (.infRight (left := left) rightA) oldA)
    (newA : EliminationTree.Assignment (K.fill left))
    (hnew : newA.IsCritical φ y) :
    ∃ oldA : EliminationTree.Assignment (K.fill (.inf left right)),
      oldA.IsCritical φ y ∧
      oldA.selectedEval φ y = newA.selectedEval φ y ∧
      (oldA.RespectsPrincipalBounds φ y ↔
        newA.RespectsPrincipalBounds φ y) := by
  induction K with
  | hole =>
      have hleft : left.eval φ y ≤ right.eval φ y := by
        by_contra hnot
        have hright : right.eval φ y ≤ left.eval φ y := le_of_not_ge hnot
        obtain ⟨rightA, hrightA⟩ := exists_isCritical right φ y
        exact (havoid (.infRight rightA) ⟨hright, hrightA⟩ rightA)
          (.refl (.infRight rightA))
      refine ⟨.infLeft newA, ⟨hleft, hnew⟩, rfl, ?_⟩
      rfl
  | principal label K ih =>
      cases newA with
      | principalNode child =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
            intro oldA hold rightA hsub
            exact (havoid (.principalNode oldA) hold rightA) (.principal hsub)
          obtain ⟨oldChild, holdCritical, hselected, hrespect⟩ :=
            ih hinner child hnew
          refine ⟨.principalNode oldChild, holdCritical, hselected, ?_⟩
          constructor
          · intro hold
            exact ⟨hselected ▸ hold.1, hrespect.mp hold.2⟩
          · intro hnewRespect
            exact ⟨hselected.symm ▸ hnewRespect.1, hrespect.mpr hnewRespect.2⟩
  | addLeft K sibling ih =>
      cases newA with
      | add innerNew siblingA =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
            intro oldA hold rightA hsub
            exact (havoid (.add oldA siblingA) ⟨hold, hnew.2⟩ rightA)
              (.addLeft hsub siblingA)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.1
          refine ⟨.add oldInner siblingA, ⟨holdCritical, hnew.2⟩, ?_, ?_⟩
          · simp only [selectedEval, hselected]
          · simp only [RespectsPrincipalBounds, hrespect]
  | addRight sibling K ih =>
      cases newA with
      | add siblingA innerNew =>
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
            intro oldA hold rightA hsub
            exact (havoid (.add siblingA oldA) ⟨hnew.1, hold⟩ rightA)
              (.addRight siblingA hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.add siblingA oldInner, ⟨hnew.1, holdCritical⟩, ?_, ?_⟩
          · simp only [selectedEval, hselected]
          · simp only [RespectsPrincipalBounds, hrespect]
  | infLeft K sibling ih =>
      cases newA with
      | infLeft innerNew =>
          have hmono : (K.fill (.inf left right)).eval φ y ≤
              (K.fill left).eval φ y :=
            eval_delete_right_le K left right φ y
          have holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y := hmono.trans hnew.1
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
            intro oldA hold rightA hsub
            exact (havoid (.infLeft oldA) ⟨holdChosen, hold⟩ rightA)
              (.infLeft hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.infLeft oldInner, ⟨holdChosen, holdCritical⟩,
            hselected, hrespect⟩
      | infRight siblingA =>
          by_cases holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y
          · have hinner : ∀ oldA : EliminationTree.Assignment
                  (K.fill (.inf left right)),
                oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                  ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
              intro oldA hold rightA hsub
              exact (havoid (.infLeft oldA) ⟨holdChosen, hold⟩ rightA)
                (.infLeft hsub)
            have heq := eval_delete_right_of_noCriticalUse K left right φ y hinner
            have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := by
              rw [heq]
              exact hnew.1
            exact ⟨.infRight siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
          · have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := le_of_not_ge holdChosen
            exact ⟨.infRight siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
  | infRight sibling K ih =>
      cases newA with
      | infLeft siblingA =>
          by_cases holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y
          · have hinner : ∀ oldA : EliminationTree.Assignment
                  (K.fill (.inf left right)),
                oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                  ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
              intro oldA hold rightA hsub
              exact (havoid (.infRight oldA) ⟨holdChosen, hold⟩ rightA)
                (.infRight hsub)
            have heq := eval_delete_right_of_noCriticalUse K left right φ y hinner
            have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := by
              rw [heq]
              exact hnew.1
            exact ⟨.infLeft siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
          · have hsiblingOld : sibling.eval φ y ≤
                (K.fill (.inf left right)).eval φ y := le_of_not_ge holdChosen
            exact ⟨.infLeft siblingA, ⟨hsiblingOld, hnew.2⟩, rfl, Iff.rfl⟩
      | infRight innerNew =>
          have hmono : (K.fill (.inf left right)).eval φ y ≤
              (K.fill left).eval φ y :=
            eval_delete_right_le K left right φ y
          have holdChosen : (K.fill (.inf left right)).eval φ y ≤
              sibling.eval φ y := hmono.trans hnew.1
          have hinner : ∀ oldA : EliminationTree.Assignment
                (K.fill (.inf left right)),
              oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
                ¬SelectedSubassignment (.infRight (left := left) rightA) oldA := by
            intro oldA hold rightA hsub
            exact (havoid (.infRight oldA) ⟨holdChosen, hold⟩ rightA)
              (.infRight hsub)
          obtain ⟨oldInner, holdCritical, hselected, hrespect⟩ :=
            ih hinner innerNew hnew.2
          refine ⟨.infRight oldInner, ⟨holdChosen, holdCritical⟩,
            hselected, hrespect⟩

/-- Principal bounds also survive globally safe right-alternative deletion. -/
theorem respectsPrincipalBounds_delete_right
    (K : EliminationTree.Context ι)
    (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → ∀ rightA : EliminationTree.Assignment right,
        ¬SelectedSubassignment (.infRight (left := left) rightA) oldA)
    (hbefore : ∀ oldA : EliminationTree.Assignment
        (K.fill (.inf left right)),
      oldA.IsCritical φ y → oldA.RespectsPrincipalBounds φ y) :
    ∀ newA : EliminationTree.Assignment (K.fill left),
      newA.IsCritical φ y → newA.RespectsPrincipalBounds φ y := by
  intro newA hnew
  obtain ⟨oldA, holdCritical, _, hrespect⟩ :=
    exists_critical_lift_delete_right K left right φ y havoid newA hnew
  exact hrespect.mp (hbefore oldA holdCritical)

end EliminationTree.Assignment

end CleanLean.KL
