/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.MarkedPruning

/-!
# Occurrence-indexed one-pass pruning

A predicate on principal labels cannot distinguish two syntactically distinct
leaves carrying equal labels.  Phase A, however, marks a particular repeated
*occurrence*.  This file therefore stores the mark in a tree with the same
syntax as `EliminationTree` and proves a one-pass semantic pruning theorem.

The important theorem is `eval_pruneOccurrences`: if no critical assignment
of the original tree hits a marked occurrence, pruning preserves functional
evaluation exactly.  The proof does not sequentially lift assignments through
earlier deletions.  It works directly on the annotated tree, so the occurrence
identity cannot be lost.
-/

namespace CleanLean.KL

namespace EliminationTree

variable {ι : Type}

/-- An elimination tree whose individual leaf occurrences carry Boolean
marks.  Equal `PrincipalLabel`s at different leaves remain distinguishable. -/
inductive OccurrenceTree (ι : Type) where
  | leaf (label : PrincipalLabel ι) (marked : Bool)
  | principal (label : PrincipalLabel ι) (body : OccurrenceTree ι)
  | add (left right : OccurrenceTree ι)
  | inf (left right : OccurrenceTree ι)

namespace OccurrenceTree

/-- Forget the occurrence marks. -/
def erase : OccurrenceTree ι → EliminationTree ι
  | .leaf label _ => .leaf label
  | .principal label body => .principal label body.erase
  | .add left right => .add left.erase right.erase
  | .inf left right => .inf left.erase right.erase

/-- A selected assignment reaches a specifically marked occurrence. -/
def Hits : (tree : OccurrenceTree ι) → Assignment tree.erase → Prop
  | .leaf _ marked, .principalLeaf _ => marked = true
  | .principal _ body, .principalNode child => body.Hits child
  | .add left right, .add leftA rightA => left.Hits leftA ∨ right.Hits rightA
  | .inf left _, .infLeft leftA => left.Hits leftA
  | .inf _ right, .infRight rightA => right.Hits rightA

/-- Every assignment through this annotated subtree hits a marked
occurrence. -/
def StructurallyDead : OccurrenceTree ι → Prop
  | .leaf _ marked => marked = true
  | .principal _ body => body.StructurallyDead
  | .add left right => left.StructurallyDead ∨ right.StructurallyDead
  | .inf left right => left.StructurallyDead ∧ right.StructurallyDead

/-- Occurrence-indexed deadness has exactly the intended assignment
semantics. -/
theorem structurallyDead_iff_forall_hits (tree : OccurrenceTree ι) :
    tree.StructurallyDead ↔ ∀ A : Assignment tree.erase, tree.Hits A := by
  induction tree with
  | leaf label marked =>
      constructor
      · intro h A
        cases A
        exact h
      · intro h
        exact h (.principalLeaf label)
  | principal label body ih =>
      constructor
      · intro h A
        cases A with
        | principalNode child => exact ih.mp h child
      · intro h
        apply ih.mpr
        intro child
        exact h (.principalNode child)
  | add left right ihLeft ihRight =>
      constructor
      · rintro (hleft | hright) A
        · cases A with
          | add leftA rightA => exact Or.inl (ihLeft.mp hleft leftA)
        · cases A with
          | add leftA rightA => exact Or.inr (ihRight.mp hright rightA)
      · intro h
        by_cases hleft : left.StructurallyDead
        · exact Or.inl hleft
        by_cases hright : right.StructurallyDead
        · exact Or.inr hright
        exfalso
        have hnleft : ¬∀ A : Assignment left.erase, left.Hits A :=
          fun hall => hleft (ihLeft.mpr hall)
        have hnright : ¬∀ A : Assignment right.erase, right.Hits A :=
          fun hall => hright (ihRight.mpr hall)
        obtain ⟨leftA, hleftA⟩ := not_forall.mp hnleft
        obtain ⟨rightA, hrightA⟩ := not_forall.mp hnright
        exact (h (.add leftA rightA)).elim hleftA hrightA
  | inf left right ihLeft ihRight =>
      constructor
      · intro h A
        cases A with
        | infLeft leftA => exact ihLeft.mp h.1 leftA
        | infRight rightA => exact ihRight.mp h.2 rightA
      · intro h
        constructor
        · apply ihLeft.mpr
          intro leftA
          exact h (.infLeft leftA)
        · apply ihRight.mpr
          intro rightA
          exact h (.infRight rightA)

/-- One-pass pruning with occurrence-specific marks. -/
def pruneOccurrences : OccurrenceTree ι → PruneResult ι
  | .leaf label marked => if marked then .dead else .live (.leaf label)
  | .principal label body =>
      match body.pruneOccurrences with
      | .dead => .dead
      | .live body' => .live (.principal label body')
  | .add left right =>
      match left.pruneOccurrences, right.pruneOccurrences with
      | .live left', .live right' => .live (.add left' right')
      | _, _ => .dead
  | .inf left right =>
      match left.pruneOccurrences, right.pruneOccurrences with
      | .dead, .dead => .dead
      | .dead, .live right' => .live right'
      | .live left', .dead => .live left'
      | .live left', .live right' => .live (.inf left' right')

/-- The one-pass pruner returns `dead` exactly when every assignment hits a
marked occurrence. -/
theorem pruneOccurrences_eq_dead_iff (tree : OccurrenceTree ι) :
    tree.pruneOccurrences = .dead ↔ tree.StructurallyDead := by
  induction tree with
  | leaf label marked => cases marked <;> simp [pruneOccurrences, StructurallyDead]
  | principal label body ih =>
      generalize hb : body.pruneOccurrences = bodyResult
      cases bodyResult <;> simp [pruneOccurrences, hb, StructurallyDead, ← ih]
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult <;> cases rightResult <;>
        simp [pruneOccurrences, hl, hr, StructurallyDead, ← ihLeft, ← ihRight]
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult <;> cases rightResult <;>
        simp [pruneOccurrences, hl, hr, StructurallyDead, ← ihLeft, ← ihRight]

/-- If no critical assignment hits a mark, occurrence pruning cannot erase
the root. -/
theorem exists_live_prune_of_noCriticalHits
    (tree : OccurrenceTree ι) (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ A : Assignment tree.erase,
      A.IsCritical φ y → ¬tree.Hits A) :
    ∃ output, tree.pruneOccurrences = .live output := by
  obtain ⟨A, hA⟩ := Assignment.exists_isCritical tree.erase φ y
  generalize hprune : tree.pruneOccurrences = result
  cases result with
  | dead =>
      exfalso
      have hdead : tree.StructurallyDead :=
        (pruneOccurrences_eq_dead_iff tree).mp hprune
      exact havoid A hA ((structurallyDead_iff_forall_hits tree).mp hdead A)
  | live output => exact ⟨output, rfl⟩

/-- Pruning marked occurrences can only increase functional evaluation. -/
theorem eval_le_of_pruneOccurrences_live
    (tree : OccurrenceTree ι) (output : EliminationTree ι)
    (hprune : tree.pruneOccurrences = .live output)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    tree.erase.eval φ y ≤ output.eval φ y := by
  induction tree generalizing output with
  | leaf label marked =>
      cases marked <;> simp [pruneOccurrences] at hprune
      subst output
      exact le_rfl
  | principal label body ih =>
      generalize hb : body.pruneOccurrences = bodyResult
      cases bodyResult with
      | dead => simp [pruneOccurrences, hb] at hprune
      | live body' =>
          simp [pruneOccurrences, hb] at hprune
          subst output
          simpa [erase, eval] using ih body' hb
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead => simp [pruneOccurrences, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact add_le_add (ihLeft left' hl) (ihRight right' hr)
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact (min_le_right _ _).trans (ihRight right' hr)
      | live left' =>
          cases rightResult with
          | dead =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact (min_le_left _ _).trans (ihLeft left' hl)
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact min_le_min (ihLeft left' hl) (ihRight right' hr)

/-- One-pass occurrence pruning is functionally exact when no critical
assignment of the original tree reaches a marked occurrence.  This packages
all deletions at once; no occurrence map has to be transported through a
sequence of intermediate trees. -/
theorem eval_pruneOccurrences
    (tree : OccurrenceTree ι) (output : EliminationTree ι)
    (hprune : tree.pruneOccurrences = .live output)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ A : Assignment tree.erase,
      A.IsCritical φ y → ¬tree.Hits A) :
    tree.erase.eval φ y = output.eval φ y := by
  induction tree generalizing output with
  | leaf label marked =>
      cases marked <;> simp [pruneOccurrences] at hprune
      subst output
      rfl
  | principal label body ih =>
      generalize hb : body.pruneOccurrences = bodyResult
      cases bodyResult with
      | dead => simp [pruneOccurrences, hb] at hprune
      | live body' =>
          simp [pruneOccurrences, hb] at hprune
          subst output
          have hbodyAvoid : ∀ A : Assignment body.erase,
              A.IsCritical φ y → ¬body.Hits A := by
            intro A hA hhit
            exact havoid (.principalNode A) hA hhit
          simpa [erase, eval] using ih body' hb hbodyAvoid
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead => simp [pruneOccurrences, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              obtain ⟨leftCritical, hleftCritical⟩ :=
                Assignment.exists_isCritical left.erase φ y
              obtain ⟨rightCritical, hrightCritical⟩ :=
                Assignment.exists_isCritical right.erase φ y
              have hleftAvoid : ∀ A : Assignment left.erase,
                  A.IsCritical φ y → ¬left.Hits A := by
                intro A hA hhit
                exact havoid (.add A rightCritical) ⟨hA, hrightCritical⟩
                  (Or.inl hhit)
              have hrightAvoid : ∀ A : Assignment right.erase,
                  A.IsCritical φ y → ¬right.Hits A := by
                intro A hA hhit
                exact havoid (.add leftCritical A) ⟨hleftCritical, hA⟩
                  (Or.inr hhit)
              exact congrArg₂ (· + ·)
                (ihLeft left' hl hleftAvoid) (ihRight right' hr hrightAvoid)
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              have hleftDead : left.StructurallyDead :=
                (pruneOccurrences_eq_dead_iff left).mp hl
              have hnotLeft : ¬left.erase.eval φ y ≤ right.erase.eval φ y := by
                intro hle
                obtain ⟨A, hA⟩ := Assignment.exists_isCritical left.erase φ y
                exact havoid (.infLeft A) ⟨hle, hA⟩
                  ((structurallyDead_iff_forall_hits left).mp hleftDead A)
              have hrightLe : right.erase.eval φ y ≤ left.erase.eval φ y :=
                le_of_not_ge hnotLeft
              have hrightAvoid : ∀ A : Assignment right.erase,
                  A.IsCritical φ y → ¬right.Hits A := by
                intro A hA hhit
                exact havoid (.infRight A) ⟨hrightLe, hA⟩ hhit
              have heq := ihRight right' hr hrightAvoid
              change min (left.erase.eval φ y) (right.erase.eval φ y) =
                right'.eval φ y
              rw [min_eq_right hrightLe, heq]
      | live left' =>
          cases rightResult with
          | dead =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              have hrightDead : right.StructurallyDead :=
                (pruneOccurrences_eq_dead_iff right).mp hr
              have hnotRight : ¬right.erase.eval φ y ≤ left.erase.eval φ y := by
                intro hle
                obtain ⟨A, hA⟩ := Assignment.exists_isCritical right.erase φ y
                exact havoid (.infRight A) ⟨hle, hA⟩
                  ((structurallyDead_iff_forall_hits right).mp hrightDead A)
              have hleftLe : left.erase.eval φ y ≤ right.erase.eval φ y :=
                le_of_not_ge hnotRight
              have hleftAvoid : ∀ A : Assignment left.erase,
                  A.IsCritical φ y → ¬left.Hits A := by
                intro A hA hhit
                exact havoid (.infLeft A) ⟨hleftLe, hA⟩ hhit
              have heq := ihLeft left' hl hleftAvoid
              change min (left.erase.eval φ y) (right.erase.eval φ y) =
                left'.eval φ y
              rw [min_eq_left hleftLe, heq]
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              by_cases hleftLe : left.erase.eval φ y ≤ right.erase.eval φ y
              · have hleftAvoid : ∀ A : Assignment left.erase,
                    A.IsCritical φ y → ¬left.Hits A := by
                  intro A hA hhit
                  exact havoid (.infLeft A) ⟨hleftLe, hA⟩ hhit
                have hleftEq := ihLeft left' hl hleftAvoid
                have hrightMono :=
                  eval_le_of_pruneOccurrences_live right right' hr φ y
                have hnewLe : left'.eval φ y ≤ right'.eval φ y := by
                  rw [← hleftEq]
                  exact hleftLe.trans hrightMono
                change min (left.erase.eval φ y) (right.erase.eval φ y) =
                  min (left'.eval φ y) (right'.eval φ y)
                rw [min_eq_left hleftLe, min_eq_left hnewLe, hleftEq]
              · have hrightLe : right.erase.eval φ y ≤ left.erase.eval φ y :=
                  le_of_not_ge hleftLe
                have hrightAvoid : ∀ A : Assignment right.erase,
                    A.IsCritical φ y → ¬right.Hits A := by
                  intro A hA hhit
                  exact havoid (.infRight A) ⟨hrightLe, hA⟩ hhit
                have hrightEq := ihRight right' hr hrightAvoid
                have hleftMono :=
                  eval_le_of_pruneOccurrences_live left left' hl φ y
                have hnewLe : right'.eval φ y ≤ left'.eval φ y := by
                  rw [← hrightEq]
                  exact hrightLe.trans hleftMono
                change min (left.erase.eval φ y) (right.erase.eval φ y) =
                  min (left'.eval φ y) (right'.eval φ y)
                rw [min_eq_right hrightLe, min_eq_right hnewLe, hrightEq]

/-- A semantic certificate for the marks: any assignment selecting one of
them contradicts its inherited principal bounds.  Phase A's occurrence
provenance must construct this predicate from repeated-label certificates. -/
def MarkingSound (tree : OccurrenceTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ A : Assignment tree.erase,
    A.RespectsPrincipalBounds φ y → tree.Hits A → False

/-- The complete one-pass Phase-B theorem at a fixed evaluation point.
Local validity supplies principal bounds for critical assignments; a sound
occurrence marking then proves root liveness and exact functional equality. -/
theorem pruneOccurrences_sound
    (tree : OccurrenceTree ι) (φ : ι → ℝ → ℝ) (y : ℝ)
    (hvalid : tree.erase.LocallyValid φ y)
    (hmarks : tree.MarkingSound φ y) :
    ∃ output, tree.pruneOccurrences = .live output ∧
      tree.erase.eval φ y = output.eval φ y := by
  have havoid : ∀ A : Assignment tree.erase,
      A.IsCritical φ y → ¬tree.Hits A := by
    intro A hcritical hhit
    exact hmarks A
      (A.respectsPrincipalBounds_of_locallyValid φ y hcritical hvalid) hhit
  obtain ⟨output, hprune⟩ :=
    exists_live_prune_of_noCriticalHits tree φ y havoid
  exact ⟨output, hprune, eval_pruneOccurrences tree output hprune φ y havoid⟩

/-- Any leaf property true before pruning remains true on every surviving
leaf. -/
theorem allLeaves_of_pruneOccurrences_live
    (tree : OccurrenceTree ι) (output : EliminationTree ι)
    (hprune : tree.pruneOccurrences = .live output)
    (P : PrincipalLabel ι → Prop)
    (hall : tree.erase.AllLeaves P) : output.AllLeaves P := by
  induction tree generalizing output with
  | leaf label marked =>
      cases marked <;> simp [pruneOccurrences] at hprune
      subst output
      exact hall
  | principal label body ih =>
      generalize hb : body.pruneOccurrences = bodyResult
      cases bodyResult with
      | dead => simp [pruneOccurrences, hb] at hprune
      | live body' =>
          simp [pruneOccurrences, hb] at hprune
          subst output
          exact ih body' hb hall
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead => simp [pruneOccurrences, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact ⟨ihLeft left' hl hall.1, ihRight right' hr hall.2⟩
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact ihRight right' hr hall.2
      | live left' =>
          cases rightResult with
          | dead =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact ihLeft left' hl hall.1
          | live right' =>
              simp [pruneOccurrences, hl, hr] at hprune
              subst output
              exact ⟨ihLeft left' hl hall.1, ihRight right' hr hall.2⟩

end OccurrenceTree

end EliminationTree

namespace ConcreteElimination

open EliminationTree
open EliminationTree.OccurrenceTree

variable {ι : Type}

/-- Occurrence-specific pruning has the same favorable LP orientation as the
label-predicate prototype: erased coefficient evaluation can only increase. -/
theorem coeffEval_le_of_pruneOccurrences_live
    (tree : OccurrenceTree ι) (output : EliminationTree ι)
    (hprune : tree.pruneOccurrences = .live output)
    (c : ι → ℝ) (lam : ℝ) :
    (eraseToRetarded tree.erase).coeffEval c lam ≤
      (eraseToRetarded output).coeffEval c lam := by
  induction tree generalizing output with
  | leaf label marked =>
      cases marked <;> simp [OccurrenceTree.pruneOccurrences] at hprune
      subst output
      exact le_rfl
  | principal label body ih =>
      generalize hb : body.pruneOccurrences = bodyResult
      cases bodyResult with
      | dead => simp [OccurrenceTree.pruneOccurrences, hb] at hprune
      | live body' =>
          simp [OccurrenceTree.pruneOccurrences, hb] at hprune
          subst output
          simpa [OccurrenceTree.erase, eraseToRetarded] using ih body' hb
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead => simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
              subst output
              simp only [OccurrenceTree.erase, eraseToRetarded,
                RetardedExpr.coeffEval]
              exact add_le_add (ihLeft left' hl) (ihRight right' hr)
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneOccurrences = leftResult
      generalize hr : right.pruneOccurrences = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
          | live right' =>
              simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
              subst output
              simp only [OccurrenceTree.erase, eraseToRetarded,
                RetardedExpr.coeffEval]
              exact (min_le_right _ _).trans (ihRight right' hr)
      | live left' =>
          cases rightResult with
          | dead =>
              simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
              subst output
              simp only [OccurrenceTree.erase, eraseToRetarded,
                RetardedExpr.coeffEval]
              exact (min_le_left _ _).trans (ihLeft left' hl)
          | live right' =>
              simp [OccurrenceTree.pruneOccurrences, hl, hr] at hprune
              subst output
              simp only [OccurrenceTree.erase, eraseToRetarded,
                RetardedExpr.coeffEval]
              exact min_le_min (ihLeft left' hl) (ihRight right' hr)

end ConcreteElimination

end CleanLean.KL
