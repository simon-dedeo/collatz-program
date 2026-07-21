/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteElimination

/-!
# Structural pruning of marked dead occurrences

Phase A of the proposed repair marks repeated branch leaves but performs no
deletions.  This file formalizes the syntax of Phase B.  A subtree is
structurally dead when every assignment through it hits a marked leaf:

* a marked leaf is dead;
* a principal node is dead when its body is dead;
* a sum is dead when either child is dead, since assignments select both;
* a minimum is dead only when both children are dead.

The pruner propagates deadness upward and removes a dead minimum alternative
when its sibling remains live.  Its surviving output has no marked leaves,
and erased coefficient evaluation can only increase.  The separate semantic
obligation is to prove that a critical assignment hitting a concrete marked
repeat is impossible under the Phase-A principal bounds.
-/

namespace CleanLean.KL

namespace EliminationTree

variable {ι : Type}

namespace Assignment

/-- A selected assignment reaches at least one leaf satisfying `marked`. -/
def Hits (marked : PrincipalLabel ι → Prop) :
    {tree : EliminationTree ι} → Assignment tree → Prop
  | .leaf _, .principalLeaf label => marked label
  | .principal _ _, .principalNode child => child.Hits marked
  | .add _ _, .add left right => left.Hits marked ∨ right.Hits marked
  | .inf _ _, .infLeft left => left.Hits marked
  | .inf _ _, .infRight right => right.Hits marked

end Assignment

/-- Syntactic deadness induced by marked leaves. -/
def StructurallyDead (marked : PrincipalLabel ι → Prop) :
    EliminationTree ι → Prop
  | .leaf label => marked label
  | .principal _ body => body.StructurallyDead marked
  | .add left right => left.StructurallyDead marked ∨ right.StructurallyDead marked
  | .inf left right => left.StructurallyDead marked ∧ right.StructurallyDead marked

/-- Structural deadness has its intended assignment semantics. -/
theorem structurallyDead_iff_forall_hits
    (marked : PrincipalLabel ι → Prop) (tree : EliminationTree ι) :
    tree.StructurallyDead marked ↔ ∀ A : Assignment tree, A.Hits marked := by
  induction tree with
  | leaf label =>
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
        by_cases hleft : left.StructurallyDead marked
        · exact Or.inl hleft
        by_cases hright : right.StructurallyDead marked
        · exact Or.inr hright
        exfalso
        have hnleft : ¬∀ A : Assignment left, A.Hits marked :=
          fun hall => hleft (ihLeft.mpr hall)
        have hnright : ¬∀ A : Assignment right, A.Hits marked :=
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

/-- Result of structurally pruning marked leaves. -/
inductive PruneResult (ι : Type) where
  | dead
  | live (tree : EliminationTree ι)

/-- Propagate marked deadness and delete a dead child only at a minimum. -/
def pruneMarked (marked : PrincipalLabel ι → Bool) :
    EliminationTree ι → PruneResult ι
  | .leaf label => if marked label then .dead else .live (.leaf label)
  | .principal label body =>
      match body.pruneMarked marked with
      | .dead => .dead
      | .live body' => .live (.principal label body')
  | .add left right =>
      match left.pruneMarked marked, right.pruneMarked marked with
      | .live left', .live right' => .live (.add left' right')
      | _, _ => .dead
  | .inf left right =>
      match left.pruneMarked marked, right.pruneMarked marked with
      | .dead, .dead => .dead
      | .dead, .live right' => .live right'
      | .live left', .dead => .live left'
      | .live left', .live right' => .live (.inf left' right')

/-- The executable pruner reports `dead` exactly for the structural predicate. -/
theorem pruneMarked_eq_dead_iff (marked : PrincipalLabel ι → Bool)
    (tree : EliminationTree ι) :
    tree.pruneMarked marked = .dead ↔
      tree.StructurallyDead (fun label => marked label = true) := by
  induction tree with
  | leaf label => simp [pruneMarked, StructurallyDead]
  | principal label body ih =>
      generalize hb : body.pruneMarked marked = bodyResult
      cases bodyResult <;> simp [pruneMarked, hb, StructurallyDead, ← ih]
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult <;> cases rightResult <;>
        simp [pruneMarked, hl, hr, StructurallyDead, ← ihLeft, ← ihRight]
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult <;> cases rightResult <;>
        simp [pruneMarked, hl, hr, StructurallyDead, ← ihLeft, ← ihRight]

/-- One assignment avoiding all marks is enough to ensure that structural
pruning leaves a live root.  The semantic Phase-B proof will obtain such an
assignment from criticality, global principal bounds, and the repeated-label
contradiction. -/
theorem exists_live_prune_of_assignment_not_hits
    (marked : PrincipalLabel ι → Bool) (tree : EliminationTree ι)
    (A : Assignment tree)
    (hA : ¬A.Hits (fun label => marked label = true)) :
    ∃ output, tree.pruneMarked marked = .live output := by
  generalize hprune : tree.pruneMarked marked = result
  cases result with
  | dead =>
      exfalso
      have hdead : tree.StructurallyDead (fun label => marked label = true) :=
        (pruneMarked_eq_dead_iff marked tree).mp hprune
      exact hA ((structurallyDead_iff_forall_hits _ _).mp hdead A)
  | live output => exact ⟨output, rfl⟩

/-- Every leaf in a live pruned result is unmarked. -/
theorem allLeaves_unmarked_of_pruneMarked_live
    (marked : PrincipalLabel ι → Bool) (tree output : EliminationTree ι)
    (hprune : tree.pruneMarked marked = .live output) :
    output.AllLeaves (fun label => marked label = false) := by
  induction tree generalizing output with
  | leaf label =>
      by_cases hm : marked label = true
      · simp [pruneMarked, hm] at hprune
      · have hmfalse : marked label = false := Bool.eq_false_of_not_eq_true hm
        simp [pruneMarked, hmfalse] at hprune
        subst output
        exact hmfalse
  | principal label body ih =>
      generalize hb : body.pruneMarked marked = bodyResult
      cases bodyResult with
      | dead => simp [pruneMarked, hb] at hprune
      | live body' =>
          simp [pruneMarked, hb] at hprune
          subst output
          exact ih body' hb
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult with
      | dead => simp [pruneMarked, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [pruneMarked, hl, hr] at hprune
          | live right' =>
              simp [pruneMarked, hl, hr] at hprune
              subst output
              exact ⟨ihLeft left' hl, ihRight right' hr⟩
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [pruneMarked, hl, hr] at hprune
          | live right' =>
              simp [pruneMarked, hl, hr] at hprune
              subst output
              exact ihRight right' hr
      | live left' =>
          cases rightResult with
          | dead =>
              simp [pruneMarked, hl, hr] at hprune
              subst output
              exact ihLeft left' hl
          | live right' =>
              simp [pruneMarked, hl, hr] at hprune
              subst output
              exact ⟨ihLeft left' hl, ihRight right' hr⟩

end EliminationTree

namespace ConcreteElimination

open EliminationTree

variable {ι : Type}

/-- Structural pruning only deletes alternatives of minima, so erased
coefficient evaluation weakly increases whenever a live result remains. -/
theorem coeffEval_le_of_pruneMarked_live
    (marked : PrincipalLabel ι → Bool) (tree output : EliminationTree ι)
    (hprune : tree.pruneMarked marked = .live output)
    (c : ι → ℝ) (lam : ℝ) :
    (eraseToRetarded tree).coeffEval c lam ≤
      (eraseToRetarded output).coeffEval c lam := by
  induction tree generalizing output with
  | leaf label =>
      by_cases hm : marked label = true
      · simp [EliminationTree.pruneMarked, hm] at hprune
      · have hmfalse : marked label = false := Bool.eq_false_of_not_eq_true hm
        simp [EliminationTree.pruneMarked, hmfalse] at hprune
        subst output
        exact le_rfl
  | principal label body ih =>
      generalize hb : body.pruneMarked marked = bodyResult
      cases bodyResult with
      | dead => simp [EliminationTree.pruneMarked, hb] at hprune
      | live body' =>
          simp [EliminationTree.pruneMarked, hb] at hprune
          subst output
          simpa [eraseToRetarded] using ih body' hb
  | add left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult with
      | dead => simp [EliminationTree.pruneMarked, hl, hr] at hprune
      | live left' =>
          cases rightResult with
          | dead => simp [EliminationTree.pruneMarked, hl, hr] at hprune
          | live right' =>
              simp [EliminationTree.pruneMarked, hl, hr] at hprune
              subst output
              simp only [eraseToRetarded, RetardedExpr.coeffEval]
              exact add_le_add (ihLeft left' hl) (ihRight right' hr)
  | inf left right ihLeft ihRight =>
      generalize hl : left.pruneMarked marked = leftResult
      generalize hr : right.pruneMarked marked = rightResult
      cases leftResult with
      | dead =>
          cases rightResult with
          | dead => simp [EliminationTree.pruneMarked, hl, hr] at hprune
          | live right' =>
              simp [EliminationTree.pruneMarked, hl, hr] at hprune
              subst output
              simp only [eraseToRetarded, RetardedExpr.coeffEval]
              exact (min_le_right _ _).trans (ihRight right' hr)
      | live left' =>
          cases rightResult with
          | dead =>
              simp [EliminationTree.pruneMarked, hl, hr] at hprune
              subst output
              simp only [eraseToRetarded, RetardedExpr.coeffEval]
              exact (min_le_left _ _).trans (ihLeft left' hl)
          | live right' =>
              simp [EliminationTree.pruneMarked, hl, hr] at hprune
              subst output
              simp only [eraseToRetarded, RetardedExpr.coeffEval]
              exact min_le_min (ihLeft left' hl) (ihRight right' hr)

end ConcreteElimination

end CleanLean.KL
