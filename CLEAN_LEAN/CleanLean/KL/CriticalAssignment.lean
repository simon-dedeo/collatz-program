/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.TreeRewrite

/-!
# Critical assignments in finite sum/min trees

Krasikov--Lagarias call a set of leaves a *critical assignment* when it keeps
both children of every sum and chooses a child attaining the minimum at every
minimum node.  This file gives that notion exact dependent-type semantics.

This is deliberately only the local, algebraic part of KL Theorem 3.2.  The
global deletion theorem additionally tracks paths through labelled principal
vertices and proves that every deleted new leaf is absent from every critical
assignment.  That path argument is not assumed here.
-/

namespace CleanLean.KL

namespace RetardedExpr

variable {ι : Type}

/-- A syntactic assignment keeps the unique leaf, keeps both assignments at
an addition, and chooses exactly one branch at a minimum. -/
inductive Assignment : (e : RetardedExpr ι) → Type
  | leaf (state : ι) (lag : ℝ) : Assignment (.leaf state lag)
  | add {left right : RetardedExpr ι} :
      Assignment left → Assignment right → Assignment (.add left right)
  | infLeft {left right : RetardedExpr ι} :
      Assignment left → Assignment (.inf left right)
  | infRight {left right : RetardedExpr ι} :
      Assignment right → Assignment (.inf left right)

namespace Assignment

/-- Sum the values of the leaves retained by an assignment. -/
def selectedEval {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  match A with
  | .leaf state lag => φ state (y - lag)
  | .add left right => left.selectedEval φ y + right.selectedEval φ y
  | .infLeft left => left.selectedEval φ y
  | .infRight right => right.selectedEval φ y

/-- The labelled leaves retained by an assignment, with multiplicity and in
left-to-right order. -/
def selectedLeaves {e : RetardedExpr ι} (A : Assignment e) : List (ι × ℝ) :=
  match A with
  | .leaf state lag => [(state, lag)]
  | .add left right => left.selectedLeaves ++ right.selectedLeaves
  | .infLeft left => left.selectedLeaves
  | .infRight right => right.selectedLeaves

/-- `selectedEval` really is the sum over the selected leaves. -/
theorem selectedEval_eq_sum {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    A.selectedEval φ y =
      (A.selectedLeaves.map fun p => φ p.1 (y - p.2)).sum := by
  induction A with
  | leaf state lag => simp [selectedEval, selectedLeaves]
  | add left right ihLeft ihRight =>
      simp [selectedEval, selectedLeaves, ihLeft, ihRight]
  | infLeft left ih => simpa [selectedEval, selectedLeaves] using ih
  | infRight right ih => simpa [selectedEval, selectedLeaves] using ih

/-- Every assignment retains at least one leaf. -/
theorem selectedLeaves_ne_nil {e : RetardedExpr ι} (A : Assignment e) :
    A.selectedLeaves ≠ [] := by
  induction A with
  | leaf state lag => simp [selectedLeaves]
  | add left right ihLeft ihRight => simp [selectedLeaves, ihLeft]
  | infLeft left ih => simpa [selectedLeaves] using ih
  | infRight right ih => simpa [selectedLeaves] using ih

/-- Strict positivity of all functions makes every selected leaf sum strictly
positive.  This is the positivity input used for the strict inequality in
KL equation (3.6). -/
theorem selectedEval_pos {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y : ℝ) (hφ : ∀ i t, 0 < φ i t) :
    0 < A.selectedEval φ y := by
  induction A with
  | leaf state lag => exact hφ state (y - lag)
  | add left right ihLeft ihRight =>
      exact add_pos ihLeft ihRight
  | infLeft left ih => exact ih
  | infRight right ih => exact ih

/-- The assignment is critical at `(φ,y)` when every chosen minimum branch
really attains the minimum.  Ties permit assignments choosing either side. -/
def IsCritical {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  match A with
  | .leaf _ _ => True
  | @add _ left right a b => a.IsCritical φ y ∧ b.IsCritical φ y
  | @infLeft _ left right a => left.eval φ y ≤ right.eval φ y ∧ a.IsCritical φ y
  | @infRight _ left right b => right.eval φ y ≤ left.eval φ y ∧ b.IsCritical φ y

/-- Every finite sum/min tree has a critical assignment at every evaluation
point. -/
theorem exists_isCritical (e : RetardedExpr ι) (φ : ι → ℝ → ℝ) (y : ℝ) :
    ∃ A : Assignment e, A.IsCritical φ y := by
  induction e with
  | leaf state lag =>
      exact ⟨.leaf state lag, trivial⟩
  | add left right ihLeft ihRight =>
      obtain ⟨a, ha⟩ := ihLeft
      obtain ⟨b, hb⟩ := ihRight
      exact ⟨.add a b, ha, hb⟩
  | inf left right ihLeft ihRight =>
      rcases le_total (left.eval φ y) (right.eval φ y) with h | h
      · obtain ⟨a, ha⟩ := ihLeft
        exact ⟨.infLeft a, h, ha⟩
      · obtain ⟨b, hb⟩ := ihRight
        exact ⟨.infRight b, h, hb⟩

/-- A critical assignment represents the value of the whole expression as
the sum of its selected leaf values.  This is the precise algebraic statement
behind KL's sentence preceding equation (3.4). -/
theorem selectedEval_eq_eval {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y : ℝ) (hA : A.IsCritical φ y) :
    A.selectedEval φ y = e.eval φ y := by
  induction A with
  | leaf state lag => rfl
  | add left right ihLeft ihRight =>
      exact congrArg₂ (· + ·) (ihLeft hA.1) (ihRight hA.2)
  | @infLeft left right a ih =>
      rw [selectedEval, eval, ih hA.2, min_eq_left hA.1]
  | @infRight left right b ih =>
      rw [selectedEval, eval, ih hA.2, min_eq_right hA.1]

/-- Consequently a root inequality bounds the sum of the leaves in every
critical assignment, not merely in one chosen assignment. -/
theorem selectedEval_le_of_critical {e : RetardedExpr ι} (A : Assignment e)
    (φ : ι → ℝ → ℝ) (y bound : ℝ) (hA : A.IsCritical φ y)
    (he : e.eval φ y ≤ bound) :
    A.selectedEval φ y ≤ bound := by
  rw [selectedEval_eq_eval A φ y hA]
  exact he

/-- At a minimum node, an assignment choosing the left branch is critical
exactly when the left value is no larger and its internal choices are
critical. -/
@[simp] theorem isCritical_infLeft {left right : RetardedExpr ι}
    (A : Assignment left) (φ : ι → ℝ → ℝ) (y : ℝ) :
    (Assignment.infLeft (right := right) A).IsCritical φ y ↔
      left.eval φ y ≤ right.eval φ y ∧ A.IsCritical φ y :=
  Iff.rfl

/-- The analogous characterization for choosing the right branch. -/
@[simp] theorem isCritical_infRight {left right : RetardedExpr ι}
    (A : Assignment right) (φ : ι → ℝ → ℝ) (y : ℝ) :
    (Assignment.infRight (left := left) A).IsCritical φ y ↔
      right.eval φ y ≤ left.eval φ y ∧ A.IsCritical φ y :=
  Iff.rfl

/-- If no critical assignment of a binary minimum can choose its left side,
then deleting that side is semantically sound at this fixed evaluation point.
The global KL proof must establish this hypothesis uniformly for the specific
path-labelled leaf it deletes. -/
theorem eval_inf_eq_right_of_no_critical_left
    (left right : RetardedExpr ι) (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ A : Assignment left,
      ¬(Assignment.infLeft (right := right) A).IsCritical φ y) :
    (RetardedExpr.inf left right).eval φ y = right.eval φ y := by
  have hnot : ¬left.eval φ y ≤ right.eval φ y := by
    intro hle
    obtain ⟨A, hA⟩ := exists_isCritical left φ y
    exact havoid A ⟨hle, hA⟩
  simp only [eval]
  exact min_eq_right (le_of_not_ge hnot)

/-- Symmetric safe-deletion lemma for the right side of a minimum. -/
theorem eval_inf_eq_left_of_no_critical_right
    (left right : RetardedExpr ι) (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ A : Assignment right,
      ¬(Assignment.infRight (left := left) A).IsCritical φ y) :
    (RetardedExpr.inf left right).eval φ y = left.eval φ y := by
  have hnot : ¬right.eval φ y ≤ left.eval φ y := by
    intro hle
    obtain ⟨A, hA⟩ := exists_isCritical right φ y
    exact havoid A ⟨hle, hA⟩
  simp only [eval]
  exact min_eq_left (le_of_not_ge hnot)

/-- Replacing equal-valued expressions inside a one-hole context preserves
the value of the whole tree. -/
theorem context_eval_fill_congr (K : Context ι) (a b : RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) (h : a.eval φ y = b.eval φ y) :
    (K.fill a).eval φ y = (K.fill b).eval φ y := by
  apply le_antisymm
  · exact K.eval_fill_mono a b φ y h.le
  · exact K.eval_fill_mono b a φ y h.ge

/-- Once the global path argument proves that no critical assignment uses a
minimum alternative, that alternative may be deleted inside any surrounding
sum/min context without changing the functional right-hand side. -/
theorem eval_delete_left_of_no_critical
    (K : Context ι) (left right : RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ A : Assignment left,
      ¬(Assignment.infLeft (right := right) A).IsCritical φ y) :
    (K.fill (.inf left right)).eval φ y = (K.fill right).eval φ y := by
  apply context_eval_fill_congr
  exact eval_inf_eq_right_of_no_critical_left left right φ y havoid

/-- Therefore a root difference inequality survives such a globally
justified deletion. -/
theorem root_inequality_of_delete_left
    (K : Context ι) (left right : RetardedExpr ι) (root : ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hroot : (K.fill (.inf left right)).eval φ y ≤ φ root y)
    (havoid : ∀ A : Assignment left,
      ¬(Assignment.infLeft (right := right) A).IsCritical φ y) :
    (K.fill right).eval φ y ≤ φ root y := by
  rw [eval_delete_left_of_no_critical K left right φ y havoid] at hroot
  exact hroot

/-- On the coefficient side, deletion needs no analytic path argument:
discarding the left alternative increases a minimum, hence only weakens the
feasibility inequality. -/
theorem coeffEval_delete_left_le
    (K : Context ι) (left right : RetardedExpr ι)
    (c : ι → ℝ) (lam : ℝ) :
    (K.fill (.inf left right)).coeffEval c lam ≤
      (K.fill right).coeffEval c lam := by
  apply K.coeffEval_fill_mono
  simp only [coeffEval]
  exact min_le_right _ _

/-- A coefficient lower bound at the root is consequently preserved by
deleting a minimum alternative. -/
theorem root_coeff_le_of_delete_left
    (K : Context ι) (left right : RetardedExpr ι)
    (c : ι → ℝ) (lam rootCoeff : ℝ)
    (hroot : rootCoeff ≤ (K.fill (.inf left right)).coeffEval c lam) :
    rootCoeff ≤ (K.fill right).coeffEval c lam :=
  hroot.trans (coeffEval_delete_left_le K left right c lam)

end Assignment

end RetardedExpr

end CleanLean.KL
