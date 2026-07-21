/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.RetardedComparison

/-!
# Sound substitution in KL sum/min trees

This file formalizes the first half of an advanced-term elimination step.
Substituting a valid difference inequality for one leaf can only decrease the
functional right-hand side.  In the associated exponential coefficient
system the orientation reverses: feasibility of the local rule makes the
substituted coefficient expression larger.

The deletion rule, which can remove alternatives from a minimum and therefore
increase the functional right-hand side, is deliberately not hidden here; its
soundness is the genuinely harder part of KL Theorem 3.2.
-/

namespace CleanLean.KL

namespace RetardedExpr

variable {ι : Type}

/-- Add a common backward lag to every leaf. -/
def shiftLags (δ : ℝ) : RetardedExpr ι → RetardedExpr ι
  | .leaf i lag => .leaf i (δ + lag)
  | .add a b => .add (a.shiftLags δ) (b.shiftLags δ)
  | .inf a b => .inf (a.shiftLags δ) (b.shiftLags δ)

@[simp] theorem eval_shiftLags (e : RetardedExpr ι)
    (δ y : ℝ) (φ : ι → ℝ → ℝ) :
    (e.shiftLags δ).eval φ y = e.eval φ (y - δ) := by
  induction e with
  | leaf i lag =>
      simp only [shiftLags, eval]
      congr 1
      ring
  | add a b iha ihb => simp [shiftLags, eval, iha, ihb]
  | inf a b iha ihb => simp [shiftLags, eval, iha, ihb]

/-- A one-hole context for a nested sum/min expression. -/
inductive Context (ι : Type) where
  | hole
  | addLeft (ctx : Context ι) (right : RetardedExpr ι)
  | addRight (left : RetardedExpr ι) (ctx : Context ι)
  | infLeft (ctx : Context ι) (right : RetardedExpr ι)
  | infRight (left : RetardedExpr ι) (ctx : Context ι)

namespace Context

/-- Fill the unique hole of a context. -/
def fill (K : Context ι) (e : RetardedExpr ι) : RetardedExpr ι :=
  match K with
  | .hole => e
  | .addLeft K b => .add (K.fill e) b
  | .addRight a K => .add a (K.fill e)
  | .infLeft K b => .inf (K.fill e) b
  | .infRight a K => .inf a (K.fill e)

/-- Evaluation is monotone in the expression filling the hole. -/
theorem eval_fill_mono (K : Context ι) (a b : RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) (h : a.eval φ y ≤ b.eval φ y) :
    (K.fill a).eval φ y ≤ (K.fill b).eval φ y := by
  induction K with
  | hole => exact h
  | addLeft K right ih =>
      simpa [fill, eval] using add_le_add_right ih (right.eval φ y)
  | addRight left K ih =>
      simpa [fill, eval] using add_le_add_left ih (left.eval φ y)
  | infLeft K right ih =>
      simpa [fill, eval] using min_le_min ih (le_refl (right.eval φ y))
  | infRight left K ih =>
      simpa [fill, eval] using min_le_min (le_refl (left.eval φ y)) ih

/-- Coefficient evaluation is likewise monotone in the hole. -/
theorem coeffEval_fill_mono (K : Context ι) (a b : RetardedExpr ι)
    (c : ι → ℝ) (lam : ℝ) (h : a.coeffEval c lam ≤ b.coeffEval c lam) :
    (K.fill a).coeffEval c lam ≤ (K.fill b).coeffEval c lam := by
  induction K with
  | hole => exact h
  | addLeft K right ih =>
      simpa [fill, coeffEval] using
        add_le_add_right ih (right.coeffEval c lam)
  | addRight left K ih =>
      simpa [fill, coeffEval] using
        add_le_add_left ih (left.coeffEval c lam)
  | infLeft K right ih =>
      simpa [fill, coeffEval] using
        min_le_min ih (le_refl (right.coeffEval c lam))
  | infRight left K ih =>
      simpa [fill, coeffEval] using
        min_le_min (le_refl (left.coeffEval c lam)) ih

end Context

/-- A valid difference rule remains valid after it is substituted for a leaf
inside any sum/min context. -/
theorem eval_split_le_original
    (K : Context ι) (rule : RetardedExpr ι) (state : ι)
    (lag y : ℝ) (φ : ι → ℝ → ℝ)
    (hrule : rule.eval φ (y - lag) ≤ φ state (y - lag)) :
    (K.fill (rule.shiftLags lag)).eval φ y ≤
      (K.fill (.leaf state lag)).eval φ y := by
  apply K.eval_fill_mono
  simpa [eval] using hrule

/-- Hence a root inequality survives the splitting substep. -/
theorem root_inequality_of_split
    (K : Context ι) (rule : RetardedExpr ι) (root state : ι)
    (lag y : ℝ) (φ : ι → ℝ → ℝ)
    (hroot : (K.fill (.leaf state lag)).eval φ y ≤ φ root y)
    (hrule : rule.eval φ (y - lag) ≤ φ state (y - lag)) :
    (K.fill (rule.shiftLags lag)).eval φ y ≤ φ root y :=
  (eval_split_le_original K rule state lag y φ hrule).trans hroot

/-- Shifting every leaf multiplies the exponential coefficient expression by
the common factor `lambda^(-delta)`. -/
theorem coeffEval_shiftLags (e : RetardedExpr ι)
    (c : ι → ℝ) {lam : ℝ} (hlam : 0 < lam) (δ : ℝ) :
    (e.shiftLags δ).coeffEval c lam =
      lam ^ (-δ) * e.coeffEval c lam := by
  induction e with
  | leaf i lag =>
      simp only [shiftLags, coeffEval]
      rw [show -(δ + lag) = -δ + -lag by ring, Real.rpow_add hlam]
      ring
  | add a b iha ihb =>
      simp only [shiftLags, coeffEval, iha, ihb]
      ring
  | inf a b iha ihb =>
      simp only [shiftLags, coeffEval, iha, ihb]
      rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hlam.le _)]

/-- The LP orientation is opposite to the functional one: local coefficient
feasibility makes a split expression dominate the old leaf coefficient. -/
theorem original_coeff_le_split
    (K : Context ι) (rule : RetardedExpr ι) (state : ι)
    (lag : ℝ) (c : ι → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hrule : c state ≤ rule.coeffEval c lam) :
    (K.fill (.leaf state lag)).coeffEval c lam ≤
      (K.fill (rule.shiftLags lag)).coeffEval c lam := by
  apply K.coeffEval_fill_mono
  rw [coeffEval, coeffEval_shiftLags rule c hlam lag]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hrule (Real.rpow_nonneg hlam.le (-lag))

/-- Positivity and time-monotonicity alone do not justify deleting an
alternative from a minimum.  KL's global critical-assignment/path argument is
essential: a purely local pruning lemma would be false. -/
theorem local_min_deletion_not_sound :
    let φ : Bool → ℝ → ℝ := fun i _ => if i then 2 else 1
    (∀ i y, 0 < φ i y) ∧
      (∀ i, Monotone (φ i)) ∧
      (RetardedExpr.inf (.leaf true 0) (.leaf false 0)).eval φ 0 ≤ φ false 0 ∧
      ¬(.leaf true 0 : RetardedExpr Bool).eval φ 0 ≤ φ false 0 := by
  dsimp only
  constructor
  · intro i y
    cases i <;> norm_num
  constructor
  · intro i x y hxy
    cases i <;> norm_num
  constructor <;> norm_num [eval]

end RetardedExpr

end CleanLean.KL
