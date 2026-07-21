/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Abstract finite Krasikov--Lagarias systems

The analytic coefficients and the concrete residue arithmetic are deliberately
separated.  This file contains only the finite combinatorial shape of the KL
operator and elementary order lemmas about its three-point fiber minimum.
-/

namespace CleanLean.KL

/-- The three residue-class behaviours in a reduced KL system. -/
inductive Branch where
  | retarded
  | neutral
  | advanced
  deriving DecidableEq, Repr

/-- Abstract data needed to write the reduced finite KL operator.  Concrete
systems on residues modulo `3 ^ k` will instantiate this structure later. -/
structure FiniteSystem where
  State : Type
  Coarse : Type
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  [coarseFintype : Fintype Coarse]
  [coarseDecidableEq : DecidableEq Coarse]
  transport : State ≃ State
  branch : State → Branch
  refinementTarget : State → Coarse
  fiber : Coarse → Fin 3 → State

attribute [instance] FiniteSystem.stateFintype FiniteSystem.stateDecidableEq
  FiniteSystem.coarseFintype FiniteSystem.coarseDecidableEq

/-- Positive coefficients of the transport, retarded, and advanced terms. -/
structure Weights (R : Type) where
  transport : R
  retarded : R
  advanced : R

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- Minimum of a function over a three-point refinement fiber. -/
def fiberMin {R : Type} [LinearOrder R] (c : S.State → R) (r : S.Coarse) : R :=
  min (c (S.fiber r 0)) (min (c (S.fiber r 1)) (c (S.fiber r 2)))

theorem fiberMin_le (c : S.State → ℝ) (r : S.Coarse) (j : Fin 3) :
    S.fiberMin c r ≤ c (S.fiber r j) := by
  fin_cases j <;> simp [fiberMin]

/-- The fiber minimum is at most the fiber average.  The factor `1/3` in the
annealed ball-mass automaton comes from exactly this finite inequality. -/
theorem three_mul_fiberMin_le_sum (c : S.State → ℝ) (r : S.Coarse) :
    3 * S.fiberMin c r ≤
      c (S.fiber r 0) + c (S.fiber r 1) + c (S.fiber r 2) := by
  have h0 := S.fiberMin_le c r 0
  have h1 := S.fiberMin_le c r 1
  have h2 := S.fiberMin_le c r 2
  linarith

theorem fiberMin_le_average (c : S.State → ℝ) (r : S.Coarse) :
    S.fiberMin c r ≤
      (c (S.fiber r 0) + c (S.fiber r 1) + c (S.fiber r 2)) / 3 := by
  linarith [S.three_mul_fiberMin_le_sum c r]

theorem fiberMin_mono {R : Type} [LinearOrder R] {c d : S.State → R}
    (h : ∀ m, c m ≤ d m) (r : S.Coarse) :
    S.fiberMin c r ≤ S.fiberMin d r := by
  simp only [fiberMin]
  exact min_le_min (h _) (min_le_min (h _) (h _))

theorem fiberMin_nonneg
    (c : S.State → ℝ) (hc : ∀ m, 0 ≤ c m) (r : S.Coarse) :
    0 ≤ S.fiberMin c r := by
  simp [fiberMin, hc]

/-- The reduced KL operator with abstract coefficients. -/
def operator (w : Weights ℝ) (c : S.State → ℝ) (m : S.State) : ℝ :=
  w.transport * c (S.transport m) +
    match S.branch m with
    | Branch.retarded => w.retarded * S.fiberMin c (S.refinementTarget m)
    | Branch.neutral => 0
    | Branch.advanced => w.advanced * S.fiberMin c (S.refinementTarget m)

/-- Arithmetic mean over a three-point refinement fiber. -/
def fiberAverage (c : S.State → ℝ) (r : S.Coarse) : ℝ :=
  (c (S.fiber r 0) + c (S.fiber r 1) + c (S.fiber r 2)) / 3

/-- The annealed finite KL operator, obtained from the adversarial operator by
replacing every three-fiber minimum with its arithmetic mean. -/
def annealedOperator (w : Weights ℝ) (c : S.State → ℝ) (m : S.State) : ℝ :=
  w.transport * c (S.transport m) +
    match S.branch m with
    | Branch.retarded => w.retarded * S.fiberAverage c (S.refinementTarget m)
    | Branch.neutral => 0
    | Branch.advanced => w.advanced * S.fiberAverage c (S.refinementTarget m)

theorem fiberAverage_add (c d : S.State → ℝ) (r : S.Coarse) :
    S.fiberAverage (c + d) r = S.fiberAverage c r + S.fiberAverage d r := by
  simp only [fiberAverage, Pi.add_apply]
  ring

theorem fiberAverage_smul (a : ℝ) (c : S.State → ℝ) (r : S.Coarse) :
    S.fiberAverage (a • c) r = a * S.fiberAverage c r := by
  simp only [fiberAverage, Pi.smul_apply, smul_eq_mul]
  ring

theorem annealedOperator_add (w : Weights ℝ) (c d : S.State → ℝ) :
    S.annealedOperator w (c + d) =
      S.annealedOperator w c + S.annealedOperator w d := by
  funext m
  cases hbranch : S.branch m <;>
    simp [annealedOperator, hbranch, S.fiberAverage_add]
  all_goals ring

theorem annealedOperator_smul (w : Weights ℝ) (a : ℝ)
    (c : S.State → ℝ) :
    S.annealedOperator w (a • c) = a • S.annealedOperator w c := by
  funext m
  cases hbranch : S.branch m <;>
    simp [annealedOperator, hbranch, S.fiberAverage_smul]
  all_goals ring

/-- The annealed operator as an honest real-linear endomorphism of the finite
state function space. -/
def annealedLinearMap (w : Weights ℝ) :
    (S.State → ℝ) →ₗ[ℝ] (S.State → ℝ) where
  toFun := S.annealedOperator w
  map_add' := S.annealedOperator_add w
  map_smul' := S.annealedOperator_smul w

/-- The adversarial operator is pointwise bounded above by its annealed
linearization when the two branch weights are nonnegative. -/
theorem operator_le_annealedOperator
    (w : Weights ℝ) (c : S.State → ℝ)
    (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced) (m : S.State) :
    S.operator w c m ≤ S.annealedOperator w c m := by
  cases hbranch : S.branch m with
  | retarded =>
      simp only [operator, annealedOperator, hbranch]
      apply add_le_add (le_refl _)
      simpa [fiberAverage] using
        (mul_le_mul_of_nonneg_left (S.fiberMin_le_average c _) hret)
  | neutral =>
      simp [operator, annealedOperator, hbranch]
  | advanced =>
      simp only [operator, annealedOperator, hbranch]
      apply add_le_add (le_refl _)
      simpa [fiberAverage] using
        (mul_le_mul_of_nonneg_left (S.fiberMin_le_average c _) hadv)

theorem operator_neutral
    (w : Weights ℝ) (c : S.State → ℝ) {m : S.State}
    (hm : S.branch m = Branch.neutral) :
    S.operator w c m = w.transport * c (S.transport m) := by
  simp [operator, hm]

theorem operator_mono
    (w : Weights ℝ) (hw0 : 0 ≤ w.transport) (hw2 : 0 ≤ w.retarded)
    (hw8 : 0 ≤ w.advanced) {c d : S.State → ℝ} (h : ∀ m, c m ≤ d m) :
    ∀ m, S.operator w c m ≤ S.operator w d m := by
  intro m
  have ht := mul_le_mul_of_nonneg_left (h (S.transport m)) hw0
  have hf := S.fiberMin_mono h (S.refinementTarget m)
  cases hb : S.branch m with
  | retarded =>
      simpa [operator, hb] using add_le_add ht (mul_le_mul_of_nonneg_left hf hw2)
  | neutral => simpa [operator, hb] using ht
  | advanced =>
      simpa [operator, hb] using add_le_add ht (mul_le_mul_of_nonneg_left hf hw8)

theorem operator_nonneg
    (w : Weights ℝ) (hw0 : 0 ≤ w.transport) (hw2 : 0 ≤ w.retarded)
    (hw8 : 0 ≤ w.advanced) (c : S.State → ℝ) (hc : ∀ m, 0 ≤ c m) :
    ∀ m, 0 ≤ S.operator w c m := by
  intro m
  have ht : 0 ≤ w.transport * c (S.transport m) := mul_nonneg hw0 (hc _)
  have hf : 0 ≤ S.fiberMin c (S.refinementTarget m) :=
    S.fiberMin_nonneg c hc (S.refinementTarget m)
  cases hb : S.branch m with
  | retarded => simpa [operator, hb] using add_nonneg ht (mul_nonneg hw2 hf)
  | neutral => simpa [operator, hb] using ht
  | advanced => simpa [operator, hb] using add_nonneg ht (mul_nonneg hw8 hf)

/-- Increasing nonnegative operator coefficients can only increase the KL
operator on a nonnegative vector. -/
theorem operator_mono_weights
    {w v : Weights ℝ} {c : S.State → ℝ}
    (hc : ∀ m, 0 ≤ c m)
    (ht : w.transport ≤ v.transport)
    (hret : w.retarded ≤ v.retarded)
    (hadv : w.advanced ≤ v.advanced) :
    ∀ m, S.operator w c m ≤ S.operator v c m := by
  intro m
  have htransport := mul_le_mul_of_nonneg_right ht (hc (S.transport m))
  have hf : 0 ≤ S.fiberMin c (S.refinementTarget m) :=
    S.fiberMin_nonneg c hc (S.refinementTarget m)
  cases hb : S.branch m with
  | retarded =>
      simpa [operator, hb] using
        add_le_add htransport (mul_le_mul_of_nonneg_right hret hf)
  | neutral => simpa [operator, hb] using htransport
  | advanced =>
      simpa [operator, hb] using
        add_le_add htransport (mul_le_mul_of_nonneg_right hadv hf)

/-- Reduced KL feasibility, with the normalization separated from the
componentwise subeigenvector inequality. -/
def Feasible (w : Weights ℝ) (c : S.State → ℝ) : Prop :=
  (∀ m, 1 ≤ c m) ∧ ∀ m, c m ≤ S.operator w c m

theorem feasible_mono_weights
    {w v : Weights ℝ} {c : S.State → ℝ}
    (h : S.Feasible w c)
    (ht : w.transport ≤ v.transport)
    (hret : w.retarded ≤ v.retarded)
    (hadv : w.advanced ≤ v.advanced) :
    S.Feasible v c := by
  constructor
  · exact h.1
  · intro m
    exact (h.2 m).trans
      (S.operator_mono_weights (fun q => (h.1 q).trans' zero_le_one)
        ht hret hadv m)

end

end FiniteSystem

end CleanLean.KL
