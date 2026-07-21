/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.FiniteSystem

/-!
# Exact rational feasibility certificates

GPU computations may propose a KL vector, but the load-bearing object is a
rational vector satisfying finitely many inequalities.  This file defines a
computable rational checker and proves that a passing rational certificate
gives a real feasible point for the abstract finite KL operator.

The multi-gigabyte level-19 and level-20 arrays are intentionally not embedded
in the Lean source.  A later streaming front end can translate their pinned
integer representation into this checker or produce a smaller proof artifact.
-/

namespace CleanLean.KL

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- The KL operator over exact rationals. -/
def operatorRat (w : Weights ℚ) (c : S.State → ℚ) (m : S.State) : ℚ :=
  w.transport * c (S.transport m) +
    match S.branch m with
    | Branch.retarded => w.retarded * S.fiberMin c (S.refinementTarget m)
    | Branch.neutral => 0
    | Branch.advanced => w.advanced * S.fiberMin c (S.refinementTarget m)

/-- Exact rational feasibility after auxiliary fiber variables have been
eliminated. -/
def FeasibleRat (w : Weights ℚ) (c : S.State → ℚ) : Prop :=
  (∀ m, 1 ≤ c m) ∧ ∀ m, c m ≤ S.operatorRat w c m

/-- Executable Boolean checker for an exact rational KL certificate. -/
def checkFeasibleRat (w : Weights ℚ) (c : S.State → ℚ) : Bool :=
  decide
    ((∀ m ∈ (Finset.univ : Finset S.State), 1 ≤ c m) ∧
      ∀ m ∈ (Finset.univ : Finset S.State), c m ≤ S.operatorRat w c m)

theorem checkFeasibleRat_eq_true_iff (w : Weights ℚ) (c : S.State → ℚ) :
    S.checkFeasibleRat w c = true ↔ S.FeasibleRat w c := by
  simp [checkFeasibleRat, FeasibleRat]

/-- Casting the exact rational operator to the reals commutes with evaluation. -/
theorem operatorRat_cast (w : Weights ℚ) (c : S.State → ℚ) (m : S.State) :
    (S.operatorRat w c m : ℝ) =
      S.operator
        { transport := (w.transport : ℝ)
          retarded := (w.retarded : ℝ)
          advanced := (w.advanced : ℝ) }
        (fun s => (c s : ℝ)) m := by
  cases hb : S.branch m <;>
    simp [operatorRat, operator, hb, fiberMin, Rat.cast_min]

/-- Casting rational feasibility to the reals is sound. -/
theorem feasible_of_feasibleRat
    (w : Weights ℚ) (c : S.State → ℚ)
    (h : S.FeasibleRat w c) :
    S.Feasible
      { transport := (w.transport : ℝ)
        retarded := (w.retarded : ℝ)
        advanced := (w.advanced : ℝ) }
      (fun s => (c s : ℝ)) := by
  constructor
  · intro m
    simpa using (Rat.natCast_le_cast (K := ℝ)).2 (h.1 m)
  · intro m
    rw [← S.operatorRat_cast w c m]
    exact (Rat.cast_le (K := ℝ)).2 (h.2 m)

/-- Soundness theorem for the executable checker.  No floating-point result
enters this implication. -/
theorem feasible_of_checkFeasibleRat
    (w : Weights ℚ) (c : S.State → ℚ)
    (hcheck : S.checkFeasibleRat w c = true) :
    S.Feasible
      { transport := (w.transport : ℝ)
        retarded := (w.retarded : ℝ)
        advanced := (w.advanced : ℝ) }
      (fun s => (c s : ℝ)) := by
  have hrat : S.FeasibleRat w c :=
    (S.checkFeasibleRat_eq_true_iff w c).1 hcheck
  exact S.feasible_of_feasibleRat w c hrat

end

end FiniteSystem

end CleanLean.KL
