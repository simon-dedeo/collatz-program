/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CountingTransfer
import CleanLean.KL.StrictLift

/-!
# From a softened KL operator back to hard-min feasibility

This file isolates the finite comparison needed by the fixed-temperature
route.  If a positive soft subeigenvector has factor `r`, the soft operator is
pointwise at most `C` times the literal hard-min KL operator, and `C < r`, then
the same vector is a hard-min subeigenvector.  Normalization gives exact finite
KL feasibility.

The theorem does not assert the power-mean sandwich or the conjectural
fixed-temperature spectral limit.  Those are the remaining analytic inputs.
The interface accepts a subeigenvector rather than an exact eigenvector so it
can also consume future interval/rational soft certificates.
-/

namespace CleanLean.KL

open Filter
open CleanLean.Collatz

namespace ResidueSystem

noncomputable section

/-- A soft subeigenvalue exceeding its pointwise hard-comparison factor gives
an exact hard-min KL feasibility witness at the same level and parameter. -/
theorem levelFeasible_of_softSubeigen_domination
    (k : ℕ) (lam r C : ℝ)
    (soft : (State k → ℝ) → State k → ℝ)
    (x : State k → ℝ)
    (hx : ∀ s, 0 < x s)
    (hC : 0 < C) (hr : C < r)
    (hsoft : ∀ s, r * x s ≤ soft x s)
    (hdom : ∀ s,
      soft x s ≤ C * (system k).operator (klWeights lam) x s) :
    LevelFeasible k lam := by
  letI : Nonempty (system k).State := by
    change Nonempty (State k)
    exact ⟨0⟩
  have hsub : ∀ s, x s ≤ (system k).operator (klWeights lam) x s := by
    intro s
    have hstrict : C * x s < r * x s :=
      mul_lt_mul_of_pos_right hr (hx s)
    have hscaled : C * x s ≤
        C * (system k).operator (klWeights lam) x s :=
      hstrict.le.trans ((hsoft s).trans (hdom s))
    exact le_of_mul_le_mul_left hscaled hC
  obtain ⟨z, hz⟩ := (system k).feasible_of_positive_subeigen
    (klWeights lam) x hx hsub
  exact ⟨z, hz⟩

/-- Fully composed sparse soft-to-hard endpoint.  For parameters tending to
two, it is enough to produce soft subeigenvectors at arbitrary finite witness
levels whose factors beat their certified hard-comparison constants. -/
theorem almostLinearPredecessorCounting_of_softSubeigen_bridges
    (mu : ℕ → ℝ) (level : ℕ → ℕ)
    (C r : ℕ → ℝ)
    (soft : (n : ℕ) →
      (State (level n) → ℝ) → State (level n) → ℝ)
    (x : (n : ℕ) → State (level n) → ℝ)
    (hmu : Tendsto mu atTop (nhds 2))
    (hmuLower : ∀ n, 1 < mu n)
    (hmuUpper : ∀ n, mu n ≤ 2)
    (hlevel : ∀ n, 2 ≤ level n)
    (hx : ∀ n s, 0 < x n s)
    (hC : ∀ n, 0 < C n)
    (hr : ∀ n, C n < r n)
    (hsoft : ∀ n s, r n * x n s ≤ soft n (x n) s)
    (hdom : ∀ n s, soft n (x n) s ≤
      C n * (system (level n)).operator (klWeights (mu n)) (x n) s) :
    AlmostLinearPredecessorCounting := by
  apply almostLinearPredecessorCounting_of_sparse_feasible_sequence
    mu level hmu hmuLower hmuUpper hlevel
  intro n
  exact levelFeasible_of_softSubeigen_domination
    (level n) (mu n) (r n) (C n) (soft n) (x n)
      (hx n) (hC n) (hr n) (hsoft n) (hdom n)

end

end ResidueSystem

end CleanLean.KL
