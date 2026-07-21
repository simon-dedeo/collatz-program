/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ResidueSystem
import CleanLean.KL.ScaledCertificate

/-!
# Critical finite-level KL parameters

This file gives a definition of the finite KL endpoint which does not depend
on a floating-point Perron computation.  It also records the direct
subeigenvector route to `lambda_k → 2`: a sequence of exactly feasible
parameters tending to two squeezes the critical endpoints to two, without
requiring critical eigenvector compactness or localization.
-/

namespace CleanLean.KL

open Filter

/-- Exact feasibility for the concrete level-`k` KL system. -/
def LevelFeasible (k : ℕ) (lam : ℝ) : Prop :=
  ∃ c : (ResidueSystem.system k).State → ℝ,
    (ResidueSystem.system k).Feasible (klWeights lam) c

/-- The critical parameter is the supremum of feasible parameters in the
closed search interval `[1,2]`. -/
noncomputable def criticalLambda (k : ℕ) : ℝ :=
  sSup {lam : ℝ | lam ∈ Set.Icc (1 : ℝ) 2 ∧ LevelFeasible k lam}

theorem levelFeasible_one (k : ℕ) : LevelFeasible k 1 := by
  refine ⟨fun _ => 1, ?_⟩
  constructor
  · intro m
    rfl
  · intro m
    cases hb : (ResidueSystem.system k).branch m <;>
      simp [FiniteSystem.operator, klWeights, FiniteSystem.fiberMin, hb]

theorem criticalSet_nonempty (k : ℕ) :
    {lam : ℝ | lam ∈ Set.Icc (1 : ℝ) 2 ∧ LevelFeasible k lam}.Nonempty := by
  exact ⟨1, by exact ⟨by norm_num, levelFeasible_one k⟩⟩

theorem criticalSet_bddAbove (k : ℕ) :
    BddAbove {lam : ℝ | lam ∈ Set.Icc (1 : ℝ) 2 ∧ LevelFeasible k lam} := by
  refine ⟨2, ?_⟩
  intro lam hlam
  exact hlam.1.2

theorem one_le_criticalLambda (k : ℕ) : 1 ≤ criticalLambda k := by
  apply le_csSup (criticalSet_bddAbove k)
  exact ⟨by norm_num, levelFeasible_one k⟩

theorem criticalLambda_le_two (k : ℕ) : criticalLambda k ≤ 2 := by
  apply csSup_le (criticalSet_nonempty k)
  intro lam hlam
  exact hlam.1.2

theorem le_criticalLambda_of_feasible {k : ℕ} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (1 : ℝ) 2) (h : LevelFeasible k lam) :
    lam ≤ criticalLambda k := by
  apply le_csSup (criticalSet_bddAbove k)
  exact ⟨hlam, h⟩

/-- A passing streamed integer certificate is a concrete witness for
`LevelFeasible`, with its exact rational parameter. -/
theorem levelFeasible_of_scaledCertificate
    (k P Q : ℕ)
    (d : (ResidueSystem.system k).ScaledCertificate)
    (hcheck : d.check = true)
    (hQ : 0 < Q)
    (hlambda : d.lambdaScale < d.lambdaNum)
    (halpha : checkAlphaLower P Q = true)
    (hweights : checkBranchWeightLowerData d.lambdaNum d.lambdaScale
      d.retardedNum d.advancedNum d.weightScale P Q = true) :
    LevelFeasible k ((d.lambdaNum : ℝ) / d.lambdaScale) := by
  refine ⟨fun m => (d.valuesRat m : ℝ), ?_⟩
  exact d.feasibleKL_of_checks P Q hcheck hQ hlambda halpha hweights

/-- Direct-feasibility alternative to the fiber-geometry route.  Producing
one exact feasible parameter per level whose values tend to two is already
enough to prove convergence of the critical endpoints. -/
theorem criticalLambda_tendsto_two_of_feasible_lower
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (nhds 2))
    (hmuRange : ∀ k, mu k ∈ Set.Icc (1 : ℝ) 2)
    (hfeasible : ∀ k, LevelFeasible k (mu k)) :
    Tendsto criticalLambda atTop (nhds 2) := by
  apply Tendsto.squeeze hmu tendsto_const_nhds
  · intro k
    exact le_criticalLambda_of_feasible (hmuRange k) (hfeasible k)
  · intro k
    exact criticalLambda_le_two k

end CleanLean.KL
