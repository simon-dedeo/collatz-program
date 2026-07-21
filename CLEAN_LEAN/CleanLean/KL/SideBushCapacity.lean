/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.SideBush
import CleanLean.KL.CountingTransfer

/-!
# KL capacity of side bushes along an injective Syracuse spine

This file combines two independently checked ingredients: deterministic
pairwise disjointness of side-target predecessor sets and the explicit finite
KL targetwise lower bound.  The result is a finite packing inequality.  It
does not assert that the inequality contradicts an infinite orbit.
-/

namespace CleanLean.KL

open CleanLean.Collatz
open scoped BigOperators

theorem sideTarget_nonperiodic
    {n₀ j : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : syracuseOrbit n₀ j % 2 = 1) :
    ¬ IsSyracusePeriodic (sideTarget n₀ j) := by
  exact sideTarget_not_periodic_raw hinj hodd

/-- A side target, placed in its literal level-`k` KL residue state. -/
def sideKLTarget
    (k n₀ j : ℕ) (hk : 1 ≤ k)
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : syracuseOrbit n₀ j % 2 = 1) :
    KLTarget k (klStateOf k (sideTarget n₀ j)) :=
  ⟨sideTarget n₀ j, sideTarget_pos n₀ j,
    klStateOf_target_modEq hk (sideTarget_mod_three n₀ j),
    sideTarget_nonperiodic hinj hodd⟩

/-- Finite side-spine capacity.  Every summand is the exact explicit KL lower
load for one side target, with its own concrete residue-state weight. -/
theorem sideSpine_capacity_of_feasible
    {k : ℕ} (hk : 2 ≤ k) {lam C : ℝ}
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (c : ResidueSystem.State k → ℝ)
    (hC : 0 < C) (hcC : ∀ state, c state ≤ C)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c)
    {n₀ X : ℕ} (J : Finset ℕ)
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : ∀ j ∈ J, syracuseOrbit n₀ j % 2 = 1)
    (hX : ∀ j ∈ J, sideTarget n₀ j ≤ X) :
    ∑ j ∈ J,
        ((1 / (4 * C)) * c (klStateOf k (sideTarget n₀ j))) *
          ((X : ℝ) / sideTarget n₀ j) ^ (klExponent lam) ≤
      (X : ℝ) := by
  have hterm : ∀ j ∈ J,
      ((1 / (4 * C)) * c (klStateOf k (sideTarget n₀ j))) *
          ((X : ℝ) / sideTarget n₀ j) ^ (klExponent lam) ≤
        (predecessorCount (sideTarget n₀ j) X : ℝ) := by
    intro j hj
    let target := sideKLTarget k n₀ j (by omega) hinj (hodd j hj)
    simpa [target, sideKLTarget] using
      predecessorCount_lower_bound_klTarget_of_feasible
        hk hlam1 hlam2 c hC hcC hfeasible target X (hX j hj)
  have hpackNat := sum_predecessorCount_sideTargets_le (X := X) J hinj hodd
  have hpackReal :
      ((∑ j ∈ J, predecessorCount (sideTarget n₀ j) X : ℕ) : ℝ) ≤ X := by
    exact_mod_cast hpackNat
  calc
    ∑ j ∈ J,
        ((1 / (4 * C)) * c (klStateOf k (sideTarget n₀ j))) *
          ((X : ℝ) / sideTarget n₀ j) ^ (klExponent lam) ≤
        ∑ j ∈ J, (predecessorCount (sideTarget n₀ j) X : ℝ) := by
      exact Finset.sum_le_sum fun j hj => hterm j hj
    _ = ((∑ j ∈ J, predecessorCount (sideTarget n₀ j) X : ℕ) : ℝ) := by
      norm_cast
    _ ≤ (X : ℝ) := hpackReal

end CleanLean.KL
