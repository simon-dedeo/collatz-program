/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ResidueSystem

/-!
# The aligned marginal oscillation mode

This file records the exact algebra behind the falsification of the first
charged spine-face Lyapunov architecture.  It is independent of numerical
precision: any profile map which is a scalar combination of the identity and
the lift swap `(1 2)` acts with the same eigenvalue on the mean mode and the
co-spine oscillation mode.

This is a no-go result for that certificate class, not evidence against the
KL limit `lambda_k → 2`.
-/

namespace CleanLean.KL

/-- The permutation of a three-lift profile induced by multiplication by two
on the lift label. -/
def swapLifts (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0, x 2, x 1]

/-- The constant (fiber-mean) direction. -/
def meanMode : Fin 3 → ℝ := ![1, 1, 1]

/-- The co-spine oscillation direction fixed by the lift swap. -/
def coSpineMode : Fin 3 → ℝ := ![2, -1, -1]

@[simp] theorem swapLifts_meanMode : swapLifts meanMode = meanMode := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem swapLifts_coSpineMode : swapLifts coSpineMode = coSpineMode := by
  funext i
  fin_cases i <;> rfl

/-- The general aligned symmetric profile map: all identity-labelled terms
sum to `a`, and all swapped terms sum to `b`. -/
def alignedSymmetricMap (a b : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => a * x i + b * swapLifts x i

theorem alignedSymmetricMap_of_swap_fixed
    (a b : ℝ) {x : Fin 3 → ℝ} (hx : swapLifts x = x) :
    alignedSymmetricMap a b x = fun i => (a + b) * x i := by
  funext i
  have hi := congrFun hx i
  simp only [alignedSymmetricMap]
  rw [hi]
  ring

/-- Mean and co-spine oscillation have exactly the same eigenvalue under
every aligned symmetric policy. -/
theorem aligned_mean_and_cospine_same_eigenvalue (a b : ℝ) :
    (alignedSymmetricMap a b meanMode = fun i => (a + b) * meanMode i) ∧
      (alignedSymmetricMap a b coSpineMode =
        fun i => (a + b) * coSpineMode i) := by
  constructor
  · exact alignedSymmetricMap_of_swap_fixed a b swapLifts_meanMode
  · exact alignedSymmetricMap_of_swap_fixed a b swapLifts_coSpineMode

/-- Consequently no strict relative contraction factor can dominate this
map on both modes when their common eigenvalue is positive. -/
theorem no_strict_relative_contraction_on_aligned_modes
    {a b rho : ℝ} (hab : 0 < a + b)
    (hcontract : ∀ x : Fin 3 → ℝ, swapLifts x = x →
      ∀ i, |alignedSymmetricMap a b x i| ≤
        rho * (a + b) * |x i|) :
    1 ≤ rho := by
  have h := hcontract meanMode swapLifts_meanMode 0
  simp [alignedSymmetricMap, meanMode, swapLifts, abs_of_pos hab] at h
  nlinarith

/-- At every residue precision, the retarded branch at coordinate zero has a
self lift at coordinate zero.  In original residue coordinates this is the
all-level B2 edge `2 → 2`. -/
theorem retarded_zero_selfLift (k : ℕ) :
    (ResidueSystem.system k).branch (0 : ResidueSystem.State k) = Branch.retarded ∧
      (ResidueSystem.system k).fiber
        ((ResidueSystem.system k).refinementTarget
          (0 : ResidueSystem.State k)) (0 : Fin 3) =
            (0 : ResidueSystem.State k) := by
  constructor
  · exact ResidueSystem.branch_zero k
  · simp [ResidueSystem.system, ResidueSystem.refinementTarget,
      ResidueSystem.branch_zero, ResidueSystem.retardedTarget,
      ResidueSystem.fiber]

end CleanLean.KL
