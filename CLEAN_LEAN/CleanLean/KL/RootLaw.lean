/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Exact algebra at the advanced fixed fiber

This file isolates the valid local calculation at the `-1` spine.  It does
not assert that the KL eigenfunction exists, that a numerical subeigenvector
is an exact eigenfunction, or that the free min-harmonic boundary datum is
uniformly controlled.
-/

namespace CleanLean.KL

/-- Solving the exact eigen-equation at the advanced fixed fiber gives the
normalized minimum.  In the KL notation, `A = λ^(α-1)` and `t = λ^(-2)`. -/
theorem advanced_fiber_min_law
    {c0 c4 m A t : ℝ} (hc0 : c0 ≠ 0) (hA : A ≠ 0)
    (heigen : c0 = t * c4 + A * m) :
    m / c0 = 1 / A - (t / A) * (c4 / c0) := by
  field_simp [hc0, hA]
  linarith

/-- At the root of the pure-branch system, the self-loop does not make the
equation vacuous: when `A > 1`, the smaller nontrivial child is exactly
`A⁻¹`. -/
theorem pureBranch_root_min
    {A p₁ p₂ : ℝ} (hA : 1 < A)
    (hroot : 1 = A * min 1 (min p₁ p₂)) :
    min p₁ p₂ = A⁻¹ := by
  by_cases h : 1 ≤ min p₁ p₂
  · rw [min_eq_left h] at hroot
    linarith
  · have hm : min p₁ p₂ ≤ 1 := le_of_not_ge h
    rw [min_eq_right hm] at hroot
    have hmul : min p₁ p₂ * A = 1 := by
      nlinarith
    have hA0 : A ≠ 0 := by linarith
    rw [← one_div]
    exact (eq_div_iff hA0).2 hmul

/-- The naive root `H = min H(children)` condition is too weak when one child
is the root self-loop.  This concrete example pinpoints the missing extra root
condition in the claimed global "iff" for the reparameterized system. -/
theorem root_min_harmonic_not_sufficient :
    (1 : ℝ) = min 1 (min 2 2) ∧
      (1 : ℝ) ≠ 2 * min 1 (min ((2 : ℝ)⁻¹ * 2) ((2 : ℝ)⁻¹ * 2)) := by
  norm_num

end CleanLean.KL
