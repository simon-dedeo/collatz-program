/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Three-fiber profiles and the transport-free local map

The transport-free renormalization proposed near the `-1` spine merely swaps
the two off-spine lift labels.  Its square is the identity, so it cannot select
the observed numerical value `a ≈ 0.6925` or provide a contraction rate.
-/

namespace CleanLean.KL

noncomputable section

/-- A real-valued profile on three lift labels. -/
abbrev Triple := Fin 3 → ℝ

/-- Mean of a three-lift profile. -/
def mean3 (x : Triple) : ℝ := (x 0 + x 1 + x 2) / 3

/-- Minimum of a three-lift profile. -/
def min3 (x : Triple) : ℝ := min (x 0) (min (x 1) (x 2))

/-- Maximum of a three-lift profile. -/
def max3 (x : Triple) : ℝ := max (x 0) (max (x 1) (x 2))

/-- Mean-normalized range of a three-lift profile. -/
def oscillation3 (x : Triple) : ℝ := (max3 x - min3 x) / mean3 x

/-- Scaling of all coordinates of a profile. -/
def scale3 (a : ℝ) (x : Triple) : Triple := fun i => a * x i

theorem mean3_scale (a : ℝ) (x : Triple) : mean3 (scale3 a x) = a * mean3 x := by
  simp only [mean3, scale3]
  ring

theorem min3_scale {a : ℝ} (ha : 0 ≤ a) (x : Triple) :
    min3 (scale3 a x) = a * min3 x := by
  simp [min3, scale3, ← mul_min_of_nonneg, ha]

theorem max3_scale {a : ℝ} (ha : 0 ≤ a) (x : Triple) :
    max3 (scale3 a x) = a * max3 x := by
  simp [max3, scale3, ← mul_max_of_nonneg, ha]

/-- Positive scalar multiplication preserves normalized oscillation.  This is
the analytic core of exact transport theorem T2. -/
theorem oscillation3_scale {a : ℝ} (ha : 0 < a) (x : Triple) :
    oscillation3 (scale3 a x) = oscillation3 x := by
  rw [oscillation3, min3_scale ha.le, max3_scale ha.le, mean3_scale]
  rw [oscillation3]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    (a * max3 x - a * min3 x) * ((mean3 x)⁻¹ * a⁻¹) =
        (a * a⁻¹) * (max3 x * (mean3 x)⁻¹) -
        (a * a⁻¹) * (min3 x * (mean3 x)⁻¹) := by ring
    _ = max3 x * (mean3 x)⁻¹ - min3 x * (mean3 x)⁻¹ := by
      rw [mul_inv_cancel₀ ha.ne']
      simp
    _ = (max3 x - min3 x) * (mean3 x)⁻¹ := by ring

/-- Swap the two nonzero lift labels. -/
def swapOff (x : Triple) : Triple := ![x 0, x 2, x 1]

@[simp] theorem swapOff_zero (x : Triple) : swapOff x 0 = x 0 := rfl
@[simp] theorem swapOff_one (x : Triple) : swapOff x 1 = x 2 := rfl
@[simp] theorem swapOff_two (x : Triple) : swapOff x 2 = x 1 := rfl

theorem swapOff_involutive (x : Triple) : swapOff (swapOff x) = x := by
  funext i
  fin_cases i <;> rfl

theorem mean3_swapOff (x : Triple) : mean3 (swapOff x) = mean3 x := by
  simp [mean3, swapOff]
  ring

theorem min3_swapOff (x : Triple) : min3 (swapOff x) = min3 x := by
  simp [min3, swapOff, min_comm]

theorem max3_swapOff (x : Triple) : max3 (swapOff x) = max3 x := by
  simp [max3, swapOff, max_comm]

theorem oscillation3_swapOff (x : Triple) :
    oscillation3 (swapOff x) = oscillation3 x := by
  simp only [oscillation3, min3_swapOff, max3_swapOff, mean3_swapOff]

/-- The mean-one local family observed at the advanced fixed spine. -/
def localProfile (a : ℝ) : Triple := ![1, a, 2 - a]

theorem mean3_localProfile (a : ℝ) : mean3 (localProfile a) = 1 := by
  simp [mean3, localProfile]
  ring

theorem localProfile_pos {a : ℝ} (ha0 : 0 < a) (ha2 : a < 2) :
    ∀ i, 0 < localProfile a i := by
  intro i
  fin_cases i <;> simp [localProfile] <;> linarith

/-- One transport-free renormalization step changes `a` to `2-a`. -/
theorem swapOff_localProfile (a : ℝ) :
    swapOff (localProfile a) = localProfile (2 - a) := by
  funext i
  fin_cases i <;> simp [swapOff, localProfile]

/-- Every member of the local family is a two-step fixed point.  Hence the
transport-free model has no mechanism selecting one value of `a`. -/
theorem localProfile_two_step (a : ℝ) :
    swapOff (swapOff (localProfile a)) = localProfile a :=
  swapOff_involutive _

end

end CleanLean.KL
