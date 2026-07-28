/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePhaseSwap

/-!
# Opposite-sign unit cells collapse to one affine rail

The unit-debris hierarchy supplies public cells with additive signs `+1` and
`-1`.  It is tempting to regard `U-1` and `U+1` as two independent rails and
hope that an opposite-sign pair transports one packet while computing a
Hensel repair bit on the other.  This module records the exact composition
before making that architectural inference.

Two signed cells always eliminate their intermediate packet to one affine
balance.  At the first positive and negative compiler levels, both possible
orders leave a *positive* power-difference debris.  The signs therefore do
not cancel and do not by themselves create a second public register.  A
genuine shuttle needs an additional nonlinear public encoding or a return
which makes the power-difference debris itself the next decoded packet.

This is an architecture reduction, not a no-counterexample theorem.
-/

namespace KontoroC
namespace SignedUnitShuttle

/-- Abstract signed unit balance over the integers. -/
def SignedStep (sign : ℤ) (ternary binary : ℕ) (source target : ℤ) : Prop :=
  (2 : ℤ) ^ binary * target = (3 : ℤ) ^ ternary * source + sign

/-- Eliminating the intermediate packet in two signed cells leaves a single
rank-one affine balance with the displayed composed debris. -/
theorem signedStep_compose
    {s₀ s₁ : ℤ} {Q₀ P₀ Q₁ P₁ : ℕ} {h₀ h₁ h₂ : ℤ}
    (hfirst : SignedStep s₀ Q₀ P₀ h₀ h₁)
    (hsecond : SignedStep s₁ Q₁ P₁ h₁ h₂) :
    (2 : ℤ) ^ (P₀ + P₁) * h₂ =
      (3 : ℤ) ^ (Q₀ + Q₁) * h₀ +
        (3 : ℤ) ^ Q₁ * s₀ + (2 : ℤ) ^ P₀ * s₁ := by
  simp only [SignedStep] at hfirst hsecond
  rw [pow_add, pow_add]
  calc
    (2 : ℤ) ^ P₀ * 2 ^ P₁ * h₂ =
        2 ^ P₀ * (2 ^ P₁ * h₂) := by ring
    _ = 2 ^ P₀ * (3 ^ Q₁ * h₁ + s₁) := by rw [hsecond]
    _ = 3 ^ Q₁ * (2 ^ P₀ * h₁) + 2 ^ P₀ * s₁ := by ring
    _ = 3 ^ Q₁ * (3 ^ Q₀ * h₀ + s₀) + 2 ^ P₀ * s₁ := by
      rw [hfirst]
    _ = 3 ^ Q₀ * 3 ^ Q₁ * h₀ + 3 ^ Q₁ * s₀ + 2 ^ P₀ * s₁ := by
      ring

/-- Public binary exponent at the first, sign-positive unit level. -/
def plusBinary (n : ℕ) : ℕ := 8 * n + 15

/-- Public ternary exponent at the first, sign-positive unit level. -/
def plusTernary (n : ℕ) : ℕ := 6 * n + 11

/-- Public binary exponent at the second, sign-negative unit level. -/
def minusBinary (n : ℕ) : ℕ := 23 * n + 54

/-- Public ternary exponent at the second, sign-negative unit level. -/
def minusTernary (n : ℕ) : ℕ := 17 * n + 40

/-- In the `+` then `-` order, the second ternary scale strictly dominates
the first binary scale. -/
theorem two_pow_plusBinary_lt_three_pow_minusTernary (n : ℕ) :
    2 ^ plusBinary n < 3 ^ minusTernary n := by
  have hexp : plusBinary n ≤ minusTernary n := by
    simp only [plusBinary, minusTernary]
    omega
  calc
    2 ^ plusBinary n < 3 ^ plusBinary n :=
      Nat.pow_lt_pow_left (by norm_num) (by simp [plusBinary])
    _ ≤ 3 ^ minusTernary n := Nat.pow_le_pow_right (by norm_num) hexp

/-- In the reverse order, the negative-level binary scale strictly dominates
the positive-level ternary scale. -/
theorem three_pow_plusTernary_lt_two_pow_minusBinary (n : ℕ) :
    3 ^ plusTernary n < 2 ^ minusBinary n := by
  have hexp : 2 * plusTernary n < minusBinary n := by
    simp only [plusTernary, minusBinary]
    omega
  calc
    3 ^ plusTernary n < 4 ^ plusTernary n :=
      Nat.pow_lt_pow_left (by norm_num) (by simp [plusTernary])
    _ = 2 ^ (2 * plusTernary n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    _ < 2 ^ minusBinary n := Nat.pow_lt_pow_right (by norm_num) hexp

/-- Positive debris left by a sign-positive cell followed by a sign-negative
cell. -/
def plusMinusDebris (n : ℕ) : ℕ :=
  3 ^ minusTernary n - 2 ^ plusBinary n

/-- Positive debris left by the reverse sign order. -/
def minusPlusDebris (n : ℕ) : ℕ :=
  2 ^ minusBinary n - 3 ^ plusTernary n

theorem plusMinusDebris_pos (n : ℕ) : 0 < plusMinusDebris n := by
  exact Nat.sub_pos_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary n)

theorem minusPlusDebris_pos (n : ℕ) : 0 < minusPlusDebris n := by
  exact Nat.sub_pos_of_lt (three_pow_plusTernary_lt_two_pow_minusBinary n)

/-- The rectified debris has no dyadic gap of its own. -/
theorem plusMinusDebris_odd (n : ℕ) : Odd (plusMinusDebris n) := by
  apply Nat.Odd.sub_even
    (Nat.le_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary n))
  · exact Odd.pow (by norm_num : Odd (3 : ℕ))
  · exact even_two.pow_of_ne_zero (by simp [plusBinary])

/-- The reverse-order debris is likewise odd. -/
theorem minusPlusDebris_odd (n : ℕ) : Odd (minusPlusDebris n) := by
  apply Nat.Even.sub_odd
    (Nat.le_of_lt (three_pow_plusTernary_lt_two_pow_minusBinary n))
  · exact even_two.pow_of_ne_zero (by simp [minusBinary])
  · exact Odd.pow (by norm_num : Odd (3 : ℕ))

/-- Exact first-level `+` followed by second-level `-` collapse. -/
theorem plus_then_minus
    {n m ell : ℕ} {h₀ h₁ h₂ : ℤ}
    (hplus : SignedStep 1 (plusTernary n) (plusBinary m) h₀ h₁)
    (hminus : SignedStep (-1) (minusTernary m) (minusBinary ell) h₁ h₂) :
    (2 : ℤ) ^ (plusBinary m + minusBinary ell) * h₂ =
      (3 : ℤ) ^ (plusTernary n + minusTernary m) * h₀ +
        plusMinusDebris m := by
  have h := signedStep_compose hplus hminus
  have hdebris : (plusMinusDebris m : ℤ) =
      (3 : ℤ) ^ minusTernary m - (2 : ℤ) ^ plusBinary m := by
    rw [plusMinusDebris, Nat.cast_sub
      (Nat.le_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary m))]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℤ) ^ (plusBinary m + minusBinary ell) * h₂ =
        3 ^ (plusTernary n + minusTernary m) * h₀ +
          3 ^ minusTernary m * 1 + 2 ^ plusBinary m * (-1) := h
    _ = 3 ^ (plusTernary n + minusTernary m) * h₀ +
          (3 ^ minusTernary m - 2 ^ plusBinary m) := by ring
    _ = 3 ^ (plusTernary n + minusTernary m) * h₀ +
          plusMinusDebris m := by rw [← hdebris]

/-- Exact second-level `-` followed by first-level `+` collapse. -/
theorem minus_then_plus
    {n m ell : ℕ} {h₀ h₁ h₂ : ℤ}
    (hminus : SignedStep (-1) (minusTernary n) (minusBinary m) h₀ h₁)
    (hplus : SignedStep 1 (plusTernary m) (plusBinary ell) h₁ h₂) :
    (2 : ℤ) ^ (minusBinary m + plusBinary ell) * h₂ =
      (3 : ℤ) ^ (minusTernary n + plusTernary m) * h₀ +
        minusPlusDebris m := by
  have h := signedStep_compose hminus hplus
  have hdebris : (minusPlusDebris m : ℤ) =
      (2 : ℤ) ^ minusBinary m - (3 : ℤ) ^ plusTernary m := by
    rw [minusPlusDebris, Nat.cast_sub
      (Nat.le_of_lt (three_pow_plusTernary_lt_two_pow_minusBinary m))]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℤ) ^ (minusBinary m + plusBinary ell) * h₂ =
        3 ^ (minusTernary n + plusTernary m) * h₀ +
          3 ^ plusTernary m * (-1) + 2 ^ minusBinary m * 1 := h
    _ = 3 ^ (minusTernary n + plusTernary m) * h₀ +
          (2 ^ minusBinary m - 3 ^ plusTernary m) := by ring
    _ = 3 ^ (minusTernary n + plusTernary m) * h₀ +
          minusPlusDebris m := by rw [← hdebris]

end SignedUnitShuttle
end KontoroC
