/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# A scalar affine reset cannot decrement a binary counter

Every fixed finite Collatz valuation word has an affine endpoint balance

`2^S * y = 3^O * x + delta`.

If the same word preserved the spacing of two adjacent members of an affine
counter family, subtracting the two balances would force `2^S = 3^O`.
This is impossible for a nonempty word (`S > 0`).  Thus a binary decrementer
cannot live in one scalar affine payload chart with unchanged stride.  The
theorem is deliberately local: payload-dependent words, nonlinear encodings,
and genuinely multi-coordinate public states remain outside its scope.
-/

namespace KontoroC
namespace AffineBinaryCounterNoGo

/-- The endpoint equation of a fixed Collatz valuation word, stated over the
integers so that the translation term may have either sign. -/
def ResetBalance (S O : ℕ) (delta x y : ℤ) : Prop :=
  (2 : ℤ) ^ S * y = (3 : ℤ) ^ O * x + delta

/-- A positive power of two is not a power of three. -/
theorem two_pow_ne_three_pow_of_pos (S O : ℕ) (hS : 0 < S) :
    (2 : ℤ) ^ S ≠ (3 : ℤ) ^ O := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  intro h
  have hmod := congrArg (fun z : ℤ => z % 2) h
  have hthree : ∀ n : ℕ, (3 : ℤ) ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, Int.mul_emod, ih]
        rfl
  rw [hthree] at hmod
  simp [pow_succ] at hmod

/-- Two equal-stride source/target pairs under one reset force equality of the
two multiplicative slopes. -/
theorem parallel_reset_forces_equal_powers
    (S O : ℕ) (delta x y d : ℤ) (hd : d ≠ 0)
    (h0 : ResetBalance S O delta x y)
    (h1 : ResetBalance S O delta (x + d) (y + d)) :
    (2 : ℤ) ^ S = (3 : ℤ) ^ O := by
  unfold ResetBalance at h0 h1
  have h1' : (2 : ℤ) ^ S * y + (2 : ℤ) ^ S * d =
      ((3 : ℤ) ^ O * x + delta) + (3 : ℤ) ^ O * d := by
    simpa only [mul_add, add_assoc, add_left_comm, add_comm] using h1
  rw [h0] at h1'
  have hmul : (2 : ℤ) ^ S * d = (3 : ℤ) ^ O * d :=
    add_left_cancel h1'
  exact mul_right_cancel₀ hd hmul

/-- No nonempty fixed Collatz word can act on two scalar affine payloads while
preserving their positive spacing. -/
theorem no_parallel_affine_reset
    (S O : ℕ) (delta x y d : ℤ) (hS : 0 < S) (hd : d ≠ 0)
    (h0 : ResetBalance S O delta x y)
    (h1 : ResetBalance S O delta (x + d) (y + d)) : False := by
  exact two_pow_ne_three_pow_of_pos S O hS
    (parallel_reset_forces_equal_powers S O delta x y d hd h0 h1)

/-- Counter specialization.  On two consecutive inputs, the same fixed word
cannot send `a*(t+1)+b` to `a*t+b` and the next member likewise, for any
nonzero affine stride `a`. -/
theorem no_fixed_word_affine_decrement
    (S O : ℕ) (delta a b : ℤ) (t : ℕ)
    (hS : 0 < S) (ha : a ≠ 0)
    (h0 : ResetBalance S O delta
      (a * ((t : ℤ) + 1) + b) (a * (t : ℤ) + b))
    (h1 : ResetBalance S O delta
      (a * ((t : ℤ) + 2) + b) (a * ((t : ℤ) + 1) + b)) : False := by
  apply no_parallel_affine_reset S O delta
    (a * ((t : ℤ) + 1) + b) (a * (t : ℤ) + b) a hS ha h0
  convert h1 using 1 <;> ring

end AffineBinaryCounterNoGo
end KontoroC
