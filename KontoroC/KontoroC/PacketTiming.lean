/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Timing separated binary packets

The separated-bit proposal schedules a high packet by multiplication by `3`
modulo a power of two.  This file isolates its exact elementary clock: modulo
`2^(n+3)`, the multiplicative order of `3` is `2^(n+1)`.
-/

namespace KontoroC

/-- The square of `3` has order `2^n` modulo `2^(n+3)`. -/
theorem orderOf_nine_twoPow (n : ℕ) :
    orderOf (9 : ZMod (2 ^ (n + 3))) = 2 ^ n := by
  convert ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two 3 (by omega)
    (by omega) 1 (by norm_num) n using 1 <;> norm_num

/-- The exact packet clock used in Kontorovich's separated-bit proposal. -/
theorem orderOf_three_twoPow (n : ℕ) :
    orderOf (3 : ZMod (2 ^ (n + 3))) = 2 ^ (n + 1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow
  · cases n with
    | zero =>
        simpa using (show (3 : ZMod 8) ≠ 1 by decide)
    | succ n =>
        have hne : (9 : ZMod (2 ^ (n + 1 + 3))) ^ (2 ^ n) ≠ 1 := by
          apply pow_ne_one_of_lt_orderOf (by positivity)
          rw [orderOf_nine_twoPow]
          exact Nat.pow_lt_pow_right (by omega) (by omega)
        intro h
        apply hne
        rw [show (9 : ZMod (2 ^ (n + 1 + 3))) = 3 ^ 2 by norm_num,
          ← pow_mul]
        convert h using 1
        simp [Nat.pow_succ, mul_comm]
  · have h9 := pow_orderOf_eq_one (9 : ZMod (2 ^ (n + 3)))
    rw [orderOf_nine_twoPow] at h9
    rw [show (9 : ZMod (2 ^ (n + 3))) = 3 ^ 2 by norm_num,
      ← pow_mul] at h9
    convert h9 using 1
    simp [Nat.pow_succ, mul_comm]

/-- Multiplying a timing exponent by one full packet period does not change
the residue of a packet modulo the chosen power of two. -/
theorem three_pow_add_period (n r t : ℕ) :
    (3 : ZMod (2 ^ (n + 3))) ^ (r + 2 ^ (n + 1) * t) =
      (3 : ZMod (2 ^ (n + 3))) ^ r := by
  simp [pow_add, ← orderOf_three_twoPow n, pow_mul, pow_orderOf_eq_one]

/-- Two multiplication times give the same packet residue exactly when their
difference is a multiple of the clock period. -/
theorem three_pow_eq_iff_modEq (n a b : ℕ) :
    (3 : ZMod (2 ^ (n + 3))) ^ a = (3 : ZMod (2 ^ (n + 3))) ^ b ↔
      a ≡ b [MOD 2 ^ (n + 1)] := by
  rw [← orderOf_three_twoPow n]
  have hfin : IsOfFinOrder (3 : ZMod (2 ^ (n + 3))) := by
    rw [← orderOf_ne_zero_iff, orderOf_three_twoPow]
    positivity
  exact hfin.pow_eq_pow_iff_modEq

end KontoroC
