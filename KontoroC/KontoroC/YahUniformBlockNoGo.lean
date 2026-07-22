/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Arithmetic obstruction to a uniform YAH block compiler

The proposed uniform-block no-go reduces its final case to an exact size
separation.  A width-`w` ternary digit block starting at the left delimiter
has value at most `2 * 3^w`, whereas the simulated binary-one side requires
`2^(2w) = 4^w`.  For `w >= 3` the latter is strictly larger.

This file kernel-checks that arithmetic endpoint and the digit-evaluation
bound.  The preceding rewriting claim—that simulation forces the relevant
image to be such a ternary block—is deliberately a separate interface.
-/

namespace KontoroC
namespace YahUniformBlockNoGo

/-- Evaluate ternary digits from an initial natural value, left to right. -/
def ternaryEvalFrom : ℕ → List (Fin 3) → ℕ
  | x, [] => x
  | x, d :: ds => ternaryEvalFrom (3 * x + d.val) ds

/-- A coarse but exact positional bound, sufficient for the obstruction. -/
theorem ternaryEvalFrom_le (x : ℕ) (digits : List (Fin 3)) :
    ternaryEvalFrom x digits ≤ 3 ^ digits.length * (x + 1) := by
  induction digits generalizing x with
  | nil => simp [ternaryEvalFrom]
  | cons d ds ih =>
      rw [ternaryEvalFrom]
      calc
        ternaryEvalFrom (3 * x + d.val) ds ≤
            3 ^ ds.length * (3 * x + d.val + 1) := ih _
        _ ≤ 3 ^ ds.length * (3 * x + 3) := by
          have hdlt : d.val < 3 := d.isLt
          have hd : d.val ≤ 2 := by omega
          have hinner : 3 * x + d.val + 1 ≤ 3 * x + 3 := by omega
          exact Nat.mul_le_mul_left _ hinner
        _ = 3 ^ (d :: ds).length * (x + 1) := by
          simp only [List.length_cons, pow_succ]
          ring

theorem ternaryEval_one_le (digits : List (Fin 3)) :
    ternaryEvalFrom 1 digits ≤ 2 * 3 ^ digits.length := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using ternaryEvalFrom_le 1 digits

/-- The strict exponential separation used by the all-width argument. -/
theorem two_mul_threePow_lt_fourPow {w : ℕ} (hw : 3 ≤ w) :
    2 * 3 ^ w < 4 ^ w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hw
  clear hw
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show 3 + (n + 1) = (3 + n) + 1 by omega]
      rw [pow_succ, pow_succ]
      nlinarith [show 0 < 3 ^ (3 + n) by positivity]

theorem fourPow_eq_twoPow_double (w : ℕ) :
    4 ^ w = 2 ^ (2 * w) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]

/-- No width-`w >= 3` ternary digit block starting at the delimiter can have
the `2^(2w)` value required by the uniform binary block side. -/
theorem no_ternary_block_value_twoPow_double
    (digits : List (Fin 3)) (hw : 3 ≤ digits.length) :
    ternaryEvalFrom 1 digits ≠ 2 ^ (2 * digits.length) := by
  intro heq
  have hle := ternaryEval_one_le digits
  have hlt := two_mul_threePow_lt_fourPow hw
  rw [← fourPow_eq_twoPow_double] at heq
  omega

/-- Abstract endpoint for the uniform-block derivation: once simulation
identifies the required value with a width-matched ternary block, the
compiler is impossible. -/
theorem no_uniform_block_endpoint
    (w : ℕ) (digits : List (Fin 3))
    (hw : 3 ≤ w) (hlen : digits.length = w)
    (hvalue : ternaryEvalFrom 1 digits = 2 ^ (2 * w)) : False := by
  subst w
  exact no_ternary_block_value_twoPow_double digits hw hvalue

end YahUniformBlockNoGo
end KontoroC
