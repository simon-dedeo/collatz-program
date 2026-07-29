/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DoublingQuineIntegerNoGo

/-!
# The first precision-affordable long doubling return

The four-cell doubling quine uses two transitions whose source and target
opcode are the large state `g`.  Its forced dyadic precision has slope `23`,
but its positive real-height budget has slope only
`2 * (17 log₂ 3 - 23)`, which is less than `23`.

There is a canonical structural escape: insert more legal self-transitions
`g -> g` before returning to state one.  If `k` is the number of transitions
whose source (and target) is `g`, the legal route is

`1 -> 1 -> g -> ... -> g -> 1`

and has total exponents

`R_k = 114 + k Q(g)`, `S_k = 154 + k P(g)`.

The forcing term still factors by only `2^(77+P(g))`; adding self-loops does
not increase the terminal precision slope.  The real-height slope, however,
is multiplied by `k`.  Exact integer comparison proves a sharp transition:

`3^(17k) > 2^(23(k+1))` if and only if `k >= 6`.

Thus the original `k=2` quine is structurally underpowered, while the
six-high-transition return is the first member of this natural family not
killed by the precision-versus-height obstruction.  This module identifies a
new candidate architecture; it does not assert an integer payload or orbit.
-/

namespace KontoroC
namespace LongDoublingQuineThreshold

def P (g : ℕ) : ℕ := 23 * g + 54
def Q (g : ℕ) : ℕ := 17 * g + 40
def A : ℕ := 3 ^ 114
def b0 : ℕ := 3 ^ 57 + 2 ^ 77

/-- Total ternary exponent for a return with `k` high-opcode transitions. -/
def R (k g : ℕ) : ℕ := 114 + k * Q g

/-- Total binary exponent for a return with `k` high-opcode transitions. -/
def S (k g : ℕ) : ℕ := 154 + k * P g

/-- The geometric tail left after extracting the invariant first dyadic
precision factor from the forcing term. -/
def forcingTail (g : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 ^ Q g * forcingTail g k + 2 ^ (k * P g)

/-- Exact composite forcing term for the legal long return. -/
def defect (k g : ℕ) : ℕ :=
  3 ^ (k * Q g) * b0 + 2 ^ (77 + P g) * forcingTail g k

theorem forcingTail_pos (g k : ℕ) : 0 < forcingTail g (k + 1) := by
  simp [forcingTail]

/-- Adding one `g -> g` self-transition multiplies the old defect by `3^Q`
and appends the new terminal power of two. -/
theorem defect_succ (k g : ℕ) :
    defect (k + 1) g =
      3 ^ Q g * defect k g + 2 ^ (77 + (k + 1) * P g) := by
  simp only [defect, forcingTail]
  rw [show (k + 1) * Q g = Q g + k * Q g by
      rw [Nat.add_mul, one_mul, Nat.add_comm], pow_add,
    show 77 + (k + 1) * P g = (77 + P g) + k * P g by
      rw [Nat.add_mul, one_mul]
      omega,
    pow_add]
  ring

theorem R_succ_split (k g : ℕ) :
    3 ^ R (k + 1) g = 3 ^ ((k + 1) * Q g) * A := by
  simp only [R, A]
  rw [show 114 + (k + 1) * Q g = (k + 1) * Q g + 114 by omega,
    pow_add]

theorem S_succ_split (k g : ℕ) :
    2 ^ S (k + 1) g =
      2 ^ (77 + P g) * 2 ^ (77 + k * P g) := by
  simp only [S]
  rw [show 154 + (k + 1) * P g =
      (77 + P g) + (77 + k * P g) by
        rw [Nat.add_mul, one_mul]
        omega, pow_add]

/-- Every nonempty long return forces exactly the same first dyadic precision
factor as the original four-cell return. -/
theorem balance_factor {k g F Fnext : ℕ}
    (h : 3 ^ R (k + 1) g * F =
      defect (k + 1) g + 2 ^ S (k + 1) g * Fnext) :
    3 ^ ((k + 1) * Q g) * (A * F - b0) =
      2 ^ (77 + P g) *
        (forcingTail g (k + 1) + 2 ^ (77 + k * P g) * Fnext) := by
  have hR := R_succ_split k g
  have hS := S_succ_split k g
  have hnorm :
      3 ^ ((k + 1) * Q g) * (A * F) =
        3 ^ ((k + 1) * Q g) * b0 +
          2 ^ (77 + P g) *
            (forcingTail g (k + 1) + 2 ^ (77 + k * P g) * Fnext) := by
    calc
      3 ^ ((k + 1) * Q g) * (A * F) = 3 ^ R (k + 1) g * F := by
        rw [hR]
        ring
      _ = defect (k + 1) g + 2 ^ S (k + 1) g * Fnext := h
      _ = 3 ^ ((k + 1) * Q g) * b0 +
          2 ^ (77 + P g) *
            (forcingTail g (k + 1) + 2 ^ (77 + k * P g) * Fnext) := by
        rw [hS]
        simp only [defect]
        ring
  have hle : b0 ≤ A * F := by
    have hmul : 3 ^ ((k + 1) * Q g) * b0 ≤
        3 ^ ((k + 1) * Q g) * (A * F) := by
      rw [hnorm]
      exact Nat.le_add_right _ _
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  calc
    3 ^ ((k + 1) * Q g) * (A * F - b0) =
        3 ^ ((k + 1) * Q g) * (A * F) -
          3 ^ ((k + 1) * Q g) * b0 := by
            exact Nat.mul_sub_left_distrib _ _ _
    _ = 2 ^ (77 + P g) *
        (forcingTail g (k + 1) + 2 ^ (77 + k * P g) * Fnext) := by
          omega

/-- The exact slope test: can the long return's real coefficient pay for the
additional `23g` bits forced at its input? -/
def PaysPrecision (k : ℕ) : Prop :=
  2 ^ (23 * (k + 1)) < 3 ^ (17 * k)

theorem three_pow_17_gt_two_pow_23 : 2 ^ 23 < 3 ^ 17 := by norm_num

set_option exponentiation.threshold 200 in
theorem six_pays_precision : PaysPrecision 6 := by
  norm_num [PaysPrecision]

theorem paysPrecision_succ {k : ℕ} (hk : PaysPrecision k) :
    PaysPrecision (k + 1) := by
  dsimp only [PaysPrecision] at hk ⊢
  rw [show 23 * (k + 1 + 1) = 23 * (k + 1) + 23 by omega,
    show 17 * (k + 1) = 17 * k + 17 by omega, pow_add, pow_add]
  exact mul_lt_mul hk three_pow_17_gt_two_pow_23.le (by positivity)
    (Nat.zero_le _)

theorem paysPrecision_of_six_le {k : ℕ} (hk : 6 ≤ k) : PaysPrecision k := by
  induction k, hk using Nat.le_induction with
  | base => exact six_pays_precision
  | succ k _ ih => exact paysPrecision_succ ih

set_option exponentiation.threshold 200 in
theorem not_paysPrecision_of_lt_six {k : ℕ} (hk : k < 6) :
    ¬ PaysPrecision k := by
  interval_cases k <;> norm_num [PaysPrecision]

/-- Six high-opcode transitions are the sharp phase boundary. -/
theorem paysPrecision_iff (k : ℕ) : PaysPrecision k ↔ 6 ≤ k := by
  constructor
  · intro hk
    by_contra hnot
    exact not_paysPrecision_of_lt_six (by omega) hk
  · exact paysPrecision_of_six_le

end LongDoublingQuineThreshold
end KontoroC
