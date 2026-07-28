/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardThreeWordZeroCarry

/-!
# The Archimedean boundary carried by a zero-carry address

Finite branch addresses determine successively finer `2`-adic cylinders, but
they do not by themselves explain how a positive ordinary charge can survive
forever.  This module isolates the missing ordinary datum without using a
limit or any numerical evidence.

For an address prefix of length `n`, write its exact affine balance as

`D_n * H_n = A_n * H_0 + C_n`.

The branch data imply the uniform, integer-valued window

`A_n * H_0 <= D_n * H_n <= A_n * (H_0 + 7)`

and the contraction estimate `9^n D_n <= 8^n A_n`.  Thus the normalized
quantity `(D_n/A_n) H_n` retains a positive contribution `H_0` at every
depth, while the address-dependent contribution `C_n/A_n` is at most `7`.
This is a reduction, not an existence theorem: a counterexample construction
must regenerate that nonzero Archimedean boundary while satisfying the
increasingly precise dyadic address constraints.
-/

namespace KontoroC
namespace OutwardThreeWordBoundaryAmplitude

open OutwardThreeWordZeroCarry

/-- Numerator of the affine forward slope of a branch. -/
def branchNumerator : Branch → ℕ
  | .A => 3
  | .B => 9
  | .C => 81

/-- Denominator of the affine forward slope of a branch. -/
def branchDenominator : Branch → ℕ
  | .A => 2
  | .B => 8
  | .C => 64

/-- Nonnegative affine offset of a branch. -/
def branchOffset : Branch → ℕ
  | .A => 0
  | .B => 3
  | .C => 63

/-- Uniform notation for the three literal branch balances. -/
theorem branch_step_iff_balance (b : Branch) (H H' : ℕ) :
    b.Step H H' ↔
      branchDenominator b * H' = branchNumerator b * H + branchOffset b := by
  cases b <;> rfl

theorem branch_numerator_pos (b : Branch) : 0 < branchNumerator b := by
  cases b <;> norm_num [branchNumerator]

theorem branch_denominator_pos (b : Branch) : 0 < branchDenominator b := by
  cases b <;> norm_num [branchDenominator]

/-- Every branch expands by at least `9/8`, including its offset. -/
theorem branch_step_nine_eighths {b : Branch} {H H' : ℕ}
    (hstep : b.Step H H') : 9 * H ≤ 8 * H' := by
  cases b <;> simp only [Branch.Step] at hstep <;> omega

/-- The inverse affine slope of every branch is at most `8/9`, expressed
without division. -/
theorem branch_inverse_contraction (b : Branch) :
    9 * branchDenominator b ≤ 8 * branchNumerator b := by
  cases b <;> norm_num [branchDenominator, branchNumerator]

/-- The offset and the remaining inverse slope fit in a common budget of
seven.  This local inequality is the source of the global boundary window. -/
theorem branch_boundary_budget (b : Branch) :
    branchOffset b + 7 * branchDenominator b ≤ 7 * branchNumerator b := by
  cases b <;>
    norm_num [branchOffset, branchDenominator, branchNumerator]

/-- Product of forward numerators along an address prefix. -/
def numeratorPrefix (branch : ℕ → Branch) : ℕ → ℕ
  | 0 => 1
  | n + 1 => branchNumerator (branch n) * numeratorPrefix branch n

/-- Product of forward denominators along an address prefix. -/
def denominatorPrefix (branch : ℕ → Branch) : ℕ → ℕ
  | 0 => 1
  | n + 1 => branchDenominator (branch n) * denominatorPrefix branch n

/-- Accumulated inhomogeneous part of the composed affine balance. -/
def offsetPrefix (branch : ℕ → Branch) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      branchNumerator (branch n) * offsetPrefix branch n +
        branchOffset (branch n) * denominatorPrefix branch n

theorem numeratorPrefix_pos (branch : ℕ → Branch) (n : ℕ) :
    0 < numeratorPrefix branch n := by
  induction n with
  | zero => simp [numeratorPrefix]
  | succ n ih =>
      simp only [numeratorPrefix]
      exact Nat.mul_pos (branch_numerator_pos _) ih

theorem denominatorPrefix_pos (branch : ℕ → Branch) (n : ℕ) :
    0 < denominatorPrefix branch n := by
  induction n with
  | zero => simp [denominatorPrefix]
  | succ n ih =>
      simp only [denominatorPrefix]
      exact Nat.mul_pos (branch_denominator_pos _) ih

/-- Exact finite unrolling of an arbitrary labeled charge path. -/
theorem prefix_balance
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1)))
    (n : ℕ) :
    denominatorPrefix branch n * charge n =
      numeratorPrefix branch n * charge 0 + offsetPrefix branch n := by
  induction n with
  | zero => simp [numeratorPrefix, denominatorPrefix, offsetPrefix]
  | succ n ih =>
      have hs := (branch_step_iff_balance (branch n)
        (charge n) (charge (n + 1))).mp (hstep n)
      calc
        denominatorPrefix branch (n + 1) * charge (n + 1) =
            denominatorPrefix branch n *
              (branchDenominator (branch n) * charge (n + 1)) := by
                simp only [denominatorPrefix]
                ring
        _ = denominatorPrefix branch n *
              (branchNumerator (branch n) * charge n + branchOffset (branch n)) := by
                rw [hs]
        _ = branchNumerator (branch n) *
              (denominatorPrefix branch n * charge n) +
                branchOffset (branch n) * denominatorPrefix branch n := by ring
        _ = branchNumerator (branch n) *
              (numeratorPrefix branch n * charge 0 + offsetPrefix branch n) +
                branchOffset (branch n) * denominatorPrefix branch n := by rw [ih]
        _ = numeratorPrefix branch (n + 1) * charge 0 +
              offsetPrefix branch (n + 1) := by
                simp only [numeratorPrefix, offsetPrefix]
                ring

/-- The inverse slope of every prefix contracts at least geometrically at
rate `8/9`. -/
theorem prefix_inverse_contraction (branch : ℕ → Branch) (n : ℕ) :
    9 ^ n * denominatorPrefix branch n ≤
      8 ^ n * numeratorPrefix branch n := by
  induction n with
  | zero => simp [numeratorPrefix, denominatorPrefix]
  | succ n ih =>
      have hb := branch_inverse_contraction (branch n)
      have hmul := Nat.mul_le_mul ih hb
      calc
        9 ^ (n + 1) * denominatorPrefix branch (n + 1) =
          (9 ^ n * denominatorPrefix branch n) *
              (9 * branchDenominator (branch n)) := by
                simp only [denominatorPrefix, pow_succ]
                ring
        _ ≤ (8 ^ n * numeratorPrefix branch n) *
              (8 * branchNumerator (branch n)) := hmul
        _ = 8 ^ (n + 1) * numeratorPrefix branch (n + 1) := by
              simp only [numeratorPrefix, pow_succ]
              ring

/-- Exact global version of the local seven-unit boundary budget. -/
theorem prefix_boundary_budget (branch : ℕ → Branch) (n : ℕ) :
    offsetPrefix branch n + 7 * denominatorPrefix branch n ≤
      7 * numeratorPrefix branch n := by
  induction n with
  | zero => simp [numeratorPrefix, denominatorPrefix, offsetPrefix]
  | succ n ih =>
      have hb := branch_boundary_budget (branch n)
      calc
        offsetPrefix branch (n + 1) +
            7 * denominatorPrefix branch (n + 1) =
          branchNumerator (branch n) * offsetPrefix branch n +
            (branchOffset (branch n) + 7 * branchDenominator (branch n)) *
              denominatorPrefix branch n := by
                simp only [offsetPrefix, denominatorPrefix]
                ring
        _ ≤ branchNumerator (branch n) * offsetPrefix branch n +
            (7 * branchNumerator (branch n)) * denominatorPrefix branch n :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_right (denominatorPrefix branch n) hb) _
        _ = branchNumerator (branch n) *
              (offsetPrefix branch n + 7 * denominatorPrefix branch n) := by
                ring
        _ ≤ branchNumerator (branch n) * (7 * numeratorPrefix branch n) :=
              Nat.mul_le_mul_left (branchNumerator (branch n)) ih
        _ = 7 * numeratorPrefix branch (n + 1) := by
              simp only [numeratorPrefix]
              ring

/-- The composed offset is uniformly at most seven numerator units. -/
theorem offsetPrefix_le_seven_numerator (branch : ℕ → Branch) (n : ℕ) :
    offsetPrefix branch n ≤ 7 * numeratorPrefix branch n :=
  le_trans (Nat.le_add_right _ _) (prefix_boundary_budget branch n)

/-- The exact Archimedean boundary window.  After normalization by the
positive numerator, the middle term lies in `[H_0, H_0+7]` at every depth. -/
theorem prefix_boundary_window
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1)))
    (n : ℕ) :
    numeratorPrefix branch n * charge 0 ≤
        denominatorPrefix branch n * charge n ∧
      denominatorPrefix branch n * charge n ≤
        numeratorPrefix branch n * (charge 0 + 7) := by
  have hbalance := prefix_balance charge branch hstep n
  have hoff := offsetPrefix_le_seven_numerator branch n
  constructor
  · rw [hbalance]
    exact Nat.le_add_right _ _
  · calc
      denominatorPrefix branch n * charge n =
          numeratorPrefix branch n * charge 0 + offsetPrefix branch n :=
            hbalance
      _ ≤ numeratorPrefix branch n * charge 0 +
          7 * numeratorPrefix branch n := Nat.add_le_add_left hoff _
      _ = numeratorPrefix branch n * (charge 0 + 7) := by ring

/-- Iterating the local `9/8` expansion gives a completely exact
exponential lower bound for every branch orbit. -/
theorem orbit_nine_eighths_growth
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1)))
    (n : ℕ) :
    9 ^ n * charge 0 ≤ 8 ^ n * charge n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := branch_step_nine_eighths (hstep n)
      calc
        9 ^ (n + 1) * charge 0 = 9 * (9 ^ n * charge 0) := by
          rw [pow_succ]
          ring
        _ ≤ 9 * (8 ^ n * charge n) := Nat.mul_le_mul_left 9 ih
        _ = 8 ^ n * (9 * charge n) := by ring
        _ ≤ 8 ^ n * (8 * charge (n + 1)) :=
          Nat.mul_le_mul_left (8 ^ n) hs
        _ = 8 ^ (n + 1) * charge (n + 1) := by
          rw [pow_succ]
          ring

end OutwardThreeWordBoundaryAmplitude
end KontoroC
