/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnSuccessorRigidity

/-!
# What eventual zero carry would mean for the successor return

The generic inverse-limit theorem produces a signed integer chain whose
initial value is merely nonnegative.  For the six-cell successor return this
is already enough: its defect is positive, odd, and strictly smaller than its
ternary multiplier.  Consequently the initial value cannot be zero and
positivity propagates forever.

Thus eventual zero carry is not a harmless coherence condition here.  It is
equivalent to the existence of the unique positive natural full-return ray.
This file proves that equivalence; it does not prove either side.
-/

namespace KontoroC
namespace LongReturnSuccessorZeroCarry

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open LongReturnSuccessorRigidity
open KLDyadicReset

/-- The six-term geometric tail is at most six copies of its largest
ternary monomial.  The deliberately coarse constant leaves enormous slack
against the fixed `3^114` boundary factor. -/
theorem forcingTail_six_le (g : ℕ) :
    forcingTail g 6 ≤ 6 * (3 ^ Q g) ^ 5 := by
  let a := 3 ^ Q g
  let b := 2 ^ P g
  have hba : b ≤ a := by
    have h2 : 2 * b < a := by
      have h := double_two_pow_P_lt_three_pow_Q g
      rw [pow_succ] at h
      simpa only [a, b, Nat.mul_comm] using h
    omega
  have hb2 : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hba 2
  have hb3 : b ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left hba 3
  have hb4 : b ^ 4 ≤ a ^ 4 := Nat.pow_le_pow_left hba 4
  have hb5 : b ^ 5 ≤ a ^ 5 := Nat.pow_le_pow_left hba 5
  have h1 : a ^ 4 * b ≤ a ^ 5 := by
    calc
      a ^ 4 * b ≤ a ^ 4 * a := Nat.mul_le_mul_left _ hba
      _ = a ^ 5 := by ring
  have h2 : a ^ 3 * b ^ 2 ≤ a ^ 5 := by
    calc
      a ^ 3 * b ^ 2 ≤ a ^ 3 * a ^ 2 := Nat.mul_le_mul_left _ hb2
      _ = a ^ 5 := by ring
  have h3 : a ^ 2 * b ^ 3 ≤ a ^ 5 := by
    calc
      a ^ 2 * b ^ 3 ≤ a ^ 2 * a ^ 3 := Nat.mul_le_mul_left _ hb3
      _ = a ^ 5 := by ring
  have h4 : a * b ^ 4 ≤ a ^ 5 := by
    calc
      a * b ^ 4 ≤ a * a ^ 4 := Nat.mul_le_mul_left _ hb4
      _ = a ^ 5 := by ring
  have htail : forcingTail g 6 =
      a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 +
        a * b ^ 4 + b ^ 5 := by
    simp only [forcingTail, a, b]
    ring
  change forcingTail g 6 ≤ 6 * a ^ 5
  rw [htail]
  omega

theorem boundary_constant_lt : b0 + 6 * 2 ^ 77 < 3 ^ 114 := by
  norm_num [b0]

/-- The positive forcing defect is smaller than one ternary source unit.
This is the Archimedean fact which turns a nonnegative signed chain into a
positive natural chain. -/
theorem defect_six_lt_three_pow_R (g : ℕ) :
    defect 6 g < 3 ^ R 6 g := by
  let a := 3 ^ Q g
  let b := 2 ^ P g
  have hb_lt : b < a := by
    have h2 : 2 * b < a := by
      have h := double_two_pow_P_lt_three_pow_Q g
      rw [pow_succ] at h
      simpa only [a, b, Nat.mul_comm] using h
    omega
  have htail := forcingTail_six_le g
  have hsecond :
      2 ^ (77 + P g) * forcingTail g 6 <
        (3 ^ Q g) ^ 6 * (6 * 2 ^ 77) := by
    rw [pow_add]
    calc
      2 ^ 77 * 2 ^ P g * forcingTail g 6 ≤
          2 ^ 77 * 2 ^ P g * (6 * (3 ^ Q g) ^ 5) :=
        Nat.mul_le_mul_left _ htail
      _ < 2 ^ 77 * 3 ^ Q g * (6 * (3 ^ Q g) ^ 5) := by
        exact Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_left hb_lt (by positivity)) (by positivity)
      _ = (3 ^ Q g) ^ 6 * (6 * 2 ^ 77) := by ring
  calc
    defect 6 g = (3 ^ Q g) ^ 6 * b0 +
        2 ^ (77 + P g) * forcingTail g 6 := by
      simp only [defect]
      rw [Nat.mul_comm 6 (Q g), pow_mul]
    _ < (3 ^ Q g) ^ 6 * b0 +
        (3 ^ Q g) ^ 6 * (6 * 2 ^ 77) :=
      Nat.add_lt_add_left hsecond _
    _ = (3 ^ Q g) ^ 6 * (b0 + 6 * 2 ^ 77) := by ring
    _ < (3 ^ Q g) ^ 6 * 3 ^ 114 :=
      Nat.mul_lt_mul_of_pos_left boundary_constant_lt (by positivity)
    _ = 3 ^ R 6 g := by
      simp only [R]
      rw [pow_add]
      ring

theorem defect_six_pos (g : ℕ) : 0 < defect 6 g := by
  simp only [defect, b0]
  positivity

theorem defect_six_odd (g : ℕ) : Odd (defect 6 g) := by
  exact LongReturnSelfDelimiting.longReturn_defect_odd 6 g

/-- A nonnegative initial value following the successor reset is actually
strictly positive.  Zero would make a positive odd defect divisible by a
positive power of two. -/
theorem follows_initial_pos {g0 : ℕ} {m : ℕ → ℤ}
    (hm : Follows (successorSixReset g0) m) (h0 : 0 ≤ m 0) :
    0 < m 0 := by
  have hs := hm 0
  simp only [successorSixReset, Nat.add_zero] at hs
  by_contra hnot
  have hm0 : m 0 = 0 := by omega
  rw [hm0] at hs
  simp only [mul_zero, zero_add] at hs
  have hdvd : (2 : ℤ) ∣ (defect 6 g0 : ℤ) := by
    have hN : 1 ≤ S 6 g0 := successorSixReset_N_pos g0 0
    have htwo : (2 : ℤ) ∣ (2 : ℤ) ^ S 6 g0 := by
      exact dvd_pow_self 2 (by omega)
    have : (2 : ℤ) ∣ -((defect 6 g0 : ℕ) : ℤ) := by
      rw [← hs]
      exact dvd_mul_of_dvd_left htwo _
    exact (Int.dvd_neg.mp this)
  have hdvdNat : 2 ∣ defect 6 g0 := by exact_mod_cast hdvd
  exact (Nat.not_even_iff_odd.mpr (defect_six_odd g0))
    (even_iff_two_dvd.mpr hdvdNat)

/-- Once positive, the signed reset chain stays positive because the defect
is smaller than one copy of the ternary multiplier. -/
theorem follows_pos {g0 : ℕ} {m : ℕ → ℤ}
    (hm : Follows (successorSixReset g0) m) (h0 : 0 ≤ m 0) :
    ∀ t, 0 < m t := by
  intro t
  induction t with
  | zero => exact follows_initial_pos hm h0
  | succ t ih =>
      have hs := hm t
      simp only [successorSixReset] at hs
      have hdef : (defect 6 (g0 + t) : ℤ) <
          (3 : ℤ) ^ R 6 (g0 + t) := by
        exact_mod_cast defect_six_lt_three_pow_R (g0 + t)
      have hnum : 0 < (3 : ℤ) ^ R 6 (g0 + t) * m t -
          (defect 6 (g0 + t) : ℤ) := by
        have hmone : 1 ≤ m t := ih
        nlinarith [show 0 < (3 : ℤ) ^ R 6 (g0 + t) by positivity]
      have hp2 : 0 < (2 : ℤ) ^ S 6 (g0 + t) := by positivity
      rw [show (3 : ℤ) ^ R 6 (g0 + t) * m t -
          (defect 6 (g0 + t) : ℤ) =
          (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) by
        calc
          _ = (3 : ℤ) ^ R 6 (g0 + t) * m t +
              -((defect 6 (g0 + t) : ℕ) : ℤ) := by ring
          _ = _ := hs.symm] at hnum
      exact ((mul_pos_iff.mp hnum).resolve_right (by omega)).2

/-- For the concrete successor program, the canonical carries eventually
vanish exactly if its unique positive natural full-return ray exists. -/
theorem eventuallyZeroCarry_iff_nonempty_balanceRay (g0 : ℕ) :
    EventuallyZeroCarry (successorSixReset g0) ↔
      Nonempty (SuccessorSixBalanceRay g0) := by
  constructor
  · intro hzero
    obtain ⟨m, hm, h0⟩ :=
      (eventuallyZeroCarry_iff_exists_nonnegative_follows
        (successorSixReset g0)).mp hzero
    apply (nonempty_successorSixBalanceRay_iff_nonnegative_follows g0).2
    exact ⟨m, hm, fun t => (follows_pos hm h0 t).le⟩
  · rintro ⟨ray⟩
    exact ray.eventuallyZeroCarry

end LongReturnSuccessorZeroCarry
end KontoroC
