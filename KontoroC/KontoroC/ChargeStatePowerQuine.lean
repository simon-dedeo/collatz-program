/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePowerResonance

/-!
# A size obstruction for the public-state 23rd-power quine

This file treats the public-state ansatz `y = s^23`, `q = t^23`.  It proves
that the pure coefficient subclass whose opcode is a positive multiple of 23
cannot satisfy both the required 2-adic divisibility and the transition
equation.  The remaining 22 residue classes are not addressed.
-/

namespace KontoroC

namespace ChargeStatePowerQuine

private theorem pow_pred_le_succ_pow_sub (x : ℕ) :
    x ^ 22 ≤ (x + 1) ^ 23 - x ^ 23 := by
  apply Nat.le_sub_of_add_le
  calc
    x ^ 22 + x ^ 23 = x ^ 22 + x ^ 22 * x := by
      rw [show x ^ 23 = x ^ 22 * x by exact pow_succ x 22]
    _ = x ^ 22 * (x + 1) := by ring
    _ ≤ (x + 1) ^ 22 * (x + 1) :=
      Nat.mul_le_mul_right (x + 1) (Nat.pow_le_pow_left (Nat.le_succ x) 22)
    _ = (x + 1) ^ 23 := (pow_succ (x + 1) 22).symm

private theorem three_pow_lt_two_pow_double {n : ℕ} (hn : 0 < n) :
    3 ^ n < 2 ^ (2 * n) := by
  have h := Nat.pow_lt_pow_left (by omega : 3 < 4) (Nat.ne_of_gt hn)
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    ← pow_mul (2 : ℕ) 2 n] at h
  exact h

/-- Every public-state transition equation splits into a complete-power part
`k = m / 23` and one of 23 genuinely scaled equations indexed by
`r = m % 23`. -/
theorem state_power_equation_reduces
    {m s t : ℕ}
    (heq : (3 ^ 17) ^ m * (s ^ 23 + 1) =
      (2 ^ 23) ^ m * (1 + (2 ^ 154 * t) ^ 23)) :
    let k := m / 23
    let r := m % 23
    3 ^ (17 * r) *
        ((3 ^ (17 * k) * s) ^ 23 + (3 ^ (17 * k)) ^ 23) =
      (2 ^ (m + 154) * t) ^ 23 + (2 ^ m) ^ 23 := by
  dsimp only
  have hm : m % 23 + 23 * (m / 23) = m := Nat.mod_add_div _ _
  have hC : (3 ^ 17) ^ m =
      3 ^ (17 * (m % 23)) * (3 ^ (17 * (m / 23))) ^ 23 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hD : (2 ^ 23) ^ m = (2 ^ m) ^ 23 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hY : (2 ^ (m + 154) * t) ^ 23 =
      (2 ^ m) ^ 23 * (2 ^ 154 * t) ^ 23 := by
    rw [pow_add, mul_assoc, mul_pow]
  rw [hC, hD] at heq
  rw [mul_add, mul_pow, hY]
  simpa [mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq

/-- Additive form of the scaled equation.  In the number field with
`θ^23 = a`, its two sides are the corresponding pure-binomial norms. -/
theorem scaled_equation_iff_gap (a X U Y Z : ℤ) :
    a * (X ^ 23 + U ^ 23) = Y ^ 23 + Z ^ 23 ↔
      Y ^ 23 - a * X ^ 23 = a * U ^ 23 - Z ^ 23 := by
  constructor <;> intro h <;> linarith

/-- The public-state reproduction equation in the coefficient class
`m = 23*k`, together with its forced 2-adic divisibility, has no positive
solution when `k > 0`. -/
theorem no_state_power_quine_of_m_multiple_23
    (k s t : ℕ) (hk : 0 < k) (hs : 0 < s) (ht : 0 < t)
    (hval : 2 ^ (529 * k) ∣ s + 1)
    (heq : (3 ^ (17 * k) * s) ^ 23 + (3 ^ (17 * k)) ^ 23 =
      (2 ^ (23 * k + 154) * t) ^ 23 + (2 ^ (23 * k)) ^ 23) : False := by
  let U := 3 ^ (17 * k)
  let Z := 2 ^ (23 * k)
  let X := U * s
  let Y := 2 ^ (23 * k + 154) * t
  have hZU : Z < U := by
    dsimp [Z, U]
    rw [pow_mul (2 : ℕ) 23 k, pow_mul (3 : ℕ) 17 k]
    exact Nat.pow_lt_pow_left (by omega : 2 ^ 23 < 3 ^ 17)
      (Nat.ne_of_gt hk)
  have hXpos : 0 < X := by positivity
  have hYpos : 0 < Y := by positivity
  have hYX : X < Y := by
    by_contra hnot
    have hYXle : Y ≤ X := Nat.le_of_not_gt hnot
    have hpYX : Y ^ 23 ≤ X ^ 23 := Nat.pow_le_pow_left hYXle 23
    have hpZU : Z ^ 23 < U ^ 23 := Nat.pow_lt_pow_left hZU (by omega)
    dsimp [X, Y, U, Z] at hpYX hpZU
    omega
  have hdiffLower : X ^ 22 ≤ Y ^ 23 - X ^ 23 := by
    have hsucc : X + 1 ≤ Y := hYX
    have hpSucc : (X + 1) ^ 23 ≤ Y ^ 23 := Nat.pow_le_pow_left hsucc 23
    exact (pow_pred_le_succ_pow_sub X).trans
      (Nat.sub_le_sub_right hpSucc (X ^ 23))
  have hdiffEq : Y ^ 23 - X ^ 23 = U ^ 23 - Z ^ 23 := by
    dsimp [X, Y, U, Z]
    omega
  have hdiffUpper : U ^ 23 - Z ^ 23 < U ^ 23 := by
    exact Nat.sub_lt (by positivity) (by positivity)
  have hXU : X ^ 22 < U ^ 23 := by
    calc
      X ^ 22 ≤ Y ^ 23 - X ^ 23 := hdiffLower
      _ = U ^ 23 - Z ^ 23 := hdiffEq
      _ < U ^ 23 := hdiffUpper
  have hsU : s ^ 22 < U := by
    have hUpos : 0 < U ^ 22 := by positivity
    rw [show X ^ 22 = U ^ 22 * s ^ 22 by simp [X, mul_pow],
      show U ^ 23 = U ^ 22 * U by rw [pow_succ]] at hXU
    exact (Nat.mul_lt_mul_left hUpos).mp hXU
  have hdvdle : 2 ^ (529 * k) ≤ s + 1 :=
    Nat.le_of_dvd (by omega) hval
  have hsmallLarge : 2 ^ (528 * k) + 1 ≤ 2 ^ (529 * k) := by
    have hexp : 528 * k < 529 * k := by omega
    exact (Nat.lt_iff_add_one_le.mp
      ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hexp))
  have hsLower : 2 ^ (528 * k) ≤ s := by omega
  have hsPowLower : 2 ^ (11616 * k) ≤ s ^ 22 := by
    have hp := Nat.pow_le_pow_left hsLower 22
    have hexp : 528 * k * 22 = 11616 * k := by omega
    rw [← pow_mul] at hp
    rw [hexp] at hp
    exact hp
  have hULower : U < 2 ^ (11616 * k) := by
    have h3 : 3 ^ (17 * k) < 2 ^ (2 * (17 * k)) :=
      three_pow_lt_two_pow_double (by omega)
    have hexp : 2 * (17 * k) < 11616 * k := by omega
    have h2 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hexp
    exact h3.trans h2
  exact Nat.not_lt_of_ge hsPowLower (hsU.trans hULower)

/-- Version stated directly with the public-state transition equation, before
normalization as an equal sum of 23rd powers. -/
theorem no_state_power_quine_equation_of_m_multiple_23
    (k s t : ℕ) (hk : 0 < k) (hs : 0 < s) (ht : 0 < t)
    (hval : 2 ^ (529 * k) ∣ s + 1)
    (heq : (3 ^ 17) ^ (23 * k) * (s ^ 23 + 1) =
      (2 ^ 23) ^ (23 * k) * (1 + (2 ^ 154 * t) ^ 23)) : False := by
  have hC : (3 ^ 17) ^ (23 * k) =
      (3 ^ (17 * k)) ^ 23 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hD : (2 ^ 23) ^ (23 * k) =
      (2 ^ (23 * k)) ^ 23 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hY : (2 ^ (23 * k + 154) * t) ^ 23 =
      (2 ^ (23 * k)) ^ 23 * (2 ^ 154 * t) ^ 23 := by
    rw [pow_add, mul_assoc, mul_pow]
  have hnormalized :
      (3 ^ (17 * k) * s) ^ 23 + (3 ^ (17 * k)) ^ 23 =
        (2 ^ (23 * k + 154) * t) ^ 23 + (2 ^ (23 * k)) ^ 23 := by
    rw [hC, hD] at heq
    rw [mul_pow, hY]
    simpa [mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  exact no_state_power_quine_of_m_multiple_23 k s t hk hs ht hval hnormalized

end ChargeStatePowerQuine

end KontoroC
