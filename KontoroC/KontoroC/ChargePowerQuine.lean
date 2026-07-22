/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerCongruence

/-!
# Perfect-power closure obstruction for the charge bouncer

This file formalizes the exact reproduction identity for the ansatz
`u = F*r^23` and the finite-field sieve for the shortest recharge.  The sieve
eliminates twenty-two of the twenty-three exponent classes.  It deliberately
leaves the generalized Fermat equation

`3^15 X^23 - 2^16 Y^23 = 5`

open: no local finite-field obstruction for that final class is asserted.
-/

namespace KontoroC

namespace ChargePowerQuine

def A : ℤ := 3 ^ 114
def B : ℤ := 2 ^ 154
def C : ℤ := 3 ^ 17
def D : ℤ := 2 ^ 23
def F : ℤ := chargeFixedDivisor

theorem A_sub_B : A - B = 5 * F := by
  norm_num [A, B, F, chargeFixedDivisor]

/-- Eliminating the collision quotient from the two radix equations gives
the denominator-cleared perfect-power reproduction equation. -/
theorem power_quine_identity
    {m m' h : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B ^ h * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A ^ h * q) :
    F * (A ^ h * C ^ m * r ^ 23 - B ^ h * D ^ m' * r' ^ 23) =
      A ^ h - B ^ h := by
  linear_combination (A ^ h) * hin - (B ^ h) * hout

/-- At the shortest recharge, cancellation of the nonzero fixed divisor
reduces the reproduction identity to the concrete generalized Fermat family.
-/
theorem shortest_recharge_equation
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A * q) :
    A * C ^ m * r ^ 23 - B * D ^ m' * r' ^ 23 = 5 := by
  have h := power_quine_identity (h := 1) hin hout
  simp only [pow_one] at h
  rw [A_sub_B] at h
  exact mul_left_cancel₀ (by norm_num [F, chargeFixedDivisor]) h

/-- The reduced equation tested by the finite-field sieve. -/
abbrev ReducedEquation (e : Fin 23) (R : Type*) [CommRing R]
    (x y : R) : Prop :=
  (3 : R) ^ e.val * x ^ 23 = 5 + 2 ^ 16 * y ^ 23

/-- Complete local calculation at `p=47`. -/
theorem sieve47 (e : Fin 23) (x y : ZMod 47)
    (h : ReducedEquation e (ZMod 47) x y) :
    e.val = 4 ∨ e.val = 6 ∨ e.val = 15 := by
  revert e x y
  decide

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The prime `139` removes the class `e=4` left by `p=47`. -/
theorem sieve139_not_four (x y : ZMod 139) :
    ¬ ReducedEquation ⟨4, by omega⟩ (ZMod 139) x y := by
  revert x y
  decide

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The prime `461` removes the class `e=6` left by the first two primes. -/
theorem sieve461_not_six (x y : ZMod 461) :
    ¬ ReducedEquation ⟨6, by omega⟩ (ZMod 461) x y := by
  revert x y
  decide

/-- Combining the three complete residue calculations leaves only `e=15`.
-/
theorem reduced_exponent_eq_fifteen (e : Fin 23) (x y : ℤ)
    (h : ReducedEquation e ℤ x y) : e.val = 15 := by
  have h47 : ReducedEquation e (ZMod 47) (x : ZMod 47) (y : ZMod 47) := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod 47)) h
    norm_num at hc
    exact hc
  rcases sieve47 e _ _ h47 with he | he | he
  · have he' : e = ⟨4, by omega⟩ := Fin.ext he
    rw [he'] at h ⊢
    have h139 : ReducedEquation ⟨4, by omega⟩ (ZMod 139)
        (x : ZMod 139) (y : ZMod 139) := by
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod 139)) h
      norm_num at hc
      exact hc
    exact (sieve139_not_four _ _ h139).elim
  · have he' : e = ⟨6, by omega⟩ := Fin.ext he
    rw [he'] at h ⊢
    have h461 : ReducedEquation ⟨6, by omega⟩ (ZMod 461)
        (x : ZMod 461) (y : ZMod 461) := by
      have hc := congrArg (fun z : ℤ ↦ (z : ZMod 461)) h
      norm_num at hc
      exact hc
    exact (sieve461_not_six _ _ h461).elim
  · exact he

/-- Absorb a complete `n`th power from a coefficient into the variable. -/
theorem absorb_complete_power (a r : ℤ) (n q s : ℕ) :
    a ^ (s + n * q) * r ^ n = a ^ s * (a ^ q * r) ^ n := by
  rw [pow_add, pow_mul, mul_pow]
  ring

/-- The shortest-recharge generalized Fermat equation reduces to one of the
twenty-three equations indexed by `(114+17m) mod 23`. -/
theorem shortest_equation_reduces
    {m m' : ℕ} {r r' : ℤ}
    (h : (3 : ℤ) ^ (114 + 17 * m) * r ^ 23 =
      5 + 2 ^ (154 + 23 * m') * r' ^ 23) :
    let k := 114 + 17 * m
    let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
    ReducedEquation e ℤ
      (3 ^ (k / 23) * r) (2 ^ (6 + m') * r') := by
  dsimp only
  have hk : (114 + 17 * m) % 23 + 23 * ((114 + 17 * m) / 23) =
      114 + 17 * m := Nat.mod_add_div _ _
  have htwo : 16 + 23 * (6 + m') = 154 + 23 * m' := by omega
  rw [← hk, ← htwo] at h
  rw [absorb_complete_power, absorb_complete_power] at h
  exact h

/-- Any shortest-recharge perfect-power transition lies in the single local
class `m = 5 (mod 23)`.  This is the semantic endpoint of the three-prime
sieve; it does not assert that the surviving class has a solution. -/
theorem shortest_recharge_opcode_mod_twentyThree
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A * q) :
    m % 23 = 5 := by
  have hshort := shortest_recharge_equation hin hout
  have hfamily : (3 : ℤ) ^ (114 + 17 * m) * r ^ 23 =
      5 + 2 ^ (154 + 23 * m') * r' ^ 23 := by
    rw [A, B, C, D] at hshort
    rw [← pow_mul (3 : ℤ) 17 m, ← pow_mul (2 : ℤ) 23 m',
      ← pow_add, ← pow_add] at hshort
    linarith
  let k := 114 + 17 * m
  let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
  have hred : ReducedEquation e ℤ
      (3 ^ (k / 23) * r) (2 ^ (6 + m') * r') := by
    exact shortest_equation_reduces hfamily
  have he : e.val = 15 := reduced_exponent_eq_fifteen e _ _ hred
  dsimp [e, k] at he
  omega

/-- The sole generalized Fermat equation not removed by the local sieve. -/
def PQ4Solution : Prop :=
  ∃ x y : ℤ, ReducedEquation ⟨15, by omega⟩ ℤ x y

/-- Every accepted shortest-recharge transition preserving the perfect-power
family supplies an integer solution to PQ4.  The converse is not claimed. -/
theorem shortest_recharge_supplies_PQ4
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A * q) :
    PQ4Solution := by
  have hshort := shortest_recharge_equation hin hout
  have hfamily : (3 : ℤ) ^ (114 + 17 * m) * r ^ 23 =
      5 + 2 ^ (154 + 23 * m') * r' ^ 23 := by
    rw [A, B, C, D] at hshort
    rw [← pow_mul (3 : ℤ) 17 m, ← pow_mul (2 : ℤ) 23 m',
      ← pow_add, ← pow_add] at hshort
    linarith
  let k := 114 + 17 * m
  let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
  let x : ℤ := 3 ^ (k / 23) * r
  let y : ℤ := 2 ^ (6 + m') * r'
  have hred : ReducedEquation e ℤ x y := by
    exact shortest_equation_reduces hfamily
  have he : e = ⟨15, by omega⟩ :=
    Fin.ext (reduced_exponent_eq_fifteen e x y hred)
  exact ⟨x, y, by simpa [he] using hred⟩

/-- Therefore an unconditional no-solution theorem for PQ4 would kill this
shortest-recharge reproducing rail. -/
theorem no_shortest_recharge_power_quine (hPQ4 : ¬ PQ4Solution) :
    ¬ ∃ (m m' : ℕ) (r r' q : ℤ),
      C ^ m * (F * r ^ 23) = 1 + B * q ∧
      D ^ m' * (F * r' ^ 23) = 1 + A * q := by
  rintro ⟨m, m', r, r', q, hin, hout⟩
  exact hPQ4 (shortest_recharge_supplies_PQ4 hin hout)

end ChargePowerQuine

end KontoroC
