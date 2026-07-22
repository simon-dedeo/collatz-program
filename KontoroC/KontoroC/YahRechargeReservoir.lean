/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRechargeRegister

/-!
# The recharge amplifier emits a triadic reservoir

The normalized recharge register has exact 3-adic valuation two.  Every
subsequent odd shortcut multiplies the defect by three while dividing it by
two, so an all-odd prefix of `J` steps leaves valuation `J+2`.  This is the
arithmetic content of QM19.
-/

namespace KontoroC
namespace YahRechargeReservoir

open YahRechargeRegister
open YahBattery
open YahQueueMacro

private theorem nine_pow_factor (q : ℕ) (hq : 0 < q) :
    9 ^ q = 3 * 3 ^ (2 * q - 1) := by
  calc
    9 ^ q = (3 ^ 2) ^ q := by norm_num
    _ = 3 ^ (2 * q) := by rw [pow_mul]
    _ = 3 ^ (1 + (2 * q - 1)) := by congr 1 <;> omega
    _ = 3 * 3 ^ (2 * q - 1) := by rw [pow_add, pow_one]

private theorem inner_mod_three (q : ℕ) (hq : 0 < q) :
    (41 * 3 ^ (2 * q - 1) + 5) % 3 = 2 := by
  have hn : 0 < 2 * q - 1 := by omega
  have hdvd : 3 ∣ 3 ^ (2 * q - 1) := dvd_pow (dvd_refl 3) hn.ne'
  have hzero : 3 ^ (2 * q - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  omega

/-- Before dyadic normalization, the raw lift has exact 3-adic valuation
two. -/
theorem rawRegister_three_val (K q₀ t : ℕ)
    (hq : 0 < q₀ + 2 ^ (K + 2) * t) :
    padicValNat 3 (rawRegister K q₀ t) = 2 := by
  let q := q₀ + 2 ^ (K + 2) * t
  let C := 41 * 3 ^ (2 * q - 1) + 5
  have hp := nine_pow_factor q (by simpa [q] using hq)
  have hraw : rawRegister K q₀ t = 9 * C := by
    dsimp [rawRegister, q, C] at hp ⊢
    rw [hp]
    ring
  have hCmod := inner_mod_three q (by simpa [q] using hq)
  have hC : C ≠ 0 := by dsimp [C]; positivity
  have hC3 : ¬3 ∣ C := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  rw [hraw, show 9 = 3 ^ 2 by norm_num,
    padicValNat.mul (by positivity) hC, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hC3]

/-- Dyadic normalization does not change the 3-adic valuation. -/
theorem normalizedRegister_three_val (K q₀ t : ℕ)
    (hq : 0 < q₀ + 2 ^ (K + 2) * t)
    (hdiv : 2 ^ (K + 5) ∣ rawRegister K q₀ t) :
    padicValNat 3 (normalizedRegister K q₀ t) = 2 := by
  have heq := Nat.mul_div_cancel' hdiv
  have hv := congrArg (padicValNat 3) heq
  have hP : 2 ^ (K + 5) ≠ 0 := by positivity
  have hrawpos : 0 < rawRegister K q₀ t := by
    dsimp [rawRegister]
    positivity
  have hApos : 0 < rawRegister K q₀ t / 2 ^ (K + 5) :=
    Nat.div_pos (Nat.le_of_dvd hrawpos hdiv) (by positivity)
  have hA : rawRegister K q₀ t / 2 ^ (K + 5) ≠ 0 := hApos.ne'
  rw [padicValNat.mul hP hA] at hv
  have hPval : padicValNat 3 (2 ^ (K + 5)) = 0 :=
    padicValNat_prime_prime_pow (p := 3) (q := 2) (K + 5) (by omega)
  rw [hPval, zero_add, rawRegister_three_val K q₀ t hq] at hv
  simpa [normalizedRegister] using hv

/-- QM19 in its generic arithmetic form: an all-odd defect balance adds one
factor of three per shortcut step. -/
theorem finish_three_val_of_allOdd_balance (start finish : List Trit) (J : ℕ)
    (hbalance : 2 ^ J * defect finish = 3 ^ J * defect start)
    (hstart : padicValNat 3 (defect start) = 2) :
    padicValNat 3 (defect finish) = J + 2 := by
  have hv := congrArg (padicValNat 3) hbalance
  have h2 : 2 ^ J ≠ 0 := by positivity
  have h3 : 3 ^ J ≠ 0 := by positivity
  have hdf : defect finish ≠ 0 := (defect_pos finish).ne'
  have hds : defect start ≠ 0 := (defect_pos start).ne'
  rw [padicValNat.mul h2 hdf, padicValNat.mul h3 hds,
    padicValNat.prime_pow] at hv
  have h2val : padicValNat 3 (2 ^ J) = 0 :=
    padicValNat_prime_prime_pow (p := 3) (q := 2) J (by omega)
  rw [h2val, zero_add, hstart] at hv
  omega

end YahRechargeReservoir
end KontoroC
