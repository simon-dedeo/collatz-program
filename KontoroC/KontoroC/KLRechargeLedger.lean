/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.PredecessorTransfer

/-!
# Exact dyadic ledger for the three reversed KL branches

For a positive Syracuse target `a = 2 (mod 3)`, the KL predecessor split has
three principal children:

* transport: `4*a`, returning to `a` in two halving steps;
* retarded: `2*((2*a-1)/3)`, returning in one halving and one odd step;
* advanced: `(2*a-1)/3`, returning in one odd step.

The translated coordinate used by the minus-one rail is `a+1`.  The advanced
branch consumes one unit of its dyadic valuation.  The other two branches can
recharge it only through high dyadic divisibility of `child+2` or `child+4`.
Thus every recharge is concentrated near a negative predecessor of the
exceptional point `-1`, rather than being a free reset of the counter.
-/

namespace KontoroC
namespace KLRechargeLedger

open CleanLean.Collatz
open CleanLean.KL

def advancedChild (a : ℕ) : ℕ := (2 * a - 1) / 3

def retardedChild (a : ℕ) : ℕ := 2 * advancedChild a

def transportChild (a : ℕ) : ℕ := 4 * a

/-! ## Literal Syracuse semantics -/

theorem advancedChild_forward {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) :
    syracuseStep (advancedChild a) = a := by
  simpa [advancedChild] using syracuseStep_oddPredecessor ha ha3

theorem retardedChild_first_step (a : ℕ) :
    syracuseStep (retardedChild a) = advancedChild a := by
  simp [retardedChild, syracuseStep]

theorem retardedChild_forward {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) :
    syracuseStep^[2] (retardedChild a) = a := by
  rw [show 2 = 1 + 1 by omega, Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [retardedChild_first_step, advancedChild_forward ha ha3]

theorem transportChild_forward (a : ℕ) :
    syracuseStep^[2] (transportChild a) = a := by
  simpa [transportChild] using iterate_syracuse_two_pow_mul a 2

/-! ## Exact translated-coordinate identities -/

theorem advanced_coordinate_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    3 * (advancedChild a + 1) = 2 * (a + 1) := by
  have hthree := three_mul_oddPredecessor ha ha3
  simp only [advancedChild]
  omega

theorem retarded_coordinate_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    4 * (a + 1) = 3 * (retardedChild a + 2) := by
  have hthree := three_mul_oddPredecessor ha ha3
  simp only [retardedChild, advancedChild]
  omega

theorem transport_coordinate_balance (a : ℕ) :
    4 * (a + 1) = transportChild a + 4 := by
  simp [transportChild]
  ring

/-! ## Dyadic resource identities -/

theorem advanced_valuation_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    padicValNat 2 (advancedChild a + 1) =
      1 + padicValNat 2 (a + 1) := by
  have hv := congrArg (padicValNat 2) (advanced_coordinate_balance ha ha3)
  have hval3 : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hval2 : padicValNat 2 2 = 1 := by
    simpa using (padicValNat.prime_pow (p := 2) 1)
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.mul (by norm_num) (by positivity),
    hval3, hval2, zero_add] at hv
  exact hv

theorem retarded_valuation_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    padicValNat 2 (retardedChild a + 2) =
      2 + padicValNat 2 (a + 1) := by
  have hv := congrArg (padicValNat 2) (retarded_coordinate_balance ha ha3)
  have hval4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  have hval3 : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.mul (by norm_num) (by positivity),
    hval4, hval3, zero_add] at hv
  exact hv.symm

theorem transport_valuation_balance (a : ℕ) :
    padicValNat 2 (transportChild a + 4) =
      2 + padicValNat 2 (a + 1) := by
  have hv := congrArg (padicValNat 2) (transport_coordinate_balance a)
  have hval4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  rw [padicValNat.mul (by norm_num) (by positivity), hval4] at hv
  exact hv.symm

/-! ## Exponential ordinary-size cost of recharge -/

theorem advanced_shadow_size {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    2 ^ (1 + padicValNat 2 (a + 1)) ≤ advancedChild a + 1 := by
  rw [← advanced_valuation_balance ha ha3]
  exact Nat.le_of_dvd (by positivity) pow_padicValNat_dvd

theorem retarded_recharge_size {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    2 ^ (2 + padicValNat 2 (a + 1)) ≤ retardedChild a + 2 := by
  rw [← retarded_valuation_balance ha ha3]
  exact Nat.le_of_dvd (by positivity) pow_padicValNat_dvd

theorem transport_recharge_size (a : ℕ) :
    2 ^ (2 + padicValNat 2 (a + 1)) ≤ transportChild a + 4 := by
  rw [← transport_valuation_balance a]
  exact Nat.le_of_dvd (by positivity) pow_padicValNat_dvd

end KLRechargeLedger
end KontoroC
