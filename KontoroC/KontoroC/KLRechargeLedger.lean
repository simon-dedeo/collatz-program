/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.PredecessorTransfer
import KontoroC.KLMinusOneRail

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

/-! ## Complementary ternary ledger and the primitive `(2,3)` core -/

theorem advanced_three_valuation_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    padicValNat 3 (a + 1) =
      1 + padicValNat 3 (advancedChild a + 1) := by
  have hv := congrArg (padicValNat 3) (advanced_coordinate_balance ha ha3)
  have hval3 : padicValNat 3 3 = 1 := by
    simpa using (padicValNat.prime_pow (p := 3) 1)
  have hval2 : padicValNat 3 2 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.mul (by norm_num) (by positivity),
    hval3, hval2, zero_add] at hv
  exact hv.symm

theorem retarded_three_valuation_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    padicValNat 3 (a + 1) =
      1 + padicValNat 3 (retardedChild a + 2) := by
  have hv := congrArg (padicValNat 3) (retarded_coordinate_balance ha ha3)
  have hval4 : padicValNat 3 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hval3 : padicValNat 3 3 = 1 := by
    simpa using (padicValNat.prime_pow (p := 3) 1)
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.mul (by norm_num) (by positivity),
    hval4, hval3, zero_add] at hv
  exact hv

theorem transport_three_valuation_balance (a : ℕ) :
    padicValNat 3 (transportChild a + 4) =
      padicValNat 3 (a + 1) := by
  have hv := congrArg (padicValNat 3) (transport_coordinate_balance a)
  have hval4 : padicValNat 3 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [padicValNat.mul (by norm_num) (by positivity), hval4, zero_add] at hv
  exact hv.symm

/-- The part of a positive natural supported at the primes two and three. -/
def content23 (z : ℕ) : ℕ :=
  2 ^ padicValNat 2 z * 3 ^ padicValNat 3 z

/-- The residual cofactor after removing all powers of two and three. -/
def core23 (z : ℕ) : ℕ := z / content23 z

theorem content23_pos (z : ℕ) : 0 < content23 z := by
  exact Nat.mul_pos (by positivity) (by positivity)

theorem content23_dvd (z : ℕ) : content23 z ∣ z := by
  apply (Nat.coprime_pow_primes
    (padicValNat 2 z) (padicValNat 3 z)
    Nat.prime_two Nat.prime_three (by norm_num)).mul_dvd_of_dvd_of_dvd
  · exact pow_padicValNat_dvd
  · exact pow_padicValNat_dvd

/-- The two prime-power ledgers cannot be budgeted independently of
ordinary height. -/
theorem content23_le {z : ℕ} (hz : 0 < z) : content23 z ≤ z :=
  Nat.le_of_dvd hz (content23_dvd z)

theorem two_pow_val_mul_three_pow_val_le {z : ℕ} (hz : 0 < z) :
    2 ^ padicValNat 2 z * 3 ^ padicValNat 3 z ≤ z := by
  exact content23_le hz

theorem content23_mul_core23 (z : ℕ) :
    content23 z * core23 z = z := by
  exact Nat.mul_div_cancel' (content23_dvd z)

/-- A primitive core is unchanged across an exact `3*x = 2*z` radix
transfer. -/
theorem core23_eq_of_three_mul_eq_two_mul {x z : ℕ}
    (hx : 0 < x) (hz : 0 < z) (h : 3 * x = 2 * z) :
    core23 x = core23 z := by
  have hv2 := congrArg (padicValNat 2) h
  have hv3 := congrArg (padicValNat 3) h
  have h2v3 : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h2v2 : padicValNat 2 2 = 1 := by
    simpa using (padicValNat.prime_pow (p := 2) 1)
  have h3v2 : padicValNat 3 2 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h3v3 : padicValNat 3 3 = 1 := by
    simpa using (padicValNat.prime_pow (p := 3) 1)
  rw [padicValNat.mul (by norm_num) hx.ne',
    padicValNat.mul (by norm_num) hz.ne', h2v3, h2v2, zero_add] at hv2
  rw [padicValNat.mul (by norm_num) hx.ne',
    padicValNat.mul (by norm_num) hz.ne', h3v3, h3v2, zero_add] at hv3
  have hc : 3 * content23 x = 2 * content23 z := by
    rw [content23, content23, hv2, ← hv3]
    simp only [pow_add, pow_one]
    ring
  have fx := content23_mul_core23 x
  have fz := content23_mul_core23 z
  have hs : (3 * content23 x) * core23 x =
      (2 * content23 z) * core23 z := by
    calc
      _ = 3 * (content23 x * core23 x) := by ring
      _ = 3 * x := by rw [fx]
      _ = 2 * z := h
      _ = 2 * (content23 z * core23 z) := by rw [fz]
      _ = _ := by ring
  rw [hc] at hs
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos z)) hs

/-- A primitive core is unchanged across an exact `3*x = 4*z` radix
transfer. -/
theorem core23_eq_of_three_mul_eq_four_mul {x z : ℕ}
    (hx : 0 < x) (hz : 0 < z) (h : 3 * x = 4 * z) :
    core23 x = core23 z := by
  have hv2 := congrArg (padicValNat 2) h
  have hv3 := congrArg (padicValNat 3) h
  have h2v3 : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h2v4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  have h3v4 : padicValNat 3 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h3v3 : padicValNat 3 3 = 1 := by
    simpa using (padicValNat.prime_pow (p := 3) 1)
  rw [padicValNat.mul (by norm_num) hx.ne',
    padicValNat.mul (by norm_num) hz.ne', h2v3, h2v4, zero_add] at hv2
  rw [padicValNat.mul (by norm_num) hx.ne',
    padicValNat.mul (by norm_num) hz.ne', h3v3, h3v4, zero_add] at hv3
  have hc : 3 * content23 x = 4 * content23 z := by
    rw [content23, content23, hv2, ← hv3]
    simp only [pow_add, pow_one]
    ring
  have fx := content23_mul_core23 x
  have fz := content23_mul_core23 z
  have hs : (3 * content23 x) * core23 x =
      (4 * content23 z) * core23 z := by
    calc
      _ = 3 * (content23 x * core23 x) := by ring
      _ = 3 * x := by rw [fx]
      _ = 4 * z := h
      _ = 4 * (content23 z * core23 z) := by rw [fz]
      _ = _ := by ring
  rw [hc] at hs
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos z)) hs

/-- A primitive core is unchanged across multiplication by four. -/
theorem core23_eq_of_eq_four_mul {x z : ℕ}
    (hx : 0 < x) (hz : 0 < z) (h : x = 4 * z) :
    core23 x = core23 z := by
  have hv2 := congrArg (padicValNat 2) h
  have hv3 := congrArg (padicValNat 3) h
  have h2v4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  have h3v4 : padicValNat 3 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [padicValNat.mul (by norm_num) hz.ne', h2v4] at hv2
  rw [padicValNat.mul (by norm_num) hz.ne', h3v4, zero_add] at hv3
  have hc : content23 x = 4 * content23 z := by
    rw [content23, content23, hv2, hv3]
    simp only [pow_add, pow_one]
    ring
  have fx := content23_mul_core23 x
  have fz := content23_mul_core23 z
  have hs : content23 x * core23 x =
      (4 * content23 z) * core23 z := by
    calc
      _ = x := fx
      _ = 4 * z := h
      _ = 4 * (content23 z * core23 z) := by rw [fz]
      _ = _ := by ring
  rw [hc] at hs
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos z)) hs

/-! ## Arbitrary moving negative center -/

def advancedCenter (h : ℕ) : ℕ := (2 * h + 1) / 3

def retardedCenter (h : ℕ) : ℕ := (4 * h + 2) / 3

def transportCenter (h : ℕ) : ℕ := 4 * h

theorem three_mul_advancedCenter {h : ℕ} (hh3 : h % 3 = 1) :
    3 * advancedCenter h = 2 * h + 1 := by
  apply Nat.mul_div_cancel'
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

theorem three_mul_retardedCenter {h : ℕ} (hh3 : h % 3 = 1) :
    3 * retardedCenter h = 4 * h + 2 := by
  apply Nat.mul_div_cancel'
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

theorem advanced_moving_center_balance {a h : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) (hh3 : h % 3 = 1) :
    3 * (advancedChild a + advancedCenter h) = 2 * (a + h) := by
  rw [mul_add, three_mul_advancedCenter hh3]
  have haeq := three_mul_oddPredecessor ha ha3
  simp only [advancedChild]
  omega

theorem retarded_moving_center_balance {a h : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) (hh3 : h % 3 = 1) :
    3 * (retardedChild a + retardedCenter h) = 4 * (a + h) := by
  rw [mul_add, three_mul_retardedCenter hh3]
  have haeq := three_mul_oddPredecessor ha ha3
  simp only [retardedChild, advancedChild]
  omega

theorem transport_moving_center_balance (a h : ℕ) :
    transportChild a + transportCenter h = 4 * (a + h) := by
  simp [transportChild, transportCenter]
  ring

theorem advanced_moving_center_core23 {a h : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) (hh3 : h % 3 = 1) :
    core23 (advancedChild a + advancedCenter h) = core23 (a + h) := by
  apply core23_eq_of_three_mul_eq_two_mul
  · have hh : 0 < h := by omega
    have hcentereq := three_mul_advancedCenter hh3
    have hc : 0 < advancedCenter h := by
      apply Nat.pos_of_mul_pos_left
      rw [hcentereq]
      positivity
    positivity
  · positivity
  · exact advanced_moving_center_balance ha ha3 hh3

theorem retarded_moving_center_core23 {a h : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) (hh3 : h % 3 = 1) :
    core23 (retardedChild a + retardedCenter h) = core23 (a + h) := by
  apply core23_eq_of_three_mul_eq_four_mul
  · have hcentereq := three_mul_retardedCenter hh3
    have hc : 0 < retardedCenter h := by
      apply Nat.pos_of_mul_pos_left
      rw [hcentereq]
      positivity
    positivity
  · positivity
  · exact retarded_moving_center_balance ha ha3 hh3

theorem transport_moving_center_core23 {a h : ℕ} (ha : 0 < a)
    (hh : 0 < h) :
    core23 (transportChild a + transportCenter h) = core23 (a + h) := by
  apply core23_eq_of_eq_four_mul
  · rw [transport_moving_center_balance]
    positivity
  · positivity
  · exact transport_moving_center_balance a h

private theorem advanced_content_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    3 * content23 (advancedChild a + 1) = 2 * content23 (a + 1) := by
  rw [content23, content23, advanced_valuation_balance ha ha3,
    advanced_three_valuation_balance ha ha3]
  simp only [pow_add, pow_one]
  ring

private theorem retarded_content_balance {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    3 * content23 (retardedChild a + 2) = 4 * content23 (a + 1) := by
  rw [content23, content23, retarded_valuation_balance ha ha3,
    retarded_three_valuation_balance ha ha3]
  simp only [pow_add, pow_one]
  ring

private theorem transport_content_balance (a : ℕ) :
    content23 (transportChild a + 4) = 4 * content23 (a + 1) := by
  rw [content23, content23, transport_valuation_balance,
    transport_three_valuation_balance]
  simp only [pow_add, pow_one]
  ring

theorem advanced_core23_invariant {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    core23 (advancedChild a + 1) = core23 (a + 1) := by
  have hcoord := advanced_coordinate_balance ha ha3
  have hcontent := advanced_content_balance ha ha3
  have hx := content23_mul_core23 (advancedChild a + 1)
  have hz := content23_mul_core23 (a + 1)
  have hscaled :
      (3 * content23 (advancedChild a + 1)) *
          core23 (advancedChild a + 1) =
        (2 * content23 (a + 1)) * core23 (a + 1) := by
    calc
      _ = 3 * (content23 (advancedChild a + 1) *
          core23 (advancedChild a + 1)) := by ring
      _ = 3 * (advancedChild a + 1) := by rw [hx]
      _ = 2 * (a + 1) := hcoord
      _ = 2 * (content23 (a + 1) * core23 (a + 1)) := by rw [hz]
      _ = _ := by ring
  rw [hcontent] at hscaled
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos (a + 1))) hscaled

theorem retarded_core23_invariant {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    core23 (retardedChild a + 2) = core23 (a + 1) := by
  have hcoord := retarded_coordinate_balance ha ha3
  have hcontent := retarded_content_balance ha ha3
  have hx := content23_mul_core23 (retardedChild a + 2)
  have hz := content23_mul_core23 (a + 1)
  have hscaled :
      (3 * content23 (retardedChild a + 2)) *
          core23 (retardedChild a + 2) =
        (4 * content23 (a + 1)) * core23 (a + 1) := by
    calc
      _ = 3 * (content23 (retardedChild a + 2) *
          core23 (retardedChild a + 2)) := by ring
      _ = 3 * (retardedChild a + 2) := by rw [hx]
      _ = 4 * (a + 1) := hcoord.symm
      _ = 4 * (content23 (a + 1) * core23 (a + 1)) := by rw [hz]
      _ = _ := by ring
  rw [hcontent] at hscaled
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos (a + 1))) hscaled

theorem transport_core23_invariant (a : ℕ) :
    core23 (transportChild a + 4) = core23 (a + 1) := by
  have hcoord := transport_coordinate_balance a
  have hcontent := transport_content_balance a
  have hx := content23_mul_core23 (transportChild a + 4)
  have hz := content23_mul_core23 (a + 1)
  have hscaled :
      content23 (transportChild a + 4) *
          core23 (transportChild a + 4) =
        (4 * content23 (a + 1)) * core23 (a + 1) := by
    calc
      _ = transportChild a + 4 := hx
      _ = 4 * (a + 1) := hcoord.symm
      _ = 4 * (content23 (a + 1) * core23 (a + 1)) := by rw [hz]
      _ = _ := by ring
  rw [hcontent] at hscaled
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (by norm_num) (content23_pos (a + 1))) hscaled

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

/-! ## The counter is exactly the next forced odd-burst length -/

/-- Dyadic depth of the translated `-1` coordinate. -/
def minusOneCounter (n : ℕ) : ℕ := padicValNat 2 (n + 1)

/-- The odd payload left after removing the maximal power of two from
`n+1`. -/
def minusOnePayload (n : ℕ) : ℕ := (n + 1).divMaxPow 2

theorem counter_payload_balance (n : ℕ) :
    2 ^ minusOneCounter n * minusOnePayload n = n + 1 := by
  simpa [minusOneCounter, minusOnePayload] using
    (Nat.pow_padicValNat_mul_divMaxPow 2 (n + 1))

theorem minusOnePayload_pos (n : ℕ) : 0 < minusOnePayload n := by
  have hbalance := counter_payload_balance n
  have hpow : 0 < 2 ^ minusOneCounter n := by positivity
  by_contra hzero
  push Not at hzero
  have : minusOnePayload n = 0 := by omega
  rw [this, mul_zero] at hbalance
  omega

theorem minusOnePayload_odd (n : ℕ) : minusOnePayload n % 2 = 1 := by
  have hnot : ¬2 ∣ minusOnePayload n := by
    exact Nat.not_dvd_divMaxPow (p := 2) (n := n + 1)
      (by norm_num) (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at hnot
  have hlt := Nat.mod_lt (minusOnePayload n) (by norm_num : 0 < 2)
  omega

theorem eq_counter_payload_sub_one (n : ℕ) :
    n = 2 ^ minusOneCounter n * minusOnePayload n - 1 := by
  have hbalance := counter_payload_balance n
  omega

/-- Every prefix of the forced burst has the closed minus-one-rail form. -/
theorem syracuse_counter_burst_prefix (n j : ℕ)
    (hj : j ≤ minusOneCounter n) :
    syracuseStep^[j] n =
      KLMinusOneRail.railState (minusOneCounter n) (minusOnePayload n) j := by
  let r := minusOneCounter n
  let t := minusOnePayload n
  change syracuseStep^[j] n = KLMinusOneRail.railState r t j
  have hn : n = 2 ^ r * t - 1 := by
    simpa [r, t] using eq_counter_payload_sub_one n
  conv_lhs => rw [hn]
  simpa [KLMinusOneRail.railState] using
    (KLMinusOneRail.syracuse_iterate_railState
      (L := r) (t := t) (j := j)
      (by simpa [t] using minusOnePayload_pos n) hj)

/-- Before the counter is exhausted, every Syracuse source is odd. -/
theorem syracuse_counter_burst_source_odd (n j : ℕ)
    (hj : j < minusOneCounter n) :
    (syracuseStep^[j] n) % 2 = 1 := by
  rw [syracuse_counter_burst_prefix n j hj.le]
  exact KLMinusOneRail.railState_odd (minusOnePayload_pos n) hj

/-- When the counter is exhausted, the endpoint is even. -/
theorem syracuse_counter_burst_endpoint_even (n : ℕ) :
    (syracuseStep^[minusOneCounter n] n) % 2 = 0 := by
  rw [syracuse_counter_burst_prefix n (minusOneCounter n) (le_refl _)]
  simp only [KLMinusOneRail.railState, Nat.sub_self, pow_zero, mul_one]
  have hpayload := minusOnePayload_odd n
  have hthree : (3 ^ minusOneCounter n) % 2 = 1 := by
    norm_num [Nat.pow_mod]
  have hprodmod :
      (3 ^ minusOneCounter n * minusOnePayload n) % 2 = 1 := by
    rw [Nat.mul_mod, hthree, hpayload]
  have hprodpos : 0 < 3 ^ minusOneCounter n * minusOnePayload n := by
    exact Nat.mul_pos (by positivity) (minusOnePayload_pos n)
  omega

/-- Operational form of the recharge/discharge law: `v2(n+1)` is exactly the
number of consecutive odd Syracuse sources starting at `n`. -/
theorem minusOneCounter_eq_maximal_odd_burst (n : ℕ) :
    (∀ j < minusOneCounter n, (syracuseStep^[j] n) % 2 = 1) ∧
      (syracuseStep^[minusOneCounter n] n) % 2 = 0 := by
  exact ⟨syracuse_counter_burst_source_odd n,
    syracuse_counter_burst_endpoint_even n⟩

end KLRechargeLedger
end KontoroC
