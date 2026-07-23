/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Tactic.ReduceModChar

/-!
# The 19-bit affine carry cycle does not reblock

The proposed third YAH chart contains `2^19` copies of a 65,536-trit atom.
On the cascade carry state, the research calculation gives the affine map

`r ↦ (262145*r + 449133) mod 524288`.

This file proves algebraically, for every starting carry state, that this map
has exact period `524288 = 2^19`.  In particular, pairing atoms does not reveal
a shorter repetition that could rewrite the lasso counter.

The theorem is deliberately scoped.  The identification of the actual word
cascade with this affine map remains a word-semantics obligation; everything
after that identification is kernel checked here.
-/

namespace KontoroC
namespace YahAffineCarryNoGo

open Function

variable {R : Type*} [CommRing R]

/-- An affine self-map of a commutative ring. -/
def affine (a b : R) (x : R) : R := a * x + b

/-- When the multiplier squares to one, two affine steps are a translation. -/
theorem affine_two_iterate (a b x : R) (ha : a * a = 1) :
    (affine a b)^[2] x = x + (a + 1) * b := by
  simp [affine, Function.iterate_succ_apply]
  calc
    a * (a * x + b) + b = (a * a) * x + (a + 1) * b := by ring
    _ = x + (a + 1) * b := by rw [ha, one_mul]

/-- Closed form for every even iterate of an involutive-multiplier affine map. -/
theorem affine_even_iterate (a b x : R) (ha : a * a = 1) (k : ℕ) :
    (affine a b)^[2 * k] x = x + (k : R) * ((a + 1) * b) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, affine_two_iterate a b _ ha, ih]
      push_cast
      ring

/-- Closed form for every odd iterate. -/
theorem affine_odd_iterate (a b x : R) (ha : a * a = 1) (k : ℕ) :
    (affine a b)^[2 * k + 1] x =
      a * (x + (k : R) * ((a + 1) * b)) + b := by
  rw [Function.iterate_succ_apply, affine_even_iterate a b _ ha]
  simp only [affine]
  have hac : a * ((a + 1) * b) = (a + 1) * b := by
    calc
      a * ((a + 1) * b) = (a * a + a) * b := by ring
      _ = (a + 1) * b := by rw [ha]; ring
  have hak : a * ((k : R) * ((a + 1) * b)) =
      (k : R) * ((a + 1) * b) := by
    calc
      a * ((k : R) * ((a + 1) * b)) =
          (k : R) * (a * ((a + 1) * b)) := by ring
      _ = (k : R) * ((a + 1) * b) := by rw [hac]
  rw [mul_add, hak]
  ring

/-- The large exponent in QM43, checked by kernel-proof-producing modular
exponentiation. -/
theorem atomMultiplier_mod : 3 ^ 65536 % 524288 = 262145 := by
  have hz : (3 : ZMod 524288) ^ 65536 = 262145 := by
    reduce_mod_char
  have hz' : ((3 ^ 65536 : ℕ) : ZMod 524288) = (262145 : ℕ) := by
    rw [Nat.cast_pow]
    exact hz
  have hm := (ZMod.natCast_eq_natCast_iff'
    (3 ^ 65536) 262145 524288).mp hz'
  have hr : 262145 % 524288 = 262145 := by norm_num
  rw [hr] at hm
  exact hm

/-- The exact order of the two-step translation `111834 = 2*55917` modulo
`2^19`. -/
theorem translation_order_iff (k : ℕ) :
    (k : ZMod 524288) * (111834 : ZMod 524288) = 0 ↔ 262144 ∣ k := by
  constructor
  · intro h
    have hdiv : 524288 ∣ k * 111834 :=
      (ZMod.natCast_eq_zero_iff (k * 111834) 524288).mp (by simpa using h)
    have h' : 262144 ∣ k * 55917 := by
      rw [show 524288 = 2 * 262144 by norm_num,
        show 111834 = 2 * 55917 by norm_num] at hdiv
      have hcancel : 2 * 262144 ∣ 2 * (k * 55917) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hcancel
    exact ((by decide : Nat.Coprime 262144 55917).dvd_mul_right).mp h'
  · intro h
    have hdiv : 524288 ∣ k * 111834 := by
      obtain ⟨q, rfl⟩ := h
      use q * 55917
      ring
    have hzero := (ZMod.natCast_eq_zero_iff (k * 111834) 524288).mpr hdiv
    simpa using hzero

/-- The 19-bit carry-state update claimed by the exact word audit. -/
def carryAffine : ZMod 524288 → ZMod 524288 := affine 262145 449133

private theorem multiplier_sq :
    (262145 : ZMod 524288) * 262145 = 1 := by
  change ((68720001025 : ℕ) : ZMod 524288) = (1 : ℕ)
  rw [ZMod.natCast_eq_natCast_iff']

private theorem translation_eq :
    ((262145 + 1) * 449133 : ZMod 524288) = 111834 := by
  change ((117738419418 : ℕ) : ZMod 524288) = (111834 : ℕ)
  rw [ZMod.natCast_eq_natCast_iff']

/-- QM44: two atom steps translate the carry state by `111834`. -/
theorem carryAffine_two_iterate (r : ZMod 524288) :
    carryAffine^[2] r = r + 111834 := by
  simpa only [carryAffine, translation_eq] using
    affine_two_iterate (262145 : ZMod 524288) 449133 r multiplier_sq

theorem carryAffine_even_iterate (r : ZMod 524288) (k : ℕ) :
    carryAffine^[2 * k] r = r + (k : ZMod 524288) * 111834 := by
  simpa only [carryAffine, translation_eq] using
    affine_even_iterate (262145 : ZMod 524288) 449133 r multiplier_sq k

/-- An odd number of atom steps flips parity, hence cannot return a carry
state to itself. -/
theorem carryAffine_odd_ne (r : ZMod 524288) (k : ℕ) :
    carryAffine^[2 * k + 1] r ≠ r := by
  rw [show carryAffine^[2 * k + 1] r =
      (262145 : ZMod 524288) *
        (r + (k : ZMod 524288) * 111834) + 449133 by
        simpa only [carryAffine, translation_eq] using
          affine_odd_iterate (262145 : ZMod 524288) 449133 r multiplier_sq k]
  intro h
  let hdiv : 2 ∣ 524288 := by norm_num
  have hmap := congrArg (ZMod.castHom hdiv (ZMod 2)) h
  have ha2 : ZMod.cast (262145 : ZMod 524288) = (1 : ZMod 2) :=
    (ZMod.cast_natCast hdiv 262145).trans (by decide)
  have hb2 : ZMod.cast (449133 : ZMod 524288) = (1 : ZMod 2) :=
    (ZMod.cast_natCast hdiv 449133).trans (by decide)
  have hc2 : ZMod.cast (111834 : ZMod 524288) = (0 : ZMod 2) :=
    (ZMod.cast_natCast hdiv 111834).trans (by decide)
  rw [ZMod.castHom_apply, ZMod.cast_add hdiv, ZMod.cast_mul hdiv,
    ZMod.cast_add hdiv, ZMod.cast_mul hdiv, ZMod.cast_natCast hdiv,
    ha2, hb2, hc2] at hmap
  simp at hmap

/-- Every carry state has exact period `2^19`: it returns after `524288`
steps and at no smaller positive time. -/
theorem carryAffine_exact_period (r : ZMod 524288) :
    carryAffine^[524288] r = r ∧
      ∀ n, 0 < n → n < 524288 → carryAffine^[n] r ≠ r := by
  constructor
  · have hz : ((262144 : ℕ) : ZMod 524288) * 111834 = 0 :=
      (translation_order_iff 262144).mpr (dvd_refl 262144)
    have h := carryAffine_even_iterate r 262144
    rw [hz, add_zero] at h
    exact h
  · intro n hn hnlt
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, rfl⟩ := heven
      simpa only [two_mul] using (show carryAffine^[2 * k] r ≠ r by
        rw [carryAffine_even_iterate]
        intro hret
        have hzero : (k : ZMod 524288) * 111834 = 0 := by
          exact add_left_cancel (hret.trans (add_zero r).symm)
        have hkdiv := (translation_order_iff k).mp hzero
        have hkpos : 0 < k := by omega
        have hkle : 262144 ≤ k := Nat.le_of_dvd hkpos hkdiv
        omega)
    · obtain ⟨k, rfl⟩ := hodd
      exact carryAffine_odd_ne r k

/-- Mathlib's dynamical `minimalPeriod` agrees with the explicit exact-period
statement. -/
theorem carryAffine_minimalPeriod (r : ZMod 524288) :
    Function.minimalPeriod carryAffine r = 524288 := by
  have hexact := carryAffine_exact_period r
  have hperiod : Function.IsPeriodicPt carryAffine 524288 r := hexact.1
  apply (hperiod.minimalPeriod_le (by norm_num)).antisymm
  by_contra hne
  have hlt : Function.minimalPeriod carryAffine r < 524288 :=
    Nat.lt_of_not_ge hne
  have hpos : 0 < Function.minimalPeriod carryAffine r :=
    hperiod.minimalPeriod_pos (by norm_num)
  exact hexact.2 _ hpos hlt (Function.iterate_minimalPeriod (f := carryAffine) (x := r))

/-- Dividing an affine numerator by a fixed denominator remains strictly
monotone when one input step changes the numerator by at least one whole
denominator.  This is the abstract injectivity seam used for quotient atoms
in QM45. -/
theorem affineQuotient_strictMono (D B c : ℕ) (hD : 0 < D) (hDB : D ≤ B) :
    StrictMono (fun r : ℕ => (B * r + c) / D) := by
  intro u v huv
  have huv' : u + 1 ≤ v := Nat.succ_le_iff.mpr huv
  have hnum : B * u + c + D ≤ B * v + c := by
    calc
      B * u + c + D ≤ B * u + c + B := Nat.add_le_add_left hDB _
      _ = B * (u + 1) + c := by ring
      _ ≤ B * v + c := Nat.add_le_add_right (Nat.mul_le_mul_left B huv') c
  calc
    (B * u + c) / D < (B * u + c) / D + 1 := Nat.lt_succ_self _
    _ = (B * u + c + D) / D := (Nat.add_div_right _ hD).symm
    _ ≤ (B * v + c) / D := Nat.div_le_div_right hnum

/-- Hence two distinct incoming carry states have distinct quotient atoms
whenever `2^s ≤ 3^m`. -/
theorem quotientAtom_injective (m s b : ℕ) (hscale : 2 ^ s ≤ 3 ^ m) :
    Function.Injective (fun r : ℕ => (3 ^ m * r + b) / 2 ^ s) :=
  (affineQuotient_strictMono (2 ^ s) (3 ^ m) b (by positivity) hscale).injective

/-- QM46: after grouping `2^s` atoms, a cylinder parameter really has lost
exactly `s` payload bits. -/
theorem canonicalReblocking_balance (a K s z : ℕ) (hsK : s ≤ K) :
    a + 2 ^ K * z = a + 2 ^ s * (2 ^ (K - s) * z) := by
  have hp := Nat.pow_sub_mul_pow 2 hsK
  rw [← hp]
  ring

end YahAffineCarryNoGo
end KontoroC
