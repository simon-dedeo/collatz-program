/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahQueueMacro
import KontoroC.AffineQuotientNoGo

/-!
# No YAH queue orbit can reproduce at every macro

The exact queue macro can occasionally increase ternary-word length by one.
This file rules out the simplest hoped-for glider: an ordinary canonical word
whose successive complete macros all increase length.

Every such increase consists of two odd shortcut steps, hence its represented
value obeys `4 * next = 9 * current + 5`.  Around the negative fixed point
this is `4 * (next + 1) = 9 * (current + 1)`.  Coprimality would force every
power of four to divide one fixed positive natural, which is impossible.

This does not rule out an infinite derivation with interspersed flat or
shrinking macros.
-/

namespace KontoroC
namespace YahPerpetualGrowthNoGo

open YahQueueMacro
open Carry Trit

/-- One deterministic complete left-delimiter macro on a pure ternary word.
The empty case is included only to make this a total function. -/
def queueMacro : List Trit → List Trit
  | [] => []
  | Trit.zero :: v => carrySweep Carry.one v
  | Trit.one :: v => carrySweep Carry.zero (carrySweep Carry.zero v)
  | Trit.two :: v => carrySweep Carry.zero (carrySweep Carry.one v)

theorem tritEvalFrom_pos (x : ℕ) (hx : 0 < x) (v : List Trit) :
    0 < tritEvalFrom x v := by
  induction v generalizing x with
  | nil => exact hx
  | cons t v ih =>
      apply ih
      have hdigit : 0 ≤ tritDigit t := Nat.zero_le _
      omega

/-- Local form of the reproducing value law, independent of an infinite
orbit wrapper. -/
theorem queueMacro_growth_balance (w : List Trit) (hnonempty : w ≠ [])
    (hgrows : (queueMacro w).length = w.length + 1) :
    4 * (tritEvalFrom 1 (queueMacro w) + 1) =
      9 * (tritEvalFrom 1 w + 1) := by
  cases w with
  | nil => exact (hnonempty rfl).elim
  | cons h v =>
      cases h with
      | zero =>
          have hnogrow := macro_zero_ne_grows v
          simp only [queueMacro, List.length_cons] at hgrows
          simp only [List.length_cons] at hnogrow
          omega
      | one =>
          have hmod := (macro_one_grows_iff_mod_four_eq_three v).mp (by
            simpa [queueMacro] using hgrows)
          have hbalance :=
            twoSweep_mod_four_three_balance Carry.zero v (by
              simpa [tritEvalFrom, tritDigit, carryBit] using hmod)
          change 4 *
              (tritEvalFrom 1
                (carrySweep Carry.zero (carrySweep Carry.zero v)) + 1) =
            9 * (tritEvalFrom 4 v + 1)
          norm_num [carryBit] at hbalance
          omega
      | two =>
          have hmod := (macro_two_grows_iff_mod_four_eq_three v).mp (by
            simpa [queueMacro] using hgrows)
          have hbalance :=
            twoSweep_mod_four_three_balance Carry.one v (by
              simpa [tritEvalFrom, tritDigit, carryBit] using hmod)
          change 4 *
              (tritEvalFrom 1
                (carrySweep Carry.zero (carrySweep Carry.one v)) + 1) =
            9 * (tritEvalFrom 5 v + 1)
          norm_num [carryBit] at hbalance
          omega

/-- A proposed ordinary orbit which gains exactly one ternary digit at every
complete queue macro. -/
structure PerpetualGrowingMacroOrbit where
  word : ℕ → List Trit
  nonempty : ∀ t, word t ≠ []
  next : ∀ t, word (t + 1) = queueMacro (word t)
  grows : ∀ t, (word (t + 1)).length = (word t).length + 1

namespace PerpetualGrowingMacroOrbit

def value (o : PerpetualGrowingMacroOrbit) (t : ℕ) : ℕ :=
  tritEvalFrom 1 (o.word t)

theorem value_pos (o : PerpetualGrowingMacroOrbit) (t : ℕ) :
    0 < o.value t := tritEvalFrom_pos 1 (by omega) (o.word t)

/-- Each hypothetical reproducing macro has the same fixed affine value law.
The zero-head case is eliminated by its independently proved length no-go. -/
theorem value_balance (o : PerpetualGrowingMacroOrbit) (t : ℕ) :
    4 * o.value (t + 1) = 9 * o.value t + 5 := by
  have hnonempty := o.nonempty t
  have hnext := o.next t
  have hgrows := o.grows t
  cases hword : o.word t with
  | nil => exact (hnonempty hword).elim
  | cons h v =>
      cases h with
      | zero =>
          rw [hword, queueMacro] at hnext
          rw [hnext, hword] at hgrows
          have hnogrow := macro_zero_ne_grows v
          simp only [List.length_cons] at hgrows hnogrow
          omega
      | one =>
          rw [hword, queueMacro] at hnext
          have hgrowthEndpoint :
              (carrySweep Carry.zero (carrySweep Carry.zero v)).length =
                (Trit.one :: v).length + 1 := by
            rw [← hnext, ← hword]
            exact hgrows
          have hmod :=
            (macro_one_grows_iff_mod_four_eq_three v).mp hgrowthEndpoint
          have hbalance :=
            twoSweep_mod_four_three_balance Carry.zero v (by
              simpa [tritEvalFrom, tritDigit, carryBit] using hmod)
          change 4 * tritEvalFrom 1 (o.word (t + 1)) =
            9 * tritEvalFrom 1 (o.word t) + 5
          rw [hnext, hword]
          simpa [queueMacro, tritEvalFrom, tritDigit, carryBit] using hbalance
      | two =>
          rw [hword, queueMacro] at hnext
          have hgrowthEndpoint :
              (carrySweep Carry.zero (carrySweep Carry.one v)).length =
                (Trit.two :: v).length + 1 := by
            rw [← hnext, ← hword]
            exact hgrows
          have hmod :=
            (macro_two_grows_iff_mod_four_eq_three v).mp hgrowthEndpoint
          have hbalance :=
            twoSweep_mod_four_three_balance Carry.one v (by
              simpa [tritEvalFrom, tritDigit, carryBit] using hmod)
          change 4 * tritEvalFrom 1 (o.word (t + 1)) =
            9 * tritEvalFrom 1 (o.word t) + 5
          rw [hnext, hword]
          simpa [queueMacro, tritEvalFrom, tritDigit, carryBit] using hbalance

def toAffineOrbit (o : PerpetualGrowingMacroOrbit) :
    PositiveAffineGainOrbit 9 4 5 where
  value := o.value
  value_pos := o.value_pos
  balance := o.value_balance

/-- There is no ordinary canonical queue orbit which reproduces on every
macro.  Its only compatible infinite address is the non-natural 2-adic fixed
point `-1`. -/
theorem impossible (o : PerpetualGrowingMacroOrbit) : False := by
  exact (o.toAffineOrbit).impossible (by norm_num) (by norm_num) (by norm_num)

theorem no_perpetual_growing_macro_orbit :
    ¬ Nonempty PerpetualGrowingMacroOrbit := by
  rintro ⟨o⟩
  exact o.impossible

end PerpetualGrowingMacroOrbit

/-! ## Finite burst certificate -/

/-- Exact fixed-point-defect scaling across a finite burst of consecutive
reproducing macros. -/
theorem growthBurst_defect_iterate (value : ℕ → ℕ) (r : ℕ)
    (hbalance : ∀ t, t < r →
      4 * value (t + 1) = 9 * value t + 5) :
    4 ^ r * (value r + 1) = 9 ^ r * (value 0 + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hprefix : ∀ t, t < r →
          4 * value (t + 1) = 9 * value t + 5 := by
        intro t ht
        exact hbalance t (by omega)
      have hi := ih hprefix
      have hlast := hbalance r (by omega)
      have hlastDefect : 4 * (value (r + 1) + 1) =
          9 * (value r + 1) := by omega
      calc
        4 ^ (r + 1) * (value (r + 1) + 1) =
            4 ^ r * (4 * (value (r + 1) + 1)) := by
              rw [pow_succ]
              ring
        _ = 4 ^ r * (9 * (value r + 1)) := by rw [hlastDefect]
        _ = 9 * (4 ^ r * (value r + 1)) := by ring
        _ = 9 * (9 ^ r * (value 0 + 1)) := by rw [hi]
        _ = 9 ^ (r + 1) * (value 0 + 1) := by
          rw [pow_succ]
          ring

/-- A burst of `r` consecutive `+1` macros pins the initial address to
`-1 mod 4^r`.  The divisibility form avoids any ambiguity about truncated
natural subtraction. -/
theorem growthBurst_pow_four_dvd (value : ℕ → ℕ) (r : ℕ)
    (hbalance : ∀ t, t < r →
      4 * value (t + 1) = 9 * value t + 5) :
    4 ^ r ∣ value 0 + 1 := by
  have hiterate := growthBurst_defect_iterate value r hbalance
  have hprod : 4 ^ r ∣ 9 ^ r * (value 0 + 1) :=
    ⟨value r + 1, hiterate.symm⟩
  have hcop : (4 ^ r).Coprime (9 ^ r) :=
    (by norm_num : Nat.Coprime 4 9).pow r r
  exact hcop.dvd_of_dvd_mul_left hprod

/-- Consequently, an explicitly bounded ordinary seed cannot support a
burst longer than its fixed-point defect can contain. -/
theorem no_growthBurst_of_defect_lt_fourPow (value : ℕ → ℕ) (r : ℕ)
    (hbalance : ∀ t, t < r →
      4 * value (t + 1) = 9 * value t + 5)
    (hsmall : value 0 + 1 < 4 ^ r) : False := by
  have hdvd := growthBurst_pow_four_dvd value r hbalance
  have hpos : 0 < value 0 + 1 := by omega
  have hle : 4 ^ r ≤ value 0 + 1 := Nat.le_of_dvd hpos hdvd
  omega

end YahPerpetualGrowthNoGo
end KontoroC
