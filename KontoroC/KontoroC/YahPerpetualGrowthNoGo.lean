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
end YahPerpetualGrowthNoGo
end KontoroC
