/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahLassoDecoder

/-!
# Exact arithmetic semantics of the YAH zero-head bit decoder

If a canonical word begins with `tri0` and its defect is `3^7 R`, its next
queue macro reads the low bit of `R`.  These generic theorems prove both
branches of QM23 directly from the already verified quotient-sweep value law.

They deliberately take the `3^7 R` word equation as a hypothesis.  QM22's
four-macro lasso construction is the separate producer of that hypothesis.
-/

namespace KontoroC
namespace YahLiftDecoderStep

open YahQueueMacro
open YahPerpetualGrowthNoGo
open YahBattery
open Carry Trit

private theorem even_terminal_one (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r)) :
    terminalCarry Carry.one v = Carry.one := by
  have hvalue : tritEvalFrom 3 v + 1 = 3 ^ 7 * (2 * r) := by
    simpa [defect, tritEvalFrom, tritDigit] using hdefect
  have hmod3 : tritEvalFrom 3 v % 2 = 1 := by
    have hmodEq := congrArg (fun n : ℕ => n % 2) hvalue
    norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq
    have hlt := Nat.mod_lt (tritEvalFrom 3 v) (by decide : 0 < 2)
    omega
  have hmod : tritEvalFrom 1 (Trit.zero :: v) % 2 = 1 := by
    simpa [tritEvalFrom, tritDigit] using hmod3
  have hcarry := macro_zero_terminal_bit v
  rw [hmod] at hcarry
  generalize hc : terminalCarry Carry.one v = c at hcarry ⊢
  cases c <;> simp [carryBit] at hcarry ⊢

private theorem odd_terminal_zero (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r + 1)) :
    terminalCarry Carry.one v = Carry.zero := by
  have hvalue : tritEvalFrom 3 v + 1 = 3 ^ 7 * (2 * r + 1) := by
    simpa [defect, tritEvalFrom, tritDigit] using hdefect
  have hmod3 : tritEvalFrom 3 v % 2 = 0 := by
    have hmodEq := congrArg (fun n : ℕ => n % 2) hvalue
    norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq
    have hlt := Nat.mod_lt (tritEvalFrom 3 v) (by decide : 0 < 2)
    omega
  have hmod : tritEvalFrom 1 (Trit.zero :: v) % 2 = 0 := by
    simpa [tritEvalFrom, tritDigit] using hmod3
  have hcarry := macro_zero_terminal_bit v
  rw [hmod] at hcarry
  generalize hc : terminalCarry Carry.one v = c at hcarry ⊢
  cases c <;> simp [carryBit] at hcarry ⊢

/-- QM23, zero branch: pop an even register bit and extend the factor of
three by one. -/
theorem even_decoder_defect (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r)) :
    defect (queueMacro (Trit.zero :: v)) = 3 ^ 8 * r := by
  have hterminal := even_terminal_one v r hdefect
  have hsweep := carrySweep_value 1 Carry.one v
  rw [hterminal] at hsweep
  simp only [queueMacro, defect]
  simp [carryBit] at hsweep
  have hvalue : tritEvalFrom 3 v + 1 = 3 ^ 7 * (2 * r) := by
    simpa [defect, tritEvalFrom, tritDigit] using hdefect
  norm_num only [Nat.reducePow] at hvalue ⊢
  omega

/-- QM23, one branch, stated without division. -/
theorem odd_decoder_defect (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r + 1)) :
    2 * defect (queueMacro (Trit.zero :: v)) =
      3 ^ 7 * (2 * r + 1) + 1 := by
  have hterminal := odd_terminal_zero v r hdefect
  have hsweep := carrySweep_value 1 Carry.one v
  rw [hterminal] at hsweep
  simp only [queueMacro, defect]
  simp [carryBit] at hsweep
  have hvalue : tritEvalFrom 3 v + 1 = 3 ^ 7 * (2 * r + 1) := by
    simpa [defect, tritEvalFrom, tritDigit] using hdefect
  norm_num only [Nat.reducePow] at hvalue ⊢
  omega

theorem even_decoder_length_neutral (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r)) :
    (queueMacro (Trit.zero :: v)).length = (Trit.zero :: v).length := by
  simp only [queueMacro]
  apply (macro_zero_length_eq_iff_odd v).2
  have hvalue : tritEvalFrom 1 (Trit.zero :: v) + 1 =
      3 ^ 7 * (2 * r) := by simpa [defect] using hdefect
  have hmodEq := congrArg (fun n : ℕ => n % 2) hvalue
  norm_num [Nat.add_mod, Nat.mul_mod] at hmodEq
  have hlt := Nat.mod_lt (tritEvalFrom 1 (Trit.zero :: v))
    (by decide : 0 < 2)
  omega

theorem odd_decoder_length_shrinks (v : List Trit) (r : ℕ)
    (hdefect : defect (Trit.zero :: v) = 3 ^ 7 * (2 * r + 1)) :
    (queueMacro (Trit.zero :: v)).length + 1 =
      (Trit.zero :: v).length := by
  have hterminal := odd_terminal_zero v r hdefect
  have hlen := macro_zero_length_charge v
  simp only [queueMacro]
  rw [hterminal] at hlen
  simpa [carryBit] using hlen

end YahLiftDecoderStep
end KontoroC
