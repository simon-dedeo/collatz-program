/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahLiftDecoderArithmetic

/-!
# Universal lasso laws for the YAH quotient decoder

These are the all-parameter finite-state lemmas behind QM24.  When a repeated
block fixes its incoming carry, quotient sweeping preserves a one-parameter
lasso.  When the block swaps two carries, the even and odd parameter classes
are lassos whose repeated blocks are the two possible ordered pairs of open
quotient blocks.

The theorems generate blocks using `quotientCore`; no 256- or 512-trit
literal is trusted.  They certify one transducer instruction, not a finite
cycle of register charts.
-/

namespace KontoroC
namespace YahLassoDecoder

open YahQueueMacro
open YahQueueCausalityNoGo
open Carry Trit

/-- Concatenate `t` copies of a finite word. -/
def repeatWord (block : List Trit) : ℕ → List Trit
  | 0 => []
  | t + 1 => block ++ repeatWord block t

@[simp] theorem repeatWord_zero (block : List Trit) :
    repeatWord block 0 = [] := rfl

@[simp] theorem repeatWord_succ (block : List Trit) (t : ℕ) :
    repeatWord block (t + 1) = block ++ repeatWord block t := rfl

theorem repeatWord_add (block : List Trit) (m n : ℕ) :
    repeatWord block (m + n) =
      repeatWord block m ++ repeatWord block n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show (m + 1) + n = (m + n) + 1 by omega]
      simp only [repeatWord_succ, ih]
      simp [List.append_assoc]

theorem repeatWord_twice (block : List Trit) (t : ℕ) :
    repeatWord block (2 * t) = repeatWord (block ++ block) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show 2 * (t + 1) = 2 + 2 * t by omega, repeatWord_add, ih]
      simp [repeatWord, List.append_assoc]

/-- Fixed-carry repeated blocks remain lassos under a quotient sweep. -/
theorem carrySweep_repeat_fixed (c : Carry) (block suffix : List Trit)
    (hfix : terminalCarry c block = c) (t : ℕ) :
    carrySweep c (repeatWord block t ++ suffix) =
      repeatWord (quotientCore c block) t ++ carrySweep c suffix := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [repeatWord_succ, List.append_assoc, carrySweep_append,
        hfix, ih]

/-- QM24's fixed-carry lasso theorem, including an arbitrary fixed prefix. -/
theorem carrySweep_lasso_fixed (c : Carry) (pre block suffix : List Trit)
    (hfix : terminalCarry (terminalCarry c pre) block =
      terminalCarry c pre) (t : ℕ) :
    carrySweep c (pre ++ repeatWord block t ++ suffix) =
      quotientCore c pre ++
        repeatWord (quotientCore (terminalCarry c pre) block) t ++
        carrySweep (terminalCarry c pre) suffix := by
  rw [List.append_assoc, carrySweep_append]
  rw [carrySweep_repeat_fixed _ _ _ hfix]
  simp [List.append_assoc]

/-- Two copies of a carry-flipping block make a fixed-carry superblock. -/
theorem carrySweep_repeat_flipping_even (c d : Carry)
    (block suffix : List Trit)
    (hcd : terminalCarry c block = d)
    (hdc : terminalCarry d block = c) (t : ℕ) :
    carrySweep c (repeatWord block (2 * t) ++ suffix) =
      repeatWord (quotientCore c block ++ quotientCore d block) t ++
        carrySweep c suffix := by
  rw [repeatWord_twice]
  have hfix : terminalCarry c (block ++ block) = c := by
    rw [terminalCarry_append, hcd, hdc]
  rw [carrySweep_repeat_fixed c (block ++ block) suffix hfix]
  rw [quotientCore_append, hcd]

/-- Odd repetition count: the first block changes chart, after which paired
blocks repeat in the opposite order. -/
theorem carrySweep_repeat_flipping_odd (c d : Carry)
    (block suffix : List Trit)
    (hcd : terminalCarry c block = d)
    (hdc : terminalCarry d block = c) (t : ℕ) :
    carrySweep c (repeatWord block (2 * t + 1) ++ suffix) =
      quotientCore c block ++
        repeatWord (quotientCore d block ++ quotientCore c block) t ++
        carrySweep d suffix := by
  rw [show 2 * t + 1 = 1 + 2 * t by omega, repeatWord_add]
  simp only [repeatWord_succ, repeatWord_zero, List.append_nil]
  rw [show (block ++ repeatWord block (2 * t)) ++ suffix =
    block ++ (repeatWord block (2 * t) ++ suffix) by
      simp [List.append_assoc]]
  rw [carrySweep_append, hcd]
  rw [carrySweep_repeat_flipping_even d c block suffix hdc hcd]
  simp [List.append_assoc]

end YahLassoDecoder
end KontoroC
