/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.TwoRailPrefixCode

/-!
# An exact saturated-map block compiled into a two-rail splash

Eliahou--Verger-Gaugry's saturated rational-base map appends digit `1` on an
odd input and digit `2` on an even input.  On one seven-bit cylinder this file
proves the universal identity

`U^7 (95 + 128*t) = 1640 + 2187*t`

and identifies its two affine sides with a kernel-checked outward two-rail
handoff.  This is one compiler instruction, not a renewing infinite program.
-/

namespace KontoroC

/-- The saturated base-`3/2` map. -/
def saturatedStep (n : ℕ) : ℕ :=
  if n % 2 = 1 then (3 * n + 1) / 2 else (3 * n + 2) / 2

/-- One saturated step preserves a low parity address and changes the
residual affine multiplier from `2` to `3`. -/
theorem saturatedStep_add_two_mul (n t : ℕ) :
    saturatedStep (n + 2 * t) = saturatedStep n + 3 * t := by
  have hmod : (n + 2 * t) % 2 = n % 2 := by omega
  simp only [saturatedStep, hmod]
  by_cases hodd : n % 2 = 1
  · rw [if_pos hodd, if_pos hodd]
    omega
  · rw [if_neg hodd, if_neg hodd]
    omega

/-- General saturated-cylinder compiler law.  A fixed `D`-bit LSB address
fixes the first `D` branches, while the unbounded tail multiplier changes
from `2^D` to `3^D`. -/
theorem saturatedStep_iterate_dyadic_cylinder (D n t : ℕ) :
    saturatedStep^[D] (n + 2 ^ D * t) =
      saturatedStep^[D] n + 3 ^ D * t := by
  induction D generalizing n t with
  | zero => simp
  | succ D ih =>
      calc
        saturatedStep^[D + 1] (n + 2 ^ (D + 1) * t) =
            saturatedStep^[D]
              (saturatedStep (n + 2 ^ (D + 1) * t)) := by
          rw [show D + 1 = D.succ by omega,
            Function.iterate_succ_apply]
        _ = saturatedStep^[D]
              (saturatedStep n + 2 ^ D * (3 * t)) := by
          congr 1
          rw [show 2 ^ (D + 1) * t = 2 * (2 ^ D * t) by
            rw [pow_succ]; ring, saturatedStep_add_two_mul]
          ring
        _ = saturatedStep^[D] (saturatedStep n) +
              3 ^ D * (3 * t) := ih (saturatedStep n) (3 * t)
        _ = saturatedStep^[D + 1] n + 3 ^ (D + 1) * t := by
          rw [show D + 1 = D.succ by omega,
            Function.iterate_succ_apply, pow_succ]
          ring

theorem saturatedStep_95 (t : ℕ) :
    saturatedStep (95 + 128 * t) = 143 + 192 * t := by
  simp only [saturatedStep]
  have hodd : (95 + 128 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

theorem saturatedStep_143 (t : ℕ) :
    saturatedStep (143 + 192 * t) = 215 + 288 * t := by
  simp only [saturatedStep]
  have hodd : (143 + 192 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

theorem saturatedStep_215 (t : ℕ) :
    saturatedStep (215 + 288 * t) = 323 + 432 * t := by
  simp only [saturatedStep]
  have hodd : (215 + 288 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

theorem saturatedStep_323 (t : ℕ) :
    saturatedStep (323 + 432 * t) = 485 + 648 * t := by
  simp only [saturatedStep]
  have hodd : (323 + 432 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

theorem saturatedStep_485 (t : ℕ) :
    saturatedStep (485 + 648 * t) = 728 + 972 * t := by
  simp only [saturatedStep]
  have hodd : (485 + 648 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

theorem saturatedStep_728 (t : ℕ) :
    saturatedStep (728 + 972 * t) = 1093 + 1458 * t := by
  simp only [saturatedStep]
  have heven : (728 + 972 * t) % 2 ≠ 1 := by omega
  rw [if_neg heven]
  omega

theorem saturatedStep_1093 (t : ℕ) :
    saturatedStep (1093 + 1458 * t) = 1640 + 2187 * t := by
  simp only [saturatedStep]
  have hodd : (1093 + 1458 * t) % 2 = 1 := by omega
  rw [if_pos hodd]
  omega

/-- Universal seven-step affine block, with digit sequence
`[1,1,1,1,1,2,1]`. -/
theorem saturatedStep_iterate_seven (t : ℕ) :
    saturatedStep^[7] (95 + 128 * t) = 1640 + 2187 * t := by
  rw [show 7 = 1 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num]
  simp only [Function.iterate_add_apply, Function.iterate_one,
    saturatedStep_95, saturatedStep_143, saturatedStep_215,
    saturatedStep_323, saturatedStep_485, saturatedStep_728,
    saturatedStep_1093]

/-- Source gate of the bridge. -/
def saturatedBridgeSourceGate : TwoRailGate where
  ampTicks := 5
  cleanTicks := 0
  toPlusExtra := 2
  toMinusExtra := 1
  outputGap := 2
  inputPayload := 253
  plusPayload := 11527
  outputPayload := 4323
  ampTicks_pos := by norm_num
  outputGap_pos := by norm_num
  inputPayload_pos := by norm_num
  plusPayload_pos := by norm_num
  outputPayload_pos := by norm_num
  inputPayload_odd := by norm_num
  plusPayload_odd := by norm_num
  outputPayload_odd := by norm_num
  toPlus_balance := by norm_num [delayState]
  toMinus_balance := by norm_num [minusOneState]

/-- Target gate of the bridge. -/
def saturatedBridgeTargetGate : TwoRailGate where
  ampTicks := 1
  cleanTicks := 0
  toPlusExtra := 2
  toMinusExtra := 1
  outputGap := 2
  inputPayload := 13
  plusPayload := 7
  outputPayload := 3
  ampTicks_pos := by norm_num
  outputGap_pos := by norm_num
  inputPayload_pos := by norm_num
  plusPayload_pos := by norm_num
  outputPayload_pos := by norm_num
  inputPayload_odd := by norm_num
  plusPayload_odd := by norm_num
  outputPayload_odd := by norm_num
  toPlus_balance := by norm_num [delayState]
  toMinus_balance := by norm_num [minusOneState]

/-- The complete source payload cylinder, generated by the universal prefix
family construction rather than trusted coefficients. -/
def saturatedBridgeSourceFamily : AffineTwoRailFamily :=
  saturatedBridgeSourceGate.prefixFamily

/-- The complete target payload cylinder. -/
def saturatedBridgeTargetFamily : AffineTwoRailFamily :=
  saturatedBridgeTargetGate.prefixFamily

theorem saturatedBridgeSource_strides :
    saturatedBridgeSourceFamily.inputStride = 256 ∧
      saturatedBridgeSourceFamily.plusStride = 11664 ∧
      saturatedBridgeSourceFamily.outputStride = 4374 := by
  norm_num [saturatedBridgeSourceFamily, saturatedBridgeSourceGate,
    TwoRailGate.prefixFamily, TwoRailGate.prefixInputStride,
    TwoRailGate.prefixPlusStride, TwoRailGate.prefixOutputStride,
    TwoRailGate.codeExponent]

theorem saturatedBridgeTarget_strides :
    saturatedBridgeTargetFamily.inputStride = 256 ∧
      saturatedBridgeTargetFamily.plusStride = 144 ∧
      saturatedBridgeTargetFamily.outputStride = 54 := by
  norm_num [saturatedBridgeTargetFamily, saturatedBridgeTargetGate,
    TwoRailGate.prefixFamily, TwoRailGate.prefixInputStride,
    TwoRailGate.prefixPlusStride, TwoRailGate.prefixOutputStride,
    TwoRailGate.codeExponent]

/-- Universal coefficientwise Collatz handoff corresponding to the saturated
seven-step block. -/
def saturatedBridgeLink :
    AffineTwoRailLink saturatedBridgeSourceFamily
      saturatedBridgeTargetFamily where
  sourceIndexBase := 95
  sourceIndexStride := 128
  targetIndexBase := 1640
  targetIndexStride := 2187
  gap_link := by
    norm_num [saturatedBridgeSourceFamily, saturatedBridgeTargetFamily,
      saturatedBridgeSourceGate, saturatedBridgeTargetGate,
      TwoRailGate.prefixFamily]
  payload_base_link := by
    norm_num [saturatedBridgeSourceFamily, saturatedBridgeTargetFamily,
      saturatedBridgeSourceGate, saturatedBridgeTargetGate,
      TwoRailGate.prefixFamily, TwoRailGate.prefixInputStride,
      TwoRailGate.prefixOutputStride, TwoRailGate.codeExponent]
  payload_stride_link := by
    norm_num [saturatedBridgeSourceFamily, saturatedBridgeTargetFamily,
      saturatedBridgeSourceGate, saturatedBridgeTargetGate,
      TwoRailGate.prefixFamily, TwoRailGate.prefixInputStride,
      TwoRailGate.prefixOutputStride, TwoRailGate.codeExponent]

/-- Every source-family member selected by the seven-bit address is outward. -/
theorem saturatedBridgeSource_outward (t : ℕ) :
    (saturatedBridgeSourceFamily.member
        (saturatedBridgeLink.sourceIndex t)).start <
      (saturatedBridgeSourceFamily.member
        (saturatedBridgeLink.sourceIndex t)).endpoint := by
  rw [TwoRailGate.outward_iff]
  norm_num [saturatedBridgeSourceFamily, saturatedBridgeSourceGate,
    saturatedBridgeLink, AffineTwoRailLink.sourceIndex,
    TwoRailGate.prefixFamily, TwoRailGate.prefixInputStride,
    TwoRailGate.prefixOutputStride, TwoRailGate.codeExponent]
  omega

/-- The Collatz endpoint is literally the next splash start indexed by the
seven-step saturated-map value. -/
theorem saturatedBridge_endpoint (t : ℕ) :
    (saturatedBridgeSourceFamily.member (95 + 128 * t)).endpoint =
      (saturatedBridgeTargetFamily.member
        (saturatedStep^[7] (95 + 128 * t))).start := by
  rw [saturatedStep_iterate_seven]
  exact saturatedBridgeLink.endpoint_link t

end KontoroC
