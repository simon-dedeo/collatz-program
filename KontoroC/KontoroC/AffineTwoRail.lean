/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.StandardTwoRail

/-!
# Infinite affine families and index transducers

The gate solver emits affine families rather than isolated large integers.
This file makes that compression kernel-facing: a base gate and two
coefficient identities generate a certified gate for every natural payload
index.  A second pair of coefficient identities certifies every member of a
handoff between two families.
-/

namespace KontoroC

/-- Coefficient data generating an infinite affine family of exact two-rail
gates with one fixed shape. -/
structure AffineTwoRailFamily where
  base : TwoRailGate
  inputStride : ℕ
  plusStride : ℕ
  outputStride : ℕ
  inputStride_even : Even inputStride
  plusStride_even : Even plusStride
  outputStride_even : Even outputStride
  toPlus_stride_balance :
    2 ^ base.toPlusExtra *
        (plusStride * 2 ^ (2 * base.cleanTicks + 2)) =
      3 ^ (base.ampTicks + 1) * inputStride
  toMinus_stride_balance :
    2 ^ base.toMinusExtra *
        (2 ^ base.outputGap * outputStride) =
      3 ^ (base.cleanTicks + 1) * plusStride

namespace AffineTwoRailFamily

/-- The `z`th gate in the affine family.  Its proof fields are reconstructed
from the base gate and coefficient identities, not trusted per member. -/
def member (f : AffineTwoRailFamily) (z : ℕ) : TwoRailGate where
  ampTicks := f.base.ampTicks
  cleanTicks := f.base.cleanTicks
  toPlusExtra := f.base.toPlusExtra
  toMinusExtra := f.base.toMinusExtra
  outputGap := f.base.outputGap
  inputPayload := f.base.inputPayload + f.inputStride * z
  plusPayload := f.base.plusPayload + f.plusStride * z
  outputPayload := f.base.outputPayload + f.outputStride * z
  ampTicks_pos := f.base.ampTicks_pos
  outputGap_pos := f.base.outputGap_pos
  inputPayload_pos := Nat.add_pos_left f.base.inputPayload_pos _
  plusPayload_pos := Nat.add_pos_left f.base.plusPayload_pos _
  outputPayload_pos := Nat.add_pos_left f.base.outputPayload_pos _
  inputPayload_odd :=
    f.base.inputPayload_odd.add_even (f.inputStride_even.mul_right z)
  plusPayload_odd :=
    f.base.plusPayload_odd.add_even (f.plusStride_even.mul_right z)
  outputPayload_odd :=
    f.base.outputPayload_odd.add_even (f.outputStride_even.mul_right z)
  toPlus_balance := by
    let B := 3 ^ (f.base.ampTicks + 1) * f.base.inputPayload
    have hB : 0 < B := by
      dsimp [B]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) f.base.inputPayload_pos
    have hbase :
        2 ^ f.base.toPlusExtra *
              delayState f.base.plusPayload (2 * f.base.cleanTicks + 2) + 1 =
          B := by
      have hb := f.base.toPlus_balance
      omega
    have hleft :
        2 ^ f.base.toPlusExtra *
            delayState (f.base.plusPayload + f.plusStride * z)
              (2 * f.base.cleanTicks + 2) =
          2 ^ f.base.toPlusExtra *
              delayState f.base.plusPayload (2 * f.base.cleanTicks + 2) +
            (2 ^ f.base.toPlusExtra *
              (f.plusStride * 2 ^ (2 * f.base.cleanTicks + 2))) * z := by
      simp only [delayState]
      ring
    have hright :
        3 ^ (f.base.ampTicks + 1) *
            (f.base.inputPayload + f.inputStride * z) =
          B + (3 ^ (f.base.ampTicks + 1) * f.inputStride) * z := by
      dsimp [B]
      ring
    rw [hleft, hright, f.toPlus_stride_balance]
    omega
  toMinus_balance := by
    let A := 2 ^ f.base.outputGap * f.base.outputPayload
    have hA : 0 < A := by
      dsimp [A]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) f.base.outputPayload_pos
    have hinside :
        minusOneState (f.base.outputPayload + f.outputStride * z)
            f.base.outputGap =
          minusOneState f.base.outputPayload f.base.outputGap +
            (2 ^ f.base.outputGap * f.outputStride) * z := by
      have hprod :
          2 ^ f.base.outputGap *
              (f.base.outputPayload + f.outputStride * z) =
            A + (2 ^ f.base.outputGap * f.outputStride) * z := by
        dsimp [A]
        ring
      simp only [minusOneState]
      rw [hprod]
      omega
    have hright :
        1 + 3 ^ (f.base.cleanTicks + 1) *
            (f.base.plusPayload + f.plusStride * z) =
          (1 + 3 ^ (f.base.cleanTicks + 1) * f.base.plusPayload) +
            (3 ^ (f.base.cleanTicks + 1) * f.plusStride) * z := by
      ring
    rw [hinside, hright]
    calc
      2 ^ f.base.toMinusExtra *
            (minusOneState f.base.outputPayload f.base.outputGap +
              2 ^ f.base.outputGap * f.outputStride * z) =
          2 ^ f.base.toMinusExtra *
              minusOneState f.base.outputPayload f.base.outputGap +
            (2 ^ f.base.toMinusExtra *
              (2 ^ f.base.outputGap * f.outputStride)) * z := by ring
      _ = (1 + 3 ^ (f.base.cleanTicks + 1) * f.base.plusPayload) +
            (3 ^ (f.base.cleanTicks + 1) * f.plusStride) * z := by
        rw [f.base.toMinus_balance, f.toMinus_stride_balance]

@[simp] theorem member_ampTicks (f : AffineTwoRailFamily) (z : ℕ) :
    (f.member z).ampTicks = f.base.ampTicks := rfl

@[simp] theorem member_outputGap (f : AffineTwoRailFamily) (z : ℕ) :
    (f.member z).outputGap = f.base.outputGap := rfl

@[simp] theorem member_inputPayload (f : AffineTwoRailFamily) (z : ℕ) :
    (f.member z).inputPayload = f.base.inputPayload + f.inputStride * z := rfl

@[simp] theorem member_outputPayload (f : AffineTwoRailFamily) (z : ℕ) :
    (f.member z).outputPayload = f.base.outputPayload + f.outputStride * z := rfl

/-- Every affine member inherits a full exact valuation proof. -/
theorem member_legal_and_endpoint (f : AffineTwoRailFamily) (z : ℕ) :
    WordLegal (f.member z).start (f.member z).word ∧
      runWord (f.member z).start (f.member z).word = (f.member z).endpoint :=
  (f.member z).legal_and_endpoint

theorem member_isStandard (f : AffineTwoRailFamily)
    (h : f.base.IsStandard) (z : ℕ) : (f.member z).IsStandard := h

end AffineTwoRailFamily

/-- A universal affine handoff.  The two index progressions select linked
members of the source and target gate families for every tail `u`. -/
structure AffineTwoRailLink (source target : AffineTwoRailFamily) where
  sourceIndexBase : ℕ
  sourceIndexStride : ℕ
  targetIndexBase : ℕ
  targetIndexStride : ℕ
  gap_link : source.base.outputGap = target.base.ampTicks + 1
  payload_base_link :
    source.base.outputPayload + source.outputStride * sourceIndexBase =
      target.base.inputPayload + target.inputStride * targetIndexBase
  payload_stride_link :
    source.outputStride * sourceIndexStride =
      target.inputStride * targetIndexStride

namespace AffineTwoRailLink

def sourceIndex {source target : AffineTwoRailFamily}
    (g : AffineTwoRailLink source target) (u : ℕ) : ℕ :=
  g.sourceIndexBase + g.sourceIndexStride * u

def targetIndex {source target : AffineTwoRailFamily}
    (g : AffineTwoRailLink source target) (u : ℕ) : ℕ :=
  g.targetIndexBase + g.targetIndexStride * u

/-- Coefficientwise linkage proves equality of the complete payloads for
every unbounded tail, not just sampled indices. -/
theorem payload_link {source target : AffineTwoRailFamily}
    (g : AffineTwoRailLink source target) (u : ℕ) :
    (source.member (g.sourceIndex u)).outputPayload =
      (target.member (g.targetIndex u)).inputPayload := by
  simp only [AffineTwoRailFamily.member_outputPayload,
    AffineTwoRailFamily.member_inputPayload, sourceIndex, targetIndex]
  calc
    source.base.outputPayload +
          source.outputStride *
            (g.sourceIndexBase + g.sourceIndexStride * u) =
        (source.base.outputPayload +
            source.outputStride * g.sourceIndexBase) +
          (source.outputStride * g.sourceIndexStride) * u := by ring
    _ = (target.base.inputPayload +
            target.inputStride * g.targetIndexBase) +
          (target.inputStride * g.targetIndexStride) * u := by
      rw [g.payload_base_link, g.payload_stride_link]
    _ = target.base.inputPayload +
          target.inputStride *
            (g.targetIndexBase + g.targetIndexStride * u) := by ring

/-- The selected source endpoint is literally the selected target start for
every tail.  This is the universal tag-transducer instruction. -/
theorem endpoint_link {source target : AffineTwoRailFamily}
    (g : AffineTwoRailLink source target) (u : ℕ) :
    (source.member (g.sourceIndex u)).endpoint =
      (target.member (g.targetIndex u)).start := by
  simp only [TwoRailGate.endpoint, TwoRailGate.start, minusOneState,
    AffineTwoRailFamily.member_outputGap,
    AffineTwoRailFamily.member_ampTicks]
  rw [g.gap_link, g.payload_link u]

end AffineTwoRailLink

/-- Kernel-checked base gate for the second standard rail length. -/
def secondStandardTwoRailGate : TwoRailGate where
  ampTicks := 5
  cleanTicks := 1
  toPlusExtra := 1
  toMinusExtra := 1
  outputGap := 7
  inputPayload := 5083
  plusPayload := 115797
  outputPayload := 4071
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

/-- The complete affine family of the first standard gate shape. -/
def firstStandardTwoRailFamily : AffineTwoRailFamily where
  base := firstStandardTwoRailGate
  inputStride := 8192
  plusStride := 62208
  outputStride := 4374
  inputStride_even := by norm_num
  plusStride_even := by norm_num
  outputStride_even := by norm_num
  toPlus_stride_balance := by norm_num [firstStandardTwoRailGate]
  toMinus_stride_balance := by norm_num [firstStandardTwoRailGate]

/-- The complete affine family of the next standard gate shape. -/
def secondStandardTwoRailFamily : AffineTwoRailFamily where
  base := secondStandardTwoRailGate
  inputStride := 16384
  plusStride := 373248
  outputStride := 13122
  inputStride_even := by norm_num
  plusStride_even := by norm_num
  outputStride_even := by norm_num
  toPlus_stride_balance := by norm_num [secondStandardTwoRailGate]
  toMinus_stride_balance := by norm_num [secondStandardTwoRailGate]

/-- Exact universal handoff found by the index transducer.  It deletes a
13-bit source address and multiplies the unbounded residual tail by `3^7` in
the target index. -/
def firstToSecondStandardLink :
    AffineTwoRailLink firstStandardTwoRailFamily
      secondStandardTwoRailFamily where
  sourceIndexBase := 6245
  sourceIndexStride := 8192
  targetIndexBase := 1667
  targetIndexStride := 2187
  gap_link := by norm_num [firstStandardTwoRailFamily,
    secondStandardTwoRailFamily, firstStandardTwoRailGate,
    secondStandardTwoRailGate]
  payload_base_link := by norm_num [firstStandardTwoRailFamily,
    secondStandardTwoRailFamily, firstStandardTwoRailGate,
    secondStandardTwoRailGate]
  payload_stride_link := by norm_num [firstStandardTwoRailFamily,
    secondStandardTwoRailFamily]

theorem firstToSecondStandardLink_all_tails (u : ℕ) :
    (firstStandardTwoRailFamily.member
        (firstToSecondStandardLink.sourceIndex u)).endpoint =
      (secondStandardTwoRailFamily.member
        (firstToSecondStandardLink.targetIndex u)).start :=
  firstToSecondStandardLink.endpoint_link u

end KontoroC
