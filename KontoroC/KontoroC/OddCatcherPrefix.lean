/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OddCatcher
import KontoroC.TwoRailPrefixCode

/-!
# Complete dyadic cylinders for odd-gap catchers

Every exact odd catcher extends to a full affine family whose input stride is
`2^(a+2s+L+2)` and output stride is `2*3^(r+s+2)`.  The recovered positive
gap also proves that odd-catcher cylinders are disjoint from even-cleanup
cylinders at the same amplifier length.
-/

namespace KontoroC

/-- Shape parameters of the odd catcher at fixed amplifier length. -/
structure OddCatcherShape where
  cleanTicks : ℕ
  toPlusExtra : ℕ
  outputGap : ℕ
deriving DecidableEq

namespace OddCatcherGate

def shape (g : OddCatcherGate) : OddCatcherShape :=
  ⟨g.cleanTicks, g.toPlusExtra, g.outputGap⟩

def codeExponent (g : OddCatcherGate) : ℕ :=
  g.toPlusExtra + 2 * g.cleanTicks + g.outputGap + 2

def prefixInputStride (g : OddCatcherGate) : ℕ :=
  2 ^ g.codeExponent

def prefixPlusStride (g : OddCatcherGate) : ℕ :=
  3 ^ (g.ampTicks + 1) * 2 ^ (g.outputGap + 1)

def prefixOutputStride (g : OddCatcherGate) : ℕ :=
  2 * 3 ^ (g.ampTicks + g.cleanTicks + 2)

theorem prefix_toPlus_stride_balance (g : OddCatcherGate) :
    2 ^ g.toPlusExtra *
        (g.prefixPlusStride * 2 ^ (2 * g.cleanTicks + 1)) =
      3 ^ (g.ampTicks + 1) * g.prefixInputStride := by
  simp only [prefixPlusStride, prefixInputStride, codeExponent]
  rw [show g.toPlusExtra + 2 * g.cleanTicks + g.outputGap + 2 =
      g.toPlusExtra + (g.outputGap + 1) +
        (2 * g.cleanTicks + 1) by omega]
  simp only [pow_add]
  ring

theorem prefix_catcher_stride_balance (g : OddCatcherGate) :
    2 ^ g.outputGap * g.prefixOutputStride =
      3 ^ (g.cleanTicks + 1) * g.prefixPlusStride := by
  simp only [prefixOutputStride, prefixPlusStride]
  rw [show g.ampTicks + g.cleanTicks + 2 =
      (g.cleanTicks + 1) + (g.ampTicks + 1) by omega,
    show g.outputGap + 1 = g.outputGap + 1 by rfl]
  simp only [pow_add]
  norm_num
  ring

/-- The `z`th member of the complete odd-catcher cylinder. -/
def prefixMember (g : OddCatcherGate) (z : ℕ) : OddCatcherGate where
  ampTicks := g.ampTicks
  cleanTicks := g.cleanTicks
  toPlusExtra := g.toPlusExtra
  outputGap := g.outputGap
  inputPayload := g.inputPayload + g.prefixInputStride * z
  plusPayload := g.plusPayload + g.prefixPlusStride * z
  outputPayload := g.outputPayload + g.prefixOutputStride * z
  outputGap_pos := g.outputGap_pos
  inputPayload_pos := Nat.add_pos_left g.inputPayload_pos _
  plusPayload_pos := Nat.add_pos_left g.plusPayload_pos _
  outputPayload_pos := Nat.add_pos_left g.outputPayload_pos _
  inputPayload_odd := g.inputPayload_odd.add_even
    ((even_two.pow_of_ne_zero (by simp [codeExponent])).mul_right z)
  plusPayload_odd := g.plusPayload_odd.add_even
    ((Even.mul_left (even_two.pow_of_ne_zero (by omega)) _).mul_right z)
  outputPayload_odd := g.outputPayload_odd.add_even
    ((even_two.mul_right _).mul_right z)
  toPlus_balance := by
    let B := 3 ^ (g.ampTicks + 1) * g.inputPayload
    have hB : 0 < B := by
      dsimp [B]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) g.inputPayload_pos
    have hbase :
        2 ^ g.toPlusExtra *
              delayState g.plusPayload (2 * g.cleanTicks + 1) + 1 = B := by
      have hb := g.toPlus_balance
      omega
    have hleft :
        2 ^ g.toPlusExtra *
            delayState (g.plusPayload + g.prefixPlusStride * z)
              (2 * g.cleanTicks + 1) =
          2 ^ g.toPlusExtra *
              delayState g.plusPayload (2 * g.cleanTicks + 1) +
            (2 ^ g.toPlusExtra *
              (g.prefixPlusStride * 2 ^ (2 * g.cleanTicks + 1))) * z := by
      simp only [delayState]
      ring
    have hright :
        3 ^ (g.ampTicks + 1) *
            (g.inputPayload + g.prefixInputStride * z) =
          B + (3 ^ (g.ampTicks + 1) * g.prefixInputStride) * z := by
      dsimp [B]
      ring
    rw [hleft, hright, g.prefix_toPlus_stride_balance]
    omega
  catcher_balance := by
    let A := 2 ^ g.outputGap * g.outputPayload
    have hA : 0 < A := by
      dsimp [A]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
    have hinside :
        minusOneState (g.outputPayload + g.prefixOutputStride * z)
            g.outputGap =
          minusOneState g.outputPayload g.outputGap +
            (2 ^ g.outputGap * g.prefixOutputStride) * z := by
      have hprod :
          2 ^ g.outputGap *
              (g.outputPayload + g.prefixOutputStride * z) =
            A + (2 ^ g.outputGap * g.prefixOutputStride) * z := by
        dsimp [A]
        ring
      simp only [minusOneState]
      rw [hprod]
      omega
    have hright :
        2 + 3 ^ (g.cleanTicks + 1) *
            (g.plusPayload + g.prefixPlusStride * z) =
          (2 + 3 ^ (g.cleanTicks + 1) * g.plusPayload) +
            (3 ^ (g.cleanTicks + 1) * g.prefixPlusStride) * z := by
      ring
    rw [hinside, hright, g.catcher_balance,
      g.prefix_catcher_stride_balance]

@[simp] theorem prefixMember_ampTicks (g : OddCatcherGate) (z : ℕ) :
    (g.prefixMember z).ampTicks = g.ampTicks := rfl

@[simp] theorem prefixMember_shape (g : OddCatcherGate) (z : ℕ) :
    (g.prefixMember z).shape = g.shape := rfl

@[simp] theorem prefixMember_inputPayload (g : OddCatcherGate) (z : ℕ) :
    (g.prefixMember z).inputPayload =
      g.inputPayload + 2 ^ g.codeExponent * z := rfl

def prefixCylinder (g : OddCatcherGate) : Set ℕ :=
  Set.range fun z => (g.prefixMember z).inputPayload

/-- Literal odd-branch decoder: fixed amplifier length and input payload
uniquely recover the catcher shape and both hidden payloads. -/
theorem decoded_parameters_unique (g h : OddCatcherGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) :
    g.shape = h.shape ∧ g.plusPayload = h.plusPayload ∧
      g.outputPayload = h.outputPayload := by
  have hfactor := twoPow_mul_odd_unique
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 1))
    (delayState_odd (by omega : 0 < 2 * h.cleanTicks + 1))
    (show 2 ^ g.toPlusExtra * g.plusState =
        2 ^ h.toPlusExtra * h.plusState by
      calc
        2 ^ g.toPlusExtra * g.plusState =
            3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := g.toPlus_balance
        _ = 3 ^ (h.ampTicks + 1) * h.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ h.toPlusExtra * h.plusState := h.toPlus_balance.symm)
  have hplus := TwoRailGate.delayState_unique g.plusPayload_odd
    h.plusPayload_odd hfactor.2
  have hs : g.cleanTicks = h.cleanTicks := by omega
  have hendpoint : g.endpoint = h.endpoint := by
    rw [show g.endpoint = 2 + 3 ^ (g.cleanTicks + 1) * g.plusPayload by
      exact g.catcher_balance,
      show h.endpoint = 2 + 3 ^ (h.cleanTicks + 1) * h.plusPayload by
        exact h.catcher_balance,
      hs, hplus.2]
  have hout := TwoRailGate.minusOneState_unique g.outputPayload_pos
    h.outputPayload_pos g.outputGap_pos h.outputGap_pos
    g.outputPayload_odd h.outputPayload_odd hendpoint
  constructor
  · change OddCatcherShape.mk g.cleanTicks g.toPlusExtra g.outputGap =
      OddCatcherShape.mk h.cleanTicks h.toPlusExtra h.outputGap
    rw [hs, hfactor.1, hout.1]
  · exact ⟨hplus.2, hout.2⟩

theorem eq_of_ampTicks_inputPayload (g h : OddCatcherGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) : g = h := by
  have hd := g.decoded_parameters_unique h hr hP
  cases g
  cases h
  simp only [shape, OddCatcherShape.mk.injEq] at hd
  simp_all

/-- Distinct odd-catcher shapes at one amplifier length have disjoint
payload cylinders. -/
theorem prefixCylinder_disjoint (g h : OddCatcherGate)
    (hr : g.ampTicks = h.ampTicks) (hshape : g.shape ≠ h.shape) :
    Disjoint g.prefixCylinder h.prefixCylinder := by
  rw [Set.disjoint_left]
  intro P hg hh
  obtain ⟨z, hz⟩ := hg
  obtain ⟨w, hw⟩ := hh
  have hamp : (g.prefixMember z).ampTicks =
      (h.prefixMember w).ampTicks := by
    change g.ampTicks = h.ampTicks
    exact hr
  have hd := (g.prefixMember z).decoded_parameters_unique
    (h.prefixMember w) hamp (hz.trans hw.symm)
  exact hshape (by simpa using hd.1)

/-- An odd-gap gate and an even-gap gate at the same `(r,P)` cannot both
exist: their uniquely recovered positive-rail gaps have opposite parity. -/
theorem ne_evenGate_of_same_ampTicks_inputPayload
    (g : OddCatcherGate) (h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) : False := by
  have hfactor := twoPow_mul_odd_unique
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 1))
    (delayState_odd (by omega : 0 < 2 * h.cleanTicks + 2))
    (show 2 ^ g.toPlusExtra * g.plusState =
        2 ^ h.toPlusExtra * h.plusState by
      calc
        2 ^ g.toPlusExtra * g.plusState =
            3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := g.toPlus_balance
        _ = 3 ^ (h.ampTicks + 1) * h.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ h.toPlusExtra * h.plusState := h.toPlus_balance.symm)
  have hgap := TwoRailGate.delayState_unique g.plusPayload_odd
    h.plusPayload_odd hfactor.2
  omega

/-- Cross-branch prefix-freeness at one amplifier length. -/
theorem prefixCylinder_disjoint_even (g : OddCatcherGate) (h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks) :
    Disjoint g.prefixCylinder h.prefixCylinder := by
  rw [Set.disjoint_left]
  intro P hg hh
  obtain ⟨z, hz⟩ := hg
  obtain ⟨w, hw⟩ := hh
  have hamp : (g.prefixMember z).ampTicks =
      (h.prefixFamily.member w).ampTicks := by
    change g.ampTicks = h.ampTicks
    exact hr
  exact (g.prefixMember z).ne_evenGate_of_same_ampTicks_inputPayload
    (h.prefixFamily.member w) hamp (hz.trans hw.symm)

end OddCatcherGate

end KontoroC
