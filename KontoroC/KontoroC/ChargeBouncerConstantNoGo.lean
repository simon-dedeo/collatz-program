/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerPadic
import KontoroC.AffineQuotientNoGo

/-!
# Eventually constant charge-bouncer opcodes are impossible

This file works entirely at the arithmetic `ChargeBouncerStep` level.  If the
positive defect and recharge opcodes freeze to `(m,h)`, the compressed states
obey one expanding coprime affine-gain recurrence.  The fixed-point defect
then acquires arbitrarily large powers of its binary denominator, contradicting
positivity.

This does not use or provide the separate compiler from normalized bouncer
coordinates to literal Collatz valuation words.  It closes an arithmetic ray
class; genuinely changing public feedback remains open.
-/

namespace KontoroC

namespace ChargeBouncerConstantNoGo

def blockA (m h : ℕ) : ℕ := 3 ^ (17 * m + 114 * h)
def blockB (m h : ℕ) : ℕ := 2 ^ (23 * m + 154 * h)
def blockGain (m h : ℕ) : ℕ :=
  3 ^ (114 * h) * (3 ^ (17 * m) - 2 ^ (23 * m))

theorem block_gap {m h : ℕ} (hm : 0 < m) (hh : 0 < h) :
    blockB m h < blockA m h := by
  have hdefectBase : 2 ^ 23 < 3 ^ 17 := by norm_num
  have hrechargeBase : 2 ^ 154 < 3 ^ 114 := by norm_num
  have hdefect : (2 ^ 23) ^ m < (3 ^ 17) ^ m :=
    (Nat.pow_lt_pow_iff_left hm.ne').2 hdefectBase
  have hrecharge : (2 ^ 154) ^ h < (3 ^ 114) ^ h :=
    (Nat.pow_lt_pow_iff_left hh.ne').2 hrechargeBase
  dsimp [blockA, blockB]
  rw [pow_add, pow_add, pow_mul, pow_mul, pow_mul, pow_mul]
  exact ((Nat.mul_lt_mul_right (by positivity)).2 hdefect).trans
    ((Nat.mul_lt_mul_left (by positivity)).2 hrecharge)

def fixedOpcodeOrbit (g : InfiniteChargeBouncerRay) (m h : ℕ)
    (hm : ∀ t, (g.stepData t).defectOpcode = m)
    (hh : ∀ t, (g.stepData t).rechargeCount = h) :
    PositiveAffineGainOrbit (blockA m h) (blockB m h) (blockGain m h) where
  value := g.state
  value_pos := g.state_pos
  balance t := by
    have hr := g.recurrence t
    simp only [InfiniteChargeBouncerRay.schedule,
      ChargeBouncerOpcodeSchedule.binaryExponent,
      ChargeBouncerOpcodeSchedule.ternaryExponent,
      ChargeBouncerOpcodeSchedule.gain] at hr
    rw [hm t, hh t] at hr
    simpa [blockA, blockB, blockGain] using hr

/-- No arithmetic bouncer ray can repeat one positive opcode pair forever. -/
theorem no_constant_opcode_ray
    (g : InfiniteChargeBouncerRay) (m h : ℕ)
    (hm_pos : 0 < m) (hh_pos : 0 < h)
    (hm : ∀ t, (g.stepData t).defectOpcode = m)
    (hh : ∀ t, (g.stepData t).rechargeCount = h) : False := by
  let o := fixedOpcodeOrbit g m h hm hh
  have hcop : (blockA m h).Coprime (blockB m h) := by
    dsimp [blockA, blockB]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  have hBone : 1 < blockB m h := by
    apply Nat.one_lt_pow
    · dsimp [blockB]
      omega
    · omega
  exact o.impossible hcop hBone (block_gap hm_pos hh_pos)

def tail (g : InfiniteChargeBouncerRay) (K : ℕ) : InfiniteChargeBouncerRay where
  state t := g.state (K + t)
  stepData t := g.stepData (K + t)
  input_eq t := g.input_eq (K + t)
  output_eq t := by
    simpa [Nat.add_assoc] using g.output_eq (K + t)

/-- Even after an arbitrary transient, the two compressed opcodes cannot both
freeze. -/
theorem no_eventually_constant_opcode_ray
    (g : InfiniteChargeBouncerRay) (K m h : ℕ)
    (hm_pos : 0 < m) (hh_pos : 0 < h)
    (hm : ∀ t, K ≤ t → (g.stepData t).defectOpcode = m)
    (hh : ∀ t, K ≤ t → (g.stepData t).rechargeCount = h) : False := by
  apply no_constant_opcode_ray (tail g K) m h hm_pos hh_pos
  · intro t
    exact hm (K + t) (by omega)
  · intro t
    exact hh (K + t) (by omega)

def pairA (m₀ h₀ m₁ h₁ : ℕ) : ℕ :=
  blockA m₀ h₀ * blockA m₁ h₁

def pairB (m₀ h₀ m₁ h₁ : ℕ) : ℕ :=
  blockB m₀ h₀ * blockB m₁ h₁

/-- Gain obtained by eliminating the middle state from two consecutive
compressed bouncer recurrences. -/
def pairGain (m₀ h₀ m₁ h₁ : ℕ) : ℕ :=
  blockA m₁ h₁ * blockGain m₀ h₀ +
    blockB m₀ h₀ * blockGain m₁ h₁

theorem pair_gap
    {m₀ h₀ m₁ h₁ : ℕ}
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀)
    (hm₁ : 0 < m₁) (hh₁ : 0 < h₁) :
    pairB m₀ h₀ m₁ h₁ < pairA m₀ h₀ m₁ h₁ := by
  have hgap₀ := block_gap hm₀ hh₀
  have hgap₁ := block_gap hm₁ hh₁
  dsimp [pairA, pairB]
  have hB₁ : 0 < blockB m₁ h₁ := by simp [blockB]
  have hA₀ : 0 < blockA m₀ h₀ := by simp [blockA]
  exact ((Nat.mul_lt_mul_right hB₁).2 hgap₀).trans
    ((Nat.mul_lt_mul_left hA₀).2 hgap₁)

def alternatingOpcodeOrbit
    (g : InfiniteChargeBouncerRay) (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : ∀ t, (g.stepData (2 * t)).defectOpcode = m₀)
    (hh₀ : ∀ t, (g.stepData (2 * t)).rechargeCount = h₀)
    (hm₁ : ∀ t, (g.stepData (2 * t + 1)).defectOpcode = m₁)
    (hh₁ : ∀ t, (g.stepData (2 * t + 1)).rechargeCount = h₁) :
    PositiveAffineGainOrbit
      (pairA m₀ h₀ m₁ h₁) (pairB m₀ h₀ m₁ h₁)
      (pairGain m₀ h₀ m₁ h₁) where
  value t := g.state (2 * t)
  value_pos t := g.state_pos (2 * t)
  balance t := by
    have hr₀ := g.recurrence (2 * t)
    have hr₁ := g.recurrence (2 * t + 1)
    simp only [InfiniteChargeBouncerRay.schedule,
      ChargeBouncerOpcodeSchedule.binaryExponent,
      ChargeBouncerOpcodeSchedule.ternaryExponent,
      ChargeBouncerOpcodeSchedule.gain] at hr₀ hr₁
    rw [hm₀ t, hh₀ t] at hr₀
    rw [hm₁ t, hh₁ t] at hr₁
    change blockB m₀ h₀ * blockB m₁ h₁ * g.state (2 * (t + 1)) =
      blockA m₀ h₀ * blockA m₁ h₁ * g.state (2 * t) +
        (blockA m₁ h₁ * blockGain m₀ h₀ +
          blockB m₀ h₀ * blockGain m₁ h₁)
    have hr₀' : blockB m₀ h₀ * g.state (2 * t + 1) =
        blockA m₀ h₀ * g.state (2 * t) + blockGain m₀ h₀ := by
      simpa [blockA, blockB, blockGain] using hr₀
    have hr₁' : blockB m₁ h₁ * g.state (2 * (t + 1)) =
        blockA m₁ h₁ * g.state (2 * t + 1) + blockGain m₁ h₁ := by
      have hidx : 2 * t + 1 + 1 = 2 * (t + 1) := by omega
      simpa [blockA, blockB, blockGain, hidx] using hr₁
    calc
      blockB m₀ h₀ * blockB m₁ h₁ * g.state (2 * (t + 1)) =
          blockB m₀ h₀ *
            (blockB m₁ h₁ * g.state (2 * (t + 1))) := by ring
      _ = blockB m₀ h₀ *
          (blockA m₁ h₁ * g.state (2 * t + 1) + blockGain m₁ h₁) := by
            rw [hr₁']
      _ = blockA m₁ h₁ *
          (blockB m₀ h₀ * g.state (2 * t + 1)) +
            blockB m₀ h₀ * blockGain m₁ h₁ := by ring
      _ = blockA m₁ h₁ *
          (blockA m₀ h₀ * g.state (2 * t) + blockGain m₀ h₀) +
            blockB m₀ h₀ * blockGain m₁ h₁ := by rw [hr₀']
      _ = blockA m₀ h₀ * blockA m₁ h₁ * g.state (2 * t) +
          (blockA m₁ h₁ * blockGain m₀ h₀ +
            blockB m₀ h₀ * blockGain m₁ h₁) := by ring

/-- The shortest nonconstant periodic compressed schedule is impossible. -/
theorem no_alternating_opcode_ray
    (g : InfiniteChargeBouncerRay) (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀_pos : 0 < m₀) (hh₀_pos : 0 < h₀)
    (hm₁_pos : 0 < m₁) (hh₁_pos : 0 < h₁)
    (hm₀ : ∀ t, (g.stepData (2 * t)).defectOpcode = m₀)
    (hh₀ : ∀ t, (g.stepData (2 * t)).rechargeCount = h₀)
    (hm₁ : ∀ t, (g.stepData (2 * t + 1)).defectOpcode = m₁)
    (hh₁ : ∀ t, (g.stepData (2 * t + 1)).rechargeCount = h₁) : False := by
  let o := alternatingOpcodeOrbit g m₀ h₀ m₁ h₁ hm₀ hh₀ hm₁ hh₁
  have hcop : (pairA m₀ h₀ m₁ h₁).Coprime
      (pairB m₀ h₀ m₁ h₁) := by
    rw [show pairA m₀ h₀ m₁ h₁ =
        3 ^ ((17 * m₀ + 114 * h₀) + (17 * m₁ + 114 * h₁)) by
          simp [pairA, blockA, pow_add],
      show pairB m₀ h₀ m₁ h₁ =
        2 ^ ((23 * m₀ + 154 * h₀) + (23 * m₁ + 154 * h₁)) by
          simp [pairB, blockB, pow_add]]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  have hBone : 1 < pairB m₀ h₀ m₁ h₁ := by
    dsimp [pairB, blockB]
    have hleft : 1 < 2 ^ (23 * m₀ + 154 * h₀) :=
      Nat.one_lt_pow (by omega) (by omega)
    have hright : 0 < 2 ^ (23 * m₁ + 154 * h₁) := by positivity
    nlinarith
  exact o.impossible hcop hBone (pair_gap hm₀_pos hh₀_pos hm₁_pos hh₁_pos)

/-- Alternation remains impossible after an arbitrary finite transient. -/
theorem no_eventually_alternating_opcode_ray
    (g : InfiniteChargeBouncerRay) (K m₀ h₀ m₁ h₁ : ℕ)
    (hm₀_pos : 0 < m₀) (hh₀_pos : 0 < h₀)
    (hm₁_pos : 0 < m₁) (hh₁_pos : 0 < h₁)
    (hm₀ : ∀ t, (g.stepData (K + 2 * t)).defectOpcode = m₀)
    (hh₀ : ∀ t, (g.stepData (K + 2 * t)).rechargeCount = h₀)
    (hm₁ : ∀ t, (g.stepData (K + (2 * t + 1))).defectOpcode = m₁)
    (hh₁ : ∀ t, (g.stepData (K + (2 * t + 1))).rechargeCount = h₁) : False := by
  apply no_alternating_opcode_ray (tail g K) m₀ h₀ m₁ h₁
    hm₀_pos hh₀_pos hm₁_pos hh₁_pos
  · intro t
    change (g.stepData (K + 2 * t)).defectOpcode = m₀
    exact hm₀ t
  · intro t
    change (g.stepData (K + 2 * t)).rechargeCount = h₀
    exact hh₀ t
  · intro t
    change (g.stepData (K + (2 * t + 1))).defectOpcode = m₁
    exact hm₁ t
  · intro t
    change (g.stepData (K + (2 * t + 1))).rechargeCount = h₁
    exact hh₁ t

end ChargeBouncerConstantNoGo

end KontoroC
