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

end ChargeBouncerConstantNoGo

end KontoroC
