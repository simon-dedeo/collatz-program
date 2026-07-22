/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SymbolicDispatcherBoundary

/-!
# Rank-one opcode banks do not imply an impossibility theorem

The synthesized-marker bank has a useful rank-one normal form: every source
and output depends on one natural register, and every individual opcode has
positive coefficient drift.  Those two properties alone do not obstruct an
ordinary infinite ray.

This file gives a deliberately elementary countermodel.  Opcode `j` has
source slope `2^(j*j)` and output slope equal to the next source slope.  Thus
every opcode is outward, its gain factor strictly increases with `j`, and the
unbounded opcode schedule `0,1,2,...` links exactly.  The register is the
ordinary natural `1`.

This is not a Collatz orbit.  Its role is logical: any no-go theorem for the
actual marker bank must use additional arithmetic information, such as the
exact source/output constants, the Collatz valuation law, or a theorem tying
unbounded opcode changes to nonzero canonical-address extensions.
-/

namespace KontoroC

/-- Every proposed positive period fails after every finite prefix. -/
def GenuinelyAperiodicSequence {α : Type*} (a : ℕ → α) : Prop :=
  ∀ K p, 0 < p → ∃ t, a (K + (t + p)) ≠ a (K + t)

/-- The semantic data actually needed to turn a family of rank-one affine
instructions into an infinite outward ray. -/
structure RankOneOutwardRay where
  source : ℕ → ℕ → ℕ
  output : ℕ → ℕ → ℕ
  opcode : ℕ → ℕ
  register : ℕ
  register_pos : 0 < register
  linked : ∀ t,
    output (opcode t) register = source (opcode (t + 1)) register
  outward : ∀ t,
    source (opcode t) register < output (opcode t) register
  opcode_aperiodic : GenuinelyAperiodicSequence opcode

namespace ToyRankOneBank

/-- Superexponential source slopes make the per-opcode gain increase, while
remaining a one-register system. -/
def sourceSlope (j : ℕ) : ℕ := 2 ^ (j * j)

/-- Output opcode `j` lands at the slope of source opcode `j+1`. -/
def outputSlope (j : ℕ) : ℕ := sourceSlope (j + 1)

def source (j v : ℕ) : ℕ := sourceSlope j * v

def output (j v : ℕ) : ℕ := outputSlope j * v

def opcode (t : ℕ) : ℕ := t

/-- The exact gain factor of opcode `j` is `2^(2*j+1)`. -/
theorem outputSlope_eq_gain_mul_sourceSlope (j : ℕ) :
    outputSlope j = 2 ^ (2 * j + 1) * sourceSlope j := by
  rw [outputSlope, sourceSlope, sourceSlope]
  rw [show (j + 1) * (j + 1) = (2 * j + 1) + j * j by ring]
  rw [pow_add]

/-- The gain factor is strictly increasing with the opcode. -/
theorem gain_strictly_mono (j : ℕ) :
    2 ^ (2 * j + 1) < 2 ^ (2 * (j + 1) + 1) := by
  exact (Nat.pow_lt_pow_iff_right (by omega)).2 (by omega)

theorem linked (t v : ℕ) :
    output (opcode t) v = source (opcode (t + 1)) v := rfl

theorem outward (j v : ℕ) (hv : 0 < v) :
    source j v < output j v := by
  apply Nat.mul_lt_mul_of_pos_right _ hv
  unfold outputSlope sourceSlope
  exact (Nat.pow_lt_pow_iff_right (by omega)).2 (by nlinarith)

theorem opcode_genuinelyAperiodic : GenuinelyAperiodicSequence opcode := by
  intro K p hp
  refine ⟨0, ?_⟩
  simp only [opcode, Nat.zero_add]
  omega

/-- A rank-one, increasing-gain, genuinely aperiodic infinite outward ray
carried by the single ordinary register `1`. -/
def ray : RankOneOutwardRay where
  source := source
  output := output
  opcode := opcode
  register := 1
  register_pos := by omega
  linked t := linked t 1
  outward t := outward t 1 (by omega)
  opcode_aperiodic := opcode_genuinelyAperiodic

end ToyRankOneBank

/-- Therefore rank one, outward drift, increasing opcode gains, and an
unbounded aperiodic opcode schedule are logically compatible. -/
theorem exists_rankOne_outward_aperiodic_ordinary_ray :
    Nonempty RankOneOutwardRay :=
  ⟨ToyRankOneBank.ray⟩

end KontoroC
