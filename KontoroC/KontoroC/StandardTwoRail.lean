/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.TwoRailChain

/-!
# Arithmetic of the standard two-rail family

The experimental standard family uses one cleanup tick, collision extras one,
and increases the `-1` gap by one.  Eliminating its intermediate positive-rail
payload reveals a single nonautonomous recurrence.  This file proves that
reduction, a forced triadic property, and automatic outwardness.
-/

namespace KontoroC

namespace TwoRailGate

/-- The fixed shape used by the 247-round finite experiment. -/
def IsStandard (g : TwoRailGate) : Prop :=
  g.cleanTicks = 1 ∧
    g.toPlusExtra = 1 ∧
    g.toMinusExtra = 1 ∧
    g.outputGap = g.ampTicks + 2

namespace IsStandard

theorem first_balance (g : TwoRailGate) (h : g.IsStandard) :
    3 ^ (g.ampTicks + 1) * g.inputPayload =
      3 + 32 * g.plusPayload := by
  rcases h with ⟨hclean, hplus, _, _⟩
  have hb := g.toPlus_balance
  rw [hclean, hplus] at hb
  norm_num [delayState] at hb
  omega

theorem second_balance (g : TwoRailGate) (h : g.IsStandard) :
    2 ^ (g.ampTicks + 3) * g.outputPayload =
      3 + 9 * g.plusPayload := by
  rcases h with ⟨hclean, _, hminus, hgap⟩
  have hb := g.toMinus_balance
  rw [hclean, hminus, hgap] at hb
  norm_num [minusOneState] at hb
  have hApos : 0 < 2 ^ (g.ampTicks + 2) * g.outputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
  have hsub :
      2 ^ (g.ampTicks + 2) * g.outputPayload - 1 + 1 =
        2 ^ (g.ampTicks + 2) * g.outputPayload :=
    Nat.sub_add_cancel (by omega)
  rw [show g.ampTicks + 3 = (g.ampTicks + 2) + 1 by omega,
    pow_succ]
  calc
    (2 ^ (g.ampTicks + 2) * 2) * g.outputPayload =
        2 * (2 ^ (g.ampTicks + 2) * g.outputPayload) := by ring
    _ = 3 + 9 * g.plusPayload := by omega

/-- Eliminating the cleanup-rail payload leaves one exact recurrence between
successive `-1`-rail payloads. -/
theorem payload_recurrence (g : TwoRailGate) (h : g.IsStandard) :
    2 ^ (g.ampTicks + 8) * g.outputPayload =
      3 ^ (g.ampTicks + 3) * g.inputPayload + 69 := by
  have hfirst := h.first_balance g
  have hsecond := h.second_balance g
  calc
    2 ^ (g.ampTicks + 8) * g.outputPayload =
        32 * (2 ^ (g.ampTicks + 3) * g.outputPayload) := by
      rw [show g.ampTicks + 8 = 5 + (g.ampTicks + 3) by omega,
        pow_add]
      norm_num
      ring
    _ = 32 * (3 + 9 * g.plusPayload) := by rw [hsecond]
    _ = 9 * (3 ^ (g.ampTicks + 1) * g.inputPayload) + 69 := by
      rw [hfirst]
      ring
    _ = 3 ^ (g.ampTicks + 3) * g.inputPayload + 69 := by
      rw [show g.ampTicks + 3 = 2 + (g.ampTicks + 1) by omega,
        pow_add]
      norm_num
      ring

/-- Every outgoing standard payload is divisible by three but not by nine.
Thus the triadic valuation is forced to be exactly one at every linked
standard gate after the first. -/
theorem output_exactly_one_factor_three (g : TwoRailGate) (h : g.IsStandard) :
    3 ∣ g.outputPayload ∧ ¬9 ∣ g.outputPayload := by
  have hb := h.second_balance g
  have hrhs : 3 ∣ 3 + 9 * g.plusPayload := by
    exact dvd_add (dvd_refl 3) (by exact ⟨3 * g.plusPayload, by ring⟩)
  have hleft : 3 ∣ 2 ^ (g.ampTicks + 3) * g.outputPayload := by
    rw [hb]
    exact hrhs
  have hcop : Nat.Coprime 3 (2 ^ (g.ampTicks + 3)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  constructor
  · exact hcop.dvd_of_dvd_mul_left hleft
  · intro h9
    have h9left : 9 ∣ 2 ^ (g.ampTicks + 3) * g.outputPayload :=
      dvd_mul_of_dvd_right h9 _
    have h9sum : 9 ∣ 3 + 9 * g.plusPayload := by
      rw [← hb]
      exact h9left
    have h9tail : 9 ∣ 9 * g.plusPayload := dvd_mul_right 9 _
    have : 9 ∣ 3 := (Nat.dvd_add_left h9tail).mp h9sum
    norm_num at this

/-- The numerical inequality which makes the standard family an amplifier
from its very first allowed rail length. -/
theorem standard_power_gap {r : ℕ} (hr : 4 ≤ r) :
    2 ^ (r + 7) < 3 ^ (r + 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 4 + n + 7 = n + 11 by omega,
    show 4 + n + 3 = n + 7 by omega,
    show n + 11 = n + 11 by rfl,
    show n + 7 = n + 7 by rfl,
    pow_add, pow_add]
  norm_num only [pow_succ, pow_zero]
  have hpow : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by omega) n
  exact Nat.mul_lt_mul_of_le_of_lt hpow (by norm_num) (by positivity)

/-- Unlike a pure positive-rail splash, every standard gate with `r ≥ 4` is
automatically outward.  No separate numerical comparison is required in a
certificate. -/
theorem outward (g : TwoRailGate) (h : g.IsStandard)
    (hr : 4 ≤ g.ampTicks) : g.start < g.endpoint := by
  have hrec := h.payload_recurrence g
  have hpow := standard_power_gap hr
  have hlead :
      2 ^ (g.ampTicks + 7) * g.inputPayload <
        3 ^ (g.ampTicks + 3) * g.inputPayload :=
    (Nat.mul_lt_mul_right g.inputPayload_pos).2 hpow
  have hscaled :
      2 ^ (g.ampTicks + 7) * g.inputPayload <
        2 ^ (g.ampTicks + 8) * g.outputPayload := by
    rw [hrec]
    omega
  have hpayload : g.inputPayload < 2 * g.outputPayload := by
    have hfactor : 0 < 2 ^ (g.ampTicks + 7) := Nat.pow_pos (by omega)
    apply (Nat.mul_lt_mul_left hfactor).mp
    calc
      2 ^ (g.ampTicks + 7) * g.inputPayload <
          2 ^ (g.ampTicks + 8) * g.outputPayload := hscaled
      _ = 2 ^ (g.ampTicks + 7) * (2 * g.outputPayload) := by
        rw [show g.ampTicks + 8 = (g.ampTicks + 7) + 1 by omega,
          pow_succ]
        ring
  apply g.outward_iff.mpr
  rw [h.2.2.2]
  calc
    2 ^ (g.ampTicks + 1) * g.inputPayload <
        2 ^ (g.ampTicks + 1) * (2 * g.outputPayload) :=
      (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2 hpayload
    _ = 2 ^ (g.ampTicks + 2) * g.outputPayload := by
      rw [show g.ampTicks + 2 = (g.ampTicks + 1) + 1 by omega,
        pow_succ]
      ring

end IsStandard

end TwoRailGate

/-- An all-level linked program in the standard shape.  Outwardness is absent
from the fields because the arithmetic above derives it automatically. -/
structure LinkedStandardTwoRailProgram where
  gate : ℕ → TwoRailGate
  standard : ∀ t, (gate t).IsStandard
  ampTicks_ge_four : ∀ t, 4 ≤ (gate t).ampTicks
  start_large : 4 < (gate 0).start
  linked : ∀ t, (gate t).endpoint = (gate (t + 1)).start

namespace LinkedStandardTwoRailProgram

theorem payload_recurrence (g : LinkedStandardTwoRailProgram) (t : ℕ) :
    2 ^ ((g.gate t).ampTicks + 8) * (g.gate t).outputPayload =
      3 ^ ((g.gate t).ampTicks + 3) * (g.gate t).inputPayload + 69 :=
  (g.standard t).payload_recurrence (g.gate t)

theorem output_exactly_one_factor_three
    (g : LinkedStandardTwoRailProgram) (t : ℕ) :
    3 ∣ (g.gate t).outputPayload ∧ ¬9 ∣ (g.gate t).outputPayload :=
  (g.standard t).output_exactly_one_factor_three (g.gate t)

/-- The standard recurrence supplies the growth field of the general
two-rail endpoint. -/
def toInfiniteTwoRailProgram
    (g : LinkedStandardTwoRailProgram) : InfiniteTwoRailProgram where
  gate := g.gate
  start_large := g.start_large
  linked := g.linked
  outward t := (g.standard t).outward (g.gate t) (g.ampTicks_ge_four t)

/-- Sound endpoint specialized to the standard family: balances and linkage
alone, with rail lengths at least four, would disprove Collatz. -/
theorem not_conjecture (g : LinkedStandardTwoRailProgram) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toInfiniteTwoRailProgram.not_conjecture

end LinkedStandardTwoRailProgram

end KontoroC
