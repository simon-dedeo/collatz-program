/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SymbolicDispatcherBoundary

/-!
# Exact reverse decoder for the fixed-form charge bouncer

The forward bouncer exposes two opcodes through exact powers of different
primes.  The output first recovers the recharge count and odd quotient by its
three-adic factorization.  A second three-adic valuation recovers the defect
opcode, and elementary division then recovers the input.

This proves information preservation for every accepted transition.  It does
not construct an infinite accepted orbit.
-/

namespace KontoroC

/-- The arithmetic data carried by one accepted fixed-form bouncer step,
already rearranged into its decoder-friendly factorization. -/
structure ChargeBouncerStep where
  defectOpcode : ℕ
  rechargeCount : ℕ
  input : ℕ
  output : ℕ
  oddPart : ℕ
  input_pos : 0 < input
  oddPart_pos : 0 < oddPart
  input_three : 3 ∣ input
  oddPart_not_three : ¬3 ∣ oddPart
  output_eq : output = 3 ^ (114 * rechargeCount) * oddPart
  rearranged :
    3 ^ (17 * defectOpcode) * (input + 1) =
      2 ^ (23 * defectOpcode) *
        (1 + 2 ^ (154 * rechargeCount) * oddPart)

namespace ChargeBouncerStep

theorem input_succ_not_three (s : ChargeBouncerStep) :
    ¬3 ∣ s.input + 1 := by
  intro hd
  have hone : 3 ∣ 1 :=
    (Nat.dvd_add_iff_left s.input_three).mpr
      (by simpa [Nat.add_comm] using hd)
  norm_num at hone

/-- The output's exact three-adic factorization reads back the recharge count
and the complete odd quotient. -/
theorem output_readback (s : ChargeBouncerStep) :
    padicValNat 3 s.output = 114 * s.rechargeCount ∧
      s.output.divMaxPow 3 = s.oddPart := by
  have hout : s.output ≠ 0 := by
    rw [s.output_eq]
    exact Nat.mul_ne_zero (pow_ne_zero _ (by omega)) s.oddPart_pos.ne'
  have hs := Nat.maxPowDvdDiv_of_pow_mul_eq hout s.output_eq.symm
    s.oddPart_not_three
  exact Prod.mk.inj hs

/-- After output readback, one more three-adic valuation recovers the defect
opcode. -/
theorem opcode_readback (s : ChargeBouncerStep) :
    padicValNat 3
      (1 + 2 ^ (154 * s.rechargeCount) * s.oddPart) =
        17 * s.defectOpcode := by
  have hinput : s.input + 1 ≠ 0 := by omega
  have hbracket :
      1 + 2 ^ (154 * s.rechargeCount) * s.oddPart ≠ 0 := by omega
  have htwo : 2 ^ (23 * s.defectOpcode) ≠ 0 := by positivity
  have hthree : 3 ^ (17 * s.defectOpcode) ≠ 0 := by positivity
  have htow_not_three : ¬3 ∣ 2 ^ (23 * s.defectOpcode) := by
    exact (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mp
      (Nat.Coprime.pow_right (23 * s.defectOpcode)
        (by norm_num : Nat.Coprime 3 2))
  have hv := congrArg (padicValNat 3) s.rearranged
  rw [padicValNat.mul hthree hinput, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd s.input_succ_not_three,
      padicValNat.mul htwo hbracket,
      padicValNat.eq_zero_of_not_dvd htow_not_three] at hv
  omega

/-- Literal inverse formula for the input. -/
theorem input_readback (s : ChargeBouncerStep) :
    s.input =
      (2 ^ (23 * s.defectOpcode) *
        (1 + 2 ^ (154 * s.rechargeCount) * s.oddPart)) /
          3 ^ (17 * s.defectOpcode) - 1 := by
  rw [← s.rearranged]
  simp

/-- An accepted output uniquely determines both opcodes, the odd quotient,
and the input. -/
theorem data_eq_of_output_eq (s t : ChargeBouncerStep)
    (hout : s.output = t.output) :
    s.rechargeCount = t.rechargeCount ∧
      s.oddPart = t.oddPart ∧
        s.defectOpcode = t.defectOpcode ∧ s.input = t.input := by
  have hsout := s.output_readback
  have htout := t.output_readback
  have hhscale : 114 * s.rechargeCount = 114 * t.rechargeCount := by
    calc
      114 * s.rechargeCount = padicValNat 3 s.output := hsout.1.symm
      _ = padicValNat 3 t.output := by rw [hout]
      _ = 114 * t.rechargeCount := htout.1
  have hh : s.rechargeCount = t.rechargeCount := by omega
  have hq : s.oddPart = t.oddPart := by
    calc
      s.oddPart = s.output.divMaxPow 3 := hsout.2.symm
      _ = t.output.divMaxPow 3 := by rw [hout]
      _ = t.oddPart := htout.2
  have hmscale : 17 * s.defectOpcode = 17 * t.defectOpcode := by
    rw [← s.opcode_readback, ← t.opcode_readback, hh, hq]
  have hm : s.defectOpcode = t.defectOpcode := by omega
  have hinput : s.input = t.input := by
    rw [s.input_readback, t.input_readback, hh, hq, hm]
  exact ⟨hh, hq, hm, hinput⟩

end ChargeBouncerStep

end KontoroC
