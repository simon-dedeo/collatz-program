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
  defectOpcode_pos : 0 < defectOpcode
  rechargeCount_pos : 0 < rechargeCount
  input_pos : 0 < input
  oddPart_pos : 0 < oddPart
  input_three : 3 ∣ input
  oddPart_odd : Odd oddPart
  oddPart_not_three : ¬3 ∣ oddPart
  output_eq : output = 3 ^ (114 * rechargeCount) * oddPart
  rearranged :
    3 ^ (17 * defectOpcode) * (input + 1) =
      2 ^ (23 * defectOpcode) *
        (1 + 2 ^ (154 * rechargeCount) * oddPart)

namespace ChargeBouncerStep

/-- The bracket exposed after the first opcode is odd.  This is the exact
two-adic condition which makes the input opcode readable from the input. -/
theorem bracket_odd (s : ChargeBouncerStep) :
    Odd (1 + 2 ^ (154 * s.rechargeCount) * s.oddPart) := by
  have hexp : 0 < 154 * s.rechargeCount :=
    Nat.mul_pos (by omega) s.rechargeCount_pos
  have hpow : Even (2 ^ (154 * s.rechargeCount)) := by
    rw [even_iff_two_dvd]
    exact dvd_pow_self 2 hexp.ne'
  exact (hpow.mul_right s.oddPart).one_add

theorem input_succ_not_three (s : ChargeBouncerStep) :
    ¬3 ∣ s.input + 1 := by
  intro hd
  have hone : 3 ∣ 1 :=
    (Nat.dvd_add_iff_left s.input_three).mpr
      (by simpa [Nat.add_comm] using hd)
  norm_num at hone

/-- The input's exact two-adic factorization reads back the defect opcode. -/
theorem input_opcode_readback (s : ChargeBouncerStep) :
    padicValNat 2 (s.input + 1) = 23 * s.defectOpcode := by
  have hinput : s.input + 1 ≠ 0 := by omega
  have hbracket :
      1 + 2 ^ (154 * s.rechargeCount) * s.oddPart ≠ 0 := by omega
  have htwo : 2 ^ (23 * s.defectOpcode) ≠ 0 := by positivity
  have hthree : 3 ^ (17 * s.defectOpcode) ≠ 0 := by positivity
  have hthree_not_two : ¬2 ∣ 3 ^ (17 * s.defectOpcode) := by
    exact (by norm_num : Nat.Prime 2).coprime_iff_not_dvd.mp
      (Nat.Coprime.pow_right (17 * s.defectOpcode)
        (by norm_num : Nat.Coprime 2 3))
  have hbracket_not_two :
      ¬2 ∣ 1 + 2 ^ (154 * s.rechargeCount) * s.oddPart :=
    s.bracket_odd.not_two_dvd_nat
  have hv := congrArg (padicValNat 2) s.rearranged
  rw [padicValNat.mul hthree hinput,
      padicValNat.eq_zero_of_not_dvd hthree_not_two,
      padicValNat.mul htwo hbracket, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hbracket_not_two] at hv
  omega

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

/-- Every accepted fixed-form transition is strictly outward.  This follows
directly from `2^23 < 3^17` and `2^154 < 3^114`; no macro replay is needed. -/
theorem strictly_outward (s : ChargeBouncerStep) : s.input < s.output := by
  let Cpow := 3 ^ (17 * s.defectOpcode)
  let Dpow := 2 ^ (23 * s.defectOpcode)
  let Apow := 3 ^ (114 * s.rechargeCount)
  let Bpow := 2 ^ (154 * s.rechargeCount)
  let bracket := 1 + Bpow * s.oddPart
  have hCDbase : 2 ^ 23 < 3 ^ 17 := by norm_num
  have hABbase : 2 ^ 154 < 3 ^ 114 := by norm_num
  have hCD : Dpow < Cpow := by
    dsimp [Cpow, Dpow]
    rw [pow_mul, pow_mul]
    exact (Nat.pow_lt_pow_iff_left s.defectOpcode_pos.ne').2 hCDbase
  have hAB : Bpow < Apow := by
    dsimp [Apow, Bpow]
    rw [pow_mul, pow_mul]
    exact (Nat.pow_lt_pow_iff_left s.rechargeCount_pos.ne').2 hABbase
  have hbracket : 0 < bracket := by dsimp [bracket]; omega
  have hsmall : s.input + 1 < bracket := by
    by_contra hnot
    have hle : bracket ≤ s.input + 1 := by omega
    have hstrict : Dpow * bracket < Cpow * bracket :=
      (Nat.mul_lt_mul_right hbracket).2 hCD
    have hlarge : Cpow * bracket ≤ Cpow * (s.input + 1) :=
      Nat.mul_le_mul_left Cpow hle
    have heq : Cpow * (s.input + 1) = Dpow * bracket := by
      simpa [Cpow, Dpow, Bpow, bracket] using s.rearranged
    omega
  have hinput_B : s.input < Bpow * s.oddPart := by
    dsimp [bracket] at hsmall
    omega
  have hBA : Bpow * s.oddPart < Apow * s.oddPart :=
    (Nat.mul_lt_mul_right s.oddPart_pos).2 hAB
  rw [s.output_eq]
  simpa [Apow] using hinput_B.trans hBA

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

/-- The accepted equations are deterministic in the forward direction as
well: the input reads the first opcode, and the remaining odd factorization
then reads the recharge count and quotient. -/
theorem data_eq_of_input_eq (s t : ChargeBouncerStep)
    (hin : s.input = t.input) :
    s.defectOpcode = t.defectOpcode ∧
      s.rechargeCount = t.rechargeCount ∧
        s.oddPart = t.oddPart ∧ s.output = t.output := by
  have hmscale : 23 * s.defectOpcode = 23 * t.defectOpcode := by
    rw [← s.input_opcode_readback, ← t.input_opcode_readback, hin]
  have hm : s.defectOpcode = t.defectOpcode := by omega
  have hbracket :
      1 + 2 ^ (154 * s.rechargeCount) * s.oddPart =
        1 + 2 ^ (154 * t.rechargeCount) * t.oddPart := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.pow_pos (by omega : 0 < 2) : 0 < 2 ^ (23 * s.defectOpcode))
    calc
      2 ^ (23 * s.defectOpcode) *
          (1 + 2 ^ (154 * s.rechargeCount) * s.oddPart) =
        3 ^ (17 * s.defectOpcode) * (s.input + 1) := s.rearranged.symm
      _ = 3 ^ (17 * t.defectOpcode) * (t.input + 1) := by rw [hm, hin]
      _ = 2 ^ (23 * t.defectOpcode) *
          (1 + 2 ^ (154 * t.rechargeCount) * t.oddPart) := t.rearranged
      _ = 2 ^ (23 * s.defectOpcode) *
          (1 + 2 ^ (154 * t.rechargeCount) * t.oddPart) := by rw [hm]
  have hfactor :
      2 ^ (154 * s.rechargeCount) * s.oddPart =
        2 ^ (154 * t.rechargeCount) * t.oddPart :=
    Nat.add_left_cancel hbracket
  have hnonzero :
      2 ^ (154 * s.rechargeCount) * s.oddPart ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ (by omega)) s.oddPart_pos.ne'
  have hs := Nat.maxPowDvdDiv_of_pow_mul_eq hnonzero rfl
    s.oddPart_odd.not_two_dvd_nat
  have ht := Nat.maxPowDvdDiv_of_pow_mul_eq hnonzero hfactor.symm
    t.oddPart_odd.not_two_dvd_nat
  have hpair :
      154 * s.rechargeCount = 154 * t.rechargeCount ∧
        s.oddPart = t.oddPart :=
    Prod.mk.inj (hs.symm.trans ht)
  have hhscale : 154 * s.rechargeCount = 154 * t.rechargeCount :=
    hpair.1
  have hh : s.rechargeCount = t.rechargeCount := by omega
  have hq : s.oddPart = t.oddPart := hpair.2
  have hout : s.output = t.output := by
    rw [s.output_eq, t.output_eq, hh, hq]
  exact ⟨hm, hh, hq, hout⟩

end ChargeBouncerStep

/-- Directed edge relation of the accepted fixed-form bouncer. -/
def ChargeBouncerPrecedes (input output : ℕ) : Prop :=
  ∃ s : ChargeBouncerStep, s.input = input ∧ s.output = output

theorem chargeBouncerPrecedes_lt {input output : ℕ}
    (h : ChargeBouncerPrecedes input output) : input < output := by
  obtain ⟨s, rfl, rfl⟩ := h
  exact s.strictly_outward

/-- There is at most one accepted successor of any input. -/
theorem chargeBouncerPrecedes_forward_unique {input left right : ℕ}
    (hleft : ChargeBouncerPrecedes input left)
    (hright : ChargeBouncerPrecedes input right) : left = right := by
  obtain ⟨s, hsinput, hsoutput⟩ := hleft
  obtain ⟨t, htinput, htoutput⟩ := hright
  have hin : s.input = t.input := hsinput.trans htinput.symm
  exact hsoutput.symm.trans ((s.data_eq_of_input_eq t hin).2.2.2.trans htoutput)

/-- There is at most one accepted predecessor of any output. -/
theorem chargeBouncerPrecedes_backward_unique {left right output : ℕ}
    (hleft : ChargeBouncerPrecedes left output)
    (hright : ChargeBouncerPrecedes right output) : left = right := by
  obtain ⟨s, hsinput, hsoutput⟩ := hleft
  obtain ⟨t, htinput, htoutput⟩ := hright
  have hout : s.output = t.output := hsoutput.trans htoutput.symm
  exact hsinput.symm.trans ((s.data_eq_of_output_eq t hout).2.2.2.trans htinput)

/-- The accepted graph is well-founded in the reverse direction.  Thus it has
no cycle or bi-infinite trajectory; a counterexample witness would have to be
a genuinely one-sided infinite outward ray. -/
theorem chargeBouncerPrecedes_wellFounded :
    WellFounded ChargeBouncerPrecedes :=
  Subrelation.wf chargeBouncerPrecedes_lt Nat.lt_wfRel.wf

end KontoroC
