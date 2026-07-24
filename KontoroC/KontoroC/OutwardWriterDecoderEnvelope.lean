/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardWriterDecoderLiteral

/-!
# Finite-height bounds for literal writer--decoder cells

The exact writer and resonant-decoder balances impose a severe height cost on
one legal cell.  This module proves the two inequalities called QM168 in the
research notes, directly for `WriterDecoderCellPayload`.

The bounds make the symbol alphabet finite at every fixed positive source
charge.  They do not give a uniform bound along an outward orbit, whose charge
may grow.
-/

namespace KontoroC
namespace OutwardWriterDecoderEnvelope

open OutwardWriterDecoderLiteral OutwardWriterDecoderSemantics

/-- An outward decoder slope forces the one-run to be longer than the
zero-run.  This elementary fact is the only size consequence of the final
first-passage inequality needed below. -/
theorem zeroCount_lt_oneCount_of_outward {z o : ℕ}
    (houtward : 2 ^ (z + o) < 3 ^ o) : z < o := by
  by_contra hnot
  have hoz : o ≤ z := by omega
  have hthreeFour : 3 ^ o ≤ 4 ^ o :=
    Nat.pow_le_pow_left (by omega) o
  have hfour : 4 ^ o = 2 ^ (o + o) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  have hexponent : o + o ≤ z + o := by omega
  have htwo : 2 ^ (o + o) ≤ 2 ^ (z + o) :=
    Nat.pow_le_pow_right (by omega) hexponent
  rw [hfour] at hthreeFour
  omega

/-- The resonance correction is strictly smaller than the corresponding
power of two. -/
theorem decoderQuotient_lt_twoPow
    {cell : WriterDecoderCellData} :
    cell.decoderQuotient < 2 ^ cell.zeroCount := by
  have hpow : 0 < 2 ^ cell.zeroCount := by positivity
  have hscale : 1 ≤ 3 ^ (cell.counter + 1) :=
    Nat.one_le_pow _ _ (by omega)
  rw [cell.resonance]
  nlinarith

/-- If the resonant one-run is longer than the zero-run, the writer quotient
strictly dominates the decoder correction. -/
theorem writerQuotient_gt_decoderQuotient
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hone : cell.zeroCount < cell.oneCount) :
    cell.decoderQuotient < payload.writerQuotient := by
  have hq : 1 ≤ payload.targetQuotient := payload.targetQuotient_pos
  have hzpow : 0 < 2 ^ cell.zeroCount := by positivity
  have hdecoder := decoderQuotient_lt_twoPow (cell := cell)
  have hexp :
      cell.zeroCount + cell.zeroCount + cell.drain + 1 ≤
        cell.zeroCount + cell.oneCount + cell.drain := by omega
  have hpow_le :
      2 ^ (cell.zeroCount + cell.zeroCount + cell.drain + 1) ≤
        2 ^ (cell.zeroCount + cell.oneCount + cell.drain) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hlarge :
      2 * 2 ^ cell.zeroCount ≤
        2 ^ (cell.zeroCount + cell.oneCount + cell.drain) := by
    calc
      2 * 2 ^ cell.zeroCount ≤
          2 ^ (cell.zeroCount + cell.zeroCount + cell.drain + 1) := by
            rw [show cell.zeroCount + cell.zeroCount + cell.drain + 1 =
              cell.zeroCount + (cell.zeroCount + cell.drain + 1) by omega,
              pow_add]
            have : 2 ≤ 2 ^ (cell.zeroCount + cell.drain + 1) := by
              have hexponent : 1 ≤ cell.zeroCount + cell.drain + 1 := by omega
              have h := Nat.pow_le_pow_right (n := 2) (by decide) hexponent
              norm_num at h ⊢
              exact h
            nlinarith
      _ ≤ _ := hpow_le
  have hlargeQ :
      2 * 2 ^ cell.zeroCount ≤
        2 ^ (cell.zeroCount + cell.oneCount + cell.drain) *
          payload.targetQuotient := by
    exact hlarge.trans (Nat.le_mul_of_pos_right _ payload.targetQuotient_pos)
  rw [← payload.decoderBalance] at hlargeQ
  nlinarith

/-- The static correction `B=7+2^(p+4)d` is smaller than the source term
`9H`.  This is the key strict estimate behind both height bounds. -/
theorem correction_lt_nine_mul_source
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hone : cell.zeroCount < cell.oneCount) :
    cell.correction < 9 * H := by
  have hquotient := writerQuotient_gt_decoderQuotient payload hone
  have hpow : 16 ≤ 2 ^ (cell.counter + 4) := by
    rw [show cell.counter + 4 = 4 + cell.counter by omega, pow_add]
    norm_num
    exact Nat.one_le_pow _ _ (by omega)
  have hmulGap :
      2 ^ (cell.counter + 4) * cell.decoderQuotient +
          2 ^ (cell.counter + 4) ≤
        2 ^ (cell.counter + 4) * payload.writerQuotient := by
    calc
      2 ^ (cell.counter + 4) * cell.decoderQuotient +
          2 ^ (cell.counter + 4) =
          2 ^ (cell.counter + 4) * (cell.decoderQuotient + 1) := by ring
      _ ≤ 2 ^ (cell.counter + 4) * payload.writerQuotient :=
        Nat.mul_le_mul_left _ (by omega)
  rw [cell.correction_eq]
  have hwriter := payload.writerBalance
  nlinarith

/-- Exact finite-height counter budget (QM168a).  The standard resonance
choice is `zeroCount = 2*3^counter`; then every legal cell at charge `H`
pays the displayed exponential cost. -/
theorem writerDecoderCell_counter_budget
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hzeroCount : cell.zeroCount = 2 * 3 ^ cell.counter)
    (hone : cell.zeroCount < cell.oneCount) :
    2 ^ (4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain) <
      9 * H := by
  have htriple := payload.payloadTriple
  have hcorrection := correction_lt_nine_mul_source payload hone
  have hQ : 1 ≤ payload.targetQuotient := payload.targetQuotient_pos
  have hdepth :
      4 * 3 ^ cell.counter + cell.counter + 5 + cell.drain ≤
        cell.depth := by
    rw [cell.depth_eq, hzeroCount]
    omega
  have hpow_le :
      2 ^ (4 * 3 ^ cell.counter + cell.counter + 5 + cell.drain) ≤
        2 ^ cell.depth := Nat.pow_le_pow_right (by omega) hdepth
  have hdouble :
      2 * 2 ^ (4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain) =
        2 ^ (4 * 3 ^ cell.counter + cell.counter + 5 + cell.drain) := by
    rw [show 4 * 3 ^ cell.counter + cell.counter + 5 + cell.drain =
      (4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain) + 1 by omega,
      pow_succ]
    ring
  have hlarge :
      2 * 2 ^ (4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain) ≤
        9 * H + cell.correction := by
    rw [hdouble]
    calc
      2 ^ (4 * 3 ^ cell.counter + cell.counter + 5 + cell.drain) ≤
          2 ^ cell.depth := hpow_le
      _ ≤ 2 ^ cell.depth * payload.targetQuotient :=
        Nat.le_mul_of_pos_right _ payload.targetQuotient_pos
      _ = 9 * H + cell.correction := htriple.balance
  nlinarith

/-- The explicit finite `(counter, drain)` search space allowed by a source
charge.  Its generous rectangular cutoff is proved from the sharper
exponential test retained in the filter. -/
def heightAdmissibleSymbols (H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (9 * H)).product (Finset.range (9 * H))).filter fun symbol =>
    2 ^ (4 * 3 ^ symbol.1 + symbol.1 + 4 + symbol.2) < 9 * H

/-- Every literal cell with the standard resonance length belongs to the
explicit finite-height alphabet.  Thus enumeration of
`heightAdmissibleSymbols H` is exhaustive, not a guessed cutoff. -/
theorem WriterDecoderCellPayload.symbol_mem_heightAdmissibleSymbols
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hzeroCount : cell.zeroCount = 2 * 3 ^ cell.counter)
    (hone : cell.zeroCount < cell.oneCount) :
    (cell.counter, cell.drain) ∈ heightAdmissibleSymbols H := by
  have hbudget := writerDecoderCell_counter_budget payload hzeroCount hone
  let exponent :=
    4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain
  have hexponent : exponent < 9 * H := by
    exact (Nat.le_of_lt exponent.lt_two_pow_self).trans_lt hbudget
  have hcounter : cell.counter < 9 * H := by
    exact (show cell.counter ≤ exponent by dsimp [exponent]; omega).trans_lt hexponent
  have hdrain : cell.drain < 9 * H := by
    exact (show cell.drain ≤ exponent by dsimp [exponent]; omega).trans_lt hexponent
  simp [heightAdmissibleSymbols, hcounter, hdrain, hbudget]

/-- Counter budget in the native first-passage interface. -/
theorem writerDecoderCell_counter_budget_of_outward
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hzeroCount : cell.zeroCount = 2 * 3 ^ cell.counter)
    (houtward :
      2 ^ (cell.zeroCount + cell.oneCount) < 3 ^ cell.oneCount) :
    2 ^ (4 * 3 ^ cell.counter + cell.counter + 4 + cell.drain) <
      9 * H :=
  writerDecoderCell_counter_budget payload hzeroCount
    (zeroCount_lt_oneCount_of_outward houtward)

/-- Exhaustive finite-alphabet membership in the native first-passage
interface. -/
theorem WriterDecoderCellPayload.symbol_mem_heightAdmissibleSymbols_of_outward
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hzeroCount : cell.zeroCount = 2 * 3 ^ cell.counter)
    (houtward :
      2 ^ (cell.zeroCount + cell.oneCount) < 3 ^ cell.oneCount) :
    (cell.counter, cell.drain) ∈ heightAdmissibleSymbols H :=
  symbol_mem_heightAdmissibleSymbols payload hzeroCount
    (zeroCount_lt_oneCount_of_outward houtward)

/-- Exact output envelope (QM168b).  `hminimal` is the adjacent slope
inequality supplied by the minimal outward one-run. -/
theorem writerDecoderCell_output_envelope
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hone : cell.zeroCount < cell.oneCount)
    (hminimal :
      3 ^ (cell.oneCount - 1) ≤
        2 ^ (cell.zeroCount + cell.oneCount - 1)) :
    16 *
        (3 ^ (cell.counter + cell.oneCount + cell.drain) *
          payload.targetQuotient) *
        2 ^ (cell.counter + cell.drain) <
      27 * H * 3 ^ (cell.counter + cell.drain) := by
  have htriple := payload.payloadTriple
  have hcorrection := correction_lt_nine_mul_source payload hone
  have hbalance_lt : 2 ^ cell.depth * payload.targetQuotient < 18 * H := by
    rw [htriple.balance]
    nlinarith
  have honePos : 0 < cell.oneCount := by omega
  have hthree :
      3 ^ cell.oneCount ≤
        3 * 2 ^ (cell.zeroCount + cell.oneCount - 1) := by
    calc
      3 ^ cell.oneCount = 3 ^ (cell.oneCount - 1) * 3 := by
        rw [← pow_succ]
        congr 1
        omega
      _ ≤ 2 ^ (cell.zeroCount + cell.oneCount - 1) * 3 :=
        Nat.mul_le_mul_right 3 hminimal
      _ = 3 * 2 ^ (cell.zeroCount + cell.oneCount - 1) := by ring
  have hscaled :
      16 * 3 ^ cell.oneCount * payload.targetQuotient *
          2 ^ (cell.counter + cell.drain) < 27 * H := by
    have hpowSplit :
        2 ^ (cell.zeroCount + cell.oneCount - 1) *
            2 ^ (cell.counter + cell.drain) =
          2 ^ (cell.depth - 5) := by
      rw [← pow_add]
      congr 1
      rw [cell.depth_eq]
      omega
    have hdepthFive : 5 ≤ cell.depth := by
      rw [cell.depth_eq]
      omega
    have hfactor :
        2 * (48 *
            (2 ^ (cell.zeroCount + cell.oneCount - 1) *
              payload.targetQuotient *
              2 ^ (cell.counter + cell.drain))) =
          3 * (2 ^ cell.depth * payload.targetQuotient) := by
      calc
        2 * (48 *
            (2 ^ (cell.zeroCount + cell.oneCount - 1) *
              payload.targetQuotient *
              2 ^ (cell.counter + cell.drain))) =
            96 *
              (2 ^ (cell.zeroCount + cell.oneCount - 1) *
                2 ^ (cell.counter + cell.drain)) *
              payload.targetQuotient := by ring
        _ = 96 * 2 ^ (cell.depth - 5) *
              payload.targetQuotient := by rw [hpowSplit]
        _ = 3 * (2 ^ cell.depth * payload.targetQuotient) := by
          rw [show cell.depth = (cell.depth - 5) + 5 by omega, pow_add]
          norm_num
          ring
    have hscale_le :
        16 * 3 ^ cell.oneCount ≤
          48 * 2 ^ (cell.zeroCount + cell.oneCount - 1) := by
      omega
    have hscale_mul := Nat.mul_le_mul_right
      (payload.targetQuotient * 2 ^ (cell.counter + cell.drain)) hscale_le
    calc
      16 * 3 ^ cell.oneCount * payload.targetQuotient *
          2 ^ (cell.counter + cell.drain) ≤
          48 *
            (2 ^ (cell.zeroCount + cell.oneCount - 1) *
              payload.targetQuotient *
              2 ^ (cell.counter + cell.drain)) := by
            simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale_mul
      _ < 27 * H := by
        have hscaledTwice :
            2 * (48 *
              (2 ^ (cell.zeroCount + cell.oneCount - 1) *
                payload.targetQuotient *
                2 ^ (cell.counter + cell.drain))) <
              54 * H := by
          rw [hfactor]
          nlinarith
        nlinarith
  have hthreeFactor :
      3 ^ (cell.counter + cell.oneCount + cell.drain) =
        3 ^ (cell.counter + cell.drain) * 3 ^ cell.oneCount := by
    rw [show cell.counter + cell.oneCount + cell.drain =
      (cell.counter + cell.drain) + cell.oneCount by omega, pow_add]
  rw [hthreeFactor]
  have hbasePos : 0 < 3 ^ (cell.counter + cell.drain) := by positivity
  have hmul := (Nat.mul_lt_mul_left hbasePos).2 hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Output envelope in exactly the two adjacent slope hypotheses used to
certify the resonant decoder as first passage. -/
theorem writerDecoderCell_output_envelope_of_firstPassage
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hminimal :
      3 ^ (cell.oneCount - 1) ≤
        2 ^ (cell.zeroCount + cell.oneCount - 1))
    (houtward :
      2 ^ (cell.zeroCount + cell.oneCount) < 3 ^ cell.oneCount) :
    16 *
        (3 ^ (cell.counter + cell.oneCount + cell.drain) *
          payload.targetQuotient) *
        2 ^ (cell.counter + cell.drain) <
      27 * H * 3 ^ (cell.counter + cell.drain) :=
  writerDecoderCell_output_envelope payload
    (zeroCount_lt_oneCount_of_outward houtward) hminimal

end OutwardWriterDecoderEnvelope
end KontoroC
