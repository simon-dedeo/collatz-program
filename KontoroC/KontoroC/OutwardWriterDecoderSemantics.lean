/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCoarseHole

/-!
# Exact arithmetic semantics for writer--decoder target cells

This file supplies the arithmetic seam between the writer--decoder worker and
the coarse dyadic-hole theorem. It records only equations which are
*necessary* for a literal composite cell. It does not define a cell to be
executable and it makes no infinite-orbit claim.

The subtraction-free payload equation `2^D Q = 9 H + B` is the exact form of
`H = (2^D Q - B) / 9`. At a candidate next cell the incoming charge has the
form `H = 3^g Q₀`. The writer counter `p` also gives the exact quotient
equation `2^(p+4) W = 9 H + 7`.

These equations imply the coarse gate used in QM170f: counters `2,...,50`
use the decoder correction `B(p)`, while every counter at least `51` lies in
the single writer class with correction `7` modulo `2^55`.
-/

namespace KontoroC
namespace OutwardWriterDecoderSemantics

open OutwardCoarseHole

/-- Exact subtraction-free payload representation for one cell boundary. -/
structure PayloadTriple (correction depth quotient charge : ℕ) : Prop where
  charge_pos : 0 < charge
  quotient_pos : 0 < quotient
  quotient_odd : Odd quotient
  balance : 2 ^ depth * quotient = 9 * charge + correction

/-- The previous cell's output charge, parameterized by an affine odd
quotient family. -/
def incomingCharge (g q stride n : ℕ) : ℕ :=
  3 ^ g * (q + 2 * stride * n)

theorem nine_mul_incomingCharge (g q stride n : ℕ) :
    9 * incomingCharge g q stride n =
      3 ^ (g + 2) * (q + 2 * stride * n) := by
  simp only [incomingCharge, pow_add]
  norm_num
  ring

/-- The exact equations necessarily presented by a candidate next
writer--decoder target. `depth_ge` is explicit: in the concrete cell it
follows from `p≥2` and the minimal decoder length, whose general Lean proof is
a separate task.

`writerBalance` is stronger than the divisibility used by the obstruction:
literal exact valuation also says that `writerQuotient` is odd. -/
structure WriterDecoderTarget
    (g q stride : ℕ) (correction : ℕ → ℕ) (n : ℕ) where
  counter : ℕ
  depth : ℕ
  targetQuotient : ℕ
  writerQuotient : ℕ
  counter_ge : 2 ≤ counter
  depth_ge : 55 ≤ depth
  payload : PayloadTriple (correction counter) depth targetQuotient
    (incomingCharge g q stride n)
  writerQuotient_pos : 0 < writerQuotient
  writerQuotient_odd : Odd writerQuotient
  writerBalance :
    2 ^ (counter + 4) * writerQuotient =
      9 * incomingCharge g q stride n + 7

/-- Existential legality according to the exact target-cell equations. This
predicate permits the full unbounded counter alphabet. -/
def WriterDecoderCellEquations
    (g q stride : ℕ) (correction : ℕ → ℕ) (n : ℕ) : Prop :=
  Nonempty (WriterDecoderTarget g q stride correction n)

theorem WriterDecoderTarget.decoderBalance
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (t : WriterDecoderTarget g q stride correction n) :
    2 ^ t.depth * t.targetQuotient =
      3 ^ (g + 2) * (q + 2 * stride * n) + correction t.counter := by
  rw [t.payload.balance, nine_mul_incomingCharge]

/-- The exact payload equation at depth at least `55` implies the small-row
coarse gate. -/
theorem WriterDecoderTarget.smallCounterGate
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (t : WriterDecoderTarget g q stride correction n) :
    AffineCoarseGate (3 ^ (g + 2)) q stride
      (correction t.counter) n := by
  have hpow : 2 ^ 55 ∣ 2 ^ t.depth :=
    Nat.pow_dvd_pow 2 t.depth_ge
  have hdvd : 2 ^ 55 ∣
      3 ^ (g + 2) * (q + 2 * stride * n) + correction t.counter := by
    rw [← t.decoderBalance]
    exact dvd_mul_of_dvd_left hpow t.targetQuotient
  rw [AffineCoarseGate, Nat.ModEq]
  exact Nat.mod_eq_zero_of_dvd hdvd

/-- For a large counter, the exact writer equation implies the common tail
gate with correction `7`. -/
theorem WriterDecoderTarget.largeCounterGate
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (t : WriterDecoderTarget g q stride correction n)
    (hlarge : 51 ≤ t.counter) :
    AffineCoarseGate (3 ^ (g + 2)) q stride 7 n := by
  have hpow : 2 ^ 55 ∣ 2 ^ (t.counter + 4) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hdvd : 2 ^ 55 ∣
      3 ^ (g + 2) * (q + 2 * stride * n) + 7 := by
    rw [← nine_mul_incomingCharge, ← t.writerBalance]
    exact dvd_mul_of_dvd_left hpow t.writerQuotient
  rw [AffineCoarseGate, Nat.ModEq]
  exact Nat.mod_eq_zero_of_dvd hdvd

/-- QM170f's arithmetic implication: every candidate satisfying the exact
writer and decoder equations belongs to the forty-nine-small-rows-plus-one-
tail coarse legality relation. -/
theorem writerDecoderCellEquations_coarse
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (h : WriterDecoderCellEquations g q stride correction n) :
    CoarseWriterDecoderLegal (3 ^ (g + 2)) q stride correction n := by
  let t := Classical.choice h
  refine ⟨t.counter, t.counter_ge, ?_⟩
  by_cases hsmall : t.counter < 51
  · simp only [hsmall, if_true]
    exact t.smallCounterGate
  · simp only [hsmall, if_false]
    exact t.largeCounterGate (by omega)

theorem threePow_odd (g : ℕ) : Odd (3 ^ g) := by
  exact Odd.pow (by norm_num)

/-- No open ternary parameter tail can satisfy the exact next-cell equations
for every positive ordinary coefficient. The counter remains unbounded. -/
theorem exists_positive_open_tail_without_writerDecoderTarget
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride) (k u₀ : ℕ) :
    ∃ m, 0 < m ∧
      ¬ WriterDecoderCellEquations g q stride correction
        (u₀ + 3 ^ k * m) := by
  obtain ⟨m, hmpos, hmcoarse⟩ :=
    exists_positive_open_tail_not_coarseWriterDecoderLegal
      (3 ^ (g + 2)) q stride correction (threePow_odd _) hstride k u₀
  exact ⟨m, hmpos, fun htarget =>
    hmcoarse (writerDecoderCellEquations_coarse htarget)⟩

/-- No complete ternary parameter cylinder can force the exact target
equations, even with an arbitrarily large selected counter at each point. -/
theorem no_ternary_cylinder_forces_writerDecoderTarget
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride) (k a : ℕ) :
    ¬ ∀ n, n ≡ a [MOD 3 ^ k] →
      WriterDecoderCellEquations g q stride correction n := by
  intro hforces
  obtain ⟨n, _, hn3, hncoarse⟩ :=
    exists_large_not_coarseWriterDecoderLegal
      (3 ^ (g + 2)) q stride correction (threePow_odd _) hstride k a 0
  exact hncoarse (writerDecoderCellEquations_coarse (hforces n hn3))

end OutwardWriterDecoderSemantics
end KontoroC
