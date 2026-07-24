/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardResonantDecoder
import KontoroC.OutwardBoundaryRenewal
import KontoroC.OutwardInvariantBridge

/-!
# Literal semantics of an all-parameter writer--decoder cell

This file composes the fixed first-passage writer `010111`, its selected
one-letter drain, a symbolic resonant decoder `0^z 1^o`, and the decoder's
selected drain.  The main theorem is an exact literal shortcut execution;
it does not infer that the composite pieces form consecutive first-passage
blocks unless the separate first-passage hypotheses are supplied.
-/

namespace KontoroC
namespace OutwardWriterDecoderLiteral

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardFirstPassage OutwardBoundaryRenewal OutwardResonantDecoder
  OutwardWriterDecoderSemantics OutwardCoarseHole
  OutwardInvariantBridge OutwardOddSlice

def writerWord : List Bool :=
  [false, true, false, true, true, true]

theorem writerWord_length : writerWord.length = 6 := rfl

theorem writerWord_oddCount : writerWord.count true = 4 := rfl

theorem writerWord_firstPassage : FirstPassage writerWord := by
  constructor
  · norm_num [writerWord, WordOutward]
  · intro u hu
    have hlen : u.length < 6 := by
      simpa [writerWord] using properPrefix_length_lt hu
    have hprefix := hu.1
    rw [List.prefix_iff_eq_take] at hprefix
    rw [hprefix]
    have hle : u.length ≤ 5 := by omega
    interval_cases h : u.length <;>
      norm_num [writerWord, WordOutward] at hlen ⊢

theorem writer_base_executes : Executes writerWord 18 26 := by
  simp only [writerWord, Executes]
  exact ⟨9, by norm_num,
    ⟨14, by norm_num,
    ⟨7, by norm_num,
    ⟨11, by norm_num,
    ⟨17, by norm_num,
    ⟨26, by norm_num, by norm_num⟩⟩⟩⟩⟩⟩

/-- The exact writer equation selects the counter `p`, executes `010111`,
and drains `p-2` one-letter boundary blocks. -/
theorem writer_then_drain_executes
    {p H W : ℕ} (hp : 2 ≤ p) (hW : 0 < W)
    (hbalance : 2 ^ (p + 4) * W = 9 * H + 7) :
    Executes (writerWord ++ List.replicate (p - 2) true)
      (3 * H - 1) (3 * (3 ^ p * W) - 1) := by
  let R := 2 ^ (p - 2) * W
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hpow : 2 ^ (p + 4) = 64 * 2 ^ (p - 2) := by
    rw [show p + 4 = 6 + (p - 2) by omega, pow_add]
    norm_num
  have hRbalance : 64 * R = 9 * H + 7 := by
    dsimp [R]
    rw [← hbalance, hpow]
    ring
  have hRmod : R % 3 = 1 := by
    have h := congrArg (fun x : ℕ => x % 3) hRbalance
    norm_num [Nat.add_mod, Nat.mul_mod] at h ⊢
    omega
  have hRone : 1 ≤ R := hRpos
  have hRmodEq : R ≡ 1 [MOD 3] := by
    rw [Nat.ModEq]
    simpa using hRmod
  have hdiv : 3 ∣ R - 1 :=
    (Nat.modEq_iff_dvd' hRone).mp hRmodEq.symm
  obtain ⟨t, ht⟩ := hdiv
  have hRt : R = 1 + 3 * t := by omega
  have hsource : 3 * H - 1 = 18 + 64 * t := by
    rw [hRt] at hRbalance
    omega
  have hwriterTarget : 3 * (9 * R) - 1 = 26 + 81 * t := by
    rw [hRt]
    omega
  have hwriter : Executes writerWord (3 * H - 1) (3 * (9 * R) - 1) := by
    rw [hsource, hwriterTarget]
    simpa [writerWord_length, writerWord_oddCount] using
      (executes_shift writerWord writer_base_executes t)
  have hcharge : 9 * R = 2 ^ (p - 2) * (9 * W) := by
    dsimp [R]
    ring
  have hdrain : Executes (List.replicate (p - 2) true)
      (3 * (9 * R) - 1) (3 * (3 ^ (p - 2) * (9 * W)) - 1) := by
    rw [hcharge]
    exact drain_executes (p - 2) (9 * W) (by positivity)
  have hfinal : 3 ^ (p - 2) * (9 * W) = 3 ^ p * W := by
    rw [show p = (p - 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [executes_append]
  exact ⟨3 * (9 * R) - 1, hwriter, by simpa [hfinal] using hdrain⟩

/-- The complete all-parameter writer--decoder execution (QM169a).  The
payload equation is subtraction-free and includes the final drain depth
`b`. -/
theorem writerDecoderCell_executes
    {p b z o d H W Q : ℕ}
    (hp : 2 ≤ p) (hW : 0 < W) (hQ : 0 < Q)
    (hwriter : 2 ^ (p + 4) * W = 9 * H + 7)
    (hresonance : 2 ^ z = 1 + 3 ^ (p + 1) * d)
    (hpayload : W + d = 2 ^ (z + o + b) * Q) :
    Executes
      ((writerWord ++ List.replicate (p - 2) true) ++
        resonantDecoderWord z o ++ List.replicate b true)
      (3 * H - 1)
      (3 * (3 ^ (p + o + b) * Q) - 1) := by
  have hfirst := writer_then_drain_executes hp hW hwriter
  have hpayloadDecoder : W + d = 2 ^ (z + o) * (2 ^ b * Q) := by
    rw [show z + o + b = (z + o) + b by omega, pow_add] at hpayload
    nlinarith
  have hdecoder := resonantDecoder_executes
    (c := p) (z := z) (o := o) (d := d) (u := W) (q := 2 ^ b * Q)
    hW (by positivity) hresonance hpayloadDecoder
  have hdrain : Executes (List.replicate b true)
      (3 * (3 ^ (p + o) * (2 ^ b * Q)) - 1)
      (3 * (3 ^ b * (3 ^ (p + o) * Q)) - 1) := by
    rw [show 3 ^ (p + o) * (2 ^ b * Q) =
      2 ^ b * (3 ^ (p + o) * Q) by ring]
    exact drain_executes b (3 ^ (p + o) * Q) (by positivity)
  have hfinal : 3 ^ b * (3 ^ (p + o) * Q) =
      3 ^ (p + o + b) * Q := by
    rw [pow_add]
    ring
  have hprefix : Executes
      ((writerWord ++ List.replicate (p - 2) true) ++
        resonantDecoderWord z o)
      (3 * H - 1)
      (3 * (3 ^ (p + o) * (2 ^ b * Q)) - 1) := by
    rw [executes_append]
    exact ⟨3 * (3 ^ p * W) - 1, hfirst, hdecoder⟩
  rw [executes_append]
  refine ⟨3 * (3 ^ (p + o) * (2 ^ b * Q)) - 1, hprefix, ?_⟩
  simpa [hfinal] using hdrain

/-! ## One coherent cell interface -/

/-- Static arithmetic data of one writer--decoder symbol.  The minimality of
`oneCount` is deliberately not built into this structure: it is needed to
show the decoder word is first passage, but not for its exact execution or
for the coarse obstruction. -/
structure WriterDecoderCellData where
  counter : ℕ
  drain : ℕ
  zeroCount : ℕ
  oneCount : ℕ
  decoderQuotient : ℕ
  correction : ℕ
  depth : ℕ
  counter_ge : 2 ≤ counter
  depth_ge : 55 ≤ depth
  resonance :
    2 ^ zeroCount = 1 + 3 ^ (counter + 1) * decoderQuotient
  correction_eq :
    correction = 7 + 2 ^ (counter + 4) * decoderQuotient
  depth_eq :
    depth = zeroCount + oneCount + counter + 4 + drain

def WriterDecoderCellData.word (cell : WriterDecoderCellData) : List Bool :=
  (writerWord ++ List.replicate (cell.counter - 2) true) ++
    resonantDecoderWord cell.zeroCount cell.oneCount ++
      List.replicate cell.drain true

/-- The first-passage block segmentation represented by one cell. -/
def WriterDecoderCellData.blocks
    (cell : WriterDecoderCellData) : List (List Bool) :=
  writerWord ::
    (List.replicate (cell.counter - 2) [true] ++
      resonantDecoderWord cell.zeroCount cell.oneCount ::
        List.replicate cell.drain [true])

theorem flattenWords_append (left right : List (List Bool)) :
    flattenWords (left ++ right) =
      flattenWords left ++ flattenWords right := by
  induction left with
  | nil => rfl
  | cons w left ih => simp [flattenWords, ih, List.append_assoc]

theorem WriterDecoderCellData.flatten_blocks
    (cell : WriterDecoderCellData) :
    flattenWords cell.blocks = cell.word := by
  simp [WriterDecoderCellData.blocks, WriterDecoderCellData.word,
    flattenWords, flattenWords_append]

/-- Dynamic positive odd payload data for a cell at source charge `H`. -/
structure WriterDecoderCellPayload
    (cell : WriterDecoderCellData) (H : ℕ) where
  writerQuotient : ℕ
  targetQuotient : ℕ
  source_pos : 0 < H
  writerQuotient_pos : 0 < writerQuotient
  writerQuotient_odd : Odd writerQuotient
  targetQuotient_pos : 0 < targetQuotient
  targetQuotient_odd : Odd targetQuotient
  writerBalance :
    2 ^ (cell.counter + 4) * writerQuotient = 9 * H + 7
  decoderBalance :
    writerQuotient + cell.decoderQuotient =
      2 ^ (cell.zeroCount + cell.oneCount + cell.drain) * targetQuotient

/-- The cell identities imply the exact subtraction-free payload triple. -/
theorem WriterDecoderCellPayload.payloadTriple
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H) :
    PayloadTriple cell.correction cell.depth payload.targetQuotient H := by
  refine ⟨payload.source_pos, payload.targetQuotient_pos,
    payload.targetQuotient_odd, ?_⟩
  have hdepth : cell.depth =
      (cell.counter + 4) +
        (cell.zeroCount + cell.oneCount + cell.drain) := by
    rw [cell.depth_eq]
    omega
  calc
    2 ^ cell.depth * payload.targetQuotient =
        2 ^ (cell.counter + 4) *
          (2 ^ (cell.zeroCount + cell.oneCount + cell.drain) *
            payload.targetQuotient) := by
              rw [hdepth, pow_add]
              ring
    _ = 2 ^ (cell.counter + 4) *
          (payload.writerQuotient + cell.decoderQuotient) := by
            rw [payload.decoderBalance]
    _ = 2 ^ (cell.counter + 4) * payload.writerQuotient +
          2 ^ (cell.counter + 4) * cell.decoderQuotient := by ring
    _ = (9 * H + 7) +
          2 ^ (cell.counter + 4) * cell.decoderQuotient := by
            rw [payload.writerBalance]
    _ = 9 * H + cell.correction := by
          rw [cell.correction_eq]
          ring

/-- The same cell object has literal shortcut semantics. -/
theorem WriterDecoderCellPayload.executes
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H) :
    Executes cell.word (3 * H - 1)
      (3 * (3 ^ (cell.counter + cell.oneCount + cell.drain) *
        payload.targetQuotient) - 1) := by
  exact writerDecoderCell_executes cell.counter_ge
    payload.writerQuotient_pos payload.targetQuotient_pos
    payload.writerBalance cell.resonance payload.decoderBalance

theorem singleton_true_firstPassage : FirstPassage [true] := by
  constructor
  · norm_num [WordOutward]
  · intro u hu
    have hlen := properPrefix_length_lt hu
    have huNil : u = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst u
    norm_num [WordOutward]

/-- Once the two adjacent decoder slope inequalities are supplied, the exact
literal cell is also a genuine nonempty first-passage boundary macro. -/
theorem WriterDecoderCellPayload.rechargeMacro
    {cell : WriterDecoderCellData} {H : ℕ}
    (payload : WriterDecoderCellPayload cell H)
    (hzero : 0 < cell.zeroCount) (hone : 0 < cell.oneCount)
    (hprevious :
      3 ^ (cell.oneCount - 1) ≤
        2 ^ (cell.zeroCount + cell.oneCount - 1))
    (houtward :
      2 ^ (cell.zeroCount + cell.oneCount) < 3 ^ cell.oneCount) :
    RechargeMacro H
      (3 ^ (cell.counter + cell.oneCount + cell.drain) *
        payload.targetQuotient)
      cell.blocks := by
  have hdecoder : FirstPassage
      (resonantDecoderWord cell.zeroCount cell.oneCount) :=
    resonantDecoder_firstPassage hzero hone hprevious houtward
  have hwords : WordsIn FirstPassageCode cell.blocks := by
    intro w hw
    simp only [WriterDecoderCellData.blocks, List.mem_cons, List.mem_append,
      List.mem_replicate] at hw
    rcases hw with rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩
    · exact writerWord_firstPassage
    · exact singleton_true_firstPassage
    · exact hdecoder
    · exact singleton_true_firstPassage
  refine ⟨payload.source_pos,
    Nat.mul_pos (by positivity) payload.targetQuotient_pos,
    ?_, hwords, ?_⟩
  · simp [WriterDecoderCellData.blocks]
  · apply executesBlocksTo_iff_flatten.mpr
    rw [cell.flatten_blocks]
    exact payload.executes

/-! ## Direct invariant endpoint -/

/-- One exact writer--decoder boundary recharge, including the hypotheses
which make its resonant decoder a first-passage word. -/
def WriterDecoderRecharge (H H' : ℕ) : Prop :=
  ∃ (cell : WriterDecoderCellData)
      (payload : WriterDecoderCellPayload cell H),
    0 < cell.zeroCount ∧
    0 < cell.oneCount ∧
    3 ^ (cell.oneCount - 1) ≤
      2 ^ (cell.zeroCount + cell.oneCount - 1) ∧
    2 ^ (cell.zeroCount + cell.oneCount) < 3 ^ cell.oneCount ∧
    H' = 3 ^ (cell.counter + cell.oneCount + cell.drain) *
      payload.targetQuotient

theorem WriterDecoderRecharge.exists_macro
    {H H' : ℕ} (h : WriterDecoderRecharge H H') :
    ∃ words, RechargeMacro H H' words := by
  rcases h with
    ⟨cell, payload, hzero, hone, hprevious, houtward, rfl⟩
  exact ⟨cell.blocks,
    payload.rechargeMacro hzero hone hprevious houtward⟩

theorem WriterDecoderRecharge.lt
    {H H' : ℕ} (h : WriterDecoderRecharge H H') : H < H' := by
  obtain ⟨words, hmacro⟩ := h.exists_macro
  exact hmacro.lt

/-- Closure of any predicate under exact writer--decoder recharges supplies
arbitrarily deep literal first-passage execution. -/
theorem writerDecoderInvariant_gives_infiniteExecution
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀) (h₀ : I H₀)
    (hclosed : ∀ H, I H →
      ∃ H', WriterDecoderRecharge H H' ∧ I H') :
    InfiniteExecution FirstPassageCode (3 * H₀ - 1) := by
  apply invariant_gives_infiniteExecution I H₀ h₀pos h₀
  intro H hI
  obtain ⟨H', hstep, hI'⟩ := hclosed H hI
  obtain ⟨words, hmacro⟩ := hstep.exists_macro
  exact ⟨H', words, hmacro, hI'⟩

theorem writerDecoderInvariant_gives_not_syracuseReachesOne
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀) (h₀ : I H₀)
    (hclosed : ∀ H, I H →
      ∃ H', WriterDecoderRecharge H H' ∧ I H') :
    ¬ CleanLean.Collatz.SyracuseReachesOne (3 * H₀ - 1) := by
  apply OutwardCodeCounterexample.not_syracuseReachesOne_of_infiniteExecution
    (C := FirstPassageCode)
  · intro w hw
    exact hw.1
  · exact writerDecoderInvariant_gives_infiniteExecution
      I H₀ h₀pos h₀ hclosed

theorem writerDecoderInvariant_gives_not_collatz
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀) (h₀ : I H₀)
    (hclosed : ∀ H, I H →
      ∃ H', WriterDecoderRecharge H H' ∧ I H') :
    ¬ CleanLean.Collatz.Conjecture := by
  apply OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
  · intro w hw
    exact hw.1
  · exact writerDecoderInvariant_gives_infiniteExecution
      I H₀ h₀pos h₀ hclosed

/-- A candidate next cell for an affine quotient family, using the same
static and dynamic objects which have literal semantics above. -/
def LiteralWriterDecoderCandidate
    (g q stride : ℕ) (correction : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ (cell : WriterDecoderCellData)
      (payload : WriterDecoderCellPayload cell
        (incomingCharge g q stride n)),
    cell.correction = correction cell.counter

/-- Exact cell data produces the equation-level target witness used by the
coarse theorem. -/
theorem literalWriterDecoderCandidate_equations
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (h : LiteralWriterDecoderCandidate g q stride correction n) :
    WriterDecoderCellEquations g q stride correction n := by
  rcases h with ⟨cell, payload, hcorrection⟩
  refine ⟨{
    counter := cell.counter
    depth := cell.depth
    targetQuotient := payload.targetQuotient
    writerQuotient := payload.writerQuotient
    counter_ge := cell.counter_ge
    depth_ge := cell.depth_ge
    payload := ?_
    writerQuotient_pos := payload.writerQuotient_pos
    writerQuotient_odd := payload.writerQuotient_odd
    writerBalance := payload.writerBalance }⟩
  simpa [hcorrection] using payload.payloadTriple

/-- The literal cell interface now discharges the remaining semantic premise
of QM170f. -/
theorem literalWriterDecoderCandidate_coarse
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (h : LiteralWriterDecoderCandidate g q stride correction n) :
    CoarseWriterDecoderLegal (3 ^ (g + 2)) q stride correction n :=
  writerDecoderCellEquations_coarse
    (literalWriterDecoderCandidate_equations h)

/-- Every unrestricted ternary parameter tail contains a positive ordinary
coefficient for which no exact literal writer--decoder candidate exists,
even with an unbounded target symbol. -/
theorem exists_positive_open_tail_without_literalWriterDecoderCandidate
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride) (k u₀ : ℕ) :
    ∃ m, 0 < m ∧
      ¬ LiteralWriterDecoderCandidate g q stride correction
        (u₀ + 3 ^ k * m) := by
  obtain ⟨m, hmpos, hmeq⟩ :=
    exists_positive_open_tail_without_writerDecoderTarget
      g q stride correction hstride k u₀
  exact ⟨m, hmpos, fun hliteral =>
    hmeq (literalWriterDecoderCandidate_equations hliteral)⟩

/-- No whole ternary parameter cylinder can force existence of an exact
literal writer--decoder cell. -/
theorem no_ternary_cylinder_forces_literalWriterDecoderCandidate
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride) (k a : ℕ) :
    ¬ ∀ n, n ≡ a [MOD 3 ^ k] →
      LiteralWriterDecoderCandidate g q stride correction n := by
  intro hforces
  apply no_ternary_cylinder_forces_writerDecoderTarget
    g q stride correction hstride k a
  intro n hn
  exact literalWriterDecoderCandidate_equations (hforces n hn)

end OutwardWriterDecoderLiteral
end KontoroC
