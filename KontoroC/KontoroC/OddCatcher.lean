/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.TwoRailGate

/-!
# The odd-gap two-rail catcher

An odd separated gap on the positive `+1` rail does not fit the valuation-two
cleanup collision used by `TwoRailGate`.  After the last valuation-two tick it
reaches `1 + 2*3^s*Q`; one valuation-one step sends this exactly to

`2 + 3^(s+1)*Q = -1 + 2^L*P'`.

This file certifies that missing parity branch for arbitrary payload size.
-/

namespace KontoroC

/-- Exact cleanup along an odd positive-rail gap, leaving gap one. -/
theorem delayState_odd_gap_word {p n : ℕ} (hp : 0 < p) (hpodd : Odd p) :
    WordLegal (delayState p (2 * n + 1)) (List.replicate n 2) ∧
      runWord (delayState p (2 * n + 1)) (List.replicate n 2) =
        delayState (3 ^ n * p) 1 := by
  induction n generalizing p with
  | zero => simp [WordLegal, delayState]
  | succ n ih =>
      have hstep := delayState_step (p := p) (J := 2 * (n + 1) + 1)
        (by omega)
      have hp' : 0 < 3 * p := by positivity
      have hpodd' : Odd (3 * p) := (by norm_num : Odd 3).mul hpodd
      have htail := ih hp' hpodd'
      rw [List.replicate_succ, WordLegal, runWord_cons, hstep.2]
      have hstate :
          delayState (3 * p) (2 * (n + 1) + 1 - 2) =
            delayState (3 * p) (2 * n + 1) := by
        congr 1
      rw [hstate]
      constructor
      · exact ⟨hstep.1, htail.1⟩
      · rw [htail.2]
        simp only [delayState, pow_succ]
        ring

/-- One exact odd-gap gate from the `-1` amplifier rail, through the `+1`
rail, and back to the `-1` rail by a valuation-one catcher. -/
structure OddCatcherGate where
  ampTicks : ℕ
  cleanTicks : ℕ
  toPlusExtra : ℕ
  outputGap : ℕ
  inputPayload : ℕ
  plusPayload : ℕ
  outputPayload : ℕ
  outputGap_pos : 0 < outputGap
  inputPayload_pos : 0 < inputPayload
  plusPayload_pos : 0 < plusPayload
  outputPayload_pos : 0 < outputPayload
  inputPayload_odd : Odd inputPayload
  plusPayload_odd : Odd plusPayload
  outputPayload_odd : Odd outputPayload
  toPlus_balance :
    2 ^ toPlusExtra * delayState plusPayload (2 * cleanTicks + 1) =
      3 ^ (ampTicks + 1) * inputPayload - 1
  catcher_balance :
    minusOneState outputPayload outputGap =
      2 + 3 ^ (cleanTicks + 1) * plusPayload

namespace OddCatcherGate

def start (g : OddCatcherGate) : ℕ :=
  minusOneState g.inputPayload (g.ampTicks + 1)

def plusState (g : OddCatcherGate) : ℕ :=
  delayState g.plusPayload (2 * g.cleanTicks + 1)

def catcherSource (g : OddCatcherGate) : ℕ :=
  delayState (3 ^ g.cleanTicks * g.plusPayload) 1

def endpoint (g : OddCatcherGate) : ℕ :=
  minusOneState g.outputPayload g.outputGap

def word (g : OddCatcherGate) : List ℕ :=
  mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra ++
    (List.replicate g.cleanTicks 2 ++ [1])

theorem amplifier_legal_and_endpoint (g : OddCatcherGate) :
    WordLegal g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) ∧
      runWord g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) = g.plusState := by
  exact mersenneMacro_legal_of_packet_equation
    (by omega) g.inputPayload_pos
    (Nat.odd_iff.mp (delayState_odd (by omega))) g.toPlus_balance

theorem cleanup_legal_and_endpoint (g : OddCatcherGate) :
    WordLegal g.plusState (List.replicate g.cleanTicks 2) ∧
      runWord g.plusState (List.replicate g.cleanTicks 2) =
        g.catcherSource := by
  simpa [plusState, catcherSource] using
    delayState_odd_gap_word g.plusPayload_pos g.plusPayload_odd

/-- The final odd-gap catcher is one exact valuation-one instruction. -/
theorem catcher_step (g : OddCatcherGate) :
    LegalInstruction g.catcherSource 1 ∧
      oddStep g.catcherSource = g.endpoint := by
  have hout := minusOneState_pos_odd g.outputPayload_pos g.outputGap_pos
  apply legalInstruction_of_step_equation
  · exact delayState_pos _ _
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · exact Nat.odd_iff.mp hout.2
  · calc
      2 ^ 1 * g.endpoint =
          2 * (2 + 3 ^ (g.cleanTicks + 1) * g.plusPayload) := by
        rw [show g.endpoint =
          2 + 3 ^ (g.cleanTicks + 1) * g.plusPayload by
            exact g.catcher_balance]
        norm_num
      _ = 3 * g.catcherSource + 1 := by
        simp only [catcherSource, delayState]
        rw [pow_succ]
        ring

/-- End-to-end exact catcher legality and endpoint. -/
theorem legal_and_endpoint (g : OddCatcherGate) :
    WordLegal g.start g.word ∧ runWord g.start g.word = g.endpoint := by
  have hamp := g.amplifier_legal_and_endpoint
  have hclean := g.cleanup_legal_and_endpoint
  have hcatch := g.catcher_step
  rw [word, wordLegal_append_iff, runWord_append]
  constructor
  · refine ⟨hamp.1, ?_⟩
    rw [hamp.2, wordLegal_append_iff]
    refine ⟨hclean.1, ?_⟩
    rw [hclean.2]
    exact ⟨hcatch.1, trivial⟩
  · rw [hamp.2, runWord_append, hclean.2]
    simpa [runWord] using hcatch.2

theorem outward_iff (g : OddCatcherGate) :
    g.start < g.endpoint ↔
      2 ^ (g.ampTicks + 1) * g.inputPayload <
        2 ^ g.outputGap * g.outputPayload := by
  have hin : 0 < 2 ^ (g.ampTicks + 1) * g.inputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.inputPayload_pos
  have hout : 0 < 2 ^ g.outputGap * g.outputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
  simp only [start, endpoint, minusOneState]
  omega

end OddCatcherGate

end KontoroC
