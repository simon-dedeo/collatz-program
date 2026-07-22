/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DelayLine

/-!
# Pure positive-rail splash gates

A state `1 + p * 2^(2*r+2)` can spend `r` ticks on the valuation-two
delay rail and then collide with its low bit.  This file certifies an
arbitrary exact collision which emits another positive delay-rail state.

The principal result is negative but useful: every such pure `+1`-rail
macro strictly decreases the represented natural number.  This is independent
of the payload sizes and of the output gap, so the result applies unchanged to
formula-generated states with thousands (or millions) of digits.
-/

namespace KontoroC

/-- Data for one exact `+1` delay/splash macro.

The balance is precisely the collision equation after the `delaySteps`
valuation-two wire ticks.  Requiring the payloads to be positive and odd makes
all claimed valuations exact rather than merely divisibility statements. -/
structure DelaySplash where
  delaySteps : ℕ
  nextDelaySteps : ℕ
  collisionExtra : ℕ
  inputPayload : ℕ
  outputPayload : ℕ
  delaySteps_pos : 0 < delaySteps
  nextDelaySteps_pos : 0 < nextDelaySteps
  collisionExtra_pos : 0 < collisionExtra
  inputPayload_pos : 0 < inputPayload
  outputPayload_pos : 0 < outputPayload
  inputPayload_odd : Odd inputPayload
  outputPayload_odd : Odd outputPayload
  balance :
    3 ^ (delaySteps + 1) * inputPayload + 1 =
      2 ^ collisionExtra *
        delayState outputPayload (2 * nextDelaySteps + 2)

namespace DelaySplash

/-- The input natural represented by a splash datum. -/
def start (g : DelaySplash) : ℕ :=
  delayState g.inputPayload (2 * g.delaySteps + 2)

/-- The output natural represented by a splash datum. -/
def endpoint (g : DelaySplash) : ℕ :=
  delayState g.outputPayload (2 * g.nextDelaySteps + 2)

/-- The compressed exact valuation word for the whole splash. -/
def word (g : DelaySplash) : List ℕ :=
  List.replicate g.delaySteps 2 ++ [2 + g.collisionExtra]

/-- State immediately before the collision, after all wire ticks. -/
def collisionSource (g : DelaySplash) : ℕ :=
  delayState (3 ^ g.delaySteps * g.inputPayload) 2

theorem delay_legal_and_endpoint (g : DelaySplash) :
    WordLegal g.start (List.replicate g.delaySteps 2) ∧
      runWord g.start (List.replicate g.delaySteps 2) =
        g.collisionSource := by
  simpa [start, collisionSource] using
    (delayState_word g.inputPayload_pos g.inputPayload_odd
      (by omega : 2 * g.delaySteps + 2 ≤ 2 * g.delaySteps + 2))

/-- The supplied affine balance forces the literal collision valuation
`2 + collisionExtra` and the claimed endpoint. -/
theorem collision_step (g : DelaySplash) :
    LegalInstruction g.collisionSource (2 + g.collisionExtra) ∧
      oddStep g.collisionSource = g.endpoint := by
  apply legalInstruction_of_step_equation
  · exact delayState_pos _ _
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · calc
      2 ^ (2 + g.collisionExtra) * g.endpoint =
          4 * (2 ^ g.collisionExtra * g.endpoint) := by
            rw [show 2 + g.collisionExtra = g.collisionExtra + 2 by omega,
              pow_add]
            norm_num
            ring
      _ = 4 * (3 ^ (g.delaySteps + 1) * g.inputPayload + 1) := by
        congr 1
        simpa [endpoint] using g.balance.symm
      _ = 3 * g.collisionSource + 1 := by
        simp only [collisionSource, delayState]
        rw [pow_succ]
        ring

/-- End-to-end literal legality and endpoint of a pure splash gate. -/
theorem legal_and_endpoint (g : DelaySplash) :
    WordLegal g.start g.word ∧ runWord g.start g.word = g.endpoint := by
  rw [word, wordLegal_append_iff, runWord_append]
  have hdelay := g.delay_legal_and_endpoint
  have hcollision := g.collision_step
  constructor
  · refine ⟨hdelay.1, ?_⟩
    rw [hdelay.2]
    exact ⟨hcollision.1, trivial⟩
  · rw [hdelay.2]
    simpa [runWord] using hcollision.2

/-- The collision output is smaller than its affine numerator. -/
theorem endpoint_lt_collisionNumerator (g : DelaySplash) :
    g.endpoint < 3 ^ (g.delaySteps + 1) * g.inputPayload + 1 := by
  have hpow : 1 < 2 ^ g.collisionExtra :=
    Nat.one_lt_pow (Nat.ne_of_gt g.collisionExtra_pos) (by omega)
  calc
    g.endpoint = 1 * g.endpoint := by simp
    _ < 2 ^ g.collisionExtra * g.endpoint :=
      (Nat.mul_lt_mul_right (delayState_pos _ _)).2 hpow
    _ = 3 ^ (g.delaySteps + 1) * g.inputPayload + 1 := g.balance.symm

/-- Every pure `+1` delay/splash gate is dissipative.  In particular it
cannot be an outward macro, however large either payload is. -/
theorem strictly_decreases (g : DelaySplash) : g.endpoint < g.start := by
  have hpow : 3 ^ (g.delaySteps + 1) < 4 ^ (g.delaySteps + 1) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hmul :
      3 ^ (g.delaySteps + 1) * g.inputPayload <
        4 ^ (g.delaySteps + 1) * g.inputPayload :=
    (Nat.mul_lt_mul_right g.inputPayload_pos).2 hpow
  have hgap : 2 ^ (2 * g.delaySteps + 2) = 4 ^ (g.delaySteps + 1) := by
    rw [show 2 * g.delaySteps + 2 = 2 * (g.delaySteps + 1) by omega,
      pow_mul]
    norm_num
  calc
    g.endpoint < 3 ^ (g.delaySteps + 1) * g.inputPayload + 1 :=
      g.endpoint_lt_collisionNumerator
    _ < 4 ^ (g.delaySteps + 1) * g.inputPayload + 1 := by omega
    _ = g.start := by
      rw [start, delayState, hgap]
      ring

theorem not_outward (g : DelaySplash) : ¬g.start < g.endpoint :=
  not_lt_of_ge (Nat.le_of_lt g.strictly_decreases)

end DelaySplash

end KontoroC
