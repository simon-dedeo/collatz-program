/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SplashGate
import KontoroC.MersenneShadow
import KontoroC.Glider

/-!
# Exact two-rail gates

The pure positive rail is dissipative, but the negative fixed point `-1`
provides a valuation-one amplifier rail.  This file certifies a complete macro
which travels along that rail, switches to a positive valuation-two cleanup
rail, and switches back to the `-1` rail.

Only two small affine balances are required.  The payloads are arbitrary, so
the certificate cost is independent of the number of digits in a represented
state.
-/

namespace KontoroC

/-- An odd positive natural on the affine rail centered at `-1`. -/
def minusOneState (p J : ℕ) : ℕ :=
  2 ^ J * p - 1

theorem minusOneState_pos_odd {p J : ℕ} (hp : 0 < p) (hJ : 0 < J) :
    0 < minusOneState p J ∧ Odd (minusOneState p J) := by
  have h := twoPow_mul_sub_one_pos_odd hJ hp
  change 0 < 2 ^ J * p - 1 ∧ Odd (2 ^ J * p - 1)
  exact ⟨h.1, Nat.odd_iff.mpr h.2⟩

/-- One exact gate from the `-1` amplifier rail, through the `+1` cleanup
rail, and back to the `-1` rail.

`ampTicks` and `cleanTicks` count the ordinary rail ticks before their
respective collisions.  The two collision extras may be zero. -/
structure TwoRailGate where
  ampTicks : ℕ
  cleanTicks : ℕ
  toPlusExtra : ℕ
  toMinusExtra : ℕ
  outputGap : ℕ
  inputPayload : ℕ
  plusPayload : ℕ
  outputPayload : ℕ
  ampTicks_pos : 0 < ampTicks
  outputGap_pos : 0 < outputGap
  inputPayload_pos : 0 < inputPayload
  plusPayload_pos : 0 < plusPayload
  outputPayload_pos : 0 < outputPayload
  inputPayload_odd : Odd inputPayload
  plusPayload_odd : Odd plusPayload
  outputPayload_odd : Odd outputPayload
  toPlus_balance :
    2 ^ toPlusExtra *
        delayState plusPayload (2 * cleanTicks + 2) =
      3 ^ (ampTicks + 1) * inputPayload - 1
  toMinus_balance :
    2 ^ toMinusExtra * minusOneState outputPayload outputGap =
      1 + 3 ^ (cleanTicks + 1) * plusPayload

namespace TwoRailGate

def start (g : TwoRailGate) : ℕ :=
  minusOneState g.inputPayload (g.ampTicks + 1)

def plusState (g : TwoRailGate) : ℕ :=
  delayState g.plusPayload (2 * g.cleanTicks + 2)

def cleanupCollisionSource (g : TwoRailGate) : ℕ :=
  delayState (3 ^ g.cleanTicks * g.plusPayload) 2

def endpoint (g : TwoRailGate) : ℕ :=
  minusOneState g.outputPayload g.outputGap

/-- The complete compressed valuation program. -/
def word (g : TwoRailGate) : List ℕ :=
  mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra ++
    (List.replicate g.cleanTicks 2 ++ [2 + g.toMinusExtra])

/-- The first balance certifies the entire valuation-one amplifier rail and
its collision into the positive rail. -/
theorem amplifier_legal_and_endpoint (g : TwoRailGate) :
    WordLegal g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) ∧
      runWord g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) = g.plusState := by
  exact mersenneMacro_legal_of_packet_equation
    (by omega) g.inputPayload_pos
    (Nat.odd_iff.mp (delayState_odd (by omega))) g.toPlus_balance

/-- The positive cleanup wire reaches the claimed collision source. -/
theorem cleanup_legal_and_endpoint (g : TwoRailGate) :
    WordLegal g.plusState (List.replicate g.cleanTicks 2) ∧
      runWord g.plusState (List.replicate g.cleanTicks 2) =
        g.cleanupCollisionSource := by
  simpa [plusState, cleanupCollisionSource] using
    (delayState_word g.plusPayload_pos g.plusPayload_odd
      (by omega : 2 * g.cleanTicks + 2 ≤ 2 * g.cleanTicks + 2))

/-- The second balance certifies the switch back to the `-1` rail. -/
theorem cleanup_collision_step (g : TwoRailGate) :
    LegalInstruction g.cleanupCollisionSource (2 + g.toMinusExtra) ∧
      oddStep g.cleanupCollisionSource = g.endpoint := by
  have hout := minusOneState_pos_odd g.outputPayload_pos g.outputGap_pos
  apply legalInstruction_of_step_equation
  · exact delayState_pos _ _
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · exact Nat.odd_iff.mp hout.2
  · calc
      2 ^ (2 + g.toMinusExtra) * g.endpoint =
          4 * (2 ^ g.toMinusExtra * g.endpoint) := by
            rw [show 2 + g.toMinusExtra = g.toMinusExtra + 2 by omega,
              pow_add]
            norm_num
            ring
      _ = 4 * (1 + 3 ^ (g.cleanTicks + 1) * g.plusPayload) := by
        congr 1
        simpa [endpoint] using g.toMinus_balance
      _ = 3 * g.cleanupCollisionSource + 1 := by
        simp only [cleanupCollisionSource, delayState]
        rw [pow_succ]
        ring

/-- End-to-end exact legality and endpoint.  No intermediate orbit replay is
required, even when the payloads have thousands of digits. -/
theorem legal_and_endpoint (g : TwoRailGate) :
    WordLegal g.start g.word ∧ runWord g.start g.word = g.endpoint := by
  have hamp := g.amplifier_legal_and_endpoint
  have hclean := g.cleanup_legal_and_endpoint
  have hcollision := g.cleanup_collision_step
  rw [word, wordLegal_append_iff, runWord_append]
  constructor
  · refine ⟨hamp.1, ?_⟩
    rw [hamp.2, wordLegal_append_iff]
    refine ⟨hclean.1, ?_⟩
    rw [hclean.2]
    exact ⟨hcollision.1, trivial⟩
  · rw [hamp.2, runWord_append, hclean.2]
    simpa [runWord] using hcollision.2

/-- A gate is outward exactly when its two sparse endpoint formulas have the
corresponding order.  This deliberately leaves growth as a transparent
arithmetic field for a controller rather than inferring it from a finite
search. -/
theorem outward_iff (g : TwoRailGate) :
    g.start < g.endpoint ↔
      2 ^ (g.ampTicks + 1) * g.inputPayload <
        2 ^ g.outputGap * g.outputPayload := by
  have hin : 0 < 2 ^ (g.ampTicks + 1) * g.inputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.inputPayload_pos
  have hout : 0 < 2 ^ g.outputGap * g.outputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
  simp only [start, endpoint, minusOneState]
  omega

end TwoRailGate

/-- An infinite linked family of outward two-rail gates.  This is the exact
additional object which a finite gate compiler does *not* supply. -/
structure InfiniteTwoRailProgram where
  gate : ℕ → TwoRailGate
  start_large : 4 < (gate 0).start
  linked : ∀ t, (gate t).endpoint = (gate (t + 1)).start
  outward : ∀ t, (gate t).start < (gate t).endpoint

namespace InfiniteTwoRailProgram

/-- An infinite linked two-rail program is a literal Collatz macro-glider. -/
def toMacroGlider (g : InfiniteTwoRailProgram) : MacroGlider where
  state t := (g.gate t).start
  word t := (g.gate t).word
  start_large := g.start_large
  word_nonempty t := by simp [TwoRailGate.word]
  legal t := (g.gate t).legal_and_endpoint.1
  transition t := (g.gate t).legal_and_endpoint.2.trans (g.linked t)
  grows t := (g.outward t).trans_le (Nat.le_of_eq (g.linked t))

/-- Sound endpoint: an actual all-level two-rail controller disproves the
standard Collatz conjecture.  A 247-round finite chain does not inhabit this
structure. -/
theorem not_conjecture (g : InfiniteTwoRailProgram) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end InfiniteTwoRailProgram

/-- Small exact regression for the first gate of the standard Python chain. -/
def firstStandardTwoRailGate : TwoRailGate where
  ampTicks := 4
  cleanTicks := 1
  toPlusExtra := 1
  toMinusExtra := 1
  outputGap := 6
  inputPayload := 2961
  plusPayload := 22485
  outputPayload := 1581
  ampTicks_pos := by norm_num
  outputGap_pos := by norm_num
  inputPayload_pos := by norm_num
  plusPayload_pos := by norm_num
  outputPayload_pos := by norm_num
  inputPayload_odd := by norm_num
  plusPayload_odd := by norm_num
  outputPayload_odd := by norm_num
  toPlus_balance := by norm_num [delayState]
  toMinus_balance := by norm_num [minusOneState]

theorem firstStandardTwoRailGate_start :
    firstStandardTwoRailGate.start = 94751 := by
  norm_num [firstStandardTwoRailGate, TwoRailGate.start, minusOneState]

theorem firstStandardTwoRailGate_endpoint :
    firstStandardTwoRailGate.endpoint = 101183 := by
  norm_num [firstStandardTwoRailGate, TwoRailGate.endpoint, minusOneState]

theorem firstStandardTwoRailGate_outward :
    firstStandardTwoRailGate.start < firstStandardTwoRailGate.endpoint := by
  norm_num [firstStandardTwoRailGate, TwoRailGate.start,
    TwoRailGate.endpoint, minusOneState]

end KontoroC
