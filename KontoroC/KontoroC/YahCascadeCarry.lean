/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahQueueMacro
import KontoroC.YahAffineCarryNoGo

/-!
# Exact carry-state law for a cascade of quotient sweeps

A stack of `s` quotient sweeps carries `s` bits across a word boundary.  This
file models that stack directly and proves, for every word and every incoming
carry vector, that its boundary state obeys

`r_next = 3^word.length * r + wordValue word  (mod 2^s)`.

This replaces finite sampling of cascade states by an all-word theorem.  A
particular large atom still needs a compact certificate for its length and
value modulo `2^s`; the transducer law itself is no longer an assumption.
-/

namespace KontoroC
namespace YahCascadeCarry

open YahQueueMacro
open Carry Trit

/-- Little-endian numerical value of a vector of carry bits. -/
def carryState : List Carry → ℕ
  | [] => 0
  | c :: cs => carryBit c + 2 * carryState cs

/-- Positional base-three value of a trit word. -/
def wordValue : List Trit → ℕ
  | [] => 0
  | t :: w => 3 ^ w.length * tritDigit t + wordValue w

/-- Send one trit through a little-endian stack of quotient transducers. -/
def cascadeDigit : List Carry → Trit → Trit × List Carry
  | [], t => (t, [])
  | c :: cs, t =>
      let first := transition c t
      let rest := cascadeDigit cs first.1
      (rest.1, first.2 :: rest.2)

/-- Send a whole word through the cascade, retaining its boundary state. -/
def cascadeWord : List Carry → List Trit → List Trit × List Carry
  | cs, [] => ([], cs)
  | cs, t :: w =>
      let first := cascadeDigit cs t
      let rest := cascadeWord first.2 w
      (first.1 :: rest.1, rest.2)

/-- The same cascade viewed as successive whole-word quotient layers. -/
def layeredOutput : List Carry → List Trit → List Trit
  | [], w => w
  | c :: cs, w => layeredOutput cs (quotientCore c w)

/-- Boundary carry emitted by each successive whole-word quotient layer. -/
def layeredTerminal : List Carry → List Trit → List Carry
  | [], _ => []
  | c :: cs, w =>
      terminalCarry c w :: layeredTerminal cs (quotientCore c w)

private theorem transition_balance (x : ℕ) (c : Carry) (t : Trit) :
    3 * (2 * x + carryBit c) + tritDigit t =
      2 * (3 * x + tritDigit (transition c t).1) +
        carryBit (transition c t).2 := by
  cases c <;> cases t <;>
    simp [carryBit, tritDigit, transition] <;> omega

theorem wordValue_eq_tritEvalFrom (x : ℕ) (w : List Trit) :
    tritEvalFrom x w = 3 ^ w.length * x + wordValue w := by
  induction w generalizing x with
  | nil => simp [tritEvalFrom, wordValue]
  | cons t w ih =>
      simp only [tritEvalFrom, List.length_cons, wordValue, ih]
      rw [pow_succ]
      ring

theorem carryState_lt_pow (cs : List Carry) : carryState cs < 2 ^ cs.length := by
  induction cs with
  | nil => simp [carryState]
  | cons c cs ih =>
      cases c <;> simp [carryState, carryBit, pow_succ] at ih ⊢ <;> omega

theorem cascadeDigit_state_length (cs : List Carry) (t : Trit) :
    (cascadeDigit cs t).2.length = cs.length := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
      cases c <;> cases t <;>
        simp [cascadeDigit, transition, ih]

/-- The exact one-digit invariant used by the Python cascade worker. -/
theorem cascadeDigit_balance (cs : List Carry) (t : Trit) :
    3 * carryState cs + tritDigit t =
      2 ^ cs.length * tritDigit (cascadeDigit cs t).1 +
        carryState (cascadeDigit cs t).2 := by
  induction cs generalizing t with
  | nil => simp [carryState, cascadeDigit]
  | cons c cs ih =>
      let first := transition c t
      let rest := cascadeDigit cs first.1
      have hfirst := transition_balance (carryState cs) c t
      have hrest := ih first.1
      change
        3 * (carryBit c + 2 * carryState cs) + tritDigit t =
          2 ^ (cs.length + 1) * tritDigit rest.1 +
            (carryBit first.2 + 2 * carryState rest.2)
      change
        3 * (2 * carryState cs + carryBit c) + tritDigit t =
          2 * (3 * carryState cs + tritDigit first.1) + carryBit first.2 at hfirst
      change
        3 * carryState cs + tritDigit first.1 =
          2 ^ cs.length * tritDigit rest.1 + carryState rest.2 at hrest
      rw [pow_succ]
      rw [show 2 ^ cs.length * 2 * tritDigit rest.1 =
        2 * (2 ^ cs.length * tritDigit rest.1) by ring]
      omega

theorem cascadeWord_output_length (cs : List Carry) (w : List Trit) :
    (cascadeWord cs w).1.length = w.length := by
  induction w generalizing cs with
  | nil => rfl
  | cons t w ih =>
      simp only [cascadeWord, List.length_cons]
      rw [ih]

theorem cascadeWord_state_length (cs : List Carry) (w : List Trit) :
    (cascadeWord cs w).2.length = cs.length := by
  induction w generalizing cs with
  | nil => rfl
  | cons t w ih =>
      simp only [cascadeWord]
      rw [ih, cascadeDigit_state_length]

/-- Processing every layer at each digit agrees with processing one complete
word layer at a time.  This is the semantic bridge from the compact cascade
state machine to the existing `quotientCore` transducer. -/
theorem cascadeWord_cons_layer (c : Carry) (cs : List Carry) (w : List Trit) :
    cascadeWord (c :: cs) w =
      let lower := cascadeWord cs (quotientCore c w)
      (lower.1, terminalCarry c w :: lower.2) := by
  induction w generalizing c cs with
  | nil => rfl
  | cons t w ih =>
      cases c <;> cases t <;>
        simp [cascadeWord, cascadeDigit, quotientCore, terminalCarry,
          transition, ih]

private theorem cascadeWord_nil_state (w : List Trit) :
    cascadeWord [] w = (w, []) := by
  induction w with
  | nil => rfl
  | cons t w ih => simp [cascadeWord, cascadeDigit, ih]

/-- Exact equivalence of the direct digit cascade and successive actual
quotient sweeps. -/
theorem cascadeWord_eq_layered (cs : List Carry) (w : List Trit) :
    cascadeWord cs w = (layeredOutput cs w, layeredTerminal cs w) := by
  induction cs generalizing w with
  | nil => simpa [layeredOutput, layeredTerminal] using cascadeWord_nil_state w
  | cons c cs ih =>
      rw [cascadeWord_cons_layer, ih]
      rfl

/-- Universal, division-free state balance for a cascade acting on a word. -/
theorem cascadeWord_balance (cs : List Carry) (w : List Trit) :
    3 ^ w.length * carryState cs + wordValue w =
      2 ^ cs.length * wordValue (cascadeWord cs w).1 +
        carryState (cascadeWord cs w).2 := by
  induction w generalizing cs with
  | nil => simp [cascadeWord, wordValue]
  | cons t w ih =>
      simp only [cascadeWord, List.length_cons, wordValue]
      have hdigit := cascadeDigit_balance cs t
      have htail := ih (cascadeDigit cs t).2
      rw [cascadeDigit_state_length] at htail
      have houtlen := cascadeWord_output_length (cascadeDigit cs t).2 w
      rw [pow_succ]
      rw [houtlen]
      calc
        3 ^ w.length * 3 * carryState cs +
              (3 ^ w.length * tritDigit t + wordValue w) =
            3 ^ w.length * (3 * carryState cs + tritDigit t) +
              wordValue w := by ring
        _ = 3 ^ w.length *
              (2 ^ cs.length * tritDigit (cascadeDigit cs t).1 +
                carryState (cascadeDigit cs t).2) + wordValue w := by rw [hdigit]
        _ = 2 ^ cs.length *
              (3 ^ w.length * tritDigit (cascadeDigit cs t).1 +
                wordValue (cascadeWord (cascadeDigit cs t).2 w).1) +
              carryState (cascadeWord (cascadeDigit cs t).2 w).2 := by
                calc
                  3 ^ w.length *
                        (2 ^ cs.length * tritDigit (cascadeDigit cs t).1 +
                          carryState (cascadeDigit cs t).2) + wordValue w =
                      2 ^ cs.length *
                          (3 ^ w.length * tritDigit (cascadeDigit cs t).1) +
                        (3 ^ w.length * carryState (cascadeDigit cs t).2 +
                          wordValue w) := by ring
                  _ = _ := by rw [htail]; ring

/-- The final state is exactly the advertised affine residue, with no sampled
states and no dependence on the output word contents. -/
theorem cascadeWord_state_mod (cs : List Carry) (w : List Trit) :
    carryState (cascadeWord cs w).2 =
      (3 ^ w.length * carryState cs + wordValue w) % 2 ^ cs.length := by
  have hbalance := cascadeWord_balance cs w
  have hlength := cascadeWord_state_length cs w
  have hlt : carryState (cascadeWord cs w).2 < 2 ^ cs.length := by
    rw [← hlength]
    exact carryState_lt_pow _
  rw [hbalance, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt hlt]

/-- Congruence form convenient for plugging in a certified block value. -/
theorem cascadeWord_state_mod_of_value (cs : List Carry) (w : List Trit)
    (b : ℕ) (hb : wordValue w % 2 ^ cs.length = b % 2 ^ cs.length) :
    carryState (cascadeWord cs w).2 =
      (3 ^ w.length * carryState cs + b) % 2 ^ cs.length := by
  rw [cascadeWord_state_mod, Nat.add_mod, hb, ← Nat.add_mod]

/-- The exact 19-bit affine law needed by QM43, reduced to two transparent
block facts: length `65536` and value `449133 mod 2^19`. -/
theorem auditedAtom_affine_state (cs : List Carry) (w : List Trit)
    (hcs : cs.length = 19) (hw : w.length = 65536)
    (hb : wordValue w % 524288 = 449133) :
    carryState (cascadeWord cs w).2 =
      (262145 * carryState cs + 449133) % 524288 := by
  have h := cascadeWord_state_mod cs w
  rw [hcs, hw] at h
  norm_num only [Nat.reducePow] at h
  rw [Nat.add_mod, Nat.mul_mod, YahAffineCarryNoGo.atomMultiplier_mod,
    hb] at h
  rw [Nat.add_mod, Nat.mul_mod]
  norm_num only [Nat.reduceMod]
  exact h

end YahCascadeCarry
end KontoroC
