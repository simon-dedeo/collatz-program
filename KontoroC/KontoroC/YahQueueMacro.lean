/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahCarryOpcode

/-!
# The exact queue macro hidden in the YAH rewrite rules

One binary digit crossing a pure ternary suffix is ordinary long division by
two in base three.  This file defines that two-state transducer and proves,
for words of every length, that its output is realized by a nonempty trace in
the pinned eleven-rule YAH system.  It then factors each of the three left
boundary rules into one or two such sweeps.

These theorems expose a useful obstruction as well as a useful construction:
one complete macro consumes a leading trit, and any replacement length comes
only from terminal binary-one carries.  No recurrence or glider is asserted.
-/

namespace KontoroC
namespace YahQueueMacro

open YahRewriteSystem
open YahRewriteSystem.Symbol

inductive Carry where
  | zero | one
  deriving DecidableEq, Repr

inductive Trit where
  | zero | one | two
  deriving DecidableEq, Repr

open Carry Trit

@[simp] def tritSymbol : Trit → Symbol
  | Trit.zero => tri0
  | Trit.one => tri1
  | Trit.two => tri2

def tritWord (v : List Trit) : Word := v.map tritSymbol

@[simp] def binarySymbol : Carry → Symbol
  | Carry.zero => bin0
  | Carry.one => bin1

/-- One digit of base-three long division by two.  The first component is
the quotient digit and the second is the outgoing remainder. -/
@[simp] def transition : Carry → Trit → Trit × Carry
  | Carry.zero, Trit.zero => (Trit.zero, Carry.zero)
  | Carry.zero, Trit.one => (Trit.zero, Carry.one)
  | Carry.zero, Trit.two => (Trit.one, Carry.zero)
  | Carry.one, Trit.zero => (Trit.one, Carry.one)
  | Carry.one, Trit.one => (Trit.two, Carry.zero)
  | Carry.one, Trit.two => (Trit.two, Carry.one)

/-- The terminal remainder of a quotient sweep. -/
def terminalCarry : Carry → List Trit → Carry
  | c, [] => c
  | c, t :: v => terminalCarry (transition c t).2 v

/-- Quotient digits, including the terminal maximal-trit deposit when the
final remainder is one. -/
def carrySweep : Carry → List Trit → List Trit
  | Carry.zero, [] => []
  | Carry.one, [] => [Trit.two]
  | c, t :: v => (transition c t).1 :: carrySweep (transition c t).2 v

def carryBit : Carry → ℕ
  | Carry.zero => 0
  | Carry.one => 1

@[simp] theorem tritWord_nil : tritWord [] = [] := rfl

@[simp] theorem tritWord_cons (t : Trit) (v : List Trit) :
    tritWord (t :: v) = tritSymbol t :: tritWord v := rfl

/-- A sweep is letter-for-letter except for its possible terminal deposit. -/
theorem carrySweep_length (c : Carry) (v : List Trit) :
    (carrySweep c v).length = v.length + carryBit (terminalCarry c v) := by
  induction v generalizing c with
  | nil => cases c <;> rfl
  | cons t v ih =>
      simp only [carrySweep, List.length_cons, terminalCarry]
      rw [ih]
      omega

private theorem transition_rule (c : Carry) (t : Trit) :
    BasicRule [binarySymbol c, tritSymbol t]
      [tritSymbol (transition c t).1, binarySymbol (transition c t).2] := by
  cases c <;> cases t <;> simp only [binarySymbol, tritSymbol, transition,
    Prod.fst, Prod.snd] <;>
    first | exact BasicRule.a00 | exact BasicRule.a01 |
      exact BasicRule.a02 | exact BasicRule.a10 | exact BasicRule.a11 |
      exact BasicRule.a12

/-- Every abstract quotient sweep is an exact nonempty pinned-system trace. -/
theorem carrySweepTrace (c : Carry) (v : List Trit) :
    Relation.TransGen Step
      ([binarySymbol c] ++ tritWord v ++ [dot])
      (tritWord (carrySweep c v) ++ [dot]) := by
  induction v generalizing c with
  | nil =>
      cases c
      · simpa [binarySymbol, carrySweep, tritWord] using
          Relation.TransGen.single (Step.context [] [] BasicRule.dt0)
      · simpa [binarySymbol, carrySweep, tritWord] using
          Relation.TransGen.single (Step.context [] [] BasicRule.dt1)
  | cons t v ih =>
      have hfirst : Step
          ([binarySymbol c] ++ tritWord (t :: v) ++ [dot])
          ([tritSymbol (transition c t).1,
              binarySymbol (transition c t).2] ++ tritWord v ++ [dot]) := by
        simpa [tritWord, List.append_assoc] using
          Step.context [] (tritWord v ++ [dot]) (transition_rule c t)
      have htail := YahContextGlider.transGen_context contextClosed
        (ih (c := (transition c t).2))
        [tritSymbol (transition c t).1] []
      exact Relation.TransGen.head hfirst (by
        simpa [carrySweep, tritWord, List.append_assoc] using htail)

def canonicalTritWord (v : List Trit) : Word :=
  [slash] ++ tritWord v ++ [dot]

/-- QM1, zero head: `/ 0v.` is exactly one carry-one quotient sweep. -/
theorem macro_zero_trace (v : List Trit) :
    Relation.TransGen Step
      (canonicalTritWord (Trit.zero :: v))
      (canonicalTritWord (carrySweep Carry.one v)) := by
  have hfirst : Step
      (canonicalTritWord (Trit.zero :: v))
      ([slash, bin1] ++ tritWord v ++ [dot]) := by
    simpa [canonicalTritWord, tritWord, List.append_assoc] using
      Step.context [] (tritWord v ++ [dot]) BasicRule.b0
  have htail := YahContextGlider.transGen_context contextClosed
    (carrySweepTrace Carry.one v) [slash] []
  exact Relation.TransGen.head hfirst (by
    simpa [canonicalTritWord, List.append_assoc] using htail)

/-- QM1, one head: `/ 1v.` is two successive carry-zero quotient sweeps. -/
theorem macro_one_trace (v : List Trit) :
    Relation.TransGen Step
      (canonicalTritWord (Trit.one :: v))
      (canonicalTritWord
        (carrySweep Carry.zero (carrySweep Carry.zero v))) := by
  have hfirst : Step
      (canonicalTritWord (Trit.one :: v))
      ([slash, bin0, bin0] ++ tritWord v ++ [dot]) := by
    simpa [canonicalTritWord, tritWord, List.append_assoc] using
      Step.context [] (tritWord v ++ [dot]) BasicRule.b1
  have hsweep1 := YahContextGlider.transGen_context contextClosed
    (carrySweepTrace Carry.zero v) [slash, bin0] []
  have hsweep2 := YahContextGlider.transGen_context contextClosed
    (carrySweepTrace Carry.zero (carrySweep Carry.zero v)) [slash] []
  exact Relation.TransGen.head hfirst
    (Relation.TransGen.trans
      (by simpa [List.append_assoc] using hsweep1)
      (by simpa [canonicalTritWord, List.append_assoc] using hsweep2))

/-- QM1, two head: `/ 2v.` is first a carry-one and then a carry-zero
quotient sweep. -/
theorem macro_two_trace (v : List Trit) :
    Relation.TransGen Step
      (canonicalTritWord (Trit.two :: v))
      (canonicalTritWord
        (carrySweep Carry.zero (carrySweep Carry.one v))) := by
  have hfirst : Step
      (canonicalTritWord (Trit.two :: v))
      ([slash, bin0, bin1] ++ tritWord v ++ [dot]) := by
    simpa [canonicalTritWord, tritWord, List.append_assoc] using
      Step.context [] (tritWord v ++ [dot]) BasicRule.b2
  have hsweep1 := YahContextGlider.transGen_context contextClosed
    (carrySweepTrace Carry.one v) [slash, bin0] []
  have hsweep2 := YahContextGlider.transGen_context contextClosed
    (carrySweepTrace Carry.zero (carrySweep Carry.one v)) [slash] []
  exact Relation.TransGen.head hfirst
    (Relation.TransGen.trans
      (by simpa [List.append_assoc] using hsweep1)
      (by simpa [canonicalTritWord, List.append_assoc] using hsweep2))

/-- QM2 for the zero-head macro: its length charge is the terminal carry
minus the one consumed head trit. -/
theorem macro_zero_length_charge (v : List Trit) :
    (carrySweep Carry.one v).length + 1 =
      (Trit.zero :: v).length + carryBit (terminalCarry Carry.one v) := by
  rw [carrySweep_length]
  simp only [List.length_cons, List.length_nil, Nat.add_zero]
  omega

/-- QM2 for the one-head macro.  The two terminal carries are displayed
without subtraction in `ℕ`, so the statement remains exact in all cases. -/
theorem macro_one_length_charge (v : List Trit) :
    (carrySweep Carry.zero (carrySweep Carry.zero v)).length + 1 =
      (Trit.one :: v).length +
        carryBit (terminalCarry Carry.zero v) +
        carryBit (terminalCarry Carry.zero (carrySweep Carry.zero v)) := by
  rw [carrySweep_length, carrySweep_length]
  simp
  omega

/-- QM2 for the two-head macro. -/
theorem macro_two_length_charge (v : List Trit) :
    (carrySweep Carry.zero (carrySweep Carry.one v)).length + 1 =
      (Trit.two :: v).length +
        carryBit (terminalCarry Carry.one v) +
        carryBit (terminalCarry Carry.zero (carrySweep Carry.one v)) := by
  rw [carrySweep_length, carrySweep_length]
  simp
  omega

end YahQueueMacro
end KontoroC
