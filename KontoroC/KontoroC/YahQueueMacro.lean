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

def tritDigit : Trit → ℕ
  | Trit.zero => 0
  | Trit.one => 1
  | Trit.two => 2

/-- Base-three evaluation with an arbitrary leading accumulator. -/
def tritEvalFrom : ℕ → List Trit → ℕ
  | x, [] => x
  | x, t :: v => tritEvalFrom (3 * x + tritDigit t) v

/-- Quotient digits before the terminal carry is deposited. -/
def quotientCore : Carry → List Trit → List Trit
  | _, [] => []
  | c, t :: v =>
      (transition c t).1 :: quotientCore (transition c t).2 v

def carryDeposit : Carry → List Trit
  | Carry.zero => []
  | Carry.one => [Trit.two]

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

theorem carrySweep_eq_core_append (c : Carry) (v : List Trit) :
    carrySweep c v = quotientCore c v ++ carryDeposit (terminalCarry c v) := by
  induction v generalizing c with
  | nil => cases c <;> rfl
  | cons t v ih =>
      simp only [carrySweep, quotientCore, terminalCarry, List.cons_append]
      rw [ih]

private theorem transition_division (x : ℕ) (c : Carry) (t : Trit) :
    3 * (2 * x + carryBit c) + tritDigit t =
      2 * (3 * x + tritDigit (transition c t).1) +
        carryBit (transition c t).2 := by
  cases c <;> cases t <;>
    simp [carryBit, tritDigit, transition] <;> omega

/-- The transducer really is Euclidean division by two: `quotientCore` is
the quotient and `terminalCarry` is the remainder. -/
theorem quotientCore_division (x : ℕ) (c : Carry) (v : List Trit) :
    tritEvalFrom (2 * x + carryBit c) v =
      2 * tritEvalFrom x (quotientCore c v) +
        carryBit (terminalCarry c v) := by
  induction v generalizing x c with
  | nil => simp [tritEvalFrom, quotientCore, terminalCarry]
  | cons t v ih =>
      simp only [tritEvalFrom, quotientCore, terminalCarry]
      rw [show 3 * (2 * x + carryBit c) + tritDigit t =
          2 * (3 * x + tritDigit (transition c t).1) +
            carryBit (transition c t).2 by
        exact transition_division x c t]
      exact ih (3 * x + tritDigit (transition c t).1)
        (transition c t).2

theorem carryBit_lt_two (c : Carry) : carryBit c < 2 := by
  cases c <;> simp [carryBit]

/-- In particular, the terminal carry is exactly the parity of the swept
integer, not merely a state-machine label. -/
theorem terminalCarry_eq_mod_two (x : ℕ) (c : Carry) (v : List Trit) :
    carryBit (terminalCarry c v) =
      tritEvalFrom (2 * x + carryBit c) v % 2 := by
  rw [quotientCore_division]
  have hlt := carryBit_lt_two (terminalCarry c v)
  omega

theorem tritEvalFrom_append (x : ℕ) (u v : List Trit) :
    tritEvalFrom x (u ++ v) = tritEvalFrom (tritEvalFrom x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons t u ih =>
      simp only [List.cons_append, tritEvalFrom]
      exact ih (3 * x + tritDigit t)

theorem tritEval_deposit (x : ℕ) (c : Carry) :
    tritEvalFrom x (carryDeposit c) =
      if c = Carry.zero then x else 3 * x + 2 := by
  cases c <;> simp [carryDeposit, tritEvalFrom, tritDigit]

/-- The quotient word has the same parity as the bare quotient even when an
odd terminal step deposits a maximal trit. -/
theorem carrySweep_parity (x : ℕ) (c : Carry) (v : List Trit) :
    tritEvalFrom x (carrySweep c v) % 2 =
      tritEvalFrom x (quotientCore c v) % 2 := by
  rw [carrySweep_eq_core_append, tritEvalFrom_append, tritEval_deposit]
  split <;> omega

/-- In a two-sweep macro, the first and second terminal carries are exactly
the low two binary bits of the input value. -/
theorem twoSweep_residue (c : Carry) (v : List Trit) :
    tritEvalFrom (4 + carryBit c) v % 4 =
      2 * carryBit
          (terminalCarry Carry.zero (carrySweep c v)) +
        carryBit (terminalCarry c v) := by
  have hdiv := quotientCore_division 2 c v
  have hsecond := terminalCarry_eq_mod_two 1 Carry.zero (carrySweep c v)
  have hparity := carrySweep_parity 2 c v
  have hqmod : carryBit
        (terminalCarry Carry.zero (carrySweep c v)) =
      tritEvalFrom 2 (quotientCore c v) % 2 := by
    rw [hsecond]
    simpa [carryBit] using hparity
  have hr1 := carryBit_lt_two (terminalCarry c v)
  have hr2 := carryBit_lt_two
    (terminalCarry Carry.zero (carrySweep c v))
  norm_num at hdiv
  omega

/-- Number of terminal carry-one events forced by a residue modulo four. -/
def twoSweepCharge : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 0

theorem twoSweep_charge_by_mod_four (c : Carry) (v : List Trit) :
    carryBit (terminalCarry c v) +
        carryBit (terminalCarry Carry.zero (carrySweep c v)) =
      twoSweepCharge (tritEvalFrom (4 + carryBit c) v % 4) := by
  have hres := twoSweep_residue c v
  have hmod : tritEvalFrom (4 + carryBit c) v % 4 < 4 :=
    Nat.mod_lt _ (by omega)
  have hr1 := carryBit_lt_two (terminalCarry c v)
  have hr2 := carryBit_lt_two
    (terminalCarry Carry.zero (carrySweep c v))
  interval_cases h : tritEvalFrom (4 + carryBit c) v % 4 <;>
    simp [twoSweepCharge, h] at hres ⊢ <;> omega

theorem macro_zero_terminal_bit (v : List Trit) :
    carryBit (terminalCarry Carry.one v) =
      tritEvalFrom 1 (Trit.zero :: v) % 2 := by
  simpa [tritEvalFrom, tritDigit, carryBit] using
    terminalCarry_eq_mod_two 1 Carry.one v

theorem macro_one_carry_charge (v : List Trit) :
    carryBit (terminalCarry Carry.zero v) +
        carryBit
          (terminalCarry Carry.zero (carrySweep Carry.zero v)) =
      twoSweepCharge (tritEvalFrom 1 (Trit.one :: v) % 4) := by
  simpa [tritEvalFrom, tritDigit, carryBit] using
    twoSweep_charge_by_mod_four Carry.zero v

theorem macro_two_carry_charge (v : List Trit) :
    carryBit (terminalCarry Carry.one v) +
        carryBit
          (terminalCarry Carry.zero (carrySweep Carry.one v)) =
      twoSweepCharge (tritEvalFrom 1 (Trit.two :: v) % 4) := by
  simpa [tritEvalFrom, tritDigit, carryBit] using
    twoSweep_charge_by_mod_four Carry.one v

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

/-- QM3, zero head: this macro never grows; it preserves length exactly on
odd values and otherwise loses the consumed head trit. -/
theorem macro_zero_length_eq_iff_odd (v : List Trit) :
    (carrySweep Carry.one v).length = (Trit.zero :: v).length ↔
      tritEvalFrom 1 (Trit.zero :: v) % 2 = 1 := by
  have hlen := macro_zero_length_charge v
  have hbit := macro_zero_terminal_bit v
  have hlt := carryBit_lt_two (terminalCarry Carry.one v)
  omega

theorem macro_zero_ne_grows (v : List Trit) :
    (carrySweep Carry.one v).length < (Trit.zero :: v).length + 1 := by
  have hlen := macro_zero_length_charge v
  have hlt := carryBit_lt_two (terminalCarry Carry.one v)
  omega

/-- QM3, one head: growth by one occurs exactly in residue class three
modulo four. -/
theorem macro_one_grows_iff_mod_four_eq_three (v : List Trit) :
    (carrySweep Carry.zero (carrySweep Carry.zero v)).length =
        (Trit.one :: v).length + 1 ↔
      tritEvalFrom 1 (Trit.one :: v) % 4 = 3 := by
  have hlen := macro_one_length_charge v
  have hcharge := macro_one_carry_charge v
  have hmod : tritEvalFrom 1 (Trit.one :: v) % 4 < 4 :=
    Nat.mod_lt _ (by omega)
  interval_cases h : tritEvalFrom 1 (Trit.one :: v) % 4 <;>
    simp [twoSweepCharge] at hcharge <;> omega

/-- QM3, two head: the same nonlocal residue criterion controls growth. -/
theorem macro_two_grows_iff_mod_four_eq_three (v : List Trit) :
    (carrySweep Carry.zero (carrySweep Carry.one v)).length =
        (Trit.two :: v).length + 1 ↔
      tritEvalFrom 1 (Trit.two :: v) % 4 = 3 := by
  have hlen := macro_two_length_charge v
  have hcharge := macro_two_carry_charge v
  have hmod : tritEvalFrom 1 (Trit.two :: v) % 4 < 4 :=
    Nat.mod_lt _ (by omega)
  interval_cases h : tritEvalFrom 1 (Trit.two :: v) % 4 <;>
    simp [twoSweepCharge] at hcharge <;> omega

/-- The alternating checksum, evaluated in `Z/4Z`.  Since three is minus
one modulo four, each new trit replaces the accumulator `a` by `digit-a`.
Unfolding this fold gives exactly the alternating signed-digit formula QM4. -/
def alternatingChecksumFrom : ZMod 4 → List Trit → ZMod 4
  | x, [] => x
  | x, t :: v =>
      alternatingChecksumFrom ((tritDigit t : ZMod 4) - x) v

def alternatingChecksum (v : List Trit) : ZMod 4 :=
  alternatingChecksumFrom 1 v

theorem tritEval_eq_alternatingChecksumFrom (x : ℕ) (v : List Trit) :
    (tritEvalFrom x v : ZMod 4) = alternatingChecksumFrom x v := by
  induction v generalizing x with
  | nil => rfl
  | cons t v ih =>
      rw [tritEvalFrom, alternatingChecksumFrom, ih]
      congr 1
      push_cast
      have hthree : (3 : ZMod 4) = -1 := by decide
      rw [hthree]
      ring

/-- QM4: the canonical value modulo four is the global alternating
checksum. -/
theorem canonical_mod_four_eq_checksum (v : List Trit) :
    (tritEvalFrom 1 v : ZMod 4) = alternatingChecksum v := by
  exact tritEval_eq_alternatingChecksumFrom 1 v

end YahQueueMacro
end KontoroC
