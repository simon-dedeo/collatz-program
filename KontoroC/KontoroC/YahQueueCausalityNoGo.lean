/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRechargeReservoir

/-!
# The YAH queue macro has no right-to-left feedback

The recharge amplifier ends with a long right-hand run of maximal ternary
digits.  That run is useful storage, but the pinned quotient transducer is
strictly left-to-right: in one complete queue macro, a suffix cannot change
the transformed image of any prefix to its left.

This file proves the exact factorization.  It rules out an *immediate*
decoder in which the new right reservoir writes a new leading recharge
address in one macro.  It does not rule out a longer program which first
consumes or transports the intervening prefix.
-/

namespace KontoroC
namespace YahQueueCausalityNoGo

open YahQueueMacro
open YahPerpetualGrowthNoGo
open Carry Trit

/-- The remainder state of a concatenation is obtained by feeding the
remainder state of the prefix into the suffix. -/
theorem terminalCarry_append (c : Carry) (u v : List Trit) :
    terminalCarry c (u ++ v) = terminalCarry (terminalCarry c u) v := by
  induction u generalizing c with
  | nil => rfl
  | cons t u ih =>
      simp only [List.cons_append, terminalCarry]
      exact ih (transition c t).2

/-- The quotient core is letter-for-letter. -/
theorem quotientCore_length (c : Carry) (u : List Trit) :
    (quotientCore c u).length = u.length := by
  induction u generalizing c with
  | nil => rfl
  | cons t u ih =>
      simp only [quotientCore, List.length_cons]
      rw [ih]

/-- Exact causal factorization of a quotient sweep.  The output before the
suffix is `quotientCore c u` and is entirely independent of `v`; only the
one-bit terminal carry of `u` crosses the boundary. -/
theorem carrySweep_append (c : Carry) (u v : List Trit) :
    carrySweep c (u ++ v) =
      quotientCore c u ++ carrySweep (terminalCarry c u) v := by
  induction u generalizing c with
  | nil => rfl
  | cons t u ih =>
      simp only [List.cons_append, carrySweep, quotientCore, terminalCarry]
      rw [ih]

/-- The prefix emitted by one whole queue macro before it reaches a chosen
suffix boundary. -/
@[simp] def macroPrefix : Trit → List Trit → List Trit
  | Trit.zero, u => quotientCore Carry.one u
  | Trit.one, u => quotientCore Carry.zero (quotientCore Carry.zero u)
  | Trit.two, u => quotientCore Carry.zero (quotientCore Carry.one u)

/-- Everything emitted at and to the right of the chosen suffix boundary. -/
@[simp] def macroSuffix : Trit → List Trit → List Trit → List Trit
  | Trit.zero, u, v => carrySweep (terminalCarry Carry.one u) v
  | Trit.one, u, v =>
      carrySweep (terminalCarry Carry.zero (quotientCore Carry.zero u))
        (carrySweep (terminalCarry Carry.zero u) v)
  | Trit.two, u, v =>
      carrySweep (terminalCarry Carry.zero (quotientCore Carry.one u))
        (carrySweep (terminalCarry Carry.one u) v)

theorem macroPrefix_length (h : Trit) (u : List Trit) :
    (macroPrefix h u).length = u.length := by
  cases h <;> simp only [macroPrefix] <;> rw [quotientCore_length] <;>
    first | rfl | rw [quotientCore_length]

/-- Exact one-macro prefix/suffix decomposition. -/
theorem queueMacro_cons_append (h : Trit) (u v : List Trit) :
    queueMacro (h :: (u ++ v)) =
      macroPrefix h u ++ macroSuffix h u v := by
  cases h <;>
    simp only [queueMacro, macroPrefix, macroSuffix, carrySweep_append]

/-- A right suffix cannot alter any of the first `u.length` output symbols. -/
theorem queueMacro_take_prefix (h : Trit) (u v : List Trit) :
    (queueMacro (h :: (u ++ v))).take u.length = macroPrefix h u := by
  rw [queueMacro_cons_append]
  rw [← macroPrefix_length h u]
  simp

/-- Extensional no-feedback form: arbitrary alternative right suffixes give
identical transformed prefixes. -/
theorem queueMacro_prefix_independent (h : Trit) (u v₁ v₂ : List Trit) :
    (queueMacro (h :: (u ++ v₁))).take u.length =
      (queueMacro (h :: (u ++ v₂))).take u.length := by
  rw [queueMacro_take_prefix, queueMacro_take_prefix]

/-- At most two carry bits cross a chosen prefix/suffix boundary during one
whole macro.  The zero-head case uses only the first component. -/
@[simp] def macroBoundary : Trit → List Trit → Carry × Carry
  | Trit.zero, u => (terminalCarry Carry.one u, Carry.zero)
  | Trit.one, u =>
      (terminalCarry Carry.zero u,
        terminalCarry Carry.zero (quotientCore Carry.zero u))
  | Trit.two, u =>
      (terminalCarry Carry.one u,
        terminalCarry Carry.zero (quotientCore Carry.one u))

@[simp] def continueFromBoundary : Trit → Carry × Carry → List Trit → List Trit
  | Trit.zero, b, v => carrySweep b.1 v
  | Trit.one, b, v => carrySweep b.2 (carrySweep b.1 v)
  | Trit.two, b, v => carrySweep b.2 (carrySweep b.1 v)

theorem macroSuffix_eq_boundary (h : Trit) (u v : List Trit) :
    macroSuffix h u v = continueFromBoundary h (macroBoundary h u) v := by
  cases h <;> rfl

/-- The arbitrary-size prefix can influence the transformation of the right
suffix through only its two-bit boundary state in one macro. -/
theorem macroSuffix_eq_of_boundary_eq (h : Trit) (u₁ u₂ v : List Trit)
    (hb : macroBoundary h u₁ = macroBoundary h u₂) :
    macroSuffix h u₁ v = macroSuffix h u₂ v := by
  rw [macroSuffix_eq_boundary, macroSuffix_eq_boundary, hb]

/-- In particular, neither the length nor the contents of a trailing maximal
trit reservoir can write into the transformed prefix in one queue macro. -/
theorem trailing_reservoir_no_one_macro_feedback
    (h : Trit) (u : List Trit) (j₁ j₂ : ℕ) :
    (queueMacro (h :: (u ++ List.replicate j₁ Trit.two))).take u.length =
      (queueMacro (h :: (u ++ List.replicate j₂ Trit.two))).take u.length := by
  exact queueMacro_prefix_independent h u _ _

end YahQueueCausalityNoGo
end KontoroC
