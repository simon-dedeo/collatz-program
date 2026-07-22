/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahVariableMorphismRigidity

/-!
# Exact carry opcodes in the pinned YAH rewrite system

These are the finite two-counter instructions left visible after independent
marker-fixed morphisms have been ruled out.  They are concrete nonempty
`TransGen Step` traces, not a claim of a glider or nontermination.
-/

namespace KontoroC
namespace YahCarryOpcode

open YahRewriteSystem
open YahRewriteSystem.Symbol
open YahVariableMorphismRigidity

theorem digit_offset_lt_slope (s : Symbol) (hs : IsDigit s) :
    symbolAction s 0 < symbolSlope s := by
  cases s <;> simp_all [IsDigit, symbolAction, symbolSlope]

/-- The intercept of a digit word is strictly smaller than its slope. -/
theorem intercept_lt_slope (w : Word) (hw : DigitOnly w) :
    wordIntercept w < wordSlope w := by
  induction w with
  | nil => simp [wordIntercept, wordSlope, mixedEvalFrom]
  | cons s rest ih =>
      have hs := hw s (by simp)
      have hrest : DigitOnly rest := by
        intro x hx
        exact hw x (by simp [hx])
      have hi := ih hrest
      have hoff := digit_offset_lt_slope s hs
      change mixedEvalFrom (symbolAction s 0) rest <
        symbolSlope s * wordSlope rest
      rw [mixedEvalFrom_affine]
      have hpos := wordSlope_pos rest hrest
      nlinarith

/-- CR1: the failed complement square misses by exactly `s-t`, which is
strictly positive for every digit word. -/
theorem carry_defect_exact (v : Word) (hv : DigitOnly v) :
    wordIntercept (bin1 :: v) - wordIntercept (v ++ [bin0]) =
      wordSlope v - wordIntercept v ∧
    0 < wordSlope v - wordIntercept v := by
  have hlt := intercept_lt_slope v hv
  have hleft : wordIntercept (bin1 :: v) =
      wordSlope v + wordIntercept v := by
    change mixedEvalFrom 1 v = wordSlope v + wordIntercept v
    rw [mixedEvalFrom_affine]
    omega
  have hright : wordIntercept (v ++ [bin0]) =
      2 * wordIntercept v := by
    rw [wordIntercept_append]
    simp [wordSlope, symbolSlope, wordIntercept, mixedEvalFrom, symbolAction]
  constructor
  · rw [hleft, hright]
    omega
  · omega

/-- CR2: a binary one traverses a saturated ternary buffer and the terminal
dynamic rule increments its length. -/
theorem saturated_run (n : ℕ) :
    Relation.TransGen Step
      ([bin1] ++ List.replicate n tri2 ++ [dot])
      (List.replicate (n + 1) tri2 ++ [dot]) := by
  induction n with
  | zero =>
      simpa using Relation.TransGen.single
        (Step.context [] [] BasicRule.dt1)
  | succ n ih =>
      have hfirst : Step
          ([bin1] ++ List.replicate (n + 1) tri2 ++ [dot])
          ([tri2, bin1] ++ List.replicate n tri2 ++ [dot]) := by
        simpa [List.replicate_succ, List.append_assoc] using
          Step.context [] (List.replicate n tri2 ++ [dot]) BasicRule.a12
      have htail := YahContextGlider.transGen_context contextClosed ih [tri2] []
      exact Relation.TransGen.head hfirst (by
        simpa [List.replicate_succ, List.append_assoc] using htail)

/-- CR3: a binary zero traverses a zero ternary buffer and is deleted. -/
theorem zero_run (n : ℕ) :
    Relation.TransGen Step
      ([bin0] ++ List.replicate n tri0 ++ [dot])
      (List.replicate n tri0 ++ [dot]) := by
  induction n with
  | zero =>
      simpa using Relation.TransGen.single
        (Step.context [] [] BasicRule.dt0)
  | succ n ih =>
      have hfirst : Step
          ([bin0] ++ List.replicate (n + 1) tri0 ++ [dot])
          ([tri0, bin0] ++ List.replicate n tri0 ++ [dot]) := by
        simpa [List.replicate_succ, List.append_assoc] using
          Step.context [] (List.replicate n tri0 ++ [dot]) BasicRule.a00
      have htail := YahContextGlider.transGen_context contextClosed ih [tri0] []
      exact Relation.TransGen.head hfirst (by
        simpa [List.replicate_succ, List.append_assoc] using htail)

/-- A binary-one carry converts each crossed ternary zero to a ternary one,
then increments the saturated right buffer. -/
theorem carry_through_zeros (k n : ℕ) :
    Relation.TransGen Step
      ([bin1] ++ List.replicate k tri0 ++ List.replicate n tri2 ++ [dot])
      (List.replicate k tri1 ++ List.replicate (n + 1) tri2 ++ [dot]) := by
  induction k with
  | zero => simpa using saturated_run n
  | succ k ih =>
      have hfirst : Step
          ([bin1] ++ List.replicate (k + 1) tri0 ++
            List.replicate n tri2 ++ [dot])
          ([tri1, bin1] ++ List.replicate k tri0 ++
            List.replicate n tri2 ++ [dot]) := by
        simpa [List.replicate_succ, List.append_assoc] using
          Step.context []
            (List.replicate k tri0 ++ List.replicate n tri2 ++ [dot])
            BasicRule.a10
      have htail := YahContextGlider.transGen_context contextClosed ih [tri1] []
      exact Relation.TransGen.head hfirst (by
        simpa [List.replicate_succ, List.append_assoc] using htail)

/-- CR4: spend one left zero token, phase-change the remaining left counter,
and increment the saturated right counter. -/
theorem two_counter_transfer (k n : ℕ) :
    Relation.TransGen Step
      ([slash] ++ List.replicate (k + 1) tri0 ++
        List.replicate n tri2 ++ [dot])
      ([slash] ++ List.replicate k tri1 ++
        List.replicate (n + 1) tri2 ++ [dot]) := by
  have hfirst : Step
      ([slash] ++ List.replicate (k + 1) tri0 ++
        List.replicate n tri2 ++ [dot])
      ([slash, bin1] ++ List.replicate k tri0 ++
        List.replicate n tri2 ++ [dot]) := by
    simpa [List.replicate_succ, List.append_assoc] using
      Step.context []
        (List.replicate k tri0 ++ List.replicate n tri2 ++ [dot])
        BasicRule.b0
  have htail := YahContextGlider.transGen_context contextClosed
    (carry_through_zeros k n) [slash] []
  exact Relation.TransGen.head hfirst (by
    simpa [List.append_assoc] using htail)

end YahCarryOpcode
end KontoroC
