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

theorem eval_tri0_run (x k : ℕ) :
    mixedEvalFrom x (List.replicate k tri0) = 3 ^ k * x := by
  induction k generalizing x with
  | zero => simp [mixedEvalFrom]
  | succ k ih =>
      rw [List.replicate_succ, mixedEvalFrom]
      change mixedEvalFrom (3 * x) (List.replicate k tri0) = _
      rw [ih, pow_succ]
      ring

theorem eval_tri1_run (x k : ℕ) :
    2 * mixedEvalFrom x (List.replicate k tri1) + 1 =
      3 ^ k * (2 * x + 1) := by
  induction k generalizing x with
  | zero => simp [mixedEvalFrom]
  | succ k ih =>
      rw [List.replicate_succ, mixedEvalFrom]
      change 2 * mixedEvalFrom (3 * x + 1) (List.replicate k tri1) + 1 = _
      rw [ih, pow_succ]
      ring

theorem eval_tri2_run (x n : ℕ) :
    mixedEvalFrom x (List.replicate n tri2) + 1 =
      3 ^ n * (x + 1) := by
  induction n generalizing x with
  | zero => simp [mixedEvalFrom]
  | succ n ih =>
      rw [List.replicate_succ, mixedEvalFrom]
      change mixedEvalFrom (3 * x + 2) (List.replicate n tri2) + 1 = _
      rw [ih, pow_succ]
      ring

theorem mixedEval_canonical (digits : Word) :
    mixedEval ([slash] ++ digits ++ [dot]) = mixedEvalFrom 1 digits := by
  simp [mixedEval, mixedEvalFrom, symbolAction, List.foldl_append]

theorem mixedEvalFrom_append (x : ℕ) (u v : Word) :
    mixedEvalFrom x (u ++ v) = mixedEvalFrom (mixedEvalFrom x u) v := by
  simp [mixedEvalFrom, List.foldl_append]

/-- The CR4 endpoint is exactly one odd shortcut step from its source. -/
theorem two_counter_transfer_value (k n : ℕ) :
    let source := [slash] ++ List.replicate (k + 1) tri0 ++
      List.replicate n tri2 ++ [dot]
    let endpoint := [slash] ++ List.replicate k tri1 ++
      List.replicate (n + 1) tri2 ++ [dot]
    2 * mixedEval endpoint = 3 * mixedEval source + 1 := by
  dsimp
  change 2 * mixedEval
      ([slash] ++ (List.replicate k tri1 ++
        List.replicate (n + 1) tri2) ++ [dot]) =
    3 * mixedEval
      ([slash] ++ (List.replicate (k + 1) tri0 ++
        List.replicate n tri2) ++ [dot]) + 1
  rw [mixedEval_canonical, mixedEval_canonical]
  rw [show mixedEvalFrom 1
        (List.replicate k tri1 ++ List.replicate (n + 1) tri2) =
      mixedEvalFrom (mixedEvalFrom 1 (List.replicate k tri1))
        (List.replicate (n + 1) tri2) by
    simp [mixedEvalFrom, List.foldl_append]]
  rw [show mixedEvalFrom 1
        (List.replicate (k + 1) tri0 ++ List.replicate n tri2) =
      mixedEvalFrom (mixedEvalFrom 1 (List.replicate (k + 1) tri0))
        (List.replicate n tri2) by
    simp [mixedEvalFrom, List.foldl_append]]
  have h0 := eval_tri0_run 1 (k + 1)
  have h1 := eval_tri1_run 1 k
  have h2s := eval_tri2_run (3 ^ (k + 1)) n
  have h2e := eval_tri2_run
    (mixedEvalFrom 1 (List.replicate k tri1)) (n + 1)
  rw [h0]
  simp only [Nat.mul_one]
  have hpk : 3 ^ (k + 1) = 3 ^ k * 3 := by rw [pow_succ]
  have hpn : 3 ^ (n + 1) = 3 ^ n * 3 := by rw [pow_succ]
  have hA : 2 * (mixedEvalFrom 1 (List.replicate k tri1) + 1) =
      3 ^ (k + 1) + 1 := by
    nlinarith
  have hES : 2 *
        (mixedEvalFrom (mixedEvalFrom 1 (List.replicate k tri1))
          (List.replicate (n + 1) tri2) + 1) =
      3 * (mixedEvalFrom (3 ^ (k + 1))
        (List.replicate n tri2) + 1) := by
    calc
      _ = 2 * (3 ^ (n + 1) *
          (mixedEvalFrom 1 (List.replicate k tri1) + 1)) := by rw [h2e]
      _ = 3 * 3 ^ n *
          (2 * (mixedEvalFrom 1 (List.replicate k tri1) + 1)) := by
            rw [hpn]
            ring
      _ = 3 * 3 ^ n * (3 ^ (k + 1) + 1) := by rw [hA]
      _ = 3 * (mixedEvalFrom (3 ^ (k + 1))
          (List.replicate n tri2) + 1) := by
            rw [h2s]
            ring
  nlinarith

/-- Therefore every CR4 instruction is strictly outward in represented
ordinary-integer value. -/
theorem two_counter_transfer_outward (k n : ℕ) :
    mixedEval
        ([slash] ++ List.replicate (k + 1) tri0 ++
          List.replicate n tri2 ++ [dot]) <
      mixedEval
        ([slash] ++ List.replicate k tri1 ++
          List.replicate (n + 1) tri2 ++ [dot]) := by
  have hrel := two_counter_transfer_value k n
  dsimp at hrel
  have hsource : 1 < mixedEval
      ([slash] ++ List.replicate (k + 1) tri0 ++
        List.replicate n tri2 ++ [dot]) := by
    change 1 < mixedEval
      ([slash] ++ (List.replicate (k + 1) tri0 ++
        List.replicate n tri2) ++ [dot])
    rw [mixedEval_canonical]
    rw [mixedEvalFrom_append, eval_tri0_run]
    simp only [Nat.mul_one]
    have hpow : 1 < 3 ^ (k + 1) := by
      exact one_lt_pow₀ (by omega) (by omega)
    have h2 := eval_tri2_run (3 ^ (k + 1)) n
    have hnpos : 0 < 3 ^ n := by positivity
    have hn : 1 ≤ 3 ^ n := by omega
    nlinarith
  have hrel' : 2 * mixedEval
        ([slash] ++ List.replicate k tri1 ++
          List.replicate (n + 1) tri2 ++ [dot]) =
      3 * mixedEval
        ([slash] ++ List.replicate (k + 1) tri0 ++
          List.replicate n tri2 ++ [dot]) + 1 := by
    simpa using hrel
  omega

end YahCarryOpcode
end KontoroC
