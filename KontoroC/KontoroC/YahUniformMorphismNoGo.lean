/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRewriteSystem
import KontoroC.YahUniformBlockNoGo

/-!
# No uniform digit-block self-simulation of the YAH system

This closes the rewriting seam left explicit by `YahUniformBlockNoGo`.  A
uniform morphism fixing the two delimiters and sending every digit to a
common-width digit block cannot simulate all eleven pinned YAH rules once
the width is at least three.
-/

namespace KontoroC
namespace YahUniformMorphismNoGo

open YahRewriteSystem
open YahRewriteSystem.Symbol

/-- The exact hygienic assumptions on a uniform block morphism. -/
structure UniformDigitMorphism (sigma : Symbol → Word) (width : ℕ) : Prop where
  slash_fixed : sigma slash = [slash]
  dot_fixed : sigma dot = [dot]
  bin0_digits : DigitOnly (sigma bin0)
  bin1_digits : DigitOnly (sigma bin1)
  tri0_digits : DigitOnly (sigma tri0)
  tri1_digits : DigitOnly (sigma tri1)
  tri2_digits : DigitOnly (sigma tri2)
  bin0_length : (sigma bin0).length = width
  bin1_length : (sigma bin1).length = width
  tri0_length : (sigma tri0).length = width
  tri1_length : (sigma tri1).length = width
  tri2_length : (sigma tri2).length = width

/-- The precise Y2 hypothesis needed here: each of the eleven generating
rules has a nonempty simulation after applying the letter morphism. -/
def BasicSimulation (sigma : Symbol → Word) : Prop :=
  ∀ {lhs rhs}, BasicRule lhs rhs →
    Relation.TransGen Step
      (YahContextGlider.wordMap sigma lhs)
      (YahContextGlider.wordMap sigma rhs)

theorem mixedEvalFrom_replicate_bin0 (x n : ℕ) :
    mixedEvalFrom x (List.replicate n bin0) = 2 ^ n * x := by
  induction n generalizing x with
  | zero => simp [mixedEvalFrom]
  | succ n ih =>
      rw [List.replicate_succ, mixedEvalFrom]
      change mixedEvalFrom (2 * x) (List.replicate n bin0) = _
      rw [ih, pow_succ]
      ring

/-- Every digit action is bounded above by the largest ternary action. -/
theorem symbolAction_le_three (s : Symbol) (x : ℕ) (hs : IsDigit s) :
    symbolAction s x ≤ 3 * x + 2 := by
  cases s <;> simp_all [IsDigit, symbolAction] <;> omega

theorem mixedEvalFrom_le (x : ℕ) (digits : Word) (hdigits : DigitOnly digits) :
    mixedEvalFrom x digits ≤ 3 ^ digits.length * (x + 1) := by
  induction digits generalizing x with
  | nil => simp [mixedEvalFrom]
  | cons s rest ih =>
      have hs : IsDigit s := hdigits s (by simp)
      have hrest : DigitOnly rest := by
        intro y hy
        exact hdigits y (by simp [hy])
      rw [mixedEvalFrom]
      calc
        mixedEvalFrom (symbolAction s x) rest ≤
            3 ^ rest.length * (symbolAction s x + 1) := ih _ hrest
        _ ≤ 3 ^ rest.length * (3 * x + 3) := by
          exact Nat.mul_le_mul_left _ (by
            have := symbolAction_le_three s x hs
            omega)
        _ = 3 ^ (s :: rest).length * (x + 1) := by
          simp only [List.length_cons, pow_succ]
          ring

/-- The terminal-zero rule alone forces the image of binary zero to be the
all-zero binary word. -/
theorem bin0_image_forced (sigma : Symbol → Word) (width : ℕ)
    (hu : UniformDigitMorphism sigma width)
    (hsim : BasicSimulation sigma) :
    sigma bin0 = List.replicate width bin0 := by
  have hdt0 := hsim BasicRule.dt0
  have hreduction : Relation.TransGen Step (sigma bin0 ++ [dot]) [dot] := by
    simpa [YahContextGlider.wordMap, hu.dot_fixed] using hdt0
  rw [← hu.bin0_length]
  exact digit_word_reducing_to_dot_all_bin0 (sigma bin0) hu.bin0_digits hreduction

/-- Simulation of the left-boundary ternary-one rule forces the numerical
identity `Val(sigma(tri1)) = 2^(2*width)`. -/
theorem tri1_image_value_forced (sigma : Symbol → Word) (width : ℕ)
    (hu : UniformDigitMorphism sigma width)
    (hsim : BasicSimulation sigma) :
    mixedEvalFrom 1 (sigma tri1) = 2 ^ (2 * width) := by
  have hb1 := hsim BasicRule.b1
  have htrace : Relation.TransGen Step
      ([slash] ++ sigma tri1)
      ([slash] ++ sigma bin0 ++ sigma bin0) := by
    simpa [YahContextGlider.wordMap, hu.slash_fixed, List.append_assoc] using hb1
  have hdot : ([slash] ++ sigma tri1).count dot = 0 := by
    simp [digitOnly_dot_count (sigma tri1) hu.tri1_digits]
  have heval := transGen_mixedEval_eq_of_dot_free htrace hdot
  rw [bin0_image_forced sigma width hu hsim] at heval
  have heval' : mixedEvalFrom 1 (sigma tri1) =
      mixedEvalFrom 1
        (List.replicate width bin0 ++ List.replicate width bin0) := by
    simpa [mixedEval, mixedEvalFrom, symbolAction, List.foldl_append] using heval
  calc
    mixedEvalFrom 1 (sigma tri1) =
        mixedEvalFrom 1
          (List.replicate width bin0 ++ List.replicate width bin0) := heval'
    _ = 2 ^ (2 * width) := by
      rw [← List.replicate_add]
      rw [mixedEvalFrom_replicate_bin0]
      simp only [Nat.mul_one]
      congr 1
      omega

/-- The full all-width-at-least-three no-go. -/
theorem no_uniform_digit_morphism (sigma : Symbol → Word) (width : ℕ)
    (hwidth : 3 ≤ width)
    (hu : UniformDigitMorphism sigma width)
    (hsim : BasicSimulation sigma) : False := by
  have hforced := tri1_image_value_forced sigma width hu hsim
  have hupper := mixedEvalFrom_le 1 (sigma tri1) hu.tri1_digits
  rw [hu.tri1_length] at hupper
  have hlt := YahUniformBlockNoGo.two_mul_threePow_lt_fourPow hwidth
  rw [YahUniformBlockNoGo.fourPow_eq_twoPow_double] at hlt
  omega

end YahUniformMorphismNoGo
end KontoroC
