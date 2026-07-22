/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineTwoRail

/-!
# Two-family affine return circuits

A shape cycle becomes a genuine infinite Collatz program only when its affine
family indices also close.  This file packages the smallest nontrivial case:
two affine gate families and coefficientwise links in both directions.  The
tail is allowed to expand on every return.
-/

namespace KontoroC

/-- A coefficientwise return circuit `left → right → left`.

`middleOffset/middleSlope` select the right-family tail from the current
left-family tail.  `returnOffset/returnSlope` select the next left-family tail
after the right gate. -/
structure AffineTwoRailTwoCycle
    (left right : AffineTwoRailFamily)
    (forward : AffineTwoRailLink left right)
    (backward : AffineTwoRailLink right left) where
  initialTail : ℕ
  middleOffset : ℕ
  middleSlope : ℕ
  returnOffset : ℕ
  returnSlope : ℕ
  middle_base_link :
    forward.targetIndexBase =
      backward.sourceIndexBase +
        backward.sourceIndexStride * middleOffset
  middle_stride_link :
    forward.targetIndexStride =
      backward.sourceIndexStride * middleSlope
  return_base_link :
    backward.targetIndexBase +
        backward.targetIndexStride * middleOffset =
      forward.sourceIndexBase +
        forward.sourceIndexStride * returnOffset
  return_stride_link :
    backward.targetIndexStride * middleSlope =
      forward.sourceIndexStride * returnSlope
  start_large :
    4 < (left.member (forward.sourceIndex initialTail)).start
  left_outward : ∀ u,
    (left.member (forward.sourceIndex u)).start <
      (left.member (forward.sourceIndex u)).endpoint
  right_outward : ∀ u,
    (right.member (backward.sourceIndex u)).start <
      (right.member (backward.sourceIndex u)).endpoint

namespace AffineTwoRailTwoCycle

def middleTail {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (u : ℕ) : ℕ :=
  g.middleOffset + g.middleSlope * u

def nextTail {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (u : ℕ) : ℕ :=
  g.returnOffset + g.returnSlope * u

def roundTail {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) : ℕ → ℕ
  | 0 => g.initialTail
  | t + 1 => g.nextTail (g.roundTail t)

theorem middle_index_link {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (u : ℕ) :
    forward.targetIndex u = backward.sourceIndex (g.middleTail u) := by
  simp only [AffineTwoRailLink.targetIndex,
    AffineTwoRailLink.sourceIndex, middleTail]
  rw [g.middle_base_link, g.middle_stride_link]
  ring

theorem return_index_link {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (u : ℕ) :
    backward.targetIndex (g.middleTail u) =
      forward.sourceIndex (g.nextTail u) := by
  simp only [AffineTwoRailLink.targetIndex,
    AffineTwoRailLink.sourceIndex, middleTail, nextTail]
  calc
    backward.targetIndexBase +
          backward.targetIndexStride *
            (g.middleOffset + g.middleSlope * u) =
        (backward.targetIndexBase +
            backward.targetIndexStride * g.middleOffset) +
          (backward.targetIndexStride * g.middleSlope) * u := by ring
    _ = (forward.sourceIndexBase +
            forward.sourceIndexStride * g.returnOffset) +
          (forward.sourceIndexStride * g.returnSlope) * u := by
      rw [g.return_base_link, g.return_stride_link]
    _ = forward.sourceIndexBase +
          forward.sourceIndexStride *
            (g.returnOffset + g.returnSlope * u) := by ring

def leftGate {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    TwoRailGate :=
  left.member (forward.sourceIndex (g.roundTail t))

def rightGate {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    TwoRailGate :=
  right.member (backward.sourceIndex (g.middleTail (g.roundTail t)))

def roundWord {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    List ℕ :=
  (g.leftGate t).word ++ (g.rightGate t).word

theorem left_to_right {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    (g.leftGate t).endpoint = (g.rightGate t).start := by
  calc
    (g.leftGate t).endpoint =
        (right.member (forward.targetIndex (g.roundTail t))).start :=
      forward.endpoint_link _
    _ = (g.rightGate t).start := by
      simp only [rightGate]
      rw [g.middle_index_link]

theorem right_to_next_left {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    (g.rightGate t).endpoint = (g.leftGate (t + 1)).start := by
  calc
    (g.rightGate t).endpoint =
        (left.member (backward.targetIndex
          (g.middleTail (g.roundTail t)))).start :=
      backward.endpoint_link _
    _ = (g.leftGate (t + 1)).start := by
      rw [g.return_index_link]
      rfl

/-- Each return round is a literal legal concatenation of two exact gates. -/
theorem round_legal_and_endpoint {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) (t : ℕ) :
    WordLegal (g.leftGate t).start (g.roundWord t) ∧
      runWord (g.leftGate t).start (g.roundWord t) =
        (g.leftGate (t + 1)).start := by
  have hl := (g.leftGate t).legal_and_endpoint
  have hr := (g.rightGate t).legal_and_endpoint
  rw [roundWord, wordLegal_append_iff, runWord_append]
  constructor
  · refine ⟨hl.1, ?_⟩
    rw [hl.2, g.left_to_right]
    exact hr.1
  · rw [hl.2, g.left_to_right, hr.2, g.right_to_next_left]

/-- A coefficientwise two-family return circuit is a genuine infinite
Collatz macro-glider. -/
def toMacroGlider {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) : MacroGlider where
  state t := (g.leftGate t).start
  word := g.roundWord
  start_large := g.start_large
  word_nonempty t := by simp [roundWord, TwoRailGate.word]
  legal t := (g.round_legal_and_endpoint t).1
  transition t := (g.round_legal_and_endpoint t).2
  grows t := by
    calc
      (g.leftGate t).start < (g.leftGate t).endpoint :=
        g.left_outward (g.roundTail t)
      _ = (g.rightGate t).start := g.left_to_right t
      _ < (g.rightGate t).endpoint :=
        g.right_outward (g.middleTail (g.roundTail t))
      _ = (g.leftGate (t + 1)).start := g.right_to_next_left t

/-- Sound endpoint for a two-family affine return circuit. -/
theorem not_conjecture {left right : AffineTwoRailFamily}
    {forward : AffineTwoRailLink left right}
    {backward : AffineTwoRailLink right left}
    (g : AffineTwoRailTwoCycle left right forward backward) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end AffineTwoRailTwoCycle

end KontoroC
