/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardNestedAllOddNoRoot
import KontoroC.OutwardFinitePrefixTailNoGo

/-!
# Exponential first-passage schedule growth does not imply positive drift

Use two distinct genuine first-passage words, `[true]` and `writerWord`, as a
binary alphabet.  There are exactly `2^n` length-`n` symbolic schedules over
that alphabet.  Assigning edge drift `-1` makes every such schedule have total
drift `-n`.

This finite exact family separates population entropy from pathwise escape:
exponentially many valid first-passage symbol strings can coexist with
strictly negative drift on every string.  Moreover, word membership alone
does not assert that any concatenation executes from one ordinary seed.
-/

namespace KontoroC
namespace OutwardEntropyDriftNoGo

open OutwardFiniteStateKraftGap OutwardCodeCompactness OutwardOddSlice
  OutwardFirstPassage OutwardWriterDecoderLiteral
  OutwardFinitePrefixTailNoGo

/-- Encode one binary choice by one of two distinct genuine first-passage
words. -/
def encodeBit (bit : Bool) : List Bool :=
  if bit then writerWord else [true]

theorem encodeBit_firstPassage (bit : Bool) :
    FirstPassage (encodeBit bit) := by
  cases bit with
  | false => exact singleton_true_firstPassage
  | true => exact writerWord_firstPassage

theorem encodeBit_injective : Function.Injective encodeBit := by
  intro left right h
  cases left <;> cases right
  · rfl
  · exact (writerWord_ne_singleton_true h.symm).elim
  · exact (writerWord_ne_singleton_true h).elim
  · rfl

/-- Blockwise encoding of a binary word. -/
def encodeSchedule (bits : List Bool) : List (List Bool) :=
  bits.map encodeBit

theorem encodeSchedule_injective : Function.Injective encodeSchedule := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons head tail => simp [encodeSchedule] at h
  | cons head tail ih =>
      intro right h
      cases right with
      | nil => simp [encodeSchedule] at h
      | cons head' tail' =>
          simp only [encodeSchedule, List.map_cons, List.cons.injEq] at h
          exact congrArg₂ List.cons (encodeBit_injective h.1) (ih h.2)

/-- All encoded schedules of exactly `n` first-passage blocks. -/
def schedules (n : ℕ) : Finset (List (List Bool)) :=
  (FirstPassageGrammar.binaryWords n).image encodeSchedule

/-- There are exactly `2^n` distinct schedules; encoding introduces no
collisions. -/
theorem card_schedules (n : ℕ) : (schedules n).card = 2 ^ n := by
  classical
  rw [schedules, Finset.card_image_of_injective _ encodeSchedule_injective,
    FirstPassageGrammar.card_binaryWords]

theorem mem_schedules_iff {n : ℕ} {schedule : List (List Bool)} :
    schedule ∈ schedules n ↔
      ∃ bits, bits.length = n ∧ encodeSchedule bits = schedule := by
  rw [schedules, Finset.mem_image]
  constructor
  · rintro ⟨bits, hbits, rfl⟩
    exact ⟨bits, FirstPassageGrammar.mem_binaryWords_iff.mp hbits, rfl⟩
  · rintro ⟨bits, hlength, rfl⟩
    exact ⟨bits, FirstPassageGrammar.mem_binaryWords_iff.mpr hlength, rfl⟩

/-- Every block of every encoded schedule belongs to the exact first-passage
code. -/
theorem schedules_wordsIn {n : ℕ} {schedule : List (List Bool)}
    (hschedule : schedule ∈ schedules n) :
    WordsIn FirstPassageCode schedule := by
  obtain ⟨bits, _, rfl⟩ := mem_schedules_iff.mp hschedule
  intro word hword
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hword
  exact encodeBit_firstPassage bit

theorem schedule_length {n : ℕ} {schedule : List (List Bool)}
    (hschedule : schedule ∈ schedules n) :
    schedule.length = n := by
  obtain ⟨bits, hlength, rfl⟩ := mem_schedules_iff.mp hschedule
  simpa [encodeSchedule] using hlength

/-- Toy counter cocycle with increment `-1` per symbolic block. -/
def assignedDrift (schedule : List (List Bool)) : ℤ :=
  -(schedule.length : ℤ)

/-- Every depth-`n` schedule has the same total negative drift `-n`. -/
theorem assignedDrift_eq_neg_depth {n : ℕ}
    {schedule : List (List Bool)} (hschedule : schedule ∈ schedules n) :
    assignedDrift schedule = -(n : ℤ) := by
  simp [assignedDrift, schedule_length hschedule]

/-- Exact entropy-versus-drift separation: for every positive depth there
are exponentially many genuine first-passage symbol schedules, but none has
nonnegative assigned drift. -/
theorem exponential_schedule_count_with_strictly_negative_drift
    {n : ℕ} (hn : 0 < n) :
    (schedules n).card = 2 ^ n ∧
      ∀ schedule ∈ schedules n,
        WordsIn FirstPassageCode schedule ∧ assignedDrift schedule < 0 := by
  refine ⟨card_schedules n, ?_⟩
  intro schedule hschedule
  refine ⟨schedules_wordsIn hschedule, ?_⟩
  rw [assignedDrift_eq_neg_depth hschedule]
  exact neg_neg_of_pos (by exact_mod_cast hn)

end OutwardEntropyDriftNoGo
end KontoroC
