/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeSemilinearOrder
import KontoroC.OutwardWriterDecoderLiteral

/-!
# Finite schedule prefixes do not decide tail recurrence

Every finite prefix of a symbolic first-passage-word schedule has valid
continuations with opposite recurrence behavior.  One continuation repeats
the concrete writer word forever; another repeats the one-letter
first-passage word forever and therefore avoids the writer word.

This is a quantifier audit for bounded survival and recurrence statistics.
It concerns schedules whose individual symbols belong to the first-passage
code.  It deliberately does not assert that either schedule is consecutively
executable from one ordinary seed; that stronger semantic condition is the
load-bearing invariant problem.
-/

namespace KontoroC
namespace OutwardFinitePrefixTailNoGo

open OutwardFirstPassage OutwardOddSlice OutwardWriterDecoderLiteral

variable {α : Type*}

/-- Replace a sequence after index `N` by one constant tail value. -/
def forceTail (base : ℕ → α) (N : ℕ) (tail : α) : ℕ → α :=
  fun n => if n < N then base n else tail

@[simp] theorem forceTail_of_lt (base : ℕ → α) (N : ℕ) (tail : α)
    {n : ℕ} (hn : n < N) :
    forceTail base N tail n = base n := by
  simp [forceTail, hn]

@[simp] theorem forceTail_of_ge (base : ℕ → α) (N : ℕ) (tail : α)
    {n : ℕ} (hn : N ≤ n) :
    forceTail base N tail n = tail := by
  simp [forceTail, Nat.not_lt.mpr hn]

/-- Two schedules agree throughout their first `N` entries. -/
def AgreeBelow (N : ℕ) (left right : ℕ → α) : Prop :=
  ∀ n, n < N → left n = right n

/-- A value appears arbitrarily far out in a schedule. -/
def InfinitelyOftenEq (value : α) (schedule : ℕ → α) : Prop :=
  ∀ bound, ∃ n, bound ≤ n ∧ schedule n = value

/-- Beyond some index the schedule always avoids a specified value. -/
def EventuallyAvoidsEq (value : α) (schedule : ℕ → α) : Prop :=
  ∃ bound, ∀ n, bound ≤ n → schedule n ≠ value

/-- A property is determined by a length-`N` prefix inside a declared class
of schedules. -/
def PrefixDecidesOn (Valid : (ℕ → α) → Prop) (N : ℕ)
    (Property : (ℕ → α) → Prop) : Prop :=
  ∀ left right, Valid left → Valid right → AgreeBelow N left right →
    (Property left ↔ Property right)

theorem forceTail_agreeBelow (base : ℕ → α) (N : ℕ)
    (leftTail rightTail : α) :
    AgreeBelow N (forceTail base N leftTail)
      (forceTail base N rightTail) := by
  intro n hn
  simp [forceTail, hn]

theorem forceTail_infinitelyOften (base : ℕ → α) (N : ℕ)
    (value : α) :
    InfinitelyOftenEq value (forceTail base N value) := by
  intro bound
  refine ⟨max N bound, Nat.le_max_right N bound, ?_⟩
  exact forceTail_of_ge base N value (Nat.le_max_left N bound)

theorem forceTail_eventuallyAvoids
    (base : ℕ → α) (N : ℕ) {value tail : α}
    (hne : tail ≠ value) :
    EventuallyAvoidsEq value (forceTail base N tail) := by
  refine ⟨N, fun n hn => ?_⟩
  rw [forceTail_of_ge base N tail hn]
  exact hne

theorem EventuallyAvoidsEq.not_infinitelyOften
    {value : α} {schedule : ℕ → α}
    (havoid : EventuallyAvoidsEq value schedule) :
    ¬InfinitelyOftenEq value schedule := by
  intro hoften
  obtain ⟨bound, hbound⟩ := havoid
  obtain ⟨n, hn, heq⟩ := hoften bound
  exact hbound n hn heq

/-- Abstract tail-law no-go: for two distinct values, infinite recurrence of
one value is not determined by any finite prefix, even without restricting
the schedule class. -/
theorem no_finite_prefix_decides_infinitelyOften
    {value tail : α} (hne : tail ≠ value) (N : ℕ) :
    ¬PrefixDecidesOn (fun _ => True) N (InfinitelyOftenEq value) := by
  intro hdecides
  let base : ℕ → α := fun _ => value
  let recurring := forceTail base N value
  let avoiding := forceTail base N tail
  have hsame : AgreeBelow N recurring avoiding :=
    forceTail_agreeBelow base N value tail
  have hrecurring : InfinitelyOftenEq value recurring :=
    forceTail_infinitelyOften base N value
  have havoiding : ¬InfinitelyOftenEq value avoiding :=
    (forceTail_eventuallyAvoids base N hne).not_infinitelyOften
  exact havoiding ((hdecides recurring avoiding trivial trivial hsame).mp
    hrecurring)

/-! ## First-passage specialization -/

/-- A symbolic schedule all of whose entries are first-passage words. -/
def FirstPassageSchedule (schedule : ℕ → List Bool) : Prop :=
  ∀ n, FirstPassage (schedule n)

theorem firstPassageSchedule_forceTail
    (base : ℕ → List Bool) (N : ℕ) (tail : List Bool)
    (hbase : FirstPassageSchedule base) (htail : FirstPassage tail) :
    FirstPassageSchedule (forceTail base N tail) := by
  intro n
  by_cases hn : n < N
  · rw [forceTail_of_lt base N tail hn]
    exact hbase n
  · rw [forceTail_of_ge base N tail (Nat.le_of_not_gt hn)]
    exact htail

theorem writerWord_ne_singleton_true : writerWord ≠ [true] := by
  norm_num [writerWord]

/-- Explicit opposite-tail continuations inside the first-passage code. -/
theorem exists_firstPassageSchedules_same_prefix_opposite_writerRecurrence
    (N : ℕ) :
    ∃ recurring avoiding : ℕ → List Bool,
      FirstPassageSchedule recurring ∧
      FirstPassageSchedule avoiding ∧
      AgreeBelow N recurring avoiding ∧
      InfinitelyOftenEq writerWord recurring ∧
      EventuallyAvoidsEq writerWord avoiding := by
  let base : ℕ → List Bool := fun _ => [true]
  let recurring := forceTail base N writerWord
  let avoiding := forceTail base N [true]
  have hbase : FirstPassageSchedule base :=
    fun _ => singleton_true_firstPassage
  refine ⟨recurring, avoiding,
    firstPassageSchedule_forceTail base N writerWord hbase
      writerWord_firstPassage,
    firstPassageSchedule_forceTail base N [true] hbase
      singleton_true_firstPassage,
    forceTail_agreeBelow base N writerWord [true],
    forceTail_infinitelyOften base N writerWord, ?_⟩
  exact forceTail_eventuallyAvoids base N writerWord_ne_singleton_true.symm

/-- No finite prefix decides infinite recurrence of the concrete writer word,
even after restricting to schedules made entirely of valid first-passage
words. -/
theorem no_finite_prefix_decides_writerWord_recurrence (N : ℕ) :
    ¬PrefixDecidesOn FirstPassageSchedule N
      (InfinitelyOftenEq writerWord) := by
  intro hdecides
  obtain ⟨recurring, avoiding, hrecurringValid, havoidingValid,
      hsame, hrecurring, havoiding⟩ :=
    exists_firstPassageSchedules_same_prefix_opposite_writerRecurrence N
  exact havoiding.not_infinitelyOften
    ((hdecides recurring avoiding hrecurringValid havoidingValid hsame).mp
      hrecurring)

end OutwardFinitePrefixTailNoGo
end KontoroC
