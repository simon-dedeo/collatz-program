/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardIteratedKraftGap
import KontoroC.OutwardFiniteHeight
import KontoroC.OutwardCodeCounterexample

/-!
# From finite residue cylinders to an ordinary first-passage seed

The iterated Kraft theorems count Boolean residue cylinders.  This file
supplies their literal semantic bridge: the canonical ordinary source of a
word in a covered cylinder executes the selected first-passage block
schedule.  At positive macro depth that source is positive.

Consequently, if every finite depth has a covered word whose canonical source
lies in one fixed natural window, finite-window compactness produces one
ordinary source valid at every depth.  The existing outward-code theorem then
gives the Syracuse and Collatz counterexample conclusions.

No bounded family of canonical sources is constructed here.
-/

namespace KontoroC
namespace OutwardResidueOrdinaryBridge

open ShortcutParityPeriodicNoGo OutwardFirstPassage OutwardCodeCompactness
  OutwardCodeCounterexample OutwardOddSlice OutwardFiniteHeight
  OutwardCylinderRenewal
  OutwardStrictKraftGap OutwardIteratedKraftGap
  OutwardFiniteStateKraftGap.FirstPassageGrammar
open CleanLean.Collatz

/-- A literal first-passage word cannot execute from source zero. -/
theorem source_pos_of_executes_firstPassage
    {w : List Bool} {source target : ℕ}
    (hfirst : FirstPassage w) (hexec : Executes w source target) :
    0 < source := by
  by_contra hnot
  have hzero : source = 0 := by omega
  have hcount := executes_zero_count_true_eq_zero (hzero ▸ hexec)
  have hout := hfirst.1
  simp only [WordOutward, hcount, pow_zero] at hout
  have hpow : 0 < 2 ^ w.length := by positivity
  omega

/-- Any nonempty list of first-passage blocks which executes literally has a
positive source. -/
theorem source_pos_of_executesBlocks_firstPassage
    {words : List (List Bool)} {source : ℕ}
    (hne : words ≠ [])
    (hwords : WordsIn FirstPassageCode words)
    (hexec : ExecutesBlocks words source) :
    0 < source := by
  cases words with
  | nil => exact (hne rfl).elim
  | cons w words =>
      obtain ⟨middle, hwexec, _⟩ := hexec
      have hwfirst : FirstPassage w := by
        simpa [FirstPassageCode] using hwords w (by simp)
      exact source_pos_of_executes_firstPassage hwfirst hwexec

/-- The canonical ordinary source of a word in a selected residue cylinder
executes exactly the schedule labelling that cylinder. -/
theorem canonicalSource_realizesDepth_of_mem_coveredAtDepth
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (hn : 0 < n)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    {z : List Bool}
    (hz : z ∈ coveredAtDepth (flattenedSchedules schedules) L) :
    RealizesDepth FirstPassageCode n (canonicalExecution z).1 := by
  rcases Finset.mem_biUnion.mp hz with ⟨pref, hpref, hzext⟩
  rcases mem_flattenedSchedules_iff.mp hpref with
    ⟨words, hwordsMem, hflatten⟩
  rcases Finset.mem_image.mp hzext with ⟨tail, _, hztail⟩
  have hcanonical : Executes z (canonicalExecution z).1
      (canonicalExecution z).2 := (canonicalExecution_spec z).2.2
  have hfull : Executes (pref ++ tail) (canonicalExecution z).1
      (canonicalExecution z).2 := by
    simpa [hztail] using hcanonical
  obtain ⟨middle, hpExec, _⟩ := (executes_append pref tail).mp hfull
  have hflatExec : Executes (flattenWords words) (canonicalExecution z).1
      middle := by
    simpa [hflatten] using hpExec
  have hblocks : ExecutesBlocks words (canonicalExecution z).1 :=
    (executesBlocks_iff words (canonicalExecution z).1).mpr
      ⟨middle, hflatExec⟩
  have hne : words ≠ [] := by
    intro heq
    have := hmacroLength words hwordsMem
    simp [heq] at this
    omega
  exact ⟨source_pos_of_executesBlocks_firstPassage hne
      (hwords words hwordsMem) hblocks,
    words, hmacroLength words hwordsMem,
    hwords words hwordsMem, hblocks⟩

/-- Bounded canonical residue representatives at every positive macro depth
produce one ordinary source with an infinite literal first-passage
execution.  The finite schedule family and residue precision may vary with
depth. -/
theorem exists_infiniteExecution_of_bounded_covered_canonicalSources
    (schedules : ℕ → Finset (List (List Bool)))
    (level : ℕ → ℕ) (B : ℕ)
    (hwords : ∀ depth words, words ∈ schedules depth →
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ depth words, words ∈ schedules depth →
      words.length = depth + 1)
    (hbounded : ∀ depth, ∃ z,
      z ∈ coveredAtDepth (flattenedSchedules (schedules depth))
        (level depth) ∧
      (canonicalExecution z).1 ≤ B) :
    ∃ start, InfiniteExecution FirstPassageCode start := by
  have hwindow : ∀ depth, ∃ start, start ≤ B ∧
      RealizesDepth FirstPassageCode depth start := by
    intro depth
    obtain ⟨z, hz, hzB⟩ := hbounded depth
    have hnext := canonicalSource_realizesDepth_of_mem_coveredAtDepth
      (schedules depth) (depth + 1) (level depth) (by omega)
      (hwords depth) (hmacroLength depth) hz
    exact ⟨(canonicalExecution z).1, hzB,
      realizesDepth_nested FirstPassageCode depth _ hnext⟩
  obtain ⟨start, _, hinfinite⟩ := finiteWindow_nested
    (RealizesDepth FirstPassageCode)
    (realizesDepth_nested FirstPassageCode) B hwindow
  exact ⟨start, hinfinite⟩

/-- Explicit Syracuse endpoint of the bounded canonical-residue criterion. -/
theorem exists_not_syracuseReachesOne_of_bounded_covered_canonicalSources
    (schedules : ℕ → Finset (List (List Bool)))
    (level : ℕ → ℕ) (B : ℕ)
    (hwords : ∀ depth words, words ∈ schedules depth →
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ depth words, words ∈ schedules depth →
      words.length = depth + 1)
    (hbounded : ∀ depth, ∃ z,
      z ∈ coveredAtDepth (flattenedSchedules (schedules depth))
        (level depth) ∧
      (canonicalExecution z).1 ≤ B) :
    ∃ start, ¬ SyracuseReachesOne start := by
  obtain ⟨start, hinfinite⟩ :=
    exists_infiniteExecution_of_bounded_covered_canonicalSources
      schedules level B hwords hmacroLength hbounded
  exact ⟨start, not_syracuseReachesOne_of_infiniteExecution
    (C := FirstPassageCode)
    (fun w hw => firstPassage_outward
      (by simpa [FirstPassageCode] using hw)) hinfinite⟩

/-- Standard unaccelerated Collatz endpoint of the bounded canonical-residue
criterion. -/
theorem not_collatz_of_bounded_covered_canonicalSources
    (schedules : ℕ → Finset (List (List Bool)))
    (level : ℕ → ℕ) (B : ℕ)
    (hwords : ∀ depth words, words ∈ schedules depth →
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ depth words, words ∈ schedules depth →
      words.length = depth + 1)
    (hbounded : ∀ depth, ∃ z,
      z ∈ coveredAtDepth (flattenedSchedules (schedules depth))
        (level depth) ∧
      (canonicalExecution z).1 ≤ B) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    exists_infiniteExecution_of_bounded_covered_canonicalSources
      schedules level B hwords hmacroLength hbounded
  exact not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
    (fun w hw => firstPassage_outward
      (by simpa [FirstPassageCode] using hw)) hinfinite

end OutwardResidueOrdinaryBridge
end KontoroC
