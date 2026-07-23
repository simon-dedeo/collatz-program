/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCodeCompactness
import CleanLean.Collatz.Syracuse

/-!
# An infinite outward code execution would refute Collatz

The compactness theorem in `OutwardCodeCompactness` produces one ordinary
natural which realizes every finite block depth.  This file proves that no
additional infinite-choice construction is needed: if every codeword is
outward, that finite-depth property already makes the starting natural a
counterexample to the Syracuse, and hence standard, Collatz conjecture.
-/

namespace KontoroC
namespace OutwardCodeCounterexample

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
open CleanLean.Collatz

/-- The relational parity-word semantics is exactly iteration of the
one-halving Syracuse map. -/
theorem executes_eq_syracuse_iterate (w : List Bool) {start finish : ℕ}
    (h : Executes w start finish) :
    finish = syracuseStep^[w.length] start := by
  induction w generalizing start with
  | nil => simpa [Executes] using h
  | cons odd w ih =>
      obtain ⟨middle, hstep, htail⟩ := h
      have hs : syracuseStep start = middle := by
        cases odd with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hstep
            have heven : start % 2 = 0 := by omega
            simp only [syracuseStep, heven, ↓reduceIte]
            omega
        | true =>
            simp only [↓reduceIte] at hstep
            have hodd : start % 2 ≠ 0 := by omega
            simp only [syracuseStep, hodd, ↓reduceIte]
            omega
      calc
        finish = syracuseStep^[w.length] middle := ih htail
        _ = syracuseStep^[w.length] (syracuseStep start) := by rw [hs]
        _ = syracuseStep^[(odd :: w).length] start := by
          rw [List.length_cons, Function.iterate_succ_apply]

/-- Every outward parity block strictly increases a positive natural at its
boundary.  This is a consequence of the exact affine execution identity,
not a heuristic comparison of logarithmic slopes. -/
theorem executes_lt_of_outward {w : List Bool} {start finish : ℕ}
    (hstart : 0 < start) (hout : WordOutward w)
    (hexec : Executes w start finish) :
    start < finish := by
  have hexact := program_exact w hexec
  rw [programData_S, programData_O] at hexact
  have hscaled : 2 ^ w.length * start < 3 ^ w.count true * start :=
    (Nat.mul_lt_mul_right hstart).2 hout
  have hle : 3 ^ w.count true * start ≤ 2 ^ w.length * finish := by
    rw [hexact]
    omega
  have hmul : 2 ^ w.length * start < 2 ^ w.length * finish :=
    hscaled.trans_le hle
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ w.length)).1 hmul

/-- A list of outward blocks raises its final boundary by at least its number
of blocks.  The theorem also exposes the flattened parity-word execution. -/
theorem executesBlocks_growth {C : Set (List Bool)}
    (hout : ∀ w ∈ C, WordOutward w)
    {ws : List (List Bool)} {start : ℕ}
    (hstart : 0 < start) (hwords : WordsIn C ws)
    (hexec : ExecutesBlocks ws start) :
    ∃ finish,
      Executes (flattenWords ws) start finish ∧ start + ws.length ≤ finish := by
  induction ws generalizing start with
  | nil =>
      exact ⟨start, by simp [flattenWords, Executes], by simp⟩
  | cons w ws ih =>
      obtain ⟨middle, hw, hrest⟩ := hexec
      have hwC : w ∈ C := hwords w (by simp)
      have hlt : start < middle := executes_lt_of_outward hstart (hout w hwC) hw
      have htailWords : WordsIn C ws := by
        intro v hv
        exact hwords v (by simp [hv])
      obtain ⟨finish, hflat, hgrowth⟩ :=
        ih (hstart.trans hlt) (by exact htailWords) hrest
      refine ⟨finish, ?_, ?_⟩
      · simp only [flattenWords]
        exact (OutwardCodeCompactness.executes_append w _).2
          ⟨middle, hw, hflat⟩
      · simp only [List.length_cons]
        omega

/-- An outward word is nonempty. -/
theorem wordOutward_ne_nil {w : List Bool} (hout : WordOutward w) : w ≠ [] := by
  intro hw
  subst w
  norm_num [WordOutward] at hout

/-- Flattening `n` outward codewords uses at least `n` Syracuse steps. -/
theorem length_le_flattenWords_length {C : Set (List Bool)}
    (hout : ∀ w ∈ C, WordOutward w)
    {ws : List (List Bool)} (hwords : WordsIn C ws) :
    ws.length ≤ (flattenWords ws).length := by
  induction ws with
  | nil => simp [flattenWords]
  | cons w ws ih =>
      have hwC : w ∈ C := hwords w (by simp)
      have hwlen : 0 < w.length :=
        List.length_pos_iff.2 (wordOutward_ne_nil (hout w hwC))
      have htail : WordsIn C ws := by
        intro v hv
        exact hwords v (by simp [hv])
      simp only [List.length_cons, flattenWords, List.length_append]
      have htailLen := ih htail
      omega

theorem syracuseStep_le_two {n : ℕ} (hn : n ≤ 2) : syracuseStep n ≤ 2 := by
  interval_cases n <;> norm_num [syracuseStep]

theorem syracuse_iterate_one_le_two (j : ℕ) :
    syracuseStep^[j] 1 ≤ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_le_two ih

/-- Once a Syracuse orbit has reached one, all later values lie in the
terminal `{1,2}` cycle (the weaker upper bound is all that is needed below). -/
theorem syracuse_iterate_le_two_of_reachesOne {start k t : ℕ}
    (hreach : syracuseStep^[k] start = 1) (hkt : k ≤ t) :
    syracuseStep^[t] start ≤ 2 := by
  calc
    syracuseStep^[t] start =
        syracuseStep^[t - k] (syracuseStep^[k] start) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkt]
    _ = syracuseStep^[t - k] 1 := by rw [hreach]
    _ ≤ 2 := syracuse_iterate_one_le_two _

/-- The all-finite-depth execution supplied by finite-window compactness is
already a genuine Syracuse counterexample when every codeword is outward. -/
theorem not_syracuseReachesOne_of_infiniteExecution
    {C : Set (List Bool)}
    (hout : ∀ w ∈ C, WordOutward w)
    {start : ℕ} (hinfinite : InfiniteExecution C start) :
    ¬ SyracuseReachesOne start := by
  rintro ⟨k, hreach⟩
  obtain ⟨hstart, ws, hlen, hwords, hexec⟩ := hinfinite (k + 2)
  obtain ⟨finish, hflat, hgrowth⟩ :=
    executesBlocks_growth hout hstart hwords hexec
  have htime : k ≤ (flattenWords ws).length := by
    have hn := length_le_flattenWords_length hout hwords
    omega
  have hfinish : finish = syracuseStep^[(flattenWords ws).length] start :=
    executes_eq_syracuse_iterate _ hflat
  have hterminal : finish ≤ 2 := by
    rw [hfinish]
    exact syracuse_iterate_le_two_of_reachesOne hreach htime
  omega

/-- Any ordinary infinite execution through an outward code refutes the
standard unaccelerated Collatz conjecture. -/
theorem not_conjecture_of_infiniteExecution
    {C : Set (List Bool)}
    (hout : ∀ w ∈ C, WordOutward w)
    {start : ℕ} (hinfinite : InfiniteExecution C start) :
    ¬ Conjecture := by
  intro hcollatz
  have hsyracuse : SyracuseReachesOne start :=
    conjecture_iff_syracuse.mp hcollatz start (hinfinite 0).1
  exact not_syracuseReachesOne_of_infiniteExecution hout hinfinite hsyracuse

/-- The exact endpoint promised in QM155d: bounded canonical minima for any
nonempty outward code would refute Collatz. -/
theorem not_conjecture_of_bounded_canonicalMinimum
    {C : Set (List Bool)} (hC : C.Nonempty)
    (hout : ∀ w ∈ C, WordOutward w)
    (hbounded : BoundedRange (canonicalMinimumStart C hC)) :
    ¬ Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    (infiniteExecution_iff_bounded_canonicalMinimum C hC).2 hbounded
  exact not_conjecture_of_infiniteExecution hout hinfinite

end OutwardCodeCounterexample
end KontoroC
