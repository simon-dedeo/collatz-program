/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CycleCertificate

/-!
# A sound endpoint for parametric Collatz gliders

A glider supplies infinitely many positive odd macro-states, a nonempty exact
valuation word from each state to the next, and strict outward growth.  The
theorem below expands the variable-length macrosteps into ordinary Collatz
time and concludes the literal negation of the standard conjecture.
-/

namespace KontoroC

open CleanLean.Collatz

structure MacroGlider where
  state : ℕ → ℕ
  word : ℕ → List ℕ
  start_large : 4 < state 0
  word_nonempty : ∀ t, word t ≠ []
  legal : ∀ t, WordLegal (state t) (word t)
  transition : ∀ t, runWord (state t) (word t) = state (t + 1)
  grows : ∀ t, state t < state (t + 1)

namespace MacroGlider

/-- Accumulated ordinary Collatz time through `t` macrosteps. -/
def time (g : MacroGlider) : ℕ → ℕ
  | 0 => 0
  | t + 1 => ordinaryDuration (g.word t) + g.time t

@[simp] theorem time_zero (g : MacroGlider) : g.time 0 = 0 := rfl

@[simp] theorem time_succ (g : MacroGlider) (t : ℕ) :
    g.time (t + 1) = ordinaryDuration (g.word t) + g.time t := rfl

theorem duration_pos (g : MacroGlider) (t : ℕ) :
    0 < ordinaryDuration (g.word t) :=
  ordinaryDuration_pos_of_ne_nil (g.word_nonempty t)

theorem index_le_time (g : MacroGlider) (t : ℕ) : t ≤ g.time t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [time_succ]
      have hdur := g.duration_pos t
      omega

theorem start_le_state (g : MacroGlider) (t : ℕ) : g.state 0 ≤ g.state t := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih => exact ih.trans (Nat.le_of_lt (g.grows t))

/-- Every macro-state is the corresponding ordinary Collatz iterate. -/
theorem step_iterate_time (g : MacroGlider) (t : ℕ) :
    step^[g.time t] (g.state 0) = g.state t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [time_succ, Function.iterate_add_apply, ih,
        step_iterate_ordinaryDuration (g.legal t), g.transition t]

/-- End-to-end glider soundness. -/
theorem not_conjecture (g : MacroGlider) : ¬Conjecture := by
  intro hconj
  have hstart : 0 < g.state 0 :=
    lt_trans (by omega) g.start_large
  obtain ⟨j, hj⟩ := hconj (g.state 0) hstart
  let t := j + 1
  have hjtime : j ≤ g.time t :=
    le_trans (by simp [t]) (g.index_le_time t)
  have hdecomp : g.time t = (g.time t - j) + j := by omega
  have hmacro := g.step_iterate_time t
  rw [hdecomp, Function.iterate_add_apply, hj] at hmacro
  have hlarge : 4 < g.state t :=
    lt_of_lt_of_le g.start_large (g.start_le_state t)
  rcases step_iterate_one (g.time t - j) with h | h | h
  · rw [h] at hmacro
    omega
  · rw [h] at hmacro
    omega
  · rw [h] at hmacro
    omega

end MacroGlider

end KontoroC
