/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# The standard Collatz conjecture

This file fixes the project's top-level specification.  The map is the
unaccelerated map on natural numbers: even inputs are halved and odd inputs
are sent to `3 * n + 1`.
-/

namespace CleanLean.Collatz

/-- The unaccelerated Collatz map on natural numbers. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The orbit of `n` under `step` eventually visits `1`. -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, step^[k] n = 1

/-- The usual Collatz conjecture, restricted to positive natural numbers. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ReachesOne n

@[simp] theorem step_zero : step 0 = 0 := by
  simp [step]

@[simp] theorem step_one : step 1 = 4 := by
  norm_num [step]

@[simp] theorem step_two : step 2 = 1 := by
  norm_num [step]

@[simp] theorem step_four : step 4 = 2 := by
  norm_num [step]

theorem step_of_even {n : ℕ} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem step_of_odd {n : ℕ} (h : n % 2 ≠ 0) : step n = 3 * n + 1 := by
  simp [step, h]

theorem step_pos {n : ℕ} (h : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

theorem iterate_pos (k : ℕ) {n : ℕ} (h : 0 < n) : 0 < step^[k] n := by
  induction k generalizing n with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih (step_pos h)

theorem iterate_zero (k : ℕ) : step^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, step_zero, ih]

theorem not_reachesOne_zero : ¬ ReachesOne 0 := by
  rintro ⟨k, hk⟩
  have hz := iterate_zero k
  omega

/-- Reaching `1` after a later segment of an orbit implies reaching it from
the beginning of that orbit. -/
theorem reachesOne_of_iterate {n k : ℕ} (h : ReachesOne (step^[k] n)) :
    ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [Function.iterate_add_apply]; exact hj⟩

/-- The familiar descent formulation is sufficient for the conjecture. -/
theorem conjecture_of_descent
    (h : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, step^[k] n < n) : Conjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hn2 : n < 2
      · have : n = 1 := by omega
        exact ⟨0, this⟩
      · obtain ⟨k, hk⟩ := h n (by omega)
        exact reachesOne_of_iterate (ih _ hk (iterate_pos k hn))

end CleanLean.Collatz
