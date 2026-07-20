/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Defs

/-!
# A relational specification of Collatz iteration

This supplies an independently shaped specification and proves that it is
equivalent to the functional one in `Defs`.  The equivalence is part of the
project's defence against stating the wrong conjecture.
-/

namespace CleanLean.Collatz

/-- One Collatz step, expressed as a relation rather than by calling `step`. -/
def StepRel (n m : ℕ) : Prop :=
  (n % 2 = 0 ∧ m = n / 2) ∨ (n % 2 ≠ 0 ∧ m = 3 * n + 1)

theorem stepRel_iff {n m : ℕ} : StepRel n m ↔ step n = m := by
  by_cases h : n % 2 = 0 <;> simp [StepRel, step, h, eq_comm]

/-- Exactly `k` applications of the relational Collatz step. -/
inductive Steps : ℕ → ℕ → ℕ → Prop
  | zero (n : ℕ) : Steps 0 n n
  | succ {k n m z : ℕ} : StepRel n m → Steps k m z → Steps (k + 1) n z

theorem steps_iff_iterate {k n m : ℕ} : Steps k n m ↔ step^[k] n = m := by
  constructor
  · intro h
    induction h with
    | zero => rfl
    | succ hnm _ ih =>
        rw [Function.iterate_succ_apply, (stepRel_iff.mp hnm), ih]
  · induction k generalizing n with
    | zero =>
        intro h
        have hnm : n = m := by simpa using h
        subst m
        exact Steps.zero n
    | succ k ih =>
        intro h
        apply Steps.succ (stepRel_iff.mpr rfl)
        apply ih
        simpa [Function.iterate_succ_apply] using h

/-- Relational version of the assertion that `n` reaches `1`. -/
def RelationallyReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, Steps k n 1

/-- Relational version of the Collatz conjecture. -/
def RelationalConjecture : Prop :=
  ∀ n : ℕ, 0 < n → RelationallyReachesOne n

theorem reachesOne_iff_relational {n : ℕ} :
    ReachesOne n ↔ RelationallyReachesOne n := by
  simp only [ReachesOne, RelationallyReachesOne]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, steps_iff_iterate.mpr hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, steps_iff_iterate.mp hk⟩

theorem conjecture_iff_relational : Conjecture ↔ RelationalConjecture := by
  constructor <;> intro h n hn
  · exact reachesOne_iff_relational.mp (h n hn)
  · exact reachesOne_iff_relational.mpr (h n hn)

end CleanLean.Collatz
