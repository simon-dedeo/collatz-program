/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Syracuse

/-!
# Syracuse predecessor counts

This file fixes the counting function which occurs in the
Krasikov--Lagarias conclusion.  The definition is intentionally stated using
the actual Syracuse iterate on positive natural numbers, so later transfer
theorems cannot silently prove a statement about a surrogate graph.
-/

namespace CleanLean.Collatz

/-- `n` is a predecessor of `a` in the transitive Syracuse graph. -/
def IsSyracusePredecessor (a n : ℕ) : Prop :=
  ∃ j : ℕ, syracuseStep^[j] n = a

/-- The finite set of positive Syracuse predecessors of `a` not exceeding
`X`. -/
noncomputable def predecessorFinset (a X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n => IsSyracusePredecessor a n

/-- The number of positive Syracuse predecessors of `a` not exceeding `X`.

This is noncomputable only because reachability through an unbounded number of
steps is not known to be decidable.  Every counted set is nevertheless a
finite subset of `Finset.Icc 1 X`.
-/
noncomputable def predecessorCount (a X : ℕ) : ℕ :=
  (predecessorFinset a X).card

theorem predecessorCount_eq_card (a X : ℕ) :
    predecessorCount a X = (predecessorFinset a X).card := rfl

theorem mem_predecessors_iff {a X n : ℕ} :
    n ∈ predecessorFinset a X ↔
      1 ≤ n ∧ n ≤ X ∧ ∃ j : ℕ, syracuseStep^[j] n = a := by
  classical
  rw [predecessorFinset, Finset.mem_filter]
  rw [Finset.mem_Icc]
  change ((1 ≤ n ∧ n ≤ X) ∧ IsSyracusePredecessor a n) ↔ _
  simp only [IsSyracusePredecessor]
  tauto

/-- The exact asymptotic conclusion sought from the infinite KL ladder.

It is deliberately kept separate from `Collatz.Conjecture`: almost-linear
predecessor counting is a strong counting theorem, but it does not assert
that every positive integer is a predecessor of `1`.
-/
def AlmostLinearPredecessorCounting : Prop :=
  ∀ a : ℕ, 0 < a → a % 3 ≠ 0 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ^ (1 - ε) ≤ (predecessorCount a X : ℝ)

end CleanLean.Collatz
