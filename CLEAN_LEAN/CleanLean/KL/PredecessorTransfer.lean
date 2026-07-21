/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.PredecessorCount

/-!
# Bounded predecessor sets for the KL counting transfer

Krasikov--Lagarias use predecessors whose entire path to the target stays
below the counting cutoff.  This file defines that literal object in terms of
the actual Syracuse iterate.  It is kept separate from the residue infimum so
the targetwise combinatorics can be audited first.
-/

namespace CleanLean.KL

open CleanLean.Collatz

/-- A positive predecessor whose witnessed Syracuse path to `a` stays in the
closed interval `[1,X]`. -/
def IsBoundedSyracusePredecessor (a X n : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ X ∧ ∃ j : ℕ,
    syracuseStep^[j] n = a ∧
      ∀ i : ℕ, i ≤ j → syracuseStep^[i] n ≤ X

/-- The finite bounded-predecessor set denoted `P*_a(X)` in the transfer
argument. -/
noncomputable def boundedPredecessorFinset (a X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n =>
    ∃ j : ℕ, syracuseStep^[j] n = a ∧
      ∀ i : ℕ, i ≤ j → syracuseStep^[i] n ≤ X

/-- Cardinality of `P*_a(X)`. -/
noncomputable def boundedPredecessorCount (a X : ℕ) : ℕ :=
  (boundedPredecessorFinset a X).card

theorem mem_boundedPredecessors_iff {a X n : ℕ} :
    n ∈ boundedPredecessorFinset a X ↔
      IsBoundedSyracusePredecessor a X n := by
  classical
  simp only [boundedPredecessorFinset, Finset.mem_filter,
    Finset.mem_Icc, IsBoundedSyracusePredecessor]
  tauto

/-- Bounded predecessors are ordinary predecessors. -/
theorem boundedPredecessorFinset_subset (a X : ℕ) :
    boundedPredecessorFinset a X ⊆ predecessorFinset a X := by
  intro n hn
  rw [mem_boundedPredecessors_iff] at hn
  rw [mem_predecessors_iff]
  exact ⟨hn.1, hn.2.1, hn.2.2.choose,
    hn.2.2.choose_spec.1⟩

theorem boundedPredecessorCount_le_predecessorCount (a X : ℕ) :
    boundedPredecessorCount a X ≤ predecessorCount a X := by
  exact Finset.card_le_card (boundedPredecessorFinset_subset a X)

/-- The target itself is always a bounded predecessor when it lies below the
cutoff. -/
theorem self_mem_boundedPredecessors {a X : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) :
    a ∈ boundedPredecessorFinset a X := by
  rw [mem_boundedPredecessors_iff]
  refine ⟨ha, haX, 0, rfl, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  simpa using haX

/-- Raising the cutoff preserves every bounded predecessor witness. -/
theorem boundedPredecessorFinset_mono {a X Y : ℕ} (hXY : X ≤ Y) :
    boundedPredecessorFinset a X ⊆ boundedPredecessorFinset a Y := by
  intro n hn
  rw [mem_boundedPredecessors_iff] at hn ⊢
  refine ⟨hn.1, hn.2.1.trans hXY, hn.2.2.choose,
    hn.2.2.choose_spec.1, ?_⟩
  intro i hi
  exact (hn.2.2.choose_spec.2 i hi).trans hXY

theorem boundedPredecessorCount_mono {a X Y : ℕ} (hXY : X ≤ Y) :
    boundedPredecessorCount a X ≤ boundedPredecessorCount a Y := by
  exact Finset.card_le_card (boundedPredecessorFinset_mono hXY)

/-- A target lies on a positive Syracuse cycle. -/
def IsSyracusePeriodic (a : ℕ) : Prop :=
  ∃ j : ℕ, 0 < j ∧ syracuseStep^[j] a = a

/-- If `a = 1 (mod 3)`, its only positive immediate Syracuse predecessor is
`2a`.  The odd inverse branch exists only for targets `2 (mod 3)`. -/
theorem syracuseStep_eq_target_mod_three_one
    {a n : ℕ} (ha3 : a % 3 = 1) :
    syracuseStep n = a ↔ n = 2 * a := by
  constructor
  · intro hstep
    by_cases heven : n % 2 = 0
    · rw [syracuseStep, if_pos heven] at hstep
      omega
    · have hnodd : n % 2 = 1 := odd_remainder heven
      have himageEven : (3 * n + 1) % 2 = 0 := odd_image_even heven
      rw [syracuseStep, if_neg heven] at hstep
      have heq : 3 * n + 1 = 2 * a := by omega
      omega
  · rintro rfl
    simp [syracuseStep]

/-- A nontrivial bounded path to a `1 (mod 3)` target reaches `2a` on its
penultimate step. -/
theorem boundedPredecessor_of_succ_to_mod_three_one
    {a X n j : ℕ} (ha3 : a % 3 = 1)
    (hn : 1 ≤ n) (hnX : n ≤ X)
    (hreach : syracuseStep^[j + 1] n = a)
    (hbounded : ∀ i : ℕ, i ≤ j + 1 → syracuseStep^[i] n ≤ X) :
    IsBoundedSyracusePredecessor (2 * a) X n := by
  have hlast : syracuseStep (syracuseStep^[j] n) = a := by
    simpa [Function.iterate_succ_apply'] using hreach
  have hdouble : syracuseStep^[j] n = 2 * a :=
    (syracuseStep_eq_target_mod_three_one ha3).mp hlast
  exact ⟨hn, hnX, j, hdouble, fun i hi => hbounded i (by omega)⟩

/-- Appending the halving edge `2a -> a` preserves boundedness when `2a` is
below the cutoff. -/
theorem boundedPredecessor_to_double_of_target
    {a X n : ℕ} (h2aX : 2 * a ≤ X)
    (hn : IsBoundedSyracusePredecessor (2 * a) X n) :
    IsBoundedSyracusePredecessor a X n := by
  obtain ⟨hnpos, hnX, j, hreach, hbounded⟩ := hn
  refine ⟨hnpos, hnX, j + 1, ?_, ?_⟩
  · rw [Function.iterate_succ_apply', hreach]
    simp [syracuseStep]
  · intro i hi
    by_cases hij : i ≤ j
    · exact hbounded i hij
    · have hiEq : i = j + 1 := by omega
      subst i
      rw [Function.iterate_succ_apply', hreach]
      have hstep : syracuseStep (2 * a) = a := by
        simp [syracuseStep]
      rw [hstep]
      exact (Nat.le_mul_of_pos_left a (by norm_num)).trans h2aX

/-- Correct targetwise replacement for the false printed KL equation (2.1):
the bounded predecessors of `a = 1 (mod 3)` are exactly `a` itself together
with the bounded predecessors of `2a`. -/
theorem boundedPredecessorFinset_eq_insert_double
    {a X : ℕ} (ha : 1 ≤ a) (ha3 : a % 3 = 1) (h2aX : 2 * a ≤ X) :
    boundedPredecessorFinset a X =
      insert a (boundedPredecessorFinset (2 * a) X) := by
  classical
  ext n
  rw [Finset.mem_insert, mem_boundedPredecessors_iff,
    mem_boundedPredecessors_iff]
  constructor
  · rintro ⟨hnpos, hnX, j, hreach, hbounded⟩
    cases j with
    | zero =>
        left
        simpa using hreach
    | succ j =>
        right
        exact boundedPredecessor_of_succ_to_mod_three_one ha3
          hnpos hnX (by simpa using hreach) (by simpa using hbounded)
  · rintro (hnEq | hn)
    · subst n
      exact (mem_boundedPredecessors_iff.mp
        (self_mem_boundedPredecessors ha
          ((Nat.le_mul_of_pos_left a (by norm_num)).trans h2aX)))
    · exact boundedPredecessor_to_double_of_target h2aX hn

/-- Nonperiodicity makes the union in the targetwise doubling decomposition
disjoint. -/
theorem self_not_mem_boundedPredecessors_double
    {a X : ℕ} (haNonperiodic : ¬ IsSyracusePeriodic a) :
    a ∉ boundedPredecessorFinset (2 * a) X := by
  intro hmem
  rw [mem_boundedPredecessors_iff] at hmem
  obtain ⟨_, _, j, hreach, _⟩ := hmem
  apply haNonperiodic
  refine ⟨j + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', hreach]
  simp [syracuseStep]

/-- Cardinal form of the corrected targetwise identity. -/
theorem boundedPredecessorCount_eq_succ_double
    {a X : ℕ} (ha : 1 ≤ a) (ha3 : a % 3 = 1)
    (haNonperiodic : ¬ IsSyracusePeriodic a) (h2aX : 2 * a ≤ X) :
    boundedPredecessorCount a X =
      boundedPredecessorCount (2 * a) X + 1 := by
  rw [boundedPredecessorCount,
    boundedPredecessorFinset_eq_insert_double ha ha3 h2aX,
    Finset.card_insert_of_notMem
      (self_not_mem_boundedPredecessors_double haNonperiodic),
    boundedPredecessorCount]

/-- Reachability of targets reverses inclusion of their ordinary predecessor
sets: if `b` reaches `a`, every predecessor of `b` is a predecessor of `a`. -/
theorem predecessorFinset_subset_of_target_reaches
    {a b X : ℕ} (hba : IsSyracusePredecessor a b) :
    predecessorFinset b X ⊆ predecessorFinset a X := by
  intro n hn
  rw [mem_predecessors_iff] at hn ⊢
  obtain ⟨hnpos, hnX, j, hj⟩ := hn
  obtain ⟨r, hr⟩ := hba
  refine ⟨hnpos, hnX, r + j, ?_⟩
  rw [Function.iterate_add_apply, hj, hr]

theorem predecessorCount_mono_of_target_reaches
    {a b X : ℕ} (hba : IsSyracusePredecessor a b) :
    predecessorCount b X ≤ predecessorCount a X := by
  exact Finset.card_le_card (predecessorFinset_subset_of_target_reaches hba)

/-- Repeated halving sends `2^r*a` to `a` in exactly `r` Syracuse steps. -/
theorem iterate_syracuse_two_pow_mul (a r : ℕ) :
    syracuseStep^[r] (2 ^ r * a) = a := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      have hstep : syracuseStep (2 ^ (r + 1) * a) = 2 ^ r * a := by
        have heq : 2 ^ (r + 1) * a = 2 * (2 ^ r * a) := by
          rw [pow_succ]
          ring
        rw [heq]
        simp [syracuseStep]
      rw [hstep]
      exact ih

/-- Hence predecessor counting at any doubled target is bounded by counting
at the original target. -/
theorem predecessorCount_two_pow_mul_le (a r X : ℕ) :
    predecessorCount (2 ^ r * a) X ≤ predecessorCount a X := by
  apply predecessorCount_mono_of_target_reaches
  exact ⟨r, iterate_syracuse_two_pow_mul a r⟩

end CleanLean.KL
