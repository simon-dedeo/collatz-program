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

/-- Path-bounded Syracuse predecessors are unbounded Syracuse predecessors. -/
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

/-- Append a bounded path from one target to another. -/
theorem boundedPredecessor_of_target_path
    {a b X n r : ℕ}
    (hreach : syracuseStep^[r] b = a)
    (hpath : ∀ i : ℕ, i ≤ r → syracuseStep^[i] b ≤ X)
    (hn : IsBoundedSyracusePredecessor b X n) :
    IsBoundedSyracusePredecessor a X n := by
  obtain ⟨hnpos, hnX, j, hj, hjbound⟩ := hn
  refine ⟨hnpos, hnX, r + j, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hj, hreach]
  · intro i hi
    by_cases hij : i ≤ j
    · exact hjbound i hij
    · have hji : j ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hij)
      have hdiff : i - j ≤ r := by omega
      calc
        syracuseStep^[i] n =
            syracuseStep^[i - j] (syracuseStep^[j] n) := by
              rw [← Function.iterate_add_apply,
                Nat.sub_add_cancel hji]
        _ = syracuseStep^[i - j] b := by rw [hj]
        _ ≤ X := hpath (i - j) hdiff

theorem boundedPredecessorFinset_subset_of_target_path
    {a b X r : ℕ}
    (hreach : syracuseStep^[r] b = a)
    (hpath : ∀ i : ℕ, i ≤ r → syracuseStep^[i] b ≤ X) :
    boundedPredecessorFinset b X ⊆ boundedPredecessorFinset a X := by
  intro n hn
  rw [mem_boundedPredecessors_iff] at hn ⊢
  exact boundedPredecessor_of_target_path hreach hpath hn

/-- A target lies on a positive Syracuse cycle. -/
def IsSyracusePeriodic (a : ℕ) : Prop :=
  ∃ j : ℕ, 0 < j ∧ syracuseStep^[j] a = a

/-- Every forward iterate of a periodic point is periodic. -/
theorem periodic_iterate {b : ℕ} (hb : IsSyracusePeriodic b) (r : ℕ) :
    IsSyracusePeriodic (syracuseStep^[r] b) := by
  obtain ⟨p, hp, hperiod⟩ := hb
  refine ⟨p, hp, ?_⟩
  calc
    syracuseStep^[p] (syracuseStep^[r] b) =
        syracuseStep^[p + r] b := by
          rw [Function.iterate_add_apply]
    _ = syracuseStep^[r + p] b := by rw [Nat.add_comm]
    _ = syracuseStep^[r] (syracuseStep^[p] b) := by
          rw [Function.iterate_add_apply]
    _ = syracuseStep^[r] b := by rw [hperiod]

/-- A periodic target cannot reach a nonperiodic target. -/
theorem nonperiodic_of_target_reaches
    {a b : ℕ} (ha : ¬ IsSyracusePeriodic a)
    (hba : IsSyracusePredecessor a b) :
    ¬ IsSyracusePeriodic b := by
  intro hb
  obtain ⟨r, hr⟩ := hba
  exact ha (hr ▸ periodic_iterate hb r)

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

/-- Reachability of targets reverses inclusion of their Syracuse predecessor
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

theorem nonperiodic_two_pow_mul {a : ℕ}
    (ha : ¬ IsSyracusePeriodic a) (r : ℕ) :
    ¬ IsSyracusePeriodic (2 ^ r * a) := by
  apply nonperiodic_of_target_reaches ha
  exact ⟨r, iterate_syracuse_two_pow_mul a r⟩

/-- Arithmetic of the odd inverse branch of a `2 (mod 3)` target. -/
theorem three_mul_oddPredecessor {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    3 * ((2 * a - 1) / 3) = 2 * a - 1 := by
  have hmod : (2 * a - 1) % 3 = 0 := by
    have hdecomp := Nat.mod_add_div a 3
    omega
  omega

theorem oddPredecessor_mod_two {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    ((2 * a - 1) / 3) % 2 = 1 := by
  have hthree := three_mul_oddPredecessor ha ha3
  have hmodlt := Nat.mod_lt ((2 * a - 1) / 3) (by norm_num : 0 < 2)
  omega

theorem syracuseStep_oddPredecessor {a : ℕ} (ha : 0 < a)
    (ha3 : a % 3 = 2) :
    syracuseStep ((2 * a - 1) / 3) = a := by
  have hthree := three_mul_oddPredecessor ha ha3
  have hodd := oddPredecessor_mod_two ha ha3
  rw [syracuseStep, if_neg (by omega)]
  have hnum : 3 * ((2 * a - 1) / 3) + 1 = 2 * a := by omega
  rw [hnum]
  omega

/-- The reverse subtrees rooted at the two distinct incoming branches `4a`
and `(2a-1)/3` are disjoint when `a` is nonperiodic.  Any common predecessor
would place one branch target on the forward orbit of the other and hence
give a positive return to `a`. -/
theorem boundedPredecessorFinset_four_disjoint_oddPredecessor
    {a X Y : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2)
    (hanon : ¬ IsSyracusePeriodic a) :
    Disjoint (boundedPredecessorFinset (4 * a) X)
      (boundedPredecessorFinset ((2 * a - 1) / 3) Y) := by
  classical
  rw [Finset.disjoint_left]
  intro n hn4 hnc
  rw [mem_boundedPredecessors_iff] at hn4 hnc
  obtain ⟨_, _, j, hj, _⟩ := hn4
  obtain ⟨_, _, l, hl, _⟩ := hnc
  let c := (2 * a - 1) / 3
  have hcstep : syracuseStep c = a := syracuseStep_oddPredecessor ha ha3
  have h4one : syracuseStep^[1] (4 * a) = 2 * a := by
    convert iterate_syracuse_two_pow_mul (2 * a) 1 using 1 <;> norm_num <;> ring
  have h4two : syracuseStep^[2] (4 * a) = a := by
    simpa using iterate_syracuse_two_pow_mul a 2
  have hc_ne_four : c ≠ 4 * a := by
    intro heq
    have hthree := three_mul_oddPredecessor ha ha3
    dsimp [c] at heq
    omega
  have hc_ne_two : c ≠ 2 * a := by
    intro heq
    have hthree := three_mul_oddPredecessor ha ha3
    dsimp [c] at heq
    omega
  by_cases hjl : j ≤ l
  · let d := l - j
    have hdj : d + j = l := Nat.sub_add_cancel hjl
    have h4c : syracuseStep^[d] (4 * a) = c := by
      calc
        syracuseStep^[d] (4 * a) =
            syracuseStep^[d] (syracuseStep^[j] n) := by rw [hj]
        _ = syracuseStep^[d + j] n := by
          rw [Function.iterate_add_apply]
        _ = syracuseStep^[l] n := by rw [hdj]
        _ = c := hl
    by_cases hd0 : d = 0
    · rw [hd0] at h4c
      change 4 * a = c at h4c
      exact hc_ne_four h4c.symm
    by_cases hd1 : d = 1
    · rw [hd1] at h4c
      rw [h4one] at h4c
      exact hc_ne_two h4c.symm
    apply hanon
    refine ⟨d - 1, by omega, ?_⟩
    calc
      syracuseStep^[d - 1] a =
          syracuseStep^[d - 1] (syracuseStep^[2] (4 * a)) := by rw [h4two]
      _ = syracuseStep^[(d - 1) + 2] (4 * a) := by
        rw [Function.iterate_add_apply]
      _ = syracuseStep^[d + 1] (4 * a) := by congr 1 <;> omega
      _ = syracuseStep (syracuseStep^[d] (4 * a)) := by
        rw [Function.iterate_succ_apply']
      _ = a := by rw [h4c, hcstep]
  · have hlj : l ≤ j := (Nat.le_of_lt (Nat.lt_of_not_ge hjl))
    let d := j - l
    have hdl : d + l = j := Nat.sub_add_cancel hlj
    have hdc : syracuseStep^[d] c = 4 * a := by
      calc
        syracuseStep^[d] c =
            syracuseStep^[d] (syracuseStep^[l] n) := by rw [hl]
        _ = syracuseStep^[d + l] n := by
          rw [Function.iterate_add_apply]
        _ = syracuseStep^[j] n := by rw [hdl]
        _ = 4 * a := hj
    apply hanon
    refine ⟨d + 1, by omega, ?_⟩
    calc
      syracuseStep^[d + 1] a =
          syracuseStep^[d + 1] (syracuseStep c) := by rw [hcstep]
      _ = syracuseStep^[(d + 1) + 1] c := by
        simpa only [Function.iterate_one] using
          (Function.iterate_add_apply syracuseStep (d + 1) 1 c).symm
      _ = syracuseStep^[2] (syracuseStep^[d] c) := by
        rw [← Function.iterate_add_apply]
        congr 1 <;> omega
      _ = a := by rw [hdc, h4two]

/-- The entire bounded reverse subtree rooted at `4a` embeds in the subtree
rooted at `a`, provided the two halving steps stay below the cutoff. -/
theorem boundedPredecessorFinset_four_subset
    {a X : ℕ} (ha : 0 < a) (h4aX : 4 * a ≤ X) :
    boundedPredecessorFinset (4 * a) X ⊆
      boundedPredecessorFinset a X := by
  have h4one : syracuseStep^[1] (4 * a) = 2 * a := by
    convert iterate_syracuse_two_pow_mul (2 * a) 1 using 1 <;> norm_num <;> ring
  have h4two : syracuseStep^[2] (4 * a) = a := by
    simpa using iterate_syracuse_two_pow_mul a 2
  apply boundedPredecessorFinset_subset_of_target_path
    (r := 2) h4two
  intro i hi
  interval_cases i
  · simpa using h4aX
  · have h2a : 2 * a ≤ X := by omega
    rw [h4one]
    exact h2a
  · have haX : a ≤ X := by omega
    rw [h4two]
    exact haX

/-- The bounded odd-inverse subtree also embeds in the target subtree.  Its
own cutoff may be smaller than the target cutoff. -/
theorem boundedPredecessorFinset_oddPredecessor_subset
    {a X Y : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2)
    (hYX : Y ≤ X) (h4aX : 4 * a ≤ X) :
    boundedPredecessorFinset ((2 * a - 1) / 3) Y ⊆
      boundedPredecessorFinset a X := by
  let c := (2 * a - 1) / 3
  have hcstep : syracuseStep c = a := syracuseStep_oddPredecessor ha ha3
  have hc_le_a : c ≤ a := by
    have hthree := three_mul_oddPredecessor ha ha3
    dsimp [c]
    omega
  have haX : a ≤ X := by omega
  intro n hn
  have hnX : n ∈ boundedPredecessorFinset c X :=
    boundedPredecessorFinset_mono hYX hn
  rw [mem_boundedPredecessors_iff] at hnX ⊢
  apply boundedPredecessor_of_target_path
    (r := 1) (by simpa using hcstep) _ hnX
  intro i hi
  interval_cases i
  · exact hc_le_a.trans haX
  · change syracuseStep c ≤ X
    rw [hcstep]
    exact haX

/-- Homogeneous targetwise core of D1/D3: the `4a` and odd-inverse reverse
subtrees inject disjointly into the reverse subtree of `a`. -/
theorem boundedPredecessorCount_four_add_oddPredecessor_le
    {a X Y : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2)
    (hanon : ¬ IsSyracusePeriodic a)
    (hYX : Y ≤ X) (h4aX : 4 * a ≤ X) :
    boundedPredecessorCount (4 * a) X +
        boundedPredecessorCount ((2 * a - 1) / 3) Y ≤
      boundedPredecessorCount a X := by
  rw [boundedPredecessorCount, boundedPredecessorCount,
    boundedPredecessorCount,
    ← Finset.card_union_of_disjoint
      (boundedPredecessorFinset_four_disjoint_oddPredecessor
        ha ha3 hanon)]
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_union] at hn
  rcases hn with hn | hn
  · exact boundedPredecessorFinset_four_subset ha h4aX hn
  · exact boundedPredecessorFinset_oddPredecessor_subset
      ha ha3 hYX h4aX hn

/-- Targetwise core of the neutral branch D2. -/
theorem boundedPredecessorCount_four_le
    {a X : ℕ} (ha : 0 < a) (h4aX : 4 * a ≤ X) :
    boundedPredecessorCount (4 * a) X ≤
      boundedPredecessorCount a X := by
  exact Finset.card_le_card
    (boundedPredecessorFinset_four_subset ha h4aX)

/-- If a periodic point `b` reaches `a`, then `b` occurs on the forward orbit
of `a`.  This is the elementary finite-cycle fact used to manufacture
nonperiodic representatives in every KL residue class. -/
theorem periodic_predecessor_is_target_iterate
    {a b r : ℕ} (hreach : syracuseStep^[r] b = a)
    (hb : IsSyracusePeriodic b) :
    ∃ q : ℕ, syracuseStep^[q] a = b := by
  obtain ⟨p, hp, hperiod⟩ := hb
  have hperiodPt : Function.IsPeriodicPt syracuseStep p b := hperiod
  have hreduce : syracuseStep^[r % p] b = a := by
    rw [hperiodPt.iterate_mod_apply]
    exact hreach
  refine ⟨p - r % p, ?_⟩
  rw [← hreduce, ← Function.iterate_add_apply]
  have hmodlt : r % p < p := Nat.mod_lt _ hp
  rw [Nat.sub_add_cancel hmodlt.le, hperiod]

/-- Every iterate of a positive-period point is bounded by the sum of one
displayed period.  We use a sum rather than a maximum because it has a very
small `Finset` proof footprint. -/
theorem periodic_iterate_le_orbitSum
    {a p n : ℕ} (hp : 0 < p)
    (ha : syracuseStep^[p] a = a) :
    syracuseStep^[n] a ≤
      ∑ i ∈ Finset.range p, syracuseStep^[i] a := by
  have hperiodPt : Function.IsPeriodicPt syracuseStep p a := ha
  rw [← hperiodPt.iterate_mod_apply n]
  exact Finset.single_le_sum
    (s := Finset.range p)
    (f := fun i => syracuseStep^[i] a)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.mod_lt n hp))

end CleanLean.KL
