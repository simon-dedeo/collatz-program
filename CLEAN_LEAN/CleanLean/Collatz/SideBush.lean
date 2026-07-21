/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.PredecessorCount

/-!
# Disjoint predecessor bushes along an injective Syracuse orbit

At every odd point of a Syracuse orbit, the doubled even side predecessor is
`2 (mod 3)`.  Along an injective orbit, the full predecessor sets rooted at
distinct such side targets are disjoint.  This is a deterministic packing
statement and makes no probabilistic or divergence assumption.
-/

namespace CleanLean.Collatz

open scoped BigOperators

/-- The Syracuse orbit starting at `n₀`. -/
def syracuseOrbit (n₀ j : ℕ) : ℕ := syracuseStep^[j] n₀

/-- The immediate even side predecessor at an odd spine point. -/
def sidePredecessor (n₀ j : ℕ) : ℕ := 3 * syracuseOrbit n₀ j + 1

/-- The doubled side predecessor, placed in the KL target class `2 mod 3`. -/
def sideTarget (n₀ j : ℕ) : ℕ := 6 * syracuseOrbit n₀ j + 2

@[simp] theorem syracuseOrbit_zero (n₀ : ℕ) : syracuseOrbit n₀ 0 = n₀ := by
  simp [syracuseOrbit]

theorem syracuseOrbit_succ (n₀ j : ℕ) :
    syracuseOrbit n₀ (j + 1) = syracuseStep (syracuseOrbit n₀ j) := by
  simp [syracuseOrbit, Function.iterate_succ_apply']

theorem sideTarget_mod_three (n₀ j : ℕ) : sideTarget n₀ j % 3 = 2 := by
  simp [sideTarget, Nat.add_mod, Nat.mul_mod]

theorem sideTarget_pos (n₀ j : ℕ) : 0 < sideTarget n₀ j := by
  unfold sideTarget
  omega

theorem sidePredecessor_mod_three (n₀ j : ℕ) :
    sidePredecessor n₀ j % 3 = 1 := by
  simp [sidePredecessor, Nat.add_mod]

theorem syracuseStep_sideTarget (n₀ j : ℕ) :
    syracuseStep (sideTarget n₀ j) = sidePredecessor n₀ j := by
  have heven : sideTarget n₀ j % 2 = 0 := by
    simp [sideTarget, Nat.mul_mod]
  rw [syracuseStep]
  simp only [heven, if_pos]
  dsimp [sideTarget, sidePredecessor]
  omega

theorem syracuseStep_sidePredecessor_of_odd
    {n₀ j : ℕ} (hodd : syracuseOrbit n₀ j % 2 = 1) :
    syracuseStep (sidePredecessor n₀ j) = syracuseOrbit n₀ (j + 1) := by
  have heven : sidePredecessor n₀ j % 2 = 0 := by
    simp [sidePredecessor, Nat.add_mod, Nat.mul_mod, hodd]
  have hodd' : syracuseOrbit n₀ j % 2 ≠ 0 := by omega
  calc
    syracuseStep (sidePredecessor n₀ j) = sidePredecessor n₀ j / 2 := by
      simp [syracuseStep, heven]
    _ = (3 * syracuseOrbit n₀ j + 1) / 2 := rfl
    _ = syracuseStep (syracuseOrbit n₀ j) := by
      simp [syracuseStep, hodd']
    _ = syracuseOrbit n₀ (j + 1) := (syracuseOrbit_succ n₀ j).symm

theorem iterate_two_sideTarget_of_odd
    {n₀ j : ℕ} (hodd : syracuseOrbit n₀ j % 2 = 1) :
    syracuseStep^[2] (sideTarget n₀ j) = syracuseOrbit n₀ (j + 1) := by
  rw [show (2 : ℕ) = 1 + 1 by omega, Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [syracuseStep_sideTarget, syracuseStep_sidePredecessor_of_odd hodd]

/-- Continuing for `d` steps from the `i`th spine point gives the
`(i+d)`th spine point. -/
theorem iterate_syracuseOrbit (n₀ i d : ℕ) :
    syracuseStep^[d] (syracuseOrbit n₀ i) = syracuseOrbit n₀ (i + d) := by
  unfold syracuseOrbit
  rw [show i + d = d + i by omega, Function.iterate_add_apply]

/-- The immediate even side predecessor is not itself on an injective spine. -/
theorem sidePredecessor_not_on_injective_orbit
    {n₀ j : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : syracuseOrbit n₀ j % 2 = 1) (t : ℕ) :
    sidePredecessor n₀ j ≠ syracuseOrbit n₀ t := by
  intro hside
  have horbit : syracuseOrbit n₀ (j + 1) = syracuseOrbit n₀ (t + 1) := by
    calc
      syracuseOrbit n₀ (j + 1) =
          syracuseStep (sidePredecessor n₀ j) :=
        (syracuseStep_sidePredecessor_of_odd hodd).symm
      _ = syracuseStep (syracuseOrbit n₀ t) := congrArg syracuseStep hside
      _ = syracuseOrbit n₀ (t + 1) := (syracuseOrbit_succ n₀ t).symm
  have hjt : j = t := by
    have := hinj horbit
    omega
  subst t
  unfold sidePredecessor at hside
  omega

/-- The KL side target is also off the injective spine. -/
theorem sideTarget_not_on_injective_orbit
    {n₀ j : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : syracuseOrbit n₀ j % 2 = 1) (t : ℕ) :
    sideTarget n₀ j ≠ syracuseOrbit n₀ t := by
  intro hside
  apply sidePredecessor_not_on_injective_orbit hinj hodd (t + 1)
  calc
    sidePredecessor n₀ j = syracuseStep (sideTarget n₀ j) :=
      (syracuseStep_sideTarget n₀ j).symm
    _ = syracuseStep (syracuseOrbit n₀ t) := congrArg syracuseStep hside
    _ = syracuseOrbit n₀ (t + 1) := (syracuseOrbit_succ n₀ t).symm

/-- A side target on an injective spine cannot lie on a positive cycle.  The
statement is kept in the defining existential form so this elementary module
does not depend on the later KL predecessor-transfer layer. -/
theorem sideTarget_not_periodic_raw
    {n₀ j : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : syracuseOrbit n₀ j % 2 = 1) :
    ¬ ∃ p : ℕ, 0 < p ∧ syracuseStep^[p] (sideTarget n₀ j) = sideTarget n₀ j := by
  rintro ⟨p, hp, hperiod⟩
  have hspinePeriodic :
      syracuseStep^[p] (syracuseOrbit n₀ (j + 1)) =
        syracuseOrbit n₀ (j + 1) := by
    calc
      syracuseStep^[p] (syracuseOrbit n₀ (j + 1)) =
          syracuseStep^[p] (syracuseStep^[2] (sideTarget n₀ j)) := by
        rw [iterate_two_sideTarget_of_odd hodd]
      _ = syracuseStep^[p + 2] (sideTarget n₀ j) := by
        rw [Function.iterate_add_apply]
      _ = syracuseStep^[2 + p] (sideTarget n₀ j) := by rw [Nat.add_comm]
      _ = syracuseStep^[2] (syracuseStep^[p] (sideTarget n₀ j)) := by
        rw [Function.iterate_add_apply]
      _ = syracuseStep^[2] (sideTarget n₀ j) := by rw [hperiod]
      _ = syracuseOrbit n₀ (j + 1) := iterate_two_sideTarget_of_odd hodd
  have hindices := hinj ((iterate_syracuseOrbit n₀ (j + 1) p).symm.trans
    hspinePeriodic)
  omega

theorem sideTarget_injective
    {n₀ : ℕ} (hinj : Function.Injective (syracuseOrbit n₀)) :
    Function.Injective (sideTarget n₀) := by
  intro i j hij
  apply hinj
  unfold sideTarget at hij
  omega

/-- No iterate of one side target can hit a distinct side target. -/
theorem iterate_sideTarget_ne_of_ne
    {n₀ i j : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hiOdd : syracuseOrbit n₀ i % 2 = 1)
    (hjOdd : syracuseOrbit n₀ j % 2 = 1)
    (hij : i ≠ j) (d : ℕ) :
    syracuseStep^[d] (sideTarget n₀ i) ≠ sideTarget n₀ j := by
  cases d with
  | zero =>
      simp only [Function.iterate_zero, id_eq]
      exact (sideTarget_injective hinj).ne hij
  | succ d =>
      cases d with
      | zero =>
          change syracuseStep (sideTarget n₀ i) ≠ sideTarget n₀ j
          rw [syracuseStep_sideTarget]
          intro h
          have hmod := congrArg (fun n : ℕ => n % 3) h
          rw [sidePredecessor_mod_three, sideTarget_mod_three] at hmod
          norm_num at hmod
      | succ q =>
          intro hhit
          have hspine :
              syracuseStep^[q + 2] (sideTarget n₀ i) =
                syracuseOrbit n₀ (i + 1 + q) := by
            calc
              syracuseStep^[q + 2] (sideTarget n₀ i) =
                  syracuseStep^[q] (syracuseStep^[2] (sideTarget n₀ i)) := by
                rw [Function.iterate_add_apply]
              _ = syracuseStep^[q] (syracuseOrbit n₀ (i + 1)) := by
                rw [iterate_two_sideTarget_of_odd hiOdd]
              _ = syracuseOrbit n₀ (i + 1 + q) :=
                iterate_syracuseOrbit n₀ (i + 1) q
          have hoff := sideTarget_not_on_injective_orbit hinj hjOdd (i + 1 + q)
          apply hoff
          exact hhit.symm.trans hspine

/-- Pairwise disjointness of the finite predecessor bushes at any cutoff. -/
theorem predecessorFinset_sideTargets_disjoint
    {n₀ i j X : ℕ}
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hiOdd : syracuseOrbit n₀ i % 2 = 1)
    (hjOdd : syracuseOrbit n₀ j % 2 = 1)
    (hij : i ≠ j) :
    Disjoint (predecessorFinset (sideTarget n₀ i) X)
      (predecessorFinset (sideTarget n₀ j) X) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmi hmj
  rw [mem_predecessors_iff] at hmi hmj
  obtain ⟨_, _, r, hr⟩ := hmi
  obtain ⟨_, _, s, hs⟩ := hmj
  rcases le_total r s with hrs | hsr
  · apply iterate_sideTarget_ne_of_ne hinj hiOdd hjOdd hij (s - r)
    calc
      syracuseStep^[s - r] (sideTarget n₀ i) =
          syracuseStep^[s - r] (syracuseStep^[r] m) := congrArg _ hr.symm
      _ = syracuseStep^[(s - r) + r] m :=
        (Function.iterate_add_apply syracuseStep (s - r) r m).symm
      _ = syracuseStep^[s] m := by rw [Nat.sub_add_cancel hrs]
      _ = sideTarget n₀ j := hs
  · apply iterate_sideTarget_ne_of_ne hinj hjOdd hiOdd hij.symm (r - s)
    calc
      syracuseStep^[r - s] (sideTarget n₀ j) =
          syracuseStep^[r - s] (syracuseStep^[s] m) := congrArg _ hs.symm
      _ = syracuseStep^[(r - s) + s] m :=
        (Function.iterate_add_apply syracuseStep (r - s) s m).symm
      _ = syracuseStep^[r] m := by rw [Nat.sub_add_cancel hsr]
      _ = sideTarget n₀ i := hr

/-- Carleson packing for any finite collection of odd positions on an
injective Syracuse spine.  Every counted predecessor lies in `[1,X]`, and the
side bushes are pairwise disjoint. -/
theorem sum_predecessorCount_sideTargets_le
    {n₀ X : ℕ} (J : Finset ℕ)
    (hinj : Function.Injective (syracuseOrbit n₀))
    (hodd : ∀ j ∈ J, syracuseOrbit n₀ j % 2 = 1) :
    ∑ j ∈ J, predecessorCount (sideTarget n₀ j) X ≤ X := by
  classical
  let f : ℕ → Finset ℕ := fun j => predecessorFinset (sideTarget n₀ j) X
  have hpair : (J : Set ℕ).PairwiseDisjoint f := by
    intro i hi j hj hij
    exact predecessorFinset_sideTargets_disjoint hinj
      (hodd i hi) (hodd j hj) hij
  have hsubset : J.biUnion f ⊆ Finset.Icc 1 X := by
    intro m hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨j, hj, hmj⟩ := hm
    dsimp [f] at hmj
    rw [mem_predecessors_iff] at hmj
    exact Finset.mem_Icc.mpr ⟨hmj.1, hmj.2.1⟩
  calc
    ∑ j ∈ J, predecessorCount (sideTarget n₀ j) X =
        ∑ j ∈ J, (f j).card := by rfl
    _ = (J.biUnion f).card := (Finset.card_biUnion hpair).symm
    _ ≤ (Finset.Icc 1 X).card := Finset.card_le_card hsubset
    _ ≤ X := by simp

end CleanLean.Collatz
