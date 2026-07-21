/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CriticalParameter

/-!
# Lifting finite KL feasibility through residue precision

Krasikov--Lagarias observe that a feasible level-`k` vector can be copied to
the three top-digit lifts at level `k+1`.  This file formalizes the concrete
residue projection and the compatibility lemmas needed for that argument.
-/

namespace CleanLean.KL

namespace ResidueSystem

/-- Forget the highest base-three digit of a level-`k+1` state. -/
def parent (k : ℕ) (s : State (k + 1)) : State k :=
  ZMod.cast s

/-- Forget the highest digit of a level-`k` state, landing in its coarse
coordinate space. -/
def coarseParent (k : ℕ) (s : State k) : Coarse k :=
  ZMod.cast s

theorem pow_parent_dvd (k : ℕ) : 3 ^ (k - 1) ∣ 3 ^ k := by
  exact pow_dvd_pow 3 (Nat.sub_le k 1)

theorem pow_coarse_dvd (k : ℕ) : 3 ^ (k - 2) ∣ 3 ^ (k - 1) := by
  exact pow_dvd_pow 3 (by omega)

@[simp] theorem parent_natCast (k n : ℕ) :
    parent k (n : State (k + 1)) = (n : State k) := by
  simp [parent, ZMod.cast_natCast (pow_parent_dvd k)]

@[simp] theorem parent_zero (k : ℕ) : parent k 0 = 0 := by
  simp [parent]

theorem parent_val (k : ℕ) (s : State (k + 1)) :
    (parent k s).val = s.val % 3 ^ (k - 1) := by
  change (ZMod.cast s : State k).val = s.val % 3 ^ (k - 1)
  rw [ZMod.cast_eq_val s]
  exact ZMod.val_natCast _ _

theorem coarseParent_val (k : ℕ) (s : State k) :
    (coarseParent k s).val = s.val % 3 ^ (k - 2) := by
  change (ZMod.cast s : Coarse k).val = s.val % 3 ^ (k - 2)
  rw [ZMod.cast_eq_val s]
  exact ZMod.val_natCast _ _

theorem parent_mod_three (k : ℕ) (hk : 2 ≤ k) (s : State (k + 1)) :
    (parent k s).val % 3 = s.val % 3 := by
  rw [parent_val]
  have hdiv : 3 ∣ 3 ^ (k - 1) := dvd_pow_self 3 (by omega)
  exact Nat.mod_mod_of_dvd s.val hdiv

/-- The low branch digit is unchanged when the top digit is forgotten. -/
@[simp] theorem parent_branch (k : ℕ) (hk : 2 ≤ k) (s : State (k + 1)) :
    branch k (parent k s) = branch (k + 1) s := by
  simp only [branch]
  rw [parent_mod_three k hk s]

/-- Low-digit coordinates commute with forgetting the highest digit. -/
@[simp] theorem parent_lowDigit (k : ℕ) (hk : 2 ≤ k)
    (r : Coarse (k + 1)) (j : Fin 3) :
    parent k (lowDigit (k + 1) r j) = lowDigit k (coarseParent k r) j := by
  apply ZMod.val_injective _
  rw [parent_val, lowDigit_val (k + 1) (by omega),
    lowDigit_val k hk, coarseParent_val]
  let n := 3 ^ (k - 2)
  have hn : 0 < n := pow_pos (by norm_num) _
  have hj : j.val < 3 := j.isLt
  have hmod : r.val ≡ r.val % n [MOD n] := (Nat.mod_modEq r.val n).symm
  have hscaled := hmod.mul_left' 3
  have hadd := hscaled.add_left j.val
  have hpow : 3 * n = 3 ^ (k - 1) := by
    simpa [n] using (three_pow_level k hk).symm
  rw [hpow] at hadd
  have hright : 3 * (r.val % n) + j.val < 3 ^ (k - 1) := by
    rw [← hpow]
    have hrmod : r.val % n < n := Nat.mod_lt _ hn
    omega
  have hout :
      (j.val + 3 * (r.val % n)) % 3 ^ (k - 1) =
        j.val + 3 * (r.val % n) :=
    Nat.mod_eq_of_lt (by simpa [add_comm] using hright)
  change (j.val + 3 * r.val) % 3 ^ (k - 1) =
    (j.val + 3 * (r.val % n)) % 3 ^ (k - 1) at hadd
  rw [hout] at hadd
  simpa [add_comm] using hadd

/-- Forgetting a top digit sends every fine lift back to its fiber base. -/
@[simp] theorem parent_fiber (k : ℕ) (r : Coarse (k + 1)) (j : Fin 3) :
    parent k (fiber (k + 1) r j) = r := by
  change parent k ((r.val + j.val * 3 ^ (k - 1) : ℕ) : State (k + 1)) = r
  rw [parent_natCast]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
    ZMod.natCast_zmod_val]

/-- Every state is one of the three lifts over its coarse projection. -/
theorem exists_fiber_coarseParent (k : ℕ) (hk : 2 ≤ k) (s : State k) :
    ∃ j : Fin 3, fiber k (coarseParent k s) j = s := by
  obtain ⟨⟨r, j⟩, hrj⟩ := (fiberEquiv k hk).surjective s
  change fiber k r j = s at hrj
  have hr : r = coarseParent k s := by
    rw [← hrj]
    symm
    change ZMod.cast (fiber k r j) = r
    have hd := pow_coarse_dvd k
    change ZMod.cast ((r.val + j.val * 3 ^ (k - 2) : ℕ) : State k) = r
    rw [ZMod.cast_natCast hd]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  rw [hr] at hrj
  exact ⟨j, hrj⟩

/-- The affine transport commutes with forgetting the top digit. -/
@[simp] theorem parent_transport (k : ℕ) (s : State (k + 1)) :
    parent k (transport (k + 1) s) = transport k (parent k s) := by
  have hd := pow_parent_dvd k
  have h4 : (ZMod.cast (4 : State (k + 1)) : State k) = 4 :=
    ZMod.cast_natCast hd 4
  have h2 : (ZMod.cast (2 : State (k + 1)) : State k) = 2 :=
    ZMod.cast_natCast hd 2
  rw [transport_apply, transport_apply]
  simp only [parent, ZMod.cast_add hd, ZMod.cast_mul hd]
  rw [h4, h2]

@[simp] theorem coarseParent_coarseMulFour (k : ℕ)
    (r : Coarse (k + 1)) :
    coarseParent k (coarseMulFour (k + 1) r) =
      coarseMulFour k (coarseParent k r) := by
  have hd := pow_coarse_dvd k
  have h4 : (ZMod.cast (4 : Coarse (k + 1)) : Coarse k) = 4 :=
    ZMod.cast_natCast hd 4
  rw [coarseMulFour_apply, coarseMulFour_apply]
  simp only [coarseParent, ZMod.cast_mul hd]
  rw [h4]

@[simp] theorem coarseParent_coarseAffineTwo (k : ℕ)
    (r : Coarse (k + 1)) :
    coarseParent k (coarseAffineTwo (k + 1) r) =
      coarseAffineTwo k (coarseParent k r) := by
  have hd := pow_coarse_dvd k
  have h1 : (ZMod.cast (1 : Coarse (k + 1)) : Coarse k) = 1 :=
    ZMod.cast_one hd
  have h2 : (ZMod.cast (2 : Coarse (k + 1)) : Coarse k) = 2 :=
    ZMod.cast_natCast hd 2
  rw [coarseAffineTwo_apply, coarseAffineTwo_apply]
  simp only [coarseParent, ZMod.cast_add hd, ZMod.cast_mul hd]
  rw [h1, h2]

/-- On the retarded branch, the refinement target at the finer level lies
over the refinement target of the projected state. -/
theorem coarseParent_refinementTarget_retarded (k : ℕ) (hk : 2 ≤ k)
    (s : State (k + 1)) (hs : branch (k + 1) s = Branch.retarded) :
    coarseParent k (refinementTarget (k + 1) s) =
      refinementTarget k (parent k s) := by
  obtain ⟨⟨r, j⟩, hrj⟩ := (lowDigitEquiv (k + 1) (by omega)).surjective s
  change lowDigit (k + 1) r j = s at hrj
  rw [← hrj] at hs ⊢
  have hjval : j.val = 0 := by
    have h := hs
    rw [branch_lowDigit (k + 1) (by omega)] at h
    generalize hq : j.val = q at h
    have hlt : q < 3 := by omega
    interval_cases q <;> simp_all
  have hj : j = 0 := Fin.ext hjval
  subst j
  rw [refinementTarget_lowDigit_zero (k + 1) (by omega),
    parent_lowDigit k hk, refinementTarget_lowDigit_zero k hk,
    coarseParent_coarseMulFour]

/-- The analogous compatibility on the advanced branch. -/
theorem coarseParent_refinementTarget_advanced (k : ℕ) (hk : 2 ≤ k)
    (s : State (k + 1)) (hs : branch (k + 1) s = Branch.advanced) :
    coarseParent k (refinementTarget (k + 1) s) =
      refinementTarget k (parent k s) := by
  obtain ⟨⟨r, j⟩, hrj⟩ := (lowDigitEquiv (k + 1) (by omega)).surjective s
  change lowDigit (k + 1) r j = s at hrj
  rw [← hrj] at hs ⊢
  have hjval : j.val = 2 := by
    have h := hs
    rw [branch_lowDigit (k + 1) (by omega)] at h
    generalize hq : j.val = q at h
    have hlt : q < 3 := by omega
    interval_cases q <;> simp_all
  have hj : j = 2 := Fin.ext hjval
  subst j
  rw [refinementTarget_lowDigit_two (k + 1) (by omega),
    parent_lowDigit k hk, refinementTarget_lowDigit_two k hk,
    coarseParent_coarseAffineTwo]

/-- Copy a level-`k` value to all three top-digit lifts at level `k+1`. -/
def liftValue (k : ℕ) (c : State k → ℝ) : State (k + 1) → ℝ :=
  fun s => c (parent k s)

/-- A copied value is constant on every new top-digit fiber. -/
@[simp] theorem fiberMin_liftValue (k : ℕ) (c : State k → ℝ)
    (r : Coarse (k + 1)) :
    (system (k + 1)).fiberMin (liftValue k c) r = c r := by
  simp [FiniteSystem.fiberMin, system, liftValue]

theorem old_fiberMin_le_retarded_target (k : ℕ) (hk : 2 ≤ k)
    (c : State k → ℝ) (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.retarded) :
    (system k).fiberMin c (refinementTarget k (parent k s)) ≤
      c (refinementTarget (k + 1) s) := by
  let r := refinementTarget (k + 1) s
  have hproj : coarseParent k r = refinementTarget k (parent k s) :=
    coarseParent_refinementTarget_retarded k hk s hs
  obtain ⟨j, hj⟩ := exists_fiber_coarseParent k hk r
  calc
    (system k).fiberMin c (refinementTarget k (parent k s)) ≤
        c ((system k).fiber (refinementTarget k (parent k s)) j) :=
      (system k).fiberMin_le c _ j
    _ = c r := by
      congr 1
      change fiber k (refinementTarget k (parent k s)) j = r
      simpa [hproj] using hj

theorem old_fiberMin_le_advanced_target (k : ℕ) (hk : 2 ≤ k)
    (c : State k → ℝ) (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.advanced) :
    (system k).fiberMin c (refinementTarget k (parent k s)) ≤
      c (refinementTarget (k + 1) s) := by
  let r := refinementTarget (k + 1) s
  have hproj : coarseParent k r = refinementTarget k (parent k s) :=
    coarseParent_refinementTarget_advanced k hk s hs
  obtain ⟨j, hj⟩ := exists_fiber_coarseParent k hk r
  calc
    (system k).fiberMin c (refinementTarget k (parent k s)) ≤
        c ((system k).fiber (refinementTarget k (parent k s)) j) :=
      (system k).fiberMin_le c _ j
    _ = c r := by
      congr 1
      change fiber k (refinementTarget k (parent k s)) j = r
      simpa [hproj] using hj

/-- The fine operator on a copied vector dominates the copied coarse
operator.  Its branch term sees one particular member of the old fiber,
which is at least the old fiber minimum. -/
theorem operator_liftValue_ge (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (c : State k → ℝ)
    (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced) (s : State (k + 1)) :
    (system k).operator w c (parent k s) ≤
      (system (k + 1)).operator w (liftValue k c) s := by
  have hb := parent_branch k hk s
  cases hs : branch (k + 1) s with
  | retarded =>
      have hold : branch k (parent k s) = Branch.retarded := hb.trans hs
      have hmin := old_fiberMin_le_retarded_target k hk c s hs
      have hmul := mul_le_mul_of_nonneg_left hmin hret
      change
        w.transport * c (transport k (parent k s)) +
            (match branch k (parent k s) with
            | .retarded => w.retarded * (system k).fiberMin c
                (refinementTarget k (parent k s))
            | .neutral => 0
            | .advanced => w.advanced * (system k).fiberMin c
                (refinementTarget k (parent k s))) ≤
          w.transport * liftValue k c (transport (k + 1) s) +
            (match branch (k + 1) s with
            | .retarded => w.retarded * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s)
            | .neutral => 0
            | .advanced => w.advanced * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s))
      rw [hold, hs, fiberMin_liftValue]
      simp only [liftValue, parent_transport]
      exact add_le_add (le_refl _) hmul
  | neutral =>
      have hold : branch k (parent k s) = Branch.neutral := hb.trans hs
      change
        w.transport * c (transport k (parent k s)) +
            (match branch k (parent k s) with
            | .retarded => w.retarded * (system k).fiberMin c
                (refinementTarget k (parent k s))
            | .neutral => 0
            | .advanced => w.advanced * (system k).fiberMin c
                (refinementTarget k (parent k s))) ≤
          w.transport * liftValue k c (transport (k + 1) s) +
            (match branch (k + 1) s with
            | .retarded => w.retarded * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s)
            | .neutral => 0
            | .advanced => w.advanced * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s))
      rw [hold, hs]
      simp only [liftValue, parent_transport]
      exact le_rfl
  | advanced =>
      have hold : branch k (parent k s) = Branch.advanced := hb.trans hs
      have hmin := old_fiberMin_le_advanced_target k hk c s hs
      have hmul := mul_le_mul_of_nonneg_left hmin hadv
      change
        w.transport * c (transport k (parent k s)) +
            (match branch k (parent k s) with
            | .retarded => w.retarded * (system k).fiberMin c
                (refinementTarget k (parent k s))
            | .neutral => 0
            | .advanced => w.advanced * (system k).fiberMin c
                (refinementTarget k (parent k s))) ≤
          w.transport * liftValue k c (transport (k + 1) s) +
            (match branch (k + 1) s with
            | .retarded => w.retarded * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s)
            | .neutral => 0
            | .advanced => w.advanced * (system (k + 1)).fiberMin
                (liftValue k c) (refinementTarget (k + 1) s))
      rw [hold, hs, fiberMin_liftValue]
      simp only [liftValue, parent_transport]
      exact add_le_add (le_refl _) hmul

/-- The Krasikov--Lagarias feasible region grows with residue precision. -/
theorem feasible_succ (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced)
    {c : State k → ℝ} (hc : (system k).Feasible w c) :
    (system (k + 1)).Feasible w (liftValue k c) := by
  constructor
  · intro s
    exact hc.1 (parent k s)
  · intro s
    exact (hc.2 (parent k s)).trans
      (operator_liftValue_ge k hk w c hret hadv s)

end ResidueSystem

/-- Exact finite feasibility is monotone in the level. -/
theorem levelFeasible_succ (k : ℕ) (hk : 2 ≤ k) (lam : ℝ) (hlam : 0 ≤ lam) :
    LevelFeasible k lam → LevelFeasible (k + 1) lam := by
  rintro ⟨c, hc⟩
  refine ⟨ResidueSystem.liftValue k c, ?_⟩
  exact ResidueSystem.feasible_succ k hk (klWeights lam)
    (Real.rpow_nonneg hlam _)
    (Real.rpow_nonneg hlam _) hc

/-- Consequently the exact critical feasibility suprema are nondecreasing. -/
theorem criticalLambda_mono_step (k : ℕ) (hk : 2 ≤ k) :
    criticalLambda k ≤ criticalLambda (k + 1) := by
  apply csSup_le (criticalSet_nonempty k)
  intro lam hlam
  apply le_csSup (criticalSet_bddAbove (k + 1))
  exact ⟨hlam.1, levelFeasible_succ k hk lam (zero_le_one.trans hlam.1.1) hlam.2⟩

end CleanLean.KL
