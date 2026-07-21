/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.StrictLift

/-!
# Coarse minimum supersolutions

Taking the minimum across the three new top-digit lifts intertwines the fine
and coarse KL operators in the supersolution direction.  This is a local
one-level fact.  It does not imply any quantitative growth of the normalized
minimum defect; that stronger statement is false for generic feasible vectors.
-/

namespace CleanLean.KL

namespace ResidueSystem

noncomputable section

/-- Minimum over the three top-digit lifts, viewed as a vector at the previous
residue precision. -/
def coarseMinimum (k : ℕ) (x : State (k + 1) → ℝ) : State k → ℝ :=
  fun r => (system (k + 1)).fiberMin x r

@[simp] theorem coarseMinimum_apply (k : ℕ) (x : State (k + 1) → ℝ)
    (r : State k) :
    coarseMinimum k x r = (system (k + 1)).fiberMin x r := rfl

/-- A fiber minimum is below every fine value above the same parent. -/
theorem fiberMin_parent_le (k : ℕ) (hk : 2 ≤ k)
    (x : State (k + 1) → ℝ) (s : State (k + 1)) :
    (system (k + 1)).fiberMin x (parent k s) ≤ x s := by
  obtain ⟨j, hj⟩ := exists_fiber_coarseParent (k + 1) (by omega) s
  have hparent : coarseParent (k + 1) s = parent k s := by
    rfl
  calc
    (system (k + 1)).fiberMin x (parent k s) =
        (system (k + 1)).fiberMin x (coarseParent (k + 1) s) := by
          rw [hparent]
    _ ≤ x (fiber (k + 1) (coarseParent (k + 1) s) j) :=
      (system (k + 1)).fiberMin_le x _ j
    _ = x s := congrArg x hj

/-- The coarse transport term is bounded by the fine transport term at every
lift of a coarse state. -/
theorem coarseMinimum_transport_le (k : ℕ) (hk : 2 ≤ k)
    (x : State (k + 1) → ℝ) (s : State (k + 1)) :
    coarseMinimum k x (transport k (parent k s)) ≤
      x (transport (k + 1) s) := by
  rw [← parent_transport]
  exact fiberMin_parent_le k hk x (transport (k + 1) s)

/-- Pointwise comparison before minimizing the three fine output rows. -/
theorem operator_coarseMinimum_le_fine (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced) (s : State (k + 1)) :
    (system k).operator w (coarseMinimum k x) (parent k s) ≤
      (system (k + 1)).operator w x s := by
  have ht := mul_le_mul_of_nonneg_left
    (coarseMinimum_transport_le k hk x s) hwt
  have hb := parent_branch k hk s
  cases hs : branch (k + 1) s with
  | retarded =>
      have hold : branch k (parent k s) = Branch.retarded := hb.trans hs
      have hmin := old_fiberMin_le_retarded_target k hk (coarseMinimum k x) s hs
      have hbranch := mul_le_mul_of_nonneg_left hmin hret
      simp only [FiniteSystem.operator, system, hold, hs]
      exact add_le_add ht hbranch
  | neutral =>
      have hold : branch k (parent k s) = Branch.neutral := hb.trans hs
      simp only [FiniteSystem.operator, system, hold, hs]
      exact add_le_add ht (le_refl (0 : ℝ))
  | advanced =>
      have hold : branch k (parent k s) = Branch.advanced := hb.trans hs
      have hmin := old_fiberMin_le_advanced_target k hk (coarseMinimum k x) s hs
      have hbranch := mul_le_mul_of_nonneg_left hmin hadv
      simp only [FiniteSystem.operator, system, hold, hs]
      exact add_le_add ht hbranch

/-- Coarse minimum supersolution: minimizing the fine operator over each new
top-digit fiber dominates applying the coarse operator after minimizing. -/
theorem operator_coarseMinimum_le (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced) (r : State k) :
    (system k).operator w (coarseMinimum k x) r ≤
      coarseMinimum k ((system (k + 1)).operator w x) r := by
  have h0 := operator_coarseMinimum_le_fine k hk w x hwt hret hadv
    (fiber (k + 1) r 0)
  have h1 := operator_coarseMinimum_le_fine k hk w x hwt hret hadv
    (fiber (k + 1) r 1)
  have h2 := operator_coarseMinimum_le_fine k hk w x hwt hret hadv
    (fiber (k + 1) r 2)
  simp only [parent_fiber] at h0 h1 h2
  simp only [coarseMinimum, FiniteSystem.fiberMin]
  exact le_min h0 (le_min h1 h2)

/-- An exact fine fixed vector becomes a coarse supersolution. -/
theorem coarseMinimum_operator_le_of_fixed (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s) (r : State k) :
    (system k).operator w (coarseMinimum k x) r ≤ coarseMinimum k x r := by
  have h := operator_coarseMinimum_le k hk w x hwt hret hadv r
  have hop : (system (k + 1)).operator w x = x := by
    funext s
    exact (hfixed s).symm
  rw [hop] at h
  exact h

/-- Coarse minimum preserves supersolutions.  This is the form needed after
the first coarse projection: later profiles need not remain exact fixed
vectors, but their operator is still pointwise below them. -/
theorem coarseMinimum_operator_le_of_supersolution
    (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hsuper : ∀ s, (system (k + 1)).operator w x s ≤ x s)
    (r : State k) :
    (system k).operator w (coarseMinimum k x) r ≤ coarseMinimum k x r := by
  exact (operator_coarseMinimum_le k hk w x hwt hret hadv r).trans
    ((system (k + 1)).fiberMin_mono hsuper r)

/-- Exact normalized slack/defect balance between arbitrary nonzero profiles
at consecutive precisions.  No fixed-vector or supersolution hypothesis is
used.  In particular, the fine normalized slack is the inherited term that
must be retained when the coarse-minimum construction is iterated. -/
theorem normalizedSlack_sub_eq_defect_gap
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (g : State k → ℝ)
    (hxmass : (system (k + 1)).totalMass x ≠ 0)
    (hgmass : (system k).totalMass g ≠ 0) :
    (system (k + 1)).normalizedSlack w x -
        (system k).normalizedSlack w g =
      (w.retarded + w.advanced) *
        ((system k).normalizedDefect g -
          (system (k + 1)).normalizedDefect x) := by
  have hfine := concrete_oscillation_identity_with_slack
    (k + 1) (by omega) w x hxmass
  have hcoarse := concrete_oscillation_identity_with_slack k hk w g hgmass
  linarith

/-- Exact normalized mass-gap identity.  Comparing the fine fixed-vector
oscillation law with the coarse law including slack shows that the coarse
super-slack is precisely the increase in normalized minimum defect. -/
theorem neg_normalizedSlack_eq_defect_gap
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (g : State k → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (hxmass : (system (k + 1)).totalMass x ≠ 0)
    (hgmass : (system k).totalMass g ≠ 0) :
    -(system k).normalizedSlack w g =
      (w.retarded + w.advanced) *
        ((system k).normalizedDefect g -
          (system (k + 1)).normalizedDefect x) := by
  have hbalance := normalizedSlack_sub_eq_defect_gap
    k hk w x g hxmass hgmass
  have hfine := (system (k + 1)).normalizedSlack_eq_zero w x hfixed
  rw [hfine, zero_sub] at hbalance
  exact hbalance

/-- Ordinary data processing for the terminal minimum defect.  The coarse
minimum of a positive exact fine fixed vector has at least the fine normalized
defect.  No quadratic improvement is claimed. -/
theorem normalizedDefect_le_coarseMinimum_of_fixed
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced) (hbranch : 0 < w.retarded + w.advanced)
    (hx : ∀ s, 0 < x s)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s) :
    (system (k + 1)).normalizedDefect x ≤
      (system k).normalizedDefect (coarseMinimum k x) := by
  let g := coarseMinimum k x
  have hg : ∀ r, 0 < g r := by
    intro r
    simp only [g, coarseMinimum, FiniteSystem.fiberMin]
    exact lt_min (hx _) (lt_min (hx _) (hx _))
  have hxmass : 0 < (system (k + 1)).totalMass x := by
    apply Finset.sum_pos
    · intro s hs
      exact hx s
    · exact ⟨(0 : State (k + 1)), Finset.mem_univ _⟩
  have hgmass : 0 < (system k).totalMass g := by
    apply Finset.sum_pos
    · intro r hr
      exact hg r
    · exact ⟨(0 : State k), Finset.mem_univ _⟩
  have hsuper : ∀ r, (system k).operator w g r ≤ g r :=
    coarseMinimum_operator_le_of_fixed k hk w x hwt hret hadv hfixed
  have hslackMass : (system k).slackMass w g ≤ 0 := by
    unfold FiniteSystem.slackMass
    apply Finset.sum_nonpos
    intro r hr
    exact sub_nonpos.mpr (hsuper r)
  have hslack : (system k).normalizedSlack w g ≤ 0 := by
    unfold FiniteSystem.normalizedSlack
    exact div_nonpos_iff.mpr (Or.inr ⟨hslackMass, hgmass.le⟩)
  have hgap := neg_normalizedSlack_eq_defect_gap k hk w x g hfixed
    hxmass.ne' hgmass.ne'
  nlinarith

end

end ResidueSystem

end CleanLean.KL
