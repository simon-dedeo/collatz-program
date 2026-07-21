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

end

end ResidueSystem

end CleanLean.KL
