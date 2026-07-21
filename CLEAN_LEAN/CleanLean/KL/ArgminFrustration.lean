/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CoarseMinimum

/-!
# Rowwise coarse-minimum mismatch and argmin frustration

This file exposes the exact local quantity whose global lower bound is the
open quadratic-defect problem.  First, the slack created by taking a coarse
fiber minimum of an exact fine fixed vector is written as the minimum of the
three fine-versus-coarse operator residuals.  The branch residuals are then
split into transport and refinement excesses.

The final lemma is the abstract three-label frustration bound: if the chosen
minimizing labels of two nonnegative residual triples disagree across a label
permutation, their weighted joint minimum pays at least the smaller weighted
second-gap.  No global anti-alignment estimate is asserted here.
-/

namespace CleanLean.KL

/-- Minimum of a real triple indexed by `Fin 3`. -/
def ternaryMin (z : Fin 3 → ℝ) : ℝ :=
  min (z 0) (min (z 1) (z 2))

theorem le_ternaryMin {z : Fin 3 → ℝ} {a : ℝ}
    (h : ∀ d, a ≤ z d) : a ≤ ternaryMin z := by
  exact le_min (h 0) (le_min (h 1) (h 2))

/-- Local label-frustration inequality.  The `gap` hypotheses say only that
all labels other than the selected one pay at least the displayed gap; ties
are handled by taking a zero gap. -/
theorem weighted_argmin_mismatch_le_ternaryMin
    (tau w gapA gapZ : ℝ) (A Z : Fin 3 → ℝ)
    (sigmaA sigmaZ : Fin 3) (pi : Equiv.Perm (Fin 3))
    (htau : 0 ≤ tau) (hw : 0 ≤ w)
    (hA : ∀ d, 0 ≤ A d) (hZ : ∀ d, 0 ≤ Z d)
    (hgapA : ∀ d, d ≠ sigmaA → gapA ≤ A d)
    (hgapZ : ∀ d, d ≠ sigmaZ → gapZ ≤ Z d)
    (hmismatch : pi sigmaA ≠ sigmaZ) :
    min (tau * gapA) (w * gapZ) ≤
      ternaryMin (fun d => tau * A d + w * Z (pi d)) := by
  apply le_ternaryMin
  intro d
  by_cases hd : d = sigmaA
  · subst d
    have hz := hgapZ (pi sigmaA) hmismatch
    have hwz : w * gapZ ≤ w * Z (pi sigmaA) :=
      mul_le_mul_of_nonneg_left hz hw
    calc
      min (tau * gapA) (w * gapZ) ≤ w * gapZ := min_le_right _ _
      _ ≤ w * Z (pi sigmaA) := hwz
      _ ≤ tau * A sigmaA + w * Z (pi sigmaA) :=
        le_add_of_nonneg_left (mul_nonneg htau (hA sigmaA))
  · have ha := hgapA d hd
    have hta : tau * gapA ≤ tau * A d :=
      mul_le_mul_of_nonneg_left ha htau
    exact (min_le_left _ _).trans
      (hta.trans (le_add_of_nonneg_right (mul_nonneg hw (hZ (pi d)))))

/-- Edgewise frustration cost, with zero cost when the chosen labels agree. -/
def localFrustration (tau w gapA gapZ : ℝ)
    (sigmaA sigmaZ : Fin 3) (pi : Equiv.Perm (Fin 3)) : ℝ :=
  if pi sigmaA = sigmaZ then 0 else min (tau * gapA) (w * gapZ)

/-- The frustration bound including the matching-label case. -/
theorem localFrustration_le_ternaryMin
    (tau w gapA gapZ : ℝ) (A Z : Fin 3 → ℝ)
    (sigmaA sigmaZ : Fin 3) (pi : Equiv.Perm (Fin 3))
    (htau : 0 ≤ tau) (hw : 0 ≤ w)
    (hA : ∀ d, 0 ≤ A d) (hZ : ∀ d, 0 ≤ Z d)
    (hgapA : ∀ d, d ≠ sigmaA → gapA ≤ A d)
    (hgapZ : ∀ d, d ≠ sigmaZ → gapZ ≤ Z d) :
    localFrustration tau w gapA gapZ sigmaA sigmaZ pi ≤
      ternaryMin (fun d => tau * A d + w * Z (pi d)) := by
  by_cases hmatch : pi sigmaA = sigmaZ
  · simp only [localFrustration, hmatch, if_pos]
    apply le_ternaryMin
    intro d
    exact add_nonneg (mul_nonneg htau (hA d)) (mul_nonneg hw (hZ (pi d)))
  · simp only [localFrustration, hmatch]
    exact weighted_argmin_mismatch_le_ternaryMin tau w gapA gapZ A Z
      sigmaA sigmaZ pi htau hw hA hZ hgapA hgapZ hmatch

/-- Summing the local label-frustration bounds over any finite edge set.  This
is the abstract content of the research note's inequality (4.6); proving a
quadratic lower bound for the left side remains open. -/
theorem sum_localFrustration_le_jointMinimum
    {E : Type} [Fintype E]
    (tau w gapA gapZ : E → ℝ)
    (A Z : E → Fin 3 → ℝ)
    (sigmaA sigmaZ : E → Fin 3)
    (pi : E → Equiv.Perm (Fin 3))
    (htau : ∀ r, 0 ≤ tau r) (hw : ∀ r, 0 ≤ w r)
    (hA : ∀ r d, 0 ≤ A r d) (hZ : ∀ r d, 0 ≤ Z r d)
    (hgapA : ∀ r d, d ≠ sigmaA r → gapA r ≤ A r d)
    (hgapZ : ∀ r d, d ≠ sigmaZ r → gapZ r ≤ Z r d) :
    (∑ r, localFrustration (tau r) (w r) (gapA r) (gapZ r)
        (sigmaA r) (sigmaZ r) (pi r)) ≤
      ∑ r, ternaryMin
        (fun d => tau r * A r d + w r * Z r (pi r d)) := by
  apply Finset.sum_le_sum
  intro r hr
  exact localFrustration_le_ternaryMin
    (tau r) (w r) (gapA r) (gapZ r) (A r) (Z r)
    (sigmaA r) (sigmaZ r) (pi r)
    (htau r) (hw r) (hA r) (hZ r) (hgapA r) (hgapZ r)

namespace ResidueSystem

noncomputable section

/-- Difference between a fine operator row and its projected coarse row. -/
def fineCoarseResidual (k : ℕ) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (s : State (k + 1)) : ℝ :=
  (system (k + 1)).operator w x s -
    (system k).operator w (coarseMinimum k x) (parent k s)

/-- The slack of a coarse fiber-minimum row is exactly the minimum of the
three fine-versus-coarse row residuals. -/
theorem coarseSlack_eq_fiberMin_fineCoarseResidual
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) :
    coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r =
      (system (k + 1)).fiberMin (fineCoarseResidual k w x) r := by
  simp only [coarseMinimum, FiniteSystem.fiberMin, fineCoarseResidual, system,
    parent_fiber]
  rw [hfixed (fiber (k + 1) r 0), hfixed (fiber (k + 1) r 1),
    hfixed (fiber (k + 1) r 2)]
  simp only [min_sub_sub_right]
  rfl

/-- The preceding identity with its three output digits displayed explicitly. -/
theorem coarseSlack_eq_ternaryMin_fineCoarseResidual
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) :
    coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r =
      ternaryMin
        (fun d => fineCoarseResidual k w x (fiber (k + 1) r d)) := by
  rw [coarseSlack_eq_fiberMin_fineCoarseResidual k w x hfixed r]
  rfl

/-- Transport excess above the minimum of its projected fine fiber. -/
def transportExcess (k : ℕ) (x : State (k + 1) → ℝ)
    (s : State (k + 1)) : ℝ :=
  x (transport (k + 1) s) -
    coarseMinimum k x (transport k (parent k s))

/-- Branch-target excess above the next coarse fiber minimum. -/
def refinementExcess (k : ℕ) (x : State (k + 1) → ℝ)
    (s : State (k + 1)) : ℝ :=
  coarseMinimum k x (refinementTarget (k + 1) s) -
    (system k).fiberMin (coarseMinimum k x)
      (refinementTarget k (parent k s))

/-- A retarded fine/coarse row residual is the weighted sum of the transport
and refinement excesses. -/
theorem fineCoarseResidual_eq_retarded
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.retarded) :
    fineCoarseResidual k w x s =
      w.transport * transportExcess k x s +
        w.retarded * refinementExcess k x s := by
  have hp : branch k (parent k s) = Branch.retarded :=
    (parent_branch k hk s).trans hs
  simp only [fineCoarseResidual, FiniteSystem.operator, system, hs, hp,
    transportExcess, refinementExcess, coarseMinimum]
  ring_nf
  rfl

/-- The analogous advanced residual identity. -/
theorem fineCoarseResidual_eq_advanced
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.advanced) :
    fineCoarseResidual k w x s =
      w.transport * transportExcess k x s +
        w.advanced * refinementExcess k x s := by
  have hp : branch k (parent k s) = Branch.advanced :=
    (parent_branch k hk s).trans hs
  simp only [fineCoarseResidual, FiniteSystem.operator, system, hs, hp,
    transportExcess, refinementExcess, coarseMinimum]
  ring_nf
  rfl

/-- Neutral rows have only transport excess. -/
theorem fineCoarseResidual_eq_neutral
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ) (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.neutral) :
    fineCoarseResidual k w x s =
      w.transport * transportExcess k x s := by
  have hp : branch k (parent k s) = Branch.neutral :=
    (parent_branch k hk s).trans hs
  simp only [fineCoarseResidual, FiniteSystem.operator, system, hs, hp,
    transportExcess, coarseMinimum]
  ring_nf
  rfl

/-- Transport excess is always nonnegative. -/
theorem transportExcess_nonneg
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ)
    (s : State (k + 1)) : 0 ≤ transportExcess k x s := by
  unfold transportExcess
  exact sub_nonneg.mpr (coarseMinimum_transport_le k hk x s)

/-- Refinement excess is nonnegative on a retarded row. -/
theorem refinementExcess_nonneg_retarded
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ)
    (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.retarded) :
    0 ≤ refinementExcess k x s := by
  unfold refinementExcess
  exact sub_nonneg.mpr
    (old_fiberMin_le_retarded_target k hk (coarseMinimum k x) s hs)

/-- Refinement excess is nonnegative on an advanced row. -/
theorem refinementExcess_nonneg_advanced
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ)
    (s : State (k + 1))
    (hs : branch (k + 1) s = Branch.advanced) :
    0 ≤ refinementExcess k x s := by
  unfold refinementExcess
  exact sub_nonneg.mpr
    (old_fiberMin_le_advanced_target k hk (coarseMinimum k x) s hs)

/-- All three fine output rows over a retarded coarse row are retarded. -/
theorem branch_fiber_retarded
    (k : ℕ) (hk : 2 ≤ k) (r : State k)
    (hr : branch k r = Branch.retarded) (d : Fin 3) :
    branch (k + 1) (fiber (k + 1) r d) = Branch.retarded := by
  have hb := parent_branch k hk (fiber (k + 1) r d)
  rw [parent_fiber] at hb
  exact hb.symm.trans hr

/-- All three fine output rows over an advanced coarse row are advanced. -/
theorem branch_fiber_advanced
    (k : ℕ) (hk : 2 ≤ k) (r : State k)
    (hr : branch k r = Branch.advanced) (d : Fin 3) :
    branch (k + 1) (fiber (k + 1) r d) = Branch.advanced := by
  have hb := parent_branch k hk (fiber (k + 1) r d)
  rw [parent_fiber] at hb
  exact hb.symm.trans hr

/-- All three fine output rows over a neutral coarse row are neutral. -/
theorem branch_fiber_neutral
    (k : ℕ) (hk : 2 ≤ k) (r : State k)
    (hr : branch k r = Branch.neutral) (d : Fin 3) :
    branch (k + 1) (fiber (k + 1) r d) = Branch.neutral := by
  have hb := parent_branch k hk (fiber (k + 1) r d)
  rw [parent_fiber] at hb
  exact hb.symm.trans hr

/-- Exact rowwise mismatch formula on a retarded coarse row.  The refinement
triple is already pulled back to output-digit labels, so its carry permutation
is implicit rather than separately named. -/
theorem coarseSlack_eq_retarded_jointMinimum
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) (hr : branch k r = Branch.retarded) :
    coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r =
      ternaryMin (fun d =>
        w.transport * transportExcess k x (fiber (k + 1) r d) +
          w.retarded * refinementExcess k x (fiber (k + 1) r d)) := by
  rw [coarseSlack_eq_ternaryMin_fineCoarseResidual k w x hfixed r]
  apply congrArg ternaryMin
  funext d
  exact fineCoarseResidual_eq_retarded k hk w x _
    (branch_fiber_retarded k hk r hr d)

/-- Exact rowwise mismatch formula on an advanced coarse row. -/
theorem coarseSlack_eq_advanced_jointMinimum
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) (hr : branch k r = Branch.advanced) :
    coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r =
      ternaryMin (fun d =>
        w.transport * transportExcess k x (fiber (k + 1) r d) +
          w.advanced * refinementExcess k x (fiber (k + 1) r d)) := by
  rw [coarseSlack_eq_ternaryMin_fineCoarseResidual k w x hfixed r]
  apply congrArg ternaryMin
  funext d
  exact fineCoarseResidual_eq_advanced k hk w x _
    (branch_fiber_advanced k hk r hr d)

/-- A neutral coarse row has only the transport excess. -/
theorem coarseSlack_eq_neutral_jointMinimum
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) (hr : branch k r = Branch.neutral) :
    coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r =
      ternaryMin (fun d =>
        w.transport * transportExcess k x (fiber (k + 1) r d)) := by
  rw [coarseSlack_eq_ternaryMin_fineCoarseResidual k w x hfixed r]
  apply congrArg ternaryMin
  funext d
  exact fineCoarseResidual_eq_neutral k hk w x _
    (branch_fiber_neutral k hk r hr d)

end

end ResidueSystem

end CleanLean.KL
