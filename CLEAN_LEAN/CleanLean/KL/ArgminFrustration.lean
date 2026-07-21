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

/-- Minimum over the two labels other than a selected label.  When a triple
has tied minima and the selected label is one of them, this quantity is zero
after subtracting the common minimum, exactly as required by the frustration
bound. -/
def ternaryOtherMin (z : Fin 3 → ℝ) (sigma : Fin 3) : ℝ :=
  if sigma = 0 then min (z 1) (z 2)
  else if sigma = 1 then min (z 0) (z 2)
  else min (z 0) (z 1)

/-- The other-label minimum is below every nonselected entry. -/
theorem ternaryOtherMin_le_of_ne
    (z : Fin 3 → ℝ) (sigma d : Fin 3) (hd : d ≠ sigma) :
    ternaryOtherMin z sigma ≤ z d := by
  fin_cases sigma <;> fin_cases d <;>
    simp_all [ternaryOtherMin]

/-- A label is a (not necessarily unique) minimizer of a ternary profile. -/
def IsTernaryArgmin (z : Fin 3 → ℝ) (sigma : Fin 3) : Prop :=
  ∀ d, z sigma ≤ z d

/-- A canonical (noncomputable) minimizing label.  Its exact tie-breaking is
irrelevant because a tied minimum makes the corresponding other-label gap
zero. -/
noncomputable def ternaryArgmin (z : Fin 3 → ℝ) : Fin 3 :=
  Classical.choose (Finite.exists_min z)

theorem ternaryArgmin_isArgmin (z : Fin 3 → ℝ) :
    IsTernaryArgmin z (ternaryArgmin z) :=
  Classical.choose_spec (Finite.exists_min z)

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

/-- Transport-excess triple over one coarse output row, indexed by the output
digit. -/
def transportExcessTriple (k : ℕ) (x : State (k + 1) → ℝ)
    (r : State k) : Fin 3 → ℝ :=
  fun d => transportExcess k x (fiber (k + 1) r d)

/-- Refinement-excess triple pulled back to the same output-digit labels. -/
def refinementExcessTriple (k : ℕ) (x : State (k + 1) → ℝ)
    (r : State k) : Fin 3 → ℝ :=
  fun d => refinementExcess k x (fiber (k + 1) r d)

/-- The branch coefficient of a coarse row. -/
def rowBranchWeight (k : ℕ) (w : Weights ℝ) (r : State k) : ℝ :=
  match branch k r with
  | Branch.retarded => w.retarded
  | Branch.neutral => 0
  | Branch.advanced => w.advanced

/-- Concrete pulled-back frustration cost on one coarse branch row.  Supplying
actual minimizing labels is recorded separately by `IsTernaryArgmin`; the
local upper bound itself only needs the two other-label gaps. -/
def pulledLocalFrustration
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3) (r : State k) : ℝ :=
  localFrustration w.transport (rowBranchWeight k w r)
    (ternaryOtherMin (transportExcessTriple k x r) (sigmaA r))
    (ternaryOtherMin (refinementExcessTriple k x r) (sigmaZ r))
    (sigmaA r) (sigmaZ r) (Equiv.refl (Fin 3))

theorem transportExcessTriple_nonneg
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ) (r : State k) :
    ∀ d, 0 ≤ transportExcessTriple k x r d := by
  intro d
  exact transportExcess_nonneg k hk x _

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

theorem refinementExcessTriple_nonneg_retarded
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ) (r : State k)
    (hr : branch k r = Branch.retarded) :
    ∀ d, 0 ≤ refinementExcessTriple k x r d := by
  intro d
  exact refinementExcess_nonneg_retarded k hk x _
    (branch_fiber_retarded k hk r hr d)

theorem refinementExcessTriple_nonneg_advanced
    (k : ℕ) (hk : 2 ≤ k) (x : State (k + 1) → ℝ) (r : State k)
    (hr : branch k r = Branch.advanced) :
    ∀ d, 0 ≤ refinementExcessTriple k x r d := by
  intro d
  exact refinementExcess_nonneg_advanced k hk x _
    (branch_fiber_advanced k hk r hr d)

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

/-- The pulled-back frustration cost is bounded by the exact coarse slack on
a retarded row. -/
theorem pulledLocalFrustration_le_coarseSlack_retarded
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) (hr : branch k r = Branch.retarded) :
    pulledLocalFrustration k w x sigmaA sigmaZ r ≤
      coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r := by
  rw [coarseSlack_eq_retarded_jointMinimum k hk w x hfixed r hr]
  unfold pulledLocalFrustration rowBranchWeight
  simp only [hr]
  exact localFrustration_le_ternaryMin
    w.transport w.retarded
    (ternaryOtherMin (transportExcessTriple k x r) (sigmaA r))
    (ternaryOtherMin (refinementExcessTriple k x r) (sigmaZ r))
    (transportExcessTriple k x r) (refinementExcessTriple k x r)
    (sigmaA r) (sigmaZ r) (Equiv.refl (Fin 3)) hwt hret
    (transportExcessTriple_nonneg k hk x r)
    (refinementExcessTriple_nonneg_retarded k hk x r hr)
    (fun d hd => ternaryOtherMin_le_of_ne _ _ d hd)
    (fun d hd => ternaryOtherMin_le_of_ne _ _ d hd)

/-- The analogous advanced-row bound. -/
theorem pulledLocalFrustration_le_coarseSlack_advanced
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3)
    (hwt : 0 ≤ w.transport) (hadv : 0 ≤ w.advanced)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (r : State k) (hr : branch k r = Branch.advanced) :
    pulledLocalFrustration k w x sigmaA sigmaZ r ≤
      coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r := by
  rw [coarseSlack_eq_advanced_jointMinimum k hk w x hfixed r hr]
  unfold pulledLocalFrustration rowBranchWeight
  simp only [hr]
  exact localFrustration_le_ternaryMin
    w.transport w.advanced
    (ternaryOtherMin (transportExcessTriple k x r) (sigmaA r))
    (ternaryOtherMin (refinementExcessTriple k x r) (sigmaZ r))
    (transportExcessTriple k x r) (refinementExcessTriple k x r)
    (sigmaA r) (sigmaZ r) (Equiv.refl (Fin 3)) hwt hadv
    (transportExcessTriple_nonneg k hk x r)
    (refinementExcessTriple_nonneg_advanced k hk x r hr)
    (fun d hd => ternaryOtherMin_le_of_ne _ _ d hd)
    (fun d hd => ternaryOtherMin_le_of_ne _ _ d hd)

/-- Sum of the concrete pulled-back frustration costs over branch rows. -/
def pulledFrustrationMass
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3) : ℝ :=
  ∑ r, match branch k r with
    | Branch.neutral => 0
    | _ => pulledLocalFrustration k w x sigmaA sigmaZ r

/-- Canonical minimizing output label for the transport residual triple. -/
noncomputable def transportArgmin
    (k : ℕ) (x : State (k + 1) → ℝ) (r : State k) : Fin 3 :=
  ternaryArgmin (transportExcessTriple k x r)

/-- Canonical minimizing output label for the pulled-back refinement triple. -/
noncomputable def refinementArgmin
    (k : ℕ) (x : State (k + 1) → ℝ) (r : State k) : Fin 3 :=
  ternaryArgmin (refinementExcessTriple k x r)

theorem transportArgmin_isArgmin
    (k : ℕ) (x : State (k + 1) → ℝ) (r : State k) :
    IsTernaryArgmin (transportExcessTriple k x r)
      (transportArgmin k x r) :=
  ternaryArgmin_isArgmin _

theorem refinementArgmin_isArgmin
    (k : ℕ) (x : State (k + 1) → ℝ) (r : State k) :
    IsTernaryArgmin (refinementExcessTriple k x r)
      (refinementArgmin k x r) :=
  ternaryArgmin_isArgmin _

/-- The canonical concrete frustration mass used by the open global bound. -/
noncomputable def canonicalFrustrationMass
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ) : ℝ :=
  pulledFrustrationMass k w x (transportArgmin k x) (refinementArgmin k x)

/-- The sole quantitative premise suggested by the selected records: the
canonical frustration mass dominates half the branch-weighted coarse mass
times the square of the fine terminal excess. -/
def HasQuadraticFrustration
    (k : ℕ) (w : Weights ℝ) (x : State (k + 1) → ℝ) : Prop :=
  ((w.retarded + w.advanced) *
      (system k).totalMass (coarseMinimum k x) / 2) *
      (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
    canonicalFrustrationMass k w x

/-- The global pulled-back frustration is bounded above by the total coarse
supersolution slack.  A quadratic lower bound for this frustration mass is the
remaining selected-critical conjecture. -/
theorem pulledFrustrationMass_le_coarseSlackSum
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s) :
    pulledFrustrationMass k w x sigmaA sigmaZ ≤
      ∑ r, (coarseMinimum k x r -
        (system k).operator w (coarseMinimum k x) r) := by
  unfold pulledFrustrationMass
  apply Finset.sum_le_sum
  intro r hr
  cases hb : branch k r with
  | retarded =>
      simp only
      exact pulledLocalFrustration_le_coarseSlack_retarded
        k hk w x sigmaA sigmaZ hwt hret hfixed r hb
  | neutral =>
      simp only
      have hsuper := coarseMinimum_operator_le_of_fixed
        k hk w x hwt hret hadv hfixed r
      linarith
  | advanced =>
      simp only
      exact pulledLocalFrustration_le_coarseSlack_advanced
        k hk w x sigmaA sigmaZ hwt hadv hfixed r hb

/-- The exact global reduction: a quadratic lower bound for the concrete
frustration mass implies one step of the conjectural `3/2` growth law for the
normalized terminal excess `3 * normalizedDefect`.  This theorem does not
prove the frustration lower bound. -/
theorem terminalExcess_quadratic_growth_of_frustration
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (sigmaA sigmaZ : State k → Fin 3)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hbranch : 0 < w.retarded + w.advanced)
    (hx : ∀ s, 0 < x s)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (hfrustration :
      ((w.retarded + w.advanced) *
          (system k).totalMass (coarseMinimum k x) / 2) *
          (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
        pulledFrustrationMass k w x sigmaA sigmaZ) :
    3 * (system (k + 1)).normalizedDefect x +
        (3 / 2 : ℝ) *
          (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
      3 * (system k).normalizedDefect (coarseMinimum k x) := by
  let g := coarseMinimum k x
  let b := w.retarded + w.advanced
  have hg : ∀ r, 0 < g r := by
    intro r
    simp only [g, coarseMinimum, FiniteSystem.fiberMin]
    exact lt_min (hx _) (lt_min (hx _) (hx _))
  have hG : 0 < (system k).totalMass g := by
    apply Finset.sum_pos
    · intro r hr
      exact hg r
    · exact ⟨(0 : State k), Finset.mem_univ _⟩
  have hxmass : 0 < (system (k + 1)).totalMass x := by
    apply Finset.sum_pos
    · intro s hs
      exact hx s
    · exact ⟨(0 : State (k + 1)), Finset.mem_univ _⟩
  have hupper := pulledFrustrationMass_le_coarseSlackSum
    k hk w x sigmaA sigmaZ hwt hret hadv hfixed
  change pulledFrustrationMass k w x sigmaA sigmaZ ≤
    ∑ r, (g r - (system k).operator w g r) at hupper
  have hsum :
      (∑ r, (g r - (system k).operator w g r)) =
        -(system k).slackMass w g := by
    unfold FiniteSystem.slackMass
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hlower :
      (b * (system k).totalMass g / 2) *
          (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
        -(system k).slackMass w g := by
    change (b * (system k).totalMass g / 2) *
      (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
        pulledFrustrationMass k w x sigmaA sigmaZ at hfrustration
    exact hfrustration.trans (hupper.trans_eq hsum)
  have hgap := neg_normalizedSlack_eq_defect_gap
    k hk w x g hfixed hxmass.ne' hG.ne'
  have hmass :
      -(system k).slackMass w g =
        (system k).totalMass g *
          (b * ((system k).normalizedDefect g -
            (system (k + 1)).normalizedDefect x)) := by
    calc
      -(system k).slackMass w g =
          (system k).totalMass g *
            (-(system k).normalizedSlack w g) := by
              unfold FiniteSystem.normalizedSlack
              field_simp [hG.ne']
      _ = (system k).totalMass g *
          (b * ((system k).normalizedDefect g -
            (system (k + 1)).normalizedDefect x)) := by
              rw [hgap]
  rw [hmass] at hlower
  have hGb : 0 < (system k).totalMass g * b :=
    mul_pos hG hbranch
  have hfactored :
      ((system k).totalMass g * b) *
          ((1 / 2 : ℝ) *
            (3 * (system (k + 1)).normalizedDefect x) ^ 2) ≤
        ((system k).totalMass g * b) *
          ((system k).normalizedDefect g -
            (system (k + 1)).normalizedDefect x) := by
    calc
      ((system k).totalMass g * b) *
          ((1 / 2 : ℝ) *
            (3 * (system (k + 1)).normalizedDefect x) ^ 2) =
          (b * (system k).totalMass g / 2) *
            (3 * (system (k + 1)).normalizedDefect x) ^ 2 := by ring
      _ ≤ (system k).totalMass g *
          (b * ((system k).normalizedDefect g -
            (system (k + 1)).normalizedDefect x)) := hlower
      _ = ((system k).totalMass g * b) *
          ((system k).normalizedDefect g -
            (system (k + 1)).normalizedDefect x) := by ring
  have hcancel := le_of_mul_le_mul_left hfactored hGb
  dsimp only [g, b] at hcancel ⊢
  nlinarith

/-- Canonical-interface version of the global reduction. -/
theorem terminalExcess_quadratic_growth_of_canonicalFrustration
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (x : State (k + 1) → ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hbranch : 0 < w.retarded + w.advanced)
    (hx : ∀ s, 0 < x s)
    (hfixed : ∀ s, x s = (system (k + 1)).operator w x s)
    (hfrustration : HasQuadraticFrustration k w x) :
    3 * (system (k + 1)).normalizedDefect x +
        (3 / 2 : ℝ) *
          (3 * (system (k + 1)).normalizedDefect x) ^ 2 ≤
      3 * (system k).normalizedDefect (coarseMinimum k x) := by
  exact terminalExcess_quadratic_growth_of_frustration
    k hk w x (transportArgmin k x) (refinementArgmin k x)
    hwt hret hadv hbranch hx hfixed hfrustration

end

end ResidueSystem

end CleanLean.KL
