/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.FiniteSystem

/-!
# The finite KL oscillation identity

This file isolates the algebra behind the oscillation law used in the
fiber-geometry program.  Two combinatorial facts are explicit hypotheses:

* the three refinement fibers partition the fine state space; and
* after summing over states, the retarded and advanced branch terms each see
  one copy of every coarse fiber minimum.

Those facts must eventually be proved for the concrete residue system.  Once
they are available, the identity below is exact; it is not a numerical or
asymptotic statement.
-/

namespace CleanLean.KL

open scoped BigOperators

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- Sum of the three values in a refinement fiber. -/
def fiberSum (c : S.State → ℝ) (r : S.Coarse) : ℝ :=
  c (S.fiber r 0) + c (S.fiber r 1) + c (S.fiber r 2)

/-- Fiber average minus fiber minimum. -/
def fiberDefect (c : S.State → ℝ) (r : S.Coarse) : ℝ :=
  S.fiberSum c r / 3 - S.fiberMin c r

/-- Total eigenfunction mass on fine states. -/
def totalMass (c : S.State → ℝ) : ℝ := ∑ m, c m

/-- Sum of all coarse fiber minima. -/
def minimumMass (c : S.State → ℝ) : ℝ := ∑ r, S.fiberMin c r

/-- Total (unnormalized) loss caused by replacing averages by minima. -/
def defectMass (c : S.State → ℝ) : ℝ := ∑ r, S.fiberDefect c r

/-- The normalized mean fiber defect appearing in the KL root law. -/
def normalizedDefect (c : S.State → ℝ) : ℝ :=
  S.defectMass c / S.totalMass c

/-- Total excess of the KL operator over a candidate vector.  For a feasible
vector every summand is nonnegative; for an exact eigenvector it vanishes. -/
def slackMass (w : Weights ℝ) (c : S.State → ℝ) : ℝ :=
  ∑ m, (S.operator w c m - c m)

/-- Aggregate KL slack, normalized by the total mass of the candidate vector.
This is the finite quantity denoted `Sigma(c,lambda)` in the limit argument. -/
def normalizedSlack (w : Weights ℝ) (c : S.State → ℝ) : ℝ :=
  S.slackMass w c / S.totalMass c

/-- The value of the averaged, rather than adversarial, operator. -/
def annealedValue (w : Weights ℝ) : ℝ :=
  w.transport + (w.retarded + w.advanced) / 3

/-- The non-transport summand in the KL operator. -/
def branchTerm (w : Weights ℝ) (c : S.State → ℝ) (m : S.State) : ℝ :=
  match S.branch m with
  | Branch.retarded => w.retarded * S.fiberMin c (S.refinementTarget m)
  | Branch.neutral => 0
  | Branch.advanced => w.advanced * S.fiberMin c (S.refinementTarget m)

theorem operator_eq_transport_add_branchTerm
    (w : Weights ℝ) (c : S.State → ℝ) (m : S.State) :
    S.operator w c m =
      w.transport * c (S.transport m) + S.branchTerm w c m := by
  rfl

/-- If the fibers partition the fine states, defect mass is exactly one third
of total mass minus the sum of the fiber minima. -/
theorem defectMass_eq
    (c : S.State → ℝ)
    (hpartition : ∑ r, S.fiberSum c r = S.totalMass c) :
    S.defectMass c = S.totalMass c / 3 - S.minimumMass c := by
  simp only [defectMass, fiberDefect, minimumMass]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hpartition]

/-- Summing the exact eigen-equation reduces it to a scalar balance law.  The
`hbranch` hypothesis is the finite branch-counting/bijection statement that
remains to be discharged for the concrete residue system. -/
theorem summed_eigen_equation
    (w : Weights ℝ) (c : S.State → ℝ)
    (hEigen : ∀ m, c m = S.operator w c m)
    (hbranch : ∑ m, S.branchTerm w c m =
      (w.retarded + w.advanced) * S.minimumMass c) :
    S.totalMass c =
      w.transport * S.totalMass c +
        (w.retarded + w.advanced) * S.minimumMass c := by
  have hsum : (∑ m, c m) = ∑ m, S.operator w c m := by
    exact Finset.sum_congr rfl fun m _ => hEigen m
  calc
    S.totalMass c = ∑ m, S.operator w c m := by
      simpa only [totalMass] using hsum
    _ = ∑ m, (w.transport * c (S.transport m) + S.branchTerm w c m) := by
      apply Finset.sum_congr rfl
      intro m _
      exact S.operator_eq_transport_add_branchTerm w c m
    _ = w.transport * (∑ m, c (S.transport m)) +
        ∑ m, S.branchTerm w c m := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = w.transport * S.totalMass c +
        (w.retarded + w.advanced) * S.minimumMass c := by
      rw [S.transport.sum_comp c, hbranch]
      rfl

/-- Summing the operator, without assuming an exact eigen-equation, expresses
the aggregate slack using only the total and minimum masses. -/
theorem slackMass_eq
    (w : Weights ℝ) (c : S.State → ℝ)
    (hbranch : ∑ m, S.branchTerm w c m =
      (w.retarded + w.advanced) * S.minimumMass c) :
    S.slackMass w c =
      (w.transport - 1) * S.totalMass c +
        (w.retarded + w.advanced) * S.minimumMass c := by
  simp only [slackMass, operator_eq_transport_add_branchTerm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    S.transport.sum_comp c, hbranch]
  simp only [totalMass]
  ring

/-- The normalized slack of an exact eigenvector is zero. -/
theorem normalizedSlack_eq_zero
    (w : Weights ℝ) (c : S.State → ℝ)
    (hEigen : ∀ m, c m = S.operator w c m) :
    S.normalizedSlack w c = 0 := by
  simp only [normalizedSlack, slackMass]
  have hzero : ∀ m, S.operator w c m - c m = 0 := fun m => by
    rw [← hEigen m]
    ring
  simp [hzero]

/-- Feasibility makes the aggregate (unnormalized) slack nonnegative. -/
theorem slackMass_nonneg
    (w : Weights ℝ) (c : S.State → ℝ) (hc : S.Feasible w c) :
    0 ≤ S.slackMass w c := by
  apply Finset.sum_nonneg
  intro m _
  exact sub_nonneg.mpr (hc.2 m)

/-- Exact finite oscillation law.  In the KL specialization the annealed value
is a function `s(λ)` and the two non-transport weights are
`λ^(α-2)` and `λ^(α-1)`, giving

`s(λ) - 1 = (λ^(α-2) + λ^(α-1)) · δ`.

The theorem deliberately exposes the two concrete obligations
`hpartition` and `hbranch`, so a formal development cannot silently replace
the KL residue system by a cleaner unrelated model. -/
theorem annealedValue_sub_one_eq_branchWeight_mul_normalizedDefect
    (w : Weights ℝ) (c : S.State → ℝ)
    (hEigen : ∀ m, c m = S.operator w c m)
    (hpartition : ∑ r, S.fiberSum c r = S.totalMass c)
    (hbranch : ∑ m, S.branchTerm w c m =
      (w.retarded + w.advanced) * S.minimumMass c)
    (hmass : S.totalMass c ≠ 0) :
    annealedValue w - 1 =
      (w.retarded + w.advanced) * S.normalizedDefect c := by
  have hscalar := S.summed_eigen_equation w c hEigen hbranch
  have hdefect := S.defectMass_eq c hpartition
  simp only [annealedValue, normalizedDefect]
  rw [← mul_div_assoc]
  apply (eq_div_iff hmass).2
  have htransport :
      (w.transport - 1) * S.totalMass c =
        -(w.retarded + w.advanced) * S.minimumMass c := by
    nlinarith [hscalar]
  calc
    (w.transport + (w.retarded + w.advanced) / 3 - 1) * S.totalMass c =
        (w.transport - 1) * S.totalMass c +
          (w.retarded + w.advanced) * (S.totalMass c / 3) := by ring
    _ = -(w.retarded + w.advanced) * S.minimumMass c +
          (w.retarded + w.advanced) * (S.totalMass c / 3) := by rw [htransport]
    _ = (w.retarded + w.advanced) *
          (S.totalMass c / 3 - S.minimumMass c) := by ring
    _ = (w.retarded + w.advanced) * S.defectMass c := by rw [hdefect]

/-- Exact finite oscillation law with aggregate feasibility slack.  Unlike the
eigenvector specialization above, this identity applies to any nonzero-mass
candidate vector. -/
theorem annealedValue_sub_one_eq_branchWeight_mul_normalizedDefect_add_slack
    (w : Weights ℝ) (c : S.State → ℝ)
    (hpartition : ∑ r, S.fiberSum c r = S.totalMass c)
    (hbranch : ∑ m, S.branchTerm w c m =
      (w.retarded + w.advanced) * S.minimumMass c)
    (hmass : S.totalMass c ≠ 0) :
    annealedValue w - 1 =
      (w.retarded + w.advanced) * S.normalizedDefect c +
        S.normalizedSlack w c := by
  have hdefect := S.defectMass_eq c hpartition
  have hslack := S.slackMass_eq w c hbranch
  simp only [annealedValue, normalizedDefect, normalizedSlack]
  rw [← mul_div_assoc, ← add_div]
  apply (eq_div_iff hmass).2
  rw [hslack]
  calc
    (w.transport + (w.retarded + w.advanced) / 3 - 1) * S.totalMass c =
        (w.transport - 1) * S.totalMass c +
          (w.retarded + w.advanced) * (S.totalMass c / 3) := by ring
    _ = (w.retarded + w.advanced) * S.defectMass c +
          ((w.transport - 1) * S.totalMass c +
            (w.retarded + w.advanced) * S.minimumMass c) := by
      rw [hdefect]
      ring

end

end FiniteSystem

end CleanLean.KL
