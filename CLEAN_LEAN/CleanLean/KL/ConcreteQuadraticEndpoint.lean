/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CoarseMinimum
import CleanLean.KL.QuadraticDefect

/-!
# The concrete coarse-minimum tower implies the KL endpoint

This file joins the scalar reciprocal telescope to the actual dependent
family of residue profiles.  For outer index `k`, profile `x k j` lives on
`State j`; the selected exact eigenvector is `x k (k+2)`, and profiles down to
precision two are its successive coarse minima.

The one intentionally open premise is a uniformly positive quadratic
normalized-slack gain at every genuine coarse step.  Nothing here replaces
that premise by first-stage fixed-vector frustration or by a statement about
an unrelated scalar sequence.
-/

namespace CleanLean.KL

namespace ResidueSystem

noncomputable section

/-- A precision-indexed family consists of literal successive coarse minima
between levels two and `k+2`. -/
def IsCoarseMinimumTower
    (x : (k p : ℕ) → State p → ℝ) : Prop :=
  ∀ k j, j < k →
    x k (j + 2) = coarseMinimum (j + 2) (x k (j + 3))

/-- The fully concrete endpoint reduction.  A selected exact KL eigenvector
at level `k+2`, its actual coarse-minimum tower, and any stage-dependent
quadratic slack gains bounded below by `a₀>0` force `lambda_k → 2`.

The positivity and upper-bound hypotheses are stated for the normalized
terminal excess itself.  They are independent finite-profile obligations,
not hidden consequences of the pressure premise. -/
theorem klLambda_tendsto_two_of_coarseMinimumTower
    (a₀ : ℝ) (a : ℕ → ℕ → ℝ) (lam : ℕ → ℝ)
    (x : (k p : ℕ) → State p → ℝ)
    (ha₀ : 0 < a₀)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (htower : IsCoarseMinimumTower x)
    (hmass : ∀ k j, j ≤ k →
      (system (j + 2)).totalMass (x k (j + 2)) ≠ 0)
    (hexcessPos : ∀ k j, j ≤ k →
      0 < 3 * (system (j + 2)).normalizedDefect (x k (j + 2)))
    (hexcessOne : ∀ k j, j ≤ k →
      3 * (system (j + 2)).normalizedDefect (x k (j + 2)) ≤ 1)
    (hcoeff : ∀ k j, j < k → a₀ ≤ a k j)
    (hfixed : ∀ k s, x k (k + 2) s =
      (system (k + 2)).operator (klWeights (lam k)) (x k (k + 2)) s)
    (hgain : ∀ k j, j < k →
      HasQuadraticCoarseSlackGainWith (a k j) (j + 2)
        (klWeights (lam k)) (x k (j + 3))) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  let e : ℕ → ℕ → ℝ := fun k j =>
    3 * (system (j + 2)).normalizedDefect (x k (j + 2))
  apply klLambda_tendsto_two_of_uniform_reverse_quadratic_terminalExcess_growth
    a₀ a lam e ha₀ hlam
  · intro k j hj
    exact hexcessPos k j hj
  · intro k j hj
    exact hexcessOne k j hj
  · exact hcoeff
  · intro k j hj
    have hbranch : 0 <
        (klWeights (lam k)).retarded + (klWeights (lam k)).advanced := by
      have hlamPos : 0 < lam k := lt_of_lt_of_le (by norm_num) (hlam k).1
      exact add_pos (Real.rpow_pos_of_pos hlamPos _)
        (Real.rpow_pos_of_pos hlamPos _)
    have hfineMass :
        (system (j + 3)).totalMass (x k (j + 3)) ≠ 0 := by
      simpa only [Nat.add_assoc] using hmass k (j + 1) (by omega)
    have hcoarseMass :
        (system (j + 2)).totalMass (coarseMinimum (j + 2) (x k (j + 3))) ≠ 0 := by
      rw [← htower k j hj]
      exact hmass k j hj.le
    have hstep := terminalExcess_quadratic_growth_of_coarseSlackGainWith
      (a k j) (j + 2) (by omega) (klWeights (lam k)) (x k (j + 3))
      hbranch hfineMass hcoarseMass (hgain k j hj)
    rw [← htower k j hj] at hstep
    exact hstep
  · intro k
    change annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) *
          ((3 * (system (k + 2)).normalizedDefect (x k (k + 2))) / 3)
    have hid := concrete_oscillation_identity
      (k + 2) (by omega) (klWeights (lam k)) (x k (k + 2))
      (hfixed k) (hmass k k le_rfl)
    change annealedKL (lam k) - 1 = _ at hid
    nlinarith

end

end ResidueSystem

end CleanLean.KL
