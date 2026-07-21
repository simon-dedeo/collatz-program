/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.KLWeights
import CleanLean.KL.LimitBridge

/-!
# The defect-to-`lambda = 2` bridge

This is the exact analytic step after the weighted oscillation defect is made
to vanish.  Existence and selection of the critical eigenfunctions, and the
localization estimate that makes their defects vanish, remain separate
obligations.
-/

namespace CleanLean.KL

theorem klWeightedDefect_mul_tendsto_zero
    (lam delta : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k =>
      mul_nonneg (klBranchWeightSum_nonneg (le_trans (by norm_num) (hlam k).1))
        (hdelta0 k)
  · exact Filter.Eventually.of_forall fun k =>
      mul_le_mul_of_nonneg_right (klBranchWeightSum_le (hlam k)) (hdelta0 k)
  · simpa using hdelta.const_mul (5 / 2 : ℝ)

/-- Once the concrete oscillation identity holds and its weighted defect
vanishes, the critical parameters converge to two. -/
theorem klLambda_tendsto_two_of_defect
    (lam delta : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  have hprod := klWeightedDefect_mul_tendsto_zero lam delta hlam hdelta0 hdelta
  have hs : Filter.Tendsto (fun k => annealedKL (lam k))
      Filter.atTop (nhds 1) := by
    have hadd := hprod.add_const 1
    have heq :
        (fun k => ((klWeights (lam k)).retarded +
          (klWeights (lam k)).advanced) * delta k + 1) =ᶠ[Filter.atTop]
          (fun k => annealedKL (lam k)) := Filter.Eventually.of_forall fun k => by
      have hi := hidentity k
      dsimp
      linarith
    simpa using hadd.congr' heq
  exact tendsto_two_of_annealed_tendsto_one annealedKL lam
    annealedKL_strictAntiOn annealedKL_two hlam hs

/-- The endpoint bridge for merely feasible vectors.  Vanishing normalized
fiber defect and vanishing aggregate normalized slack together force the KL
parameters to converge to two. -/
theorem klLambda_tendsto_two_of_defect_and_slack
    (lam delta sigma : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0))
    (hsigma : Filter.Tendsto sigma Filter.atTop (nhds 0))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k + sigma k) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  have hprod := klWeightedDefect_mul_tendsto_zero lam delta hlam hdelta0 hdelta
  have hsum : Filter.Tendsto
      (fun k => ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k + sigma k)
      Filter.atTop (nhds 0) := by
    simpa using hprod.add hsigma
  have hs : Filter.Tendsto (fun k => annealedKL (lam k))
      Filter.atTop (nhds 1) := by
    have hadd := hsum.add_const 1
    have heq :
        (fun k => ((klWeights (lam k)).retarded +
          (klWeights (lam k)).advanced) * delta k + sigma k + 1) =ᶠ[Filter.atTop]
          (fun k => annealedKL (lam k)) := Filter.Eventually.of_forall fun k => by
      have hi := hidentity k
      dsimp
      linarith
    simpa using hadd.congr' heq
  exact tendsto_two_of_annealed_tendsto_one annealedKL lam
    annealedKL_strictAntiOn annealedKL_two hlam hs

/-- Terminal `L¹` localization implies vanishing min-defect through the lower
comparison `2 delta ≤ Delta`; adding vanishing aggregate slack then forces the
KL endpoint. -/
theorem klLambda_tendsto_two_of_terminalVariation_and_slack
    (lam delta terminalVariation sigma : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hcompare : ∀ k, 2 * delta k ≤ terminalVariation k)
    (hterminal : Filter.Tendsto terminalVariation Filter.atTop (nhds 0))
    (hsigma : Filter.Tendsto sigma Filter.atTop (nhds 0))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k + sigma k) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  have hdeltaUpper : ∀ k, delta k ≤ terminalVariation k := by
    intro k
    linarith [hcompare k, hdelta0 k]
  have hdelta : Filter.Tendsto delta Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall hdelta0
    · exact Filter.Eventually.of_forall hdeltaUpper
    · exact hterminal
  exact klLambda_tendsto_two_of_defect_and_slack lam delta sigma hlam
    hdelta0 hdelta hsigma hidentity

end CleanLean.KL
