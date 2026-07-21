/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteQuadraticEndpoint
import CleanLean.KL.CountingTransfer
import CleanLean.KL.StrictLift

/-!
# From the concrete coarse-minimum tower to predecessor counting

This file closes the compositional seam between the selected-profile endpoint
and the already formalized KL counting theorem.  The mathematical premise is
still the uniform positive quadratic slack gain along the literal tower.
Nothing here proves that premise.
-/

namespace CleanLean.KL

open Filter
open CleanLean.Collatz
open scoped BigOperators

namespace ResidueSystem

noncomputable section

/-- The fully composed conditional endpoint.  Positive exact fixed vectors,
their literal successive coarse minima, and a uniformly positive quadratic
normalized-slack gain imply `X^(1-epsilon)` one-halving Syracuse predecessor
counting for every positive target not divisible by three.

Unlike `klLambda_tendsto_two_of_coarseMinimumTower`, this theorem explicitly
normalizes each selected fixed vector into a finite KL feasibility witness and
invokes the repaired finite-feasibility-to-counting transfer. -/
theorem almostLinearPredecessorCounting_of_coarseMinimumTower
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
    (hpositive : ∀ k s, 0 < x k (k + 2) s)
    (hfixed : ∀ k s, x k (k + 2) s =
      (system (k + 2)).operator (klWeights (lam k)) (x k (k + 2)) s)
    (hgain : ∀ k j, j < k →
      HasQuadraticCoarseSlackGainWith (a k j) (j + 2)
        (klWeights (lam k)) (x k (j + 3))) :
    AlmostLinearPredecessorCounting := by
  have hlamLimit : Tendsto lam atTop (nhds 2) :=
    klLambda_tendsto_two_of_coarseMinimumTower
      a₀ a lam x ha₀ hlam htower hmass hexcessPos hexcessOne hcoeff hfixed hgain
  have hgammaLimit : Tendsto (fun k => klExponent (lam k)) atTop (nhds 1) :=
    klExponent_tendsto_one lam hlamLimit
  intro target htarget htarget3 epsilon hepsilon
  have hgammaNear :
      ∀ᶠ k : ℕ in atTop, 1 - epsilon < klExponent (lam k) :=
    hgammaLimit.eventually (Ioi_mem_nhds (by linarith))
  have hlamStrict : ∀ᶠ k : ℕ in atTop, 1 < lam k :=
    hlamLimit.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨k, hgamma, hlamOne⟩ := (hgammaNear.and hlamStrict).exists
  have hfeasible : LevelFeasible (k + 2) (lam k) := by
    letI : Nonempty (system (k + 2)).State := by
      change Nonempty (State (k + 2))
      exact ⟨(0 : State (k + 2))⟩
    obtain ⟨z, hz⟩ := (system (k + 2)).feasible_of_positive_subeigen
      (klWeights (lam k)) (x k (k + 2)) (hpositive k)
      (fun s => (hfixed k s).le)
    exact ⟨z, hz⟩
  have hcount := hasPredecessorExponent_of_levelFeasible
    (k := k + 2) (by omega) hlamOne (hlam k).2 hfeasible
    htarget htarget3
  exact hasPredecessorExponent_mono hgamma hcount

/-- Almost-linear predecessor counting from intermittent coarse-minimum
pressure.  Compared with `almostLinearPredecessorCounting_of_coarseMinimumTower`,
this requires no uniform positive gain: the effective gains need only be
nonnegative and have divergent total `∑ a/(1+a)`. -/
theorem almostLinearPredecessorCounting_of_coarseMinimumTower_divergentGain
    (a : ℕ → ℕ → ℝ) (lam : ℕ → ℝ)
    (x : (k p : ℕ) → State p → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (htower : IsCoarseMinimumTower x)
    (hmass : ∀ k j, j ≤ k →
      (system (j + 2)).totalMass (x k (j + 2)) ≠ 0)
    (hexcessPos : ∀ k j, j ≤ k →
      0 < 3 * (system (j + 2)).normalizedDefect (x k (j + 2)))
    (hexcessOne : ∀ k j, j ≤ k →
      3 * (system (j + 2)).normalizedDefect (x k (j + 2)) ≤ 1)
    (hcoeff : ∀ k j, j < k → 0 ≤ a k j)
    (hpositive : ∀ k s, 0 < x k (k + 2) s)
    (hfixed : ∀ k s, x k (k + 2) s =
      (system (k + 2)).operator (klWeights (lam k)) (x k (k + 2)) s)
    (hgain : ∀ k j, j < k →
      HasQuadraticCoarseSlackGainWith (a k j) (j + 2)
        (klWeights (lam k)) (x k (j + 3)))
    (hdiv : Tendsto
      (fun k => ∑ j ∈ Finset.range k, a k j / (1 + a k j))
      atTop atTop) :
    AlmostLinearPredecessorCounting := by
  have hlamLimit : Tendsto lam atTop (nhds 2) :=
    klLambda_tendsto_two_of_coarseMinimumTower_divergentGain
      a lam x hlam htower hmass hexcessPos hexcessOne hcoeff hfixed hgain hdiv
  have hgammaLimit : Tendsto (fun k => klExponent (lam k)) atTop (nhds 1) :=
    klExponent_tendsto_one lam hlamLimit
  intro target htarget htarget3 epsilon hepsilon
  have hgammaNear :
      ∀ᶠ k : ℕ in atTop, 1 - epsilon < klExponent (lam k) :=
    hgammaLimit.eventually (Ioi_mem_nhds (by linarith))
  have hlamStrict : ∀ᶠ k : ℕ in atTop, 1 < lam k :=
    hlamLimit.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨k, hgamma, hlamOne⟩ := (hgammaNear.and hlamStrict).exists
  have hfeasible : LevelFeasible (k + 2) (lam k) := by
    letI : Nonempty (system (k + 2)).State := by
      change Nonempty (State (k + 2))
      exact ⟨(0 : State (k + 2))⟩
    obtain ⟨z, hz⟩ := (system (k + 2)).feasible_of_positive_subeigen
      (klWeights (lam k)) (x k (k + 2)) (hpositive k)
      (fun s => (hfixed k s).le)
    exact ⟨z, hz⟩
  have hcount := hasPredecessorExponent_of_levelFeasible
    (k := k + 2) (by omega) hlamOne (hlam k).2 hfeasible
    htarget htarget3
  exact hasPredecessorExponent_mono hgamma hcount

/-- Almost-linear counting from net gain on multi-step precision checkpoints
of the literal tower.  No sign condition is imposed between checkpoints. -/
theorem almostLinearPredecessorCounting_of_coarseMinimumTower_checkpointGain
    (m : ℕ → ℕ) (q : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (lam : ℕ → ℝ) (x : (k p : ℕ) → State p → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (htower : IsCoarseMinimumTower x)
    (hqBound : ∀ k i, i ≤ m k → q k i ≤ k)
    (hqMono : ∀ k i, i < m k → q k i < q k (i + 1))
    (hqTop : ∀ k, q k (m k) = k)
    (hmass : ∀ k j, j ≤ k →
      (system (j + 2)).totalMass (x k (j + 2)) ≠ 0)
    (hexcessPos : ∀ k j, j ≤ k →
      0 < 3 * (system (j + 2)).normalizedDefect (x k (j + 2)))
    (hexcessOne : ∀ k j, j ≤ k →
      3 * (system (j + 2)).normalizedDefect (x k (j + 2)) ≤ 1)
    (hcoeff : ∀ k i, i < m k → 0 ≤ a k i)
    (hpositive : ∀ k s, 0 < x k (k + 2) s)
    (hfixed : ∀ k s, x k (k + 2) s =
      (system (k + 2)).operator (klWeights (lam k)) (x k (k + 2)) s)
    (hblock : ∀ k i, i < m k →
      3 * (system (q k (i + 1) + 2)).normalizedDefect
          (x k (q k (i + 1) + 2)) +
        a k i *
          (3 * (system (q k (i + 1) + 2)).normalizedDefect
            (x k (q k (i + 1) + 2))) ^ 2 ≤
      3 * (system (q k i + 2)).normalizedDefect
        (x k (q k i + 2)))
    (hdiv : Tendsto
      (fun k => ∑ i ∈ Finset.range (m k), a k i / (1 + a k i))
      atTop atTop) :
    AlmostLinearPredecessorCounting := by
  have hlamLimit : Tendsto lam atTop (nhds 2) :=
    klLambda_tendsto_two_of_coarseMinimumTower_checkpointGain
      m q a lam x hlam htower hqBound hqMono hqTop hmass hexcessPos hexcessOne
        hcoeff hfixed hblock hdiv
  have hgammaLimit : Tendsto (fun k => klExponent (lam k)) atTop (nhds 1) :=
    klExponent_tendsto_one lam hlamLimit
  intro target htarget htarget3 epsilon hepsilon
  have hgammaNear :
      ∀ᶠ k : ℕ in atTop, 1 - epsilon < klExponent (lam k) :=
    hgammaLimit.eventually (Ioi_mem_nhds (by linarith))
  have hlamStrict : ∀ᶠ k : ℕ in atTop, 1 < lam k :=
    hlamLimit.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨k, hgamma, hlamOne⟩ := (hgammaNear.and hlamStrict).exists
  have hfeasible : LevelFeasible (k + 2) (lam k) := by
    letI : Nonempty (system (k + 2)).State := by
      change Nonempty (State (k + 2))
      exact ⟨(0 : State (k + 2))⟩
    obtain ⟨z, hz⟩ := (system (k + 2)).feasible_of_positive_subeigen
      (klWeights (lam k)) (x k (k + 2)) (hpositive k)
      (fun s => (hfixed k s).le)
    exact ⟨z, hz⟩
  have hcount := hasPredecessorExponent_of_levelFeasible
    (k := k + 2) (by omega) hlamOne (hlam k).2 hfeasible
    htarget htarget3
  exact hasPredecessorExponent_mono hgamma hcount

end

end ResidueSystem

end CleanLean.KL
