/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# The weighted-tail reduction

This is the finite inequality at the heart of corrected Proposition R'.  The
weights are arbitrary probability weights; in the KL application they are
the normalized fiber-mean eigenfunction masses, not Haar weights.
-/

namespace CleanLean.KL

open scoped BigOperators

section WeightedTail

variable {ι : Type} [Fintype ι]

/-- Mass of the strict `t`-tail of `o` under weights `ν`. -/
noncomputable def tailMass (ν o : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if t < o i then ν i else 0

/-- The normalization used by the KL oscillation defect. -/
noncomputable def weightedDefect (ν u : ι → ℝ) : ℝ :=
  (∑ i, ν i * u i) / 3

/-- Correct finite weighted-tail estimate.  No counting or Haar measure occurs
in the statement. -/
theorem weightedDefect_le_tail
    (ν u o : ι → ℝ) (t : ℝ)
    (hν : ∀ i, 0 ≤ ν i)
    (huo : ∀ i, u i ≤ o i)
    (hu1 : ∀ i, u i ≤ 1)
    (ht : 0 ≤ t)
    (hprob : ∑ i, ν i = 1) :
    weightedDefect ν u ≤ (t + tailMass ν o t) / 3 := by
  classical
  have hpoint : ∀ i : ι,
      ν i * u i ≤ ν i * t + if t < o i then ν i else 0 := by
    intro i
    by_cases hi : t < o i
    · have hmul : ν i * u i ≤ ν i := by
        simpa using mul_le_mul_of_nonneg_left (hu1 i) (hν i)
      have : ν i ≤ ν i * t + ν i := by
        nlinarith [mul_nonneg (hν i) ht]
      simpa [hi] using hmul.trans this
    · have hot : o i ≤ t := le_of_not_gt hi
      have hut : u i ≤ t := (huo i).trans hot
      simpa [hi] using mul_le_mul_of_nonneg_left hut (hν i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
  have hfirst : (∑ i : ι, ν i * t) = t := by
    rw [← Finset.sum_mul, hprob, one_mul]
  have hsecond : (∑ i : ι, if t < o i then ν i else 0) = tailMass ν o t := by
    rfl
  rw [Finset.sum_add_distrib, hfirst, hsecond] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num)

/-- Asymptotic form of corrected Proposition R': if every fixed positive
oscillation tail vanishes and `δ` satisfies the finite weighted-tail estimate,
then `δ` vanishes.  The finite state spaces may vary with `k`; all of that
geometry is compressed into `tail`. -/
theorem tendsto_zero_of_weighted_tail
    (δ : ℕ → ℝ) (tail : ℕ → ℝ → ℝ)
    (hδ : ∀ k, 0 ≤ δ k)
    (hbound : ∀ k t, 0 ≤ t → δ k ≤ (t + tail k t) / 3)
    (htail : ∀ t, 0 < t → Filter.Tendsto (fun k => tail k t)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let t : ℝ := 3 * ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  rcases Metric.tendsto_atTop.1 (htail t ht) t ht with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  have htail_lt : tail n t < t := by
    rw [Real.dist_eq, sub_zero, abs_lt] at hdist
    exact hdist.2
  have hδle := hbound n t ht.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδ n)]
  dsimp [t] at htail_lt hδle
  linarith

/-- A geometric restricted-pressure estimate is more than enough for the tail
hypothesis in `tendsto_zero_of_weighted_tail`. -/
theorem tail_tendsto_zero_of_geometric_bound
    (tail : ℕ → ℝ) (C q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htail0 : ∀ k, 0 ≤ tail k)
    (htail : ∀ k, tail k ≤ C * q ^ k) :
    Filter.Tendsto tail Filter.atTop (nhds 0) := by
  have hgeom : Filter.Tendsto (fun k : ℕ => C * q ^ k)
      Filter.atTop (nhds 0) :=
    by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall htail0)
    (Filter.Eventually.of_forall htail) hgeom

/-- Complete abstract pressure-to-defect interface: a separate geometric bound
may be supplied for each fixed positive threshold.  The concrete KL work is to
derive these hypotheses from a uniform product-cone/pressure certificate. -/
theorem tendsto_zero_of_geometric_weighted_tails
    (δ : ℕ → ℝ) (tail : ℕ → ℝ → ℝ)
    (hδ : ∀ k, 0 ≤ δ k)
    (hbound : ∀ k t, 0 ≤ t → δ k ≤ (t + tail k t) / 3)
    (htail0 : ∀ k t, 0 ≤ tail k t)
    (hgeo : ∀ t, 0 < t → ∃ C q : ℝ,
      0 ≤ q ∧ q < 1 ∧ ∀ k, tail k t ≤ C * q ^ k) :
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  apply tendsto_zero_of_weighted_tail δ tail hδ hbound
  intro t ht
  obtain ⟨C, q, hq0, hq1, htail⟩ := hgeo t ht
  exact tail_tendsto_zero_of_geometric_bound
    (fun k => tail k t) C q hq0 hq1 (fun k => htail0 k t) htail

end WeightedTail

end CleanLean.KL
