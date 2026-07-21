/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# From the annealed root law to the endpoint

This file records the compact one-dimensional argument used after the
oscillation defect has been shown to vanish.  It does not assume a numerical
fit: a strictly decreasing annealed function on `[1,2]`, whose value at two
is one, forces any sequence with annealed values tending to one to converge
to two.
-/

namespace CleanLean.KL

/-- Root-selection at the right endpoint of a compact interval. -/
theorem tendsto_two_of_annealed_tendsto_one
    (s : ℝ → ℝ) (lam : ℕ → ℝ)
    (hs : StrictAntiOn s (Set.Icc (1 : ℝ) 2))
    (hs2 : s 2 = 1)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hlim : Filter.Tendsto (fun k => s (lam k)) Filter.atTop (nhds 1)) :
    Filter.Tendsto lam Filter.atTop (nhds 2) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd0 : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε := by
    have hdle : d ≤ ε / 2 := min_le_left _ _
    linarith
  let x : ℝ := 2 - d
  have hx : x ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · have hdle : d ≤ 1 / 2 := min_le_right _ _
      dsimp [x]
      linarith
    · dsimp [x]
      linarith
  have h2 : (2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := by norm_num
  have hx2 : x < 2 := by dsimp [x]; linarith
  have hgap : 0 < s x - 1 := by
    have hstrict := hs hx h2 hx2
    rw [hs2] at hstrict
    linarith
  rcases Metric.tendsto_atTop.1 hlim (s x - 1) hgap with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hnear := hN n hn
  rw [Real.dist_eq] at hnear
  have hslt : s (lam n) < s x := by
    have habs : |s (lam n) - 1| < s x - 1 := hnear
    have hu := (abs_lt.1 habs).2
    linarith
  have hxlam : x < lam n := by
    by_contra hnot
    have hle : lam n ≤ x := le_of_not_gt hnot
    have hanti : s x ≤ s (lam n) := hs.antitoneOn (hlam n) hx hle
    exact (not_lt_of_ge hanti) hslt
  rw [Real.dist_eq, abs_of_nonpos]
  · dsimp [x] at hxlam
    linarith
  · exact sub_nonpos.2 (hlam n).2

end CleanLean.KL
