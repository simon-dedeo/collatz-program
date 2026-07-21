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

end WeightedTail

end CleanLean.KL
