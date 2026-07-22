/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The two-Kraft obstruction to a complete outward valuation ISA

There are two probability weights on a positive valuation letter `k`:
`2^-k` and `3*4^-k`.  A prefix code satisfies a Kraft bound for either
weight.  If it is complete for the first weight while every leaf has outward
slope, the second weight strictly dominates the first leaf by leaf and
violates its own Kraft bound.

This file checks the two exact geometric distributions, the leafwise
outwardness comparison, and finite/countable abstract two-Kraft
contradictions.  The tree-theoretic fact that a particular code has both
Kraft bounds remains a separate reusable interface.
-/

namespace KontoroC
namespace TwoKraftObstruction

open scoped BigOperators

/-- Ordinary cylinder probability of the positive valuation `n+1`. -/
noncomputable def pLetter (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- Tilted cylinder probability of the same valuation. -/
noncomputable def qLetter (n : ℕ) : ℝ := 3 / (4 : ℝ) ^ (n + 1)

/-- First half of TK1. -/
theorem hasSum_pLetter : HasSum pLetter 1 := by
  have h := (hasSum_geometric_of_norm_lt_one
    (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_left (1 / 2 : ℝ)
  have hfun : pLetter = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    simp only [pLetter, pow_succ]
    ring
  rw [← hfun] at h
  have hend : (1 / 2 : ℝ) * (1 - 1 / 2)⁻¹ = 1 := by norm_num
  rw [hend] at h
  exact h

/-- Second half of TK1. -/
theorem hasSum_qLetter : HasSum qLetter 1 := by
  have h := (hasSum_geometric_of_norm_lt_one
    (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)).mul_left (3 / 4 : ℝ)
  have hfun : qLetter = fun n => (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ n := by
    funext n
    simp only [qLetter, pow_succ, div_pow]
    field_simp
    ring
  rw [← hfun] at h
  have hend : (3 / 4 : ℝ) * (1 - 1 / 4)⁻¹ = 1 := by norm_num
  rw [hend] at h
  exact h

theorem tsum_pLetter : ∑' n, pLetter n = 1 := hasSum_pLetter.tsum_eq
theorem tsum_qLetter : ∑' n, qLetter n = 1 := hasSum_qLetter.tsum_eq

/-- Ordinary cylinder weight of a valuation word. -/
noncomputable def pWeight (w : List ℕ) : ℝ := 1 / (2 : ℝ) ^ w.sum

/-- Tilted cylinder weight of a valuation word. -/
noncomputable def qWeight (w : List ℕ) : ℝ :=
  (3 : ℝ) ^ w.length / (4 : ℝ) ^ w.sum

theorem pWeight_append (u v : List ℕ) :
    pWeight (u ++ v) = pWeight u * pWeight v := by
  simp only [pWeight, List.sum_append, pow_add]
  field_simp

theorem qWeight_append (u v : List ℕ) :
    qWeight (u ++ v) = qWeight u * qWeight v := by
  simp only [qWeight, List.length_append, List.sum_append, pow_add]
  field_simp

/-- The tilted weight strictly dominates the ordinary weight exactly in the
outward direction needed here. -/
theorem pWeight_lt_qWeight_of_outward (w : List ℕ)
    (hout : 2 ^ w.sum < 3 ^ w.length) : pWeight w < qWeight w := by
  have houtR : (2 : ℝ) ^ w.sum < (3 : ℝ) ^ w.length := by
    exact_mod_cast hout
  have hp : pWeight w = (2 : ℝ) ^ w.sum / (4 : ℝ) ^ w.sum := by
    simp only [pWeight]
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    field_simp
  rw [hp, qWeight]
  exact (div_lt_div_iff_of_pos_right (by positivity)).2 houtR

/-- Finite abstract two-Kraft contradiction.  Prefix-freeness is used only
to supply the two mass bounds, so the logical core is kept explicit. -/
theorem finite_two_kraft_contradiction {Code : Type*}
    (C : Finset Code) (p q : Code → ℝ)
    (hcomplete : ∑ x ∈ C, p x = 1)
    (hqKraft : ∑ x ∈ C, q x ≤ 1)
    (hstrict : ∀ x ∈ C, p x < q x)
    (hne : C.Nonempty) : False := by
  have hlt : (∑ x ∈ C, p x) < ∑ x ∈ C, q x := by
    apply Finset.sum_lt_sum
    · intro x hx
      exact le_of_lt (hstrict x hx)
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, hstrict x hx⟩
  linarith

/-- Countable abstract two-Kraft contradiction, suitable for a countable
prefix code over the positive valuation alphabet. -/
theorem countable_two_kraft_contradiction {Code : Type*}
    (p q : Code → ℝ) (hpSum : Summable p) (hqSum : Summable q)
    (hcomplete : ∑' x, p x = 1) (hqKraft : ∑' x, q x ≤ 1)
    (hle : ∀ x, p x ≤ q x) (x₀ : Code) (hstrict : p x₀ < q x₀) : False := by
  have hlt : (∑' x, p x) < ∑' x, q x :=
    Summable.tsum_lt_tsum hle hstrict hpSum hqSum
  linarith

/-- Concrete finite endpoint: if both Kraft bounds are available for a
nonempty valuation-word code and every leaf is outward, completeness is
impossible. -/
theorem no_finite_complete_uniformly_outward
    (C : Finset (List ℕ)) (hne : C.Nonempty)
    (hcomplete : ∑ w ∈ C, pWeight w = 1)
    (hqKraft : ∑ w ∈ C, qWeight w ≤ 1)
    (hout : ∀ w ∈ C, 2 ^ w.sum < 3 ^ w.length) : False := by
  exact finite_two_kraft_contradiction C pWeight qWeight hcomplete hqKraft
    (fun w hw => pWeight_lt_qWeight_of_outward w (hout w hw)) hne

end TwoKraftObstruction
end KontoroC
