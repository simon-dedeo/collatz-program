/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import KontoroC.PrefixKraft

/-!
# The two-Kraft obstruction to a complete outward valuation ISA

There are two probability weights on a positive valuation letter `k`:
`2^-k` and `3*4^-k`.  A prefix code satisfies a Kraft bound for either
weight.  If it is complete for the first weight while every leaf has outward
slope, the second weight strictly dominates the first leaf by leaf and
violates its own Kraft bound.

This file checks the two exact geometric distributions, the leafwise
outwardness comparison, finite/countable abstract two-Kraft contradictions,
and the full finite prefix-code theorem.  The two Kraft bounds are obtained
from self-delimiting uniform encodings in `PrefixKraft`.
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

/-- TK2 for the ordinary valuation-cylinder law, derived from prefix-freeness
rather than assumed as an interface. -/
theorem finite_prefix_pKraft (C : Finset (List ℕ))
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixKraft.PrefixFree (C : Set (List ℕ))) :
    ∑ w ∈ C, pWeight w ≤ 1 := by
  simpa [pWeight, one_div, inv_pow] using
    PrefixKraft.pKraft_finite C hpos hne hpf

/-- TK2 for the tilted valuation-cylinder law.  Each valuation letter is
expanded into three possible terminals in a four-symbol self-delimiting
code, giving exactly `3^length / 4^sum`. -/
theorem finite_prefix_qKraft (C : Finset (List ℕ))
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixKraft.PrefixFree (C : Set (List ℕ))) :
    ∑ w ∈ C, qWeight w ≤ 1 := by
  simpa [qWeight] using PrefixKraft.qKraft_finite C hpos hne hpf

/-- Full finite two-Kraft obstruction: no nonempty prefix-free positive
valuation code can simultaneously be complete for ordinary cylinders and
outward at every leaf. -/
theorem no_finite_prefix_complete_uniformly_outward
    (C : Finset (List ℕ)) (hC : C.Nonempty)
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixKraft.PrefixFree (C : Set (List ℕ)))
    (hcomplete : ∑ w ∈ C, pWeight w = 1)
    (hout : ∀ w ∈ C, 2 ^ w.sum < 3 ^ w.length) : False := by
  exact no_finite_complete_uniformly_outward C hC hcomplete
    (finite_prefix_qKraft C hpos hne hpf) hout

/-- Multiplicative outward factor of a valuation word. -/
noncomputable def outwardFactor (w : List ℕ) : ℝ :=
  (3 : ℝ) ^ w.length / (2 : ℝ) ^ w.sum

theorem qWeight_eq_pWeight_mul_outwardFactor (w : List ℕ) :
    qWeight w = pWeight w * outwardFactor w := by
  simp only [qWeight, pWeight, outwardFactor]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  field_simp

/-- Quantitative two-Kraft bound.  If every leaf expands by at least
`lambda > 0`, its ordinary cylinder mass is at most `1 / lambda`. -/
theorem finite_uniform_outward_mass_bound
    (C : Finset (List ℕ))
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixKraft.PrefixFree (C : Set (List ℕ)))
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hout : ∀ w ∈ C, lambda ≤ outwardFactor w) :
    ∑ w ∈ C, pWeight w ≤ 1 / lambda := by
  have hpoint : ∀ w ∈ C, lambda * pWeight w ≤ qWeight w := by
    intro w hw
    rw [qWeight_eq_pWeight_mul_outwardFactor, mul_comm lambda]
    exact mul_le_mul_of_nonneg_left (hout w hw) (by
      simp only [pWeight]
      positivity)
  have hsum : ∑ w ∈ C, lambda * pWeight w ≤ ∑ w ∈ C, qWeight w :=
    Finset.sum_le_sum fun w hw => hpoint w hw
  have hq := finite_prefix_qKraft C hpos hne hpf
  have hmass : lambda * (∑ w ∈ C, pWeight w) ≤ 1 := by
    rw [Finset.mul_sum]
    exact hsum.trans hq
  exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hmass)

end TwoKraftObstruction
end KontoroC
