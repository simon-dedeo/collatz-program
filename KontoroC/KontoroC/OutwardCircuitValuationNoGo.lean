/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSArithmeticStabilization

/-!
# Exact unique-valuation-minimum obstruction for integer circuits

In a finite integer relation, one term cannot have uniquely least `p`-adic
valuation: after dividing out the common lower power, every other term
vanishes modulo `p`, leaving the alleged unique minimum uncancelled.

The certificate below is phrased only with exact divisibility.  No floating
tropical computation or valuation implementation is trusted.  It is a
necessary consistency filter for candidate affine/resource circuits, not a
representability or orbit theorem.
-/

namespace KontoroC
namespace OutwardCircuitValuationNoGo

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- `i` is the unique term of exact divisibility level `k` among the terms
indexed by `support`: it is divisible by `p^k` but not `p^(k+1)`, while every
other supported term is divisible by `p^(k+1)`. -/
def HasUniqueDivisibilityMinimumAt
    (p k : ℕ) (support : Finset ι) (term : ι → ℤ) (i : ι) : Prop :=
  i ∈ support ∧
  (p : ℤ) ^ k ∣ term i ∧
  ¬(p : ℤ) ^ (k + 1) ∣ term i ∧
  ∀ j ∈ support, j ≠ i → (p : ℤ) ^ (k + 1) ∣ term j

/-- Exact noncancellation theorem: a unique divisibility minimum makes the
finite sum nonzero.  Primality of `p` is unnecessary once the divisibility
certificate itself is supplied. -/
theorem sum_ne_zero_of_uniqueDivisibilityMinimum
    (p k : ℕ) (support : Finset ι) (term : ι → ℤ) (i : ι)
    (hunique : HasUniqueDivisibilityMinimumAt p k support term i) :
    (∑ j ∈ support, term j) ≠ 0 := by
  intro hsum
  rcases hunique with ⟨hi, _, hnot, hother⟩
  have hrest :
      (p : ℤ) ^ (k + 1) ∣ ∑ j ∈ support.erase i, term j := by
    apply Finset.dvd_sum
    intro j hj
    have hjsupport : j ∈ support := (Finset.mem_erase.mp hj).2
    have hji : j ≠ i := by
      exact (Finset.mem_erase.mp hj).1
    exact hother j hjsupport hji
  have hdecomp := Finset.sum_erase_add support term hi
  rw [hsum] at hdecomp
  have hterm : term i = -(∑ j ∈ support.erase i, term j) := by
    linarith
  apply hnot
  rw [hterm]
  exact (dvd_neg.mpr hrest)

/-- Contrapositive worker form: every exact zero-sum relation rejects every
claimed unique `p`-adic minimum certificate. -/
theorem no_uniqueDivisibilityMinimum_of_sum_eq_zero
    (p k : ℕ) (support : Finset ι) (term : ι → ℤ) (i : ι)
    (hsum : ∑ j ∈ support, term j = 0) :
    ¬HasUniqueDivisibilityMinimumAt p k support term i := by
  intro hunique
  exact (sum_ne_zero_of_uniqueDivisibilityMinimum
    p k support term i hunique) hsum

/-- Two-adic specialization used by the paired-valuation preflight. -/
theorem no_unique_twoAdic_minimum_of_sum_eq_zero
    (k : ℕ) (support : Finset ι) (term : ι → ℤ) (i : ι)
    (hsum : ∑ j ∈ support, term j = 0) :
    ¬HasUniqueDivisibilityMinimumAt 2 k support term i :=
  no_uniqueDivisibilityMinimum_of_sum_eq_zero 2 k support term i hsum

/-- Three-adic specialization used by the paired-valuation preflight. -/
theorem no_unique_threeAdic_minimum_of_sum_eq_zero
    (k : ℕ) (support : Finset ι) (term : ι → ℤ) (i : ι)
    (hsum : ∑ j ∈ support, term j = 0) :
    ¬HasUniqueDivisibilityMinimumAt 3 k support term i :=
  no_uniqueDivisibilityMinimum_of_sum_eq_zero 3 k support term i hsum

/-- Affine-circuit adapter: coefficients times proposed values are the terms
to which the unique-minimum obstruction is applied. -/
theorem affine_sum_ne_zero_of_uniqueDivisibilityMinimum
    (p k : ℕ) (support : Finset ι)
    (coefficient value : ι → ℤ) (i : ι)
    (hunique : HasUniqueDivisibilityMinimumAt p k support
      (fun j => coefficient j * value j) i) :
    (∑ j ∈ support, coefficient j * value j) ≠ 0 :=
  sum_ne_zero_of_uniqueDivisibilityMinimum p k support
    (fun j => coefficient j * value j) i hunique

end OutwardCircuitValuationNoGo
end KontoroC
