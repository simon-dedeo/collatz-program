/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LaurentCoboundaryNoGo

/-!
# Rational period-three coboundaries reduce to Laurent support

This file formalizes the denominator-divisibility core of QM69--QM71 in the
homogeneous univariate chart.  It deliberately stops before representing a
quotient with monomial denominator as the `Finsupp` used by the Laurent
no-go theorem.
-/

namespace KontoroC
namespace RationalCoboundaryReduction

open Polynomial

/-- Diagonal substitution `P(z) ↦ P(r*z)`. -/
noncomputable def scalePoly (r : ℚ) (P : ℚ[X]) : ℚ[X] :=
  P.comp (C r * X)

theorem scalePoly_coeff (r : ℚ) (P : ℚ[X]) (n : ℕ) :
    (scalePoly r P).coeff n = P.coeff n * r ^ n := by
  exact Polynomial.comp_C_mul_X_coeff

theorem scalePoly_ne_zero (r : ℚ) (P : ℚ[X])
    (hr : r ≠ 0) (hP : P ≠ 0) :
    scalePoly r P ≠ 0 := by
  rw [scalePoly]
  exact (Polynomial.comp_C_mul_X_eq_zero_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr)).not.mpr hP

theorem scalePoly_natDegree (r : ℚ) (P : ℚ[X]) (hr : r ≠ 0) :
    (scalePoly r P).natDegree = P.natDegree := by
  rw [scalePoly, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X r hr, mul_one]

theorem scalePoly_isCoprime (r : ℚ) {N D : ℚ[X]}
    (hcop : IsCoprime N D) :
    IsCoprime (scalePoly r N) (scalePoly r D) := by
  simpa [scalePoly] using hcop.map (Polynomial.compRingHom (C r * X))

/-- QM69c: the cleared reduced rational equation forces the scaled
denominator to divide the original denominator.  `B` packages the
parenthesized polynomial on the right of QM69b. -/
theorem scaled_denominator_dvd
    (a r : ℚ) (N D B : ℚ[X])
    (ha : a ≠ 0) (hcop : IsCoprime N D)
    (hclear : C a * scalePoly r N * D = scalePoly r D * B) :
    scalePoly r D ∣ D := by
  have hdvd0 : scalePoly r D ∣ C a * scalePoly r N * D :=
    ⟨B, hclear⟩
  have hdvd1 : scalePoly r D ∣ scalePoly r N * (C a * D) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd0
  have hcop_scaled : IsCoprime (scalePoly r D) (scalePoly r N) :=
    (scalePoly_isCoprime r hcop).symm
  have hdvd2 : scalePoly r D ∣ C a * D :=
    hcop_scaled.dvd_of_dvd_mul_left hdvd1
  have hunit : IsUnit (C a : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
  exact hunit.dvd_mul_left.mp hdvd2

/-- Equal degree upgrades QM69c to association. -/
theorem scaled_denominator_associated
    (r : ℚ) (D : ℚ[X]) (hr : r ≠ 0) (hD : D ≠ 0)
    (hdvd : scalePoly r D ∣ D) :
    Associated (scalePoly r D) D := by
  apply Polynomial.associated_of_dvd_of_natDegree_le hdvd hD
  rw [scalePoly_natDegree r D hr]

/-- QM70 in its essential form: if scaling by a real rational `r>1` changes
a polynomial only by a unit, its support contains at most one exponent. -/
theorem support_subsingleton_of_associated_scale
    (r : ℚ) (D : ℚ[X]) (hr : 1 < r)
    (hassoc : Associated (scalePoly r D) D) :
    D.support.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨c, hcunit, hCc⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hu' : scalePoly r D * C c = D := by
    simpa [hCc] using hu
  have hci : D.coeff i ≠ 0 := by
    exact Polynomial.mem_support_iff.mp hi
  have hcj : D.coeff j ≠ 0 := by
    exact Polynomial.mem_support_iff.mp hj
  have hi_coeff := congrArg (fun P : ℚ[X] => P.coeff i) hu'
  have hj_coeff := congrArg (fun P : ℚ[X] => P.coeff j) hu'
  rw [Polynomial.coeff_mul_C, scalePoly_coeff] at hi_coeff hj_coeff
  have hi_weight : r ^ i * c = 1 := by
    apply mul_left_cancel₀ hci
    simpa [mul_assoc] using hi_coeff
  have hj_weight : r ^ j * c = 1 := by
    apply mul_left_cancel₀ hcj
    simpa [mul_assoc] using hj_coeff
  have hc : c ≠ 0 := isUnit_iff_ne_zero.mp hcunit
  have hpows : r ^ i = r ^ j := by
    apply mul_right_cancel₀ hc
    exact hi_weight.trans hj_weight.symm
  have hrpos : (0 : ℚ) < r := lt_trans (by norm_num) hr
  have hstrict : StrictMono (fun n : ℕ => r ^ n) :=
    strictMono_nat_of_lt_succ fun n => by
      rw [pow_succ]
      have hpow : (0 : ℚ) < r ^ n := pow_pos hrpos n
      nlinarith
  exact hstrict.injective hpows

/-- A nonzero polynomial whose support has cardinality at most one is
literally one monomial, not merely associated to one. -/
theorem eq_monomial_natDegree_of_support_card_le_one
    (D : ℚ[X]) (hD : D ≠ 0) (hsupport : D.support.card ≤ 1) :
    D = Polynomial.monomial D.natDegree D.leadingCoeff := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_monomial]
  by_cases hn : D.natDegree = n
  · subst n
    simp [Polynomial.coeff_natDegree]
  · have hn_zero : D.coeff n = 0 := by
      by_contra hcoeff
      have hn_mem : n ∈ D.support := Polynomial.mem_support_iff.mpr hcoeff
      have htop_mem : D.natDegree ∈ D.support := by
        apply Polynomial.mem_support_iff.mpr
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hD
      have heq := Finset.card_le_one.mp hsupport n hn_mem D.natDegree htop_mem
      exact hn heq.symm
    simp [hn, hn_zero]

/-- The complete algebraic core of the homogeneous rational reduction:
every reduced denominator satisfying the cleared identity has monomial
support. -/
theorem reduced_denominator_support_subsingleton
    (a r : ℚ) (N D B : ℚ[X])
    (ha : a ≠ 0) (hr : 1 < r) (hD : D ≠ 0)
    (hcop : IsCoprime N D)
    (hclear : C a * scalePoly r N * D = scalePoly r D * B) :
    D.support.card ≤ 1 := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans (by norm_num) hr)
  have hdvd := scaled_denominator_dvd a r N D B ha hcop hclear
  have hassoc := scaled_denominator_associated r D hr0 hD hdvd
  exact support_subsingleton_of_associated_scale r D hr hassoc

theorem reduced_denominator_eq_monomial
    (a r : ℚ) (N D B : ℚ[X])
    (ha : a ≠ 0) (hr : 1 < r) (hD : D ≠ 0)
    (hcop : IsCoprime N D)
    (hclear : C a * scalePoly r N * D = scalePoly r D * B) :
    D = Polynomial.monomial D.natDegree D.leadingCoeff := by
  apply eq_monomial_natDegree_of_support_card_le_one D hD
  exact reduced_denominator_support_subsingleton a r N D B
    ha hr hD hcop hclear

/-- The period-three chart's actual scale ratio `Y/X`. -/
def ec17ScaleRatio (K : ℕ) : ℚ :=
  (3 : ℚ) ^ (6 * K) / (2 : ℚ) ^ (8 * K)

theorem one_lt_ec17ScaleRatio (K : ℕ) (hK : 0 < K) :
    1 < ec17ScaleRatio K := by
  rw [ec17ScaleRatio]
  apply (one_lt_div (by positivity : (0 : ℚ) < 2 ^ (8 * K))).2
  exact_mod_cast (show 2 ^ (8 * K) < 3 ^ (6 * K) by
    calc
      2 ^ (8 * K) = (2 ^ 8) ^ K := by rw [pow_mul]
      _ < (3 ^ 6) ^ K := Nat.pow_lt_pow_left (by norm_num) hK.ne'
      _ = 3 ^ (6 * K) := by rw [pow_mul])

theorem ec17_reduced_denominator_support_subsingleton
    (K : ℕ) (hK : 0 < K) (a : ℚ) (N D B : ℚ[X])
    (ha : a ≠ 0) (hD : D ≠ 0) (hcop : IsCoprime N D)
    (hclear : C a * scalePoly (ec17ScaleRatio K) N * D =
      scalePoly (ec17ScaleRatio K) D * B) :
    D.support.card ≤ 1 :=
  reduced_denominator_support_subsingleton a (ec17ScaleRatio K) N D B
    ha (one_lt_ec17ScaleRatio K hK) hD hcop hclear

theorem ec17_reduced_denominator_eq_monomial
    (K : ℕ) (hK : 0 < K) (a : ℚ) (N D B : ℚ[X])
    (ha : a ≠ 0) (hD : D ≠ 0) (hcop : IsCoprime N D)
    (hclear : C a * scalePoly (ec17ScaleRatio K) N * D =
      scalePoly (ec17ScaleRatio K) D * B) :
    D = Polynomial.monomial D.natDegree D.leadingCoeff :=
  reduced_denominator_eq_monomial a (ec17ScaleRatio K) N D B
    ha (one_lt_ec17ScaleRatio K hK) hD hcop hclear

end RationalCoboundaryReduction
end KontoroC
