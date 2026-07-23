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

/-! ## Closing the homogeneous rational equation -/

theorem scalePoly_monomial (r c : ℚ) (m : ℕ) :
    scalePoly r (Polynomial.monomial m c) =
      Polynomial.monomial m (c * r ^ m) := by
  apply Polynomial.ext
  intro n
  rw [scalePoly_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_monomial]
  by_cases h : m = n
  · subst n
    simp
  · simp [h]

/-- A nonzero coefficient of a quadratic multiplied by `c*z^m` must have
index in the interval `[m,m+2]`. -/
theorem coeff_mul_monomial_ne_zero_bounds
    (R : ℚ[X]) (m k : ℕ) (c : ℚ) (hc : c ≠ 0)
    (hdegree : R.natDegree ≤ 2)
    (hcoeff : (R * Polynomial.monomial m c).coeff k ≠ 0) :
    m ≤ k ∧ k ≤ m + 2 := by
  constructor
  · by_contra hnot
    have hklt : k < m := Nat.lt_of_not_ge hnot
    apply hcoeff
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [show R * (C c * X ^ m) = (R * C c) * X ^ m by ring,
      Polynomial.coeff_mul_X_pow']
    simp [not_le_of_gt hklt]
  · have hkdeg := Polynomial.le_natDegree_of_ne_zero hcoeff
    have hmuldeg : (R * Polynomial.monomial m c).natDegree ≤
        R.natDegree + (Polynomial.monomial m c).natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_monomial, if_neg hc] at hmuldeg
    omega

/-- Exact cancellation after a reduced denominator has been proved to be a
monomial.  This is the source-faithful bridge from QM69b to the finite
polynomial support contradiction below. -/
theorem normalized_identity_of_monomial_denominator
    (a r C0 : ℚ) (N D R : ℚ[X]) (m : ℕ) (c : ℚ)
    (hD : D ≠ 0) (hmono : D = Polynomial.monomial m c)
    (hclear : C a * scalePoly r N * D =
      scalePoly r D * (C C0 * (X ^ 3 * N) + R * D)) :
    C a * scalePoly r N =
      C (r ^ m) * (C C0 * (X ^ 3 * N) + R * D) := by
  have hc : c ≠ 0 := by
    intro hc
    apply hD
    rw [hmono, hc, Polynomial.monomial_zero_right]
  have hscale : scalePoly r D = D * C (r ^ m) := by
    rw [hmono, scalePoly_monomial]
    rw [Polynomial.monomial_mul_C]
  rw [hscale] at hclear
  apply mul_left_cancel₀ (a := D) hD
  calc
    D * (C a * scalePoly r N) = C a * scalePoly r N * D := by ring
    _ = D * C (r ^ m) * (C C0 * (X ^ 3 * N) + R * D) := hclear
    _ = D * (C (r ^ m) * (C C0 * (X ^ 3 * N) + R * D)) := by ring

/-- No nonzero polynomial numerator can satisfy the normalized rational
coboundary equation once the denominator is a monomial and the forcing is
quadratic.  The lowest numerator exponent must be at least `m`, while the
coefficient three beyond its degree forces the degree below `m`. -/
theorem no_normalized_monomial_denominator_identity
    (a r C0 c : ℚ) (N R : ℚ[X]) (m : ℕ)
    (ha : a ≠ 0) (hr : r ≠ 0) (hC0 : C0 ≠ 0) (hc : c ≠ 0)
    (hN : N ≠ 0) (hdegree : R.natDegree ≤ 2)
    (heq : C a * scalePoly r N =
      C (r ^ m) *
        (C C0 * (X ^ 3 * N) + R * Polynomial.monomial m c)) :
    False := by
  have hs : N.support.Nonempty := Polynomial.support_nonempty.mpr hN
  let nmin : ℕ := N.support.min' hs
  let nmax : ℕ := N.natDegree
  have hnmin_mem : nmin ∈ N.support := Finset.min'_mem N.support hs
  have hnmin : N.coeff nmin ≠ 0 := Polynomial.mem_support_iff.mp hnmin_mem
  have hnmax : N.coeff nmax ≠ 0 := by
    rw [show N.coeff nmax = N.leadingCoeff by
      exact Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hN
  have hnmin_le_nmax : nmin ≤ nmax :=
    Polynomial.le_natDegree_of_mem_supp nmin hnmin_mem
  have hshift_min : (X ^ 3 * N).coeff nmin = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hthree
    · apply not_ne_iff.mp
      intro hpred
      have hpred_mem : nmin - 3 ∈ N.support :=
        Polynomial.mem_support_iff.mpr hpred
      have hleast := Finset.min'_le N.support (nmin - 3) hpred_mem
      omega
    · rfl
  have hforcing_min :
      (R * Polynomial.monomial m c).coeff nmin ≠ 0 := by
    intro hzero
    have h := congrArg (fun P : ℚ[X] => P.coeff nmin) heq
    rw [Polynomial.coeff_C_mul, scalePoly_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, hshift_min, hzero] at h
    simp only [mul_zero, add_zero] at h
    exact (mul_ne_zero ha (mul_ne_zero hnmin (pow_ne_zero _ hr))) h
  have hmin_bounds := coeff_mul_monomial_ne_zero_bounds
    R m nmin c hc hdegree hforcing_min
  have hscale_max : (scalePoly r N).coeff (nmax + 3) = 0 := by
    rw [scalePoly_coeff]
    have hz : N.coeff (nmax + 3) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul]
  have hshift_max : (X ^ 3 * N).coeff (nmax + 3) = N.coeff nmax := by
    simpa [Nat.add_comm] using Polynomial.coeff_X_pow_mul N 3 nmax
  have hforcing_max :
      (R * Polynomial.monomial m c).coeff (nmax + 3) ≠ 0 := by
    intro hzero
    have h := congrArg (fun P : ℚ[X] => P.coeff (nmax + 3)) heq
    rw [Polynomial.coeff_C_mul, hscale_max,
      Polynomial.coeff_C_mul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, hshift_max, hzero] at h
    simp only [mul_zero, zero_eq_mul] at h
    rcases h with hrm | hinner
    · exact (pow_ne_zero _ hr) hrm
    · exact (mul_ne_zero hC0 hnmax) (by simpa only [add_zero] using hinner)
  have hmax_bounds := coeff_mul_monomial_ne_zero_bounds
    R m (nmax + 3) c hc hdegree hforcing_max
  omega

/-- Homogeneous rational no-go in cleared-denominator form.  The reduced
denominator theorem and the normalized support contradiction are composed
without an external quotient-to-Laurent seam. -/
theorem no_reduced_homogeneous_rational_identity
    (a r C0 : ℚ) (N D R : ℚ[X])
    (ha : a ≠ 0) (hr : 1 < r) (hC0 : C0 ≠ 0)
    (hN : N ≠ 0) (hD : D ≠ 0) (hcop : IsCoprime N D)
    (hdegree : R.natDegree ≤ 2)
    (hclear : C a * scalePoly r N * D =
      scalePoly r D * (C C0 * (X ^ 3 * N) + R * D)) :
    False := by
  let B : ℚ[X] := C C0 * (X ^ 3 * N) + R * D
  let m : ℕ := D.natDegree
  have hmono : D = Polynomial.monomial m D.leadingCoeff :=
    reduced_denominator_eq_monomial a r N D B
    ha hr hD hcop hclear
  have hc : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have hnormalized := normalized_identity_of_monomial_denominator
    a r C0 N D R m D.leadingCoeff hD hmono hclear
  have hnormalized' : C a * scalePoly r N =
      C (r ^ m) *
        (C C0 * (X ^ 3 * N) +
          R * Polynomial.monomial m D.leadingCoeff) := by
    rw [← hmono]
    exact hnormalized
  exact no_normalized_monomial_denominator_identity
    a r C0 D.leadingCoeff N R m ha
    (ne_of_gt (lt_trans (by norm_num) hr)) hC0 hc hN hdegree hnormalized'

end RationalCoboundaryReduction
end KontoroC
