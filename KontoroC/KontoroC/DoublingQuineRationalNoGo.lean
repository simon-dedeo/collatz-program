/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DoublingQuineNoGo
import KontoroC.SuccessorQuineRationalNoGo
import Mathlib.Algebra.Polynomial.Expand

/-!
# Rational-denominator obstruction for the base-squaring return quine

The first genuinely nonlinear payload ansatz obeys

`A f(z) - D z^2 f(kappa z^2) = b0 + b1 z + b2 z^2`.

For a reduced rational presentation `f=N/Q`, clearing denominators twice
forces both

`Q ∣ Q(kappa z^2)` and `Q(kappa z^2) ∣ z^2 Q`.

The second divisibility bounds `deg Q` by two.  Comparing the few remaining
coefficients leaves only monomial denominators (finite Laurent payloads) and
the simple fixed pole `1-kappa*z`; the latter would require the false residue
identity `2*A*kappa^2=D`.  This closes rational payloads without searching
over degrees or coefficients.  Genuinely infinite Mahler/automatic payloads
remain outside the theorem.
-/

namespace KontoroC
namespace DoublingQuineRationalNoGo

open Polynomial
open SuccessorQuineRationalNoGo

/-- Base-squaring substitution on polynomials. -/
noncomputable def squareScale (kappa : ℚ) (p : ℚ[X]) : ℚ[X] :=
  p.comp (C kappa * X ^ 2)

/-- Ring-hom form of the base-squaring substitution. -/
noncomputable def squareScaleRingHom (kappa : ℚ) : ℚ[X] →+* ℚ[X] :=
  Polynomial.compRingHom (C kappa * X ^ 2)

@[simp] theorem squareScaleRingHom_apply (kappa : ℚ) (p : ℚ[X]) :
    squareScaleRingHom kappa p = squareScale kappa p := rfl

theorem squareScale_ne_zero {kappa : ℚ} (hkappa : kappa ≠ 0)
    {p : ℚ[X]} (hp : p ≠ 0) : squareScale kappa p ≠ 0 := by
  intro hcomp
  rw [squareScale, comp_eq_zero_iff] at hcomp
  rcases hcomp with hpzero | ⟨_, hconstant⟩
  · exact hp hpzero
  have hnonzero : C kappa * X ^ 2 ≠ (0 : ℚ[X]) :=
    mul_ne_zero (C_ne_zero.mpr hkappa) (pow_ne_zero _ X_ne_zero)
  have hcoeff0 : (C kappa * X ^ 2).coeff 0 = 0 := by simp
  rw [hcoeff0, C_0] at hconstant
  exact hnonzero hconstant

@[simp] theorem natDegree_squareScale {kappa : ℚ} (hkappa : kappa ≠ 0)
    (p : ℚ[X]) :
    (squareScale kappa p).natDegree = 2 * p.natDegree := by
  rw [squareScale, natDegree_comp]
  simp [hkappa]
  omega

theorem squareScale_coeff_zero (kappa : ℚ) (p : ℚ[X]) :
    (squareScale kappa p).coeff 0 = p.coeff 0 := by
  rw [show squareScale kappa p =
      Polynomial.expand ℚ 2 (scale kappa p) by
    rw [squareScale, scale, expand_eq_comp_X_pow, comp_assoc]
    simp]
  rw [coeff_expand (by norm_num)]
  simp [scale_coeff]

theorem squareScale_coeff_one (kappa : ℚ) (p : ℚ[X]) :
    (squareScale kappa p).coeff 1 = 0 := by
  rw [show squareScale kappa p =
      Polynomial.expand ℚ 2 (scale kappa p) by
    rw [squareScale, scale, expand_eq_comp_X_pow, comp_assoc]
    simp]
  rw [coeff_expand (by norm_num)]
  norm_num

theorem squareScale_coeff_two (kappa : ℚ) (p : ℚ[X]) :
    (squareScale kappa p).coeff 2 = kappa * p.coeff 1 := by
  rw [show squareScale kappa p =
      Polynomial.expand ℚ 2 (scale kappa p) by
    rw [squareScale, scale, expand_eq_comp_X_pow, comp_assoc]
    simp]
  rw [coeff_expand (by norm_num)]
  simp [scale_coeff]
  ring

private theorem coeff_mul_zero (p q : ℚ[X]) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  simp [coeff_mul]

private theorem coeff_mul_one (p q : ℚ[X]) :
    (p * q).coeff 1 =
      p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  simp [coeff_mul, Finset.antidiagonal]

private theorem coeff_mul_two (p q : ℚ[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 +
      p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  simp [coeff_mul, Finset.antidiagonal]
  ring

/-! ## The two denominator divisibilities -/

/-- Reduction modulo the original denominator. -/
theorem denom_dvd_squareScale_of_cleared_equation
    {a d kappa : ℚ} (ha : a ≠ 0)
    {N Q B : ℚ[X]} (hcop : IsCoprime N Q)
    (heq : C a * N * squareScale kappa Q -
        C d * X ^ 2 * squareScale kappa N * Q =
      B * Q * squareScale kappa Q) :
    Q ∣ squareScale kappa Q := by
  have hmain : Q ∣ C a * N * squareScale kappa Q := by
    have hright : Q ∣ B * Q * squareScale kappa Q := by
      refine ⟨B * squareScale kappa Q, ?_⟩
      ring
    have hshift : Q ∣ C d * X ^ 2 * squareScale kappa N * Q := by
      refine ⟨C d * X ^ 2 * squareScale kappa N, ?_⟩
      ring
    have hsum := dvd_add hright hshift
    convert hsum using 1
    calc
      C a * N * squareScale kappa Q =
          (C a * N * squareScale kappa Q -
            C d * X ^ 2 * squareScale kappa N * Q) +
              C d * X ^ 2 * squareScale kappa N * Q := by ring
      _ = B * Q * squareScale kappa Q +
          C d * X ^ 2 * squareScale kappa N * Q := by rw [heq]
  have hwithoutScalar : Q ∣ N * squareScale kappa Q := by
    obtain ⟨t, ht⟩ := hmain
    refine ⟨C (a⁻¹) * t, ?_⟩
    calc
      N * squareScale kappa Q =
          C (a⁻¹) * (C a * N * squareScale kappa Q) := by
        rw [← mul_assoc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha,
          C_1, one_mul]
      _ = C (a⁻¹) * (Q * t) := by rw [ht]
      _ = Q * (C (a⁻¹) * t) := by ring
  exact hcop.symm.dvd_of_dvd_mul_left hwithoutScalar

/-- Reduction modulo the substituted denominator.  Reducedness survives the
substitution, so the substituted numerator can be removed. -/
theorem squareScale_denom_dvd_X_sq_mul_of_cleared_equation
    {a d kappa : ℚ} (hd : d ≠ 0)
    {N Q B : ℚ[X]} (hcop : IsCoprime N Q)
    (heq : C a * N * squareScale kappa Q -
        C d * X ^ 2 * squareScale kappa N * Q =
      B * Q * squareScale kappa Q) :
    squareScale kappa Q ∣ X ^ 2 * Q := by
  have hmain : squareScale kappa Q ∣
      C d * X ^ 2 * squareScale kappa N * Q := by
    have hfirst : squareScale kappa Q ∣
        C a * N * squareScale kappa Q := by
      refine ⟨C a * N, ?_⟩
      ring
    have hright : squareScale kappa Q ∣
        B * Q * squareScale kappa Q := by
      refine ⟨B * Q, ?_⟩
      ring
    have hsub := dvd_sub hfirst hright
    have hidentity :
      C a * N * squareScale kappa Q - B * Q * squareScale kappa Q =
          C d * X ^ 2 * squareScale kappa N * Q := by
      rw [← heq]
      ring
    rw [hidentity] at hsub
    exact hsub
  have hwithoutScalar : squareScale kappa Q ∣
      squareScale kappa N * (X ^ 2 * Q) := by
    obtain ⟨t, ht⟩ := hmain
    refine ⟨C (d⁻¹) * t, ?_⟩
    calc
      squareScale kappa N * (X ^ 2 * Q) =
          (C (d⁻¹) * C d) *
            (X ^ 2 * squareScale kappa N * Q) := by
        rw [← C_mul, inv_mul_cancel₀ hd, C_1, one_mul]
        ring
      _ =
          C (d⁻¹) *
            (C d * X ^ 2 * squareScale kappa N * Q) := by
        ring
      _ = C (d⁻¹) * (squareScale kappa Q * t) := by rw [ht]
      _ = squareScale kappa Q * (C (d⁻¹) * t) := by ring
  exact IsCoprime.dvd_of_dvd_mul_left
    (IsCoprime.symm (hcop.map (squareScaleRingHom kappa))) hwithoutScalar

/-- The reverse divisibility makes every reduced rational denominator have
degree at most two. -/
theorem denom_natDegree_le_two
    {kappa : ℚ} (hkappa : kappa ≠ 0)
    {Q : ℚ[X]} (hQ : Q ≠ 0)
    (hdiv : squareScale kappa Q ∣ X ^ 2 * Q) :
    Q.natDegree ≤ 2 := by
  have hright : X ^ 2 * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  have hdegree := natDegree_le_of_dvd hdiv hright
  rw [natDegree_squareScale hkappa,
    natDegree_X_pow_mul 2 hQ] at hdegree
  omega

/-! ## Classification of the degree-two remainder -/

theorem eq_linear_of_natDegree_le_one (p : ℚ[X]) (hdegree : p.natDegree ≤ 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) := by
  exact eq_X_add_C_of_degree_le_one
    (natDegree_le_iff_degree_le.mp hdegree)

theorem eq_quadratic_of_natDegree_le_two
    (p : ℚ[X]) (hdegree : p.natDegree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 +
      C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hn2 : n = 2
  · subst n
    simp
  have hn : 2 < n := by omega
  have hpzero : p.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hn)
  rw [hpzero]
  simp [coeff_C, coeff_C_mul, coeff_X, hn0, hn2, Ne.symm hn1]

/-- Complete list of reduced denominator shapes left by the two
divisibilities. -/
def DenomShape (kappa : ℚ) (Q : ℚ[X]) : Prop :=
  (∃ q : ℚ, q ≠ 0 ∧ Q = C q) ∨
  (∃ q : ℚ, q ≠ 0 ∧ Q = C q * X) ∨
  (∃ q : ℚ, q ≠ 0 ∧ Q = C q * X ^ 2) ∨
  (∃ q : ℚ, q ≠ 0 ∧ Q = C q * (1 - C kappa * X))

/-- Forward and reverse denominator closure leave only constants, the first
two Laurent monomials, and the simple nonzero fixed pole. -/
theorem denom_shape
    {kappa : ℚ} (hkappa : kappa ≠ 0)
    {Q : ℚ[X]} (hQ : Q ≠ 0)
    (hforward : Q ∣ squareScale kappa Q)
    (hreverse : squareScale kappa Q ∣ X ^ 2 * Q) :
    DenomShape kappa Q := by
  have hle := denom_natDegree_le_two hkappa hQ hreverse
  interval_cases hdegree : Q.natDegree
  · left
    refine ⟨Q.coeff 0, ?_, ?_⟩
    · intro hzero
      have hshape := eq_C_of_natDegree_eq_zero hdegree
      rw [hzero, C_0] at hshape
      exact hQ hshape
    · exact eq_C_of_natDegree_eq_zero hdegree
  · have hq1 : Q.coeff 1 ≠ 0 := by
      simpa only [leadingCoeff, hdegree] using leadingCoeff_ne_zero.mpr hQ
    have hQshape := eq_linear_of_natDegree_le_one Q (by omega)
    by_cases hq0 : Q.coeff 0 = 0
    · right; left
      refine ⟨Q.coeff 1, hq1, ?_⟩
      calc
        Q = C (Q.coeff 1) * X + C (Q.coeff 0) := hQshape
        _ = C (Q.coeff 1) * X := by rw [hq0, C_0, add_zero]
    · obtain ⟨T, hT⟩ := hforward
      have hscaled : squareScale kappa Q ≠ 0 :=
        squareScale_ne_zero hkappa hQ
      have hTne : T ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hT
        exact hscaled hT
      have hTdegree : T.natDegree = 1 := by
        have hdegrees := congrArg Polynomial.natDegree hT
        rw [natDegree_squareScale hkappa,
          natDegree_mul hQ hTne, hdegree] at hdegrees
        omega
      have hTshape := eq_linear_of_natDegree_le_one T (by omega)
      have hq2zero : Q.coeff 2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      have ht2zero : T.coeff 2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hT
      have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hT
      have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) hT
      rw [squareScale_coeff_zero, coeff_mul_zero] at h0
      rw [squareScale_coeff_one, coeff_mul_one] at h1
      rw [squareScale_coeff_two, coeff_mul_two,
        hq2zero, ht2zero] at h2
      ring_nf at h1 h2
      have ht0 : T.coeff 0 = 1 := by
        apply mul_left_cancel₀ hq0
        simpa only [mul_one] using h0.symm
      have ht1 : T.coeff 1 = kappa := by
        apply mul_left_cancel₀ hq1
        simpa only [mul_comm] using h2.symm
      right; right; right
      refine ⟨Q.coeff 0, hq0, ?_⟩
      rw [ht0, ht1] at h1
      have hq1eq : Q.coeff 1 = -(Q.coeff 0 * kappa) := by
        linarith
      calc
        Q = C (Q.coeff 1) * X + C (Q.coeff 0) := hQshape
        _ = C (Q.coeff 0) * (1 - C kappa * X) := by
          rw [hq1eq]
          simp only [C_neg, C_mul]
          ring
  · have hq2 : Q.coeff 2 ≠ 0 := by
      simpa only [leadingCoeff, hdegree] using leadingCoeff_ne_zero.mpr hQ
    obtain ⟨T, hT⟩ := hreverse
    have hright : X ^ 2 * Q ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
    have hscaled : squareScale kappa Q ≠ 0 :=
      squareScale_ne_zero hkappa hQ
    have hTne : T ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hT
      exact hright hT
    have hTdegree : T.natDegree = 0 := by
      have hdegrees := congrArg Polynomial.natDegree hT
      rw [natDegree_X_pow_mul 2 hQ, natDegree_mul hscaled hTne] at hdegrees
      rw [natDegree_squareScale hkappa, hdegree] at hdegrees
      omega
    have hTshape := eq_C_of_natDegree_eq_zero hTdegree
    have ht0 : T.coeff 0 ≠ 0 := by
      intro ht
      rw [ht, C_0] at hTshape
      exact hTne hTshape
    have hTcomm : Q * X ^ 2 =
        squareScale kappa Q * C (T.coeff 0) := by
      rw [← hTshape]
      simpa only [mul_comm] using hT
    have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hTcomm
    have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) hTcomm
    have h0eq : 0 = Q.coeff 0 * T.coeff 0 := by
      calc
        0 = (Q * X ^ 2).coeff 0 := by
          rw [coeff_mul_X_pow']
          norm_num
        _ = (squareScale kappa Q * C (T.coeff 0)).coeff 0 := h0
        _ = Q.coeff 0 * T.coeff 0 := by
          rw [coeff_mul_C, squareScale_coeff_zero]
    have h2eq : Q.coeff 0 =
        (kappa * Q.coeff 1) * T.coeff 0 := by
      calc
        Q.coeff 0 = (Q * X ^ 2).coeff 2 := by
          simpa using (coeff_mul_X_pow Q 2 0).symm
        _ = (squareScale kappa Q * C (T.coeff 0)).coeff 2 := h2
        _ = (kappa * Q.coeff 1) * T.coeff 0 := by
          rw [coeff_mul_C, squareScale_coeff_two]
    have hq0 : Q.coeff 0 = 0 := by
      exact (mul_eq_zero.mp h0eq.symm).resolve_right ht0
    rw [hq0] at h2eq
    have hq1 : Q.coeff 1 = 0 := by
      have hprod : kappa * Q.coeff 1 = 0 := by
        exact (mul_eq_zero.mp h2eq.symm).resolve_right ht0
      exact (mul_eq_zero.mp hprod).resolve_left hkappa
    right; right; left
    refine ⟨Q.coeff 2, hq2, ?_⟩
    calc
      Q = C (Q.coeff 2) * X ^ 2 +
          C (Q.coeff 1) * X + C (Q.coeff 0) :=
        eq_quadratic_of_natDegree_le_two Q (by omega)
      _ = C (Q.coeff 2) * X ^ 2 := by
        rw [hq0, hq1, C_0, zero_mul, add_zero]
        simp

/-! ## The four shapes contradict the functional equation -/

private theorem coeff_one_quadratic_mul_C
    (b0 b1 b2 q : ℚ) :
    (quadratic b0 b1 b2 * C q).coeff 1 = b1 * q := by
  rw [coeff_mul_C]
  simp [quadratic]

private theorem coprime_monomial_denom_coeff_zero_ne
    {N Q : ℚ[X]} (hcop : IsCoprime N Q)
    (hXQ : X ∣ Q) : N.coeff 0 ≠ 0 := by
  intro hzero
  have hXN : X ∣ N := X_dvd_iff.mpr hzero
  exact not_isUnit_X (hcop.isUnit_of_dvd' hXN hXQ)

/-- A constant denominator would make the payload polynomial.  Positive
degree is destroyed by the degree-doubling term; degree zero cannot supply
the nonzero linear forcing coefficient. -/
theorem no_constant_denom_cleared_solution
    {a d kappa b0 b1 b2 q : ℚ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hkappa : kappa ≠ 0)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hq : q ≠ 0) :
    ¬ ∃ N : ℚ[X],
      C a * N * C q - C d * X ^ 2 * squareScale kappa N * C q =
        quadratic b0 b1 b2 * C q * C q := by
  rintro ⟨N, heq⟩
  have hqpoly : C q ≠ (0 : ℚ[X]) := C_ne_zero.mpr hq
  have hreduced : C a * N - C d * X ^ 2 * squareScale kappa N =
      quadratic b0 b1 b2 * C q := by
    apply mul_right_cancel₀ hqpoly
    calc
      (C a * N - C d * X ^ 2 * squareScale kappa N) * C q =
          C a * N * C q -
            C d * X ^ 2 * squareScale kappa N * C q := by ring
      _ = quadratic b0 b1 b2 * C q * C q := heq
      _ = (quadratic b0 b1 b2 * C q) * C q := by ring
  by_cases hN : N = 0
  · subst N
    have hleftZero :
        C a * (0 : ℚ[X]) -
          C d * X ^ 2 * squareScale kappa (0 : ℚ[X]) = 0 := by
      simp [squareScale]
    rw [hleftZero] at hreduced
    have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hreduced
    rw [coeff_zero, coeff_one_quadratic_mul_C] at hcoeff
    exact (mul_ne_zero hb1 hq) hcoeff.symm
  let n := N.natDegree
  by_cases hn : n = 0
  · have hN1 : N.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (by dsimp only [n] at hn ⊢; omega)
    have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hreduced
    have hshift :
        (C d * X ^ 2 * squareScale kappa N).coeff 1 = 0 := by
      rw [show C d * X ^ 2 * squareScale kappa N =
        (C d * squareScale kappa N) * X ^ 2 by ring,
        coeff_mul_X_pow']
      norm_num
    rw [coeff_sub, coeff_C_mul, hN1, mul_zero, hshift, sub_zero,
      coeff_one_quadratic_mul_C] at hcoeff
    exact (mul_ne_zero hb1 hq) hcoeff.symm
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hscaled : squareScale kappa N ≠ 0 :=
      squareScale_ne_zero hkappa hN
    have hfirstDegree : (C a * N).natDegree = n := by
      rw [natDegree_C_mul ha]
    have hsecondDegree :
        (C d * X ^ 2 * squareScale kappa N).natDegree = 2 + 2 * n := by
      rw [show C d * X ^ 2 * squareScale kappa N =
        C d * (X ^ 2 * squareScale kappa N) by ring,
        natDegree_C_mul hd, natDegree_X_pow_mul 2 hscaled,
        natDegree_squareScale hkappa]
      dsimp only [n]
      omega
    have hleftDegree :
        (C a * N - C d * X ^ 2 * squareScale kappa N).natDegree =
          2 + 2 * n := by
      rw [natDegree_sub_eq_right_of_natDegree_lt]
      · exact hsecondDegree
      · rw [hfirstDegree, hsecondDegree]
        omega
    have hforcing : quadratic b0 b1 b2 ≠ 0 := by
      intro hzero
      have hlead := congrArg (fun p : ℚ[X] ↦ p.coeff 2) hzero
      norm_num [quadratic] at hlead
      exact hb2 hlead
    have hrightDegree :
        (quadratic b0 b1 b2 * C q).natDegree = 2 := by
      have hquadDegree : (quadratic b0 b1 b2).natDegree = 2 := by
        rw [show quadratic b0 b1 b2 =
          C b2 * X ^ 2 + C b1 * X + C b0 by
            simp [quadratic]
            ring]
        exact natDegree_quadratic hb2
      rw [natDegree_mul hforcing hqpoly, hquadDegree]
      simp
    have hdegrees := congrArg Polynomial.natDegree hreduced
    rw [hleftDegree, hrightDegree] at hdegrees
    omega

/-- A first-order Laurent pole makes the degree-two coefficient of the
cleared equation nonzero before either other term begins. -/
theorem no_X_denom_cleared_solution
    {a d kappa b0 b1 b2 q : ℚ}
    (ha : a ≠ 0) (hkappa : kappa ≠ 0) (hq : q ≠ 0)
    {N : ℚ[X]} (hcop : IsCoprime N (C q * X)) :
    C a * N * squareScale kappa (C q * X) -
        C d * X ^ 2 * squareScale kappa N * (C q * X) ≠
      quadratic b0 b1 b2 * (C q * X) * squareScale kappa (C q * X) := by
  intro heq
  have hXQ : X ∣ C q * X := by
    refine ⟨C q, ?_⟩
    ring
  have hN0 := coprime_monomial_denom_coeff_zero_ne hcop hXQ
  have hscaleQ : squareScale kappa (C q * X) =
      C (q * kappa) * X ^ 2 := by
    rw [squareScale]
    simp
    ring
  rw [hscaleQ] at heq
  have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 2) heq
  have hfirst : (C a * N * (C (q * kappa) * X ^ 2)).coeff 2 =
      a * q * kappa * N.coeff 0 := by
    rw [show C a * N * (C (q * kappa) * X ^ 2) =
      (C (a * q * kappa) * N) * X ^ 2 by simp [C_mul]; ring,
      coeff_mul_X_pow]
    simp
  have hsecond :
      (C d * X ^ 2 * squareScale kappa N * (C q * X)).coeff 2 = 0 := by
    rw [show C d * X ^ 2 * squareScale kappa N * (C q * X) =
      (C (d * q) * squareScale kappa N) * X ^ 3 by
        simp [C_mul, pow_succ]
        ring,
      coeff_mul_X_pow']
    norm_num
  have hright :
      (quadratic b0 b1 b2 * (C q * X) *
        (C (q * kappa) * X ^ 2)).coeff 2 = 0 := by
    rw [show quadratic b0 b1 b2 * (C q * X) *
        (C (q * kappa) * X ^ 2) =
      (C (q * q * kappa) * quadratic b0 b1 b2) * X ^ 3 by
        simp [C_mul, pow_succ]
        ring,
      coeff_mul_X_pow']
    norm_num
  rw [coeff_sub, hfirst, hsecond, sub_zero, hright] at hcoeff
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hq) hkappa) hN0)
    (by simpa [mul_assoc] using hcoeff)

/-- A second-order Laurent pole would require `a*kappa^2=d`. -/
theorem no_X_sq_denom_cleared_solution
    {a d kappa b0 b1 b2 q : ℚ}
    (_hkappa : kappa ≠ 0) (hq : q ≠ 0)
    (hresidue : a * kappa ^ 2 ≠ d)
    {N : ℚ[X]} (hcop : IsCoprime N (C q * X ^ 2)) :
    C a * N * squareScale kappa (C q * X ^ 2) -
        C d * X ^ 2 * squareScale kappa N * (C q * X ^ 2) ≠
      quadratic b0 b1 b2 * (C q * X ^ 2) *
        squareScale kappa (C q * X ^ 2) := by
  intro heq
  have hXQ : X ∣ C q * X ^ 2 := by
    refine ⟨C q * X, ?_⟩
    ring
  have hN0 := coprime_monomial_denom_coeff_zero_ne hcop hXQ
  have hscaleQ : squareScale kappa (C q * X ^ 2) =
      C (q * kappa ^ 2) * X ^ 4 := by
    rw [squareScale]
    simp
    ring
  rw [hscaleQ] at heq
  have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 4) heq
  have hfirst :
      (C a * N * (C (q * kappa ^ 2) * X ^ 4)).coeff 4 =
        a * q * kappa ^ 2 * N.coeff 0 := by
    rw [show C a * N * (C (q * kappa ^ 2) * X ^ 4) =
      (C (a * q * kappa ^ 2) * N) * X ^ 4 by simp [C_mul]; ring,
      coeff_mul_X_pow]
    rw [coeff_C_mul]
  have hsecond :
      (C d * X ^ 2 * squareScale kappa N * (C q * X ^ 2)).coeff 4 =
        d * q * N.coeff 0 := by
    rw [show C d * X ^ 2 * squareScale kappa N * (C q * X ^ 2) =
      (C (d * q) * squareScale kappa N) * X ^ 4 by
        simp [C_mul]
        ring,
      coeff_mul_X_pow]
    rw [coeff_C_mul, squareScale_coeff_zero]
  have hright :
      (quadratic b0 b1 b2 * (C q * X ^ 2) *
        (C (q * kappa ^ 2) * X ^ 4)).coeff 4 = 0 := by
    rw [show quadratic b0 b1 b2 * (C q * X ^ 2) *
        (C (q * kappa ^ 2) * X ^ 4) =
      (C (q * q * kappa ^ 2) * quadratic b0 b1 b2) * X ^ 6 by
        simp [C_mul]
        ring,
      coeff_mul_X_pow']
    norm_num
  rw [coeff_sub, hfirst, hsecond, hright] at hcoeff
  have hfactor : q * N.coeff 0 * (a * kappa ^ 2 - d) = 0 := by
    linarith
  exact (mul_ne_zero (mul_ne_zero hq hN0) (sub_ne_zero.mpr hresidue)) hfactor

/-- The only genuinely rational denominator left by the classification is a
simple pole at the nonzero fixed point `z=1/kappa`.  Cancellation of its
principal part would require `2*a*kappa^2=d`. -/
theorem no_fixedPole_denom_cleared_solution
    {a d kappa b0 b1 b2 q : ℚ}
    (hkappa : kappa ≠ 0) (hq : q ≠ 0)
    (hresidue : 2 * a * kappa ^ 2 ≠ d)
    {N : ℚ[X]}
    (hcop : IsCoprime N (C q * (1 - C kappa * X))) :
    C a * N * squareScale kappa (C q * (1 - C kappa * X)) -
        C d * X ^ 2 * squareScale kappa N *
          (C q * (1 - C kappa * X)) ≠
      quadratic b0 b1 b2 * (C q * (1 - C kappa * X)) *
        squareScale kappa (C q * (1 - C kappa * X)) := by
  intro heq
  let Q : ℚ[X] := C q * (1 - C kappa * X)
  let L : ℚ[X] := 1 + C kappa * X
  have hlinear : 1 - C kappa * X ≠ (0 : ℚ[X]) := by
    intro hzero
    have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hzero
    norm_num at hcoeff
  have hQ : Q ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr hq) hlinear
  have hscaleQ : squareScale kappa Q = Q * L := by
    dsimp only [Q, L, squareScale]
    simp
    ring
  change C a * N * squareScale kappa Q -
      C d * X ^ 2 * squareScale kappa N * Q =
    quadratic b0 b1 b2 * Q * squareScale kappa Q at heq
  rw [hscaleQ] at heq
  have hreduced : C a * N * L - C d * X ^ 2 * squareScale kappa N =
      quadratic b0 b1 b2 * Q * L := by
    apply mul_right_cancel₀ hQ
    calc
      (C a * N * L - C d * X ^ 2 * squareScale kappa N) * Q =
          C a * N * (Q * L) -
            C d * X ^ 2 * squareScale kappa N * Q := by ring
      _ = quadratic b0 b1 b2 * Q * (Q * L) := heq
      _ = (quadratic b0 b1 b2 * Q * L) * Q := by ring
  let alpha : ℚ := kappa⁻¹
  have hfixed : kappa * alpha ^ 2 = alpha := by
    dsimp only [alpha]
    field_simp
  have hQeval : Q.eval alpha = 0 := by
    dsimp only [Q]
    rw [eval_mul, eval_C, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    dsimp only [alpha]
    field_simp
    ring
  have hLeval : L.eval alpha = 2 := by
    dsimp only [L]
    rw [eval_add, eval_one, eval_mul, eval_C, eval_X]
    dsimp only [alpha]
    field_simp
    ring
  have hscaleEval : (squareScale kappa N).eval alpha = N.eval alpha := by
    rw [squareScale, eval_comp, eval_mul, eval_C, eval_pow, eval_X, hfixed]
  have hNalpha : N.eval alpha ≠ 0 := by
    intro hroot
    have hXN : X - C alpha ∣ N := dvd_iff_isRoot.mpr hroot
    have hXQ : X - C alpha ∣ Q :=
      dvd_iff_isRoot.mpr hQeval
    exact not_isUnit_X_sub_C alpha (hcop.isUnit_of_dvd' hXN hXQ)
  have heval := congrArg (fun p : ℚ[X] ↦ p.eval alpha) hreduced
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_pow] at heval
  rw [hLeval, hscaleEval, hQeval] at heval
  simp only [mul_zero, zero_mul] at heval
  have hfactor : (2 * a * kappa ^ 2 - d) * N.eval alpha = 0 := by
    dsimp only [alpha] at heval
    field_simp at heval
    simpa [mul_comm, mul_left_comm, mul_assoc] using heval
  exact (mul_ne_zero (sub_ne_zero.mpr hresidue) hNalpha) hfactor

/-! ## Complete reduced and rational-function no-go -/

/-- No reduced numerator/denominator pair can satisfy the base-squaring
functional equation under the four displayed nonvanishing conditions. -/
theorem no_reduced_cleared_solution
    {a d kappa b0 b1 b2 : ℚ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hkappa : kappa ≠ 0)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (hsecond : a * kappa ^ 2 ≠ d)
    (hfixed : 2 * a * kappa ^ 2 ≠ d) :
    ¬ ∃ (N Q : ℚ[X]), Q ≠ 0 ∧ IsCoprime N Q ∧
      C a * N * squareScale kappa Q -
          C d * X ^ 2 * squareScale kappa N * Q =
        quadratic b0 b1 b2 * Q * squareScale kappa Q := by
  rintro ⟨N, Q, hQ, hcop, heq⟩
  have hforward := denom_dvd_squareScale_of_cleared_equation
    ha hcop heq
  have hreverse := squareScale_denom_dvd_X_sq_mul_of_cleared_equation
    hd hcop heq
  rcases denom_shape hkappa hQ hforward hreverse with
    ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact no_constant_denom_cleared_solution ha hd hkappa hb1 hb2 hq
      ⟨N, by simpa [squareScale] using heq⟩
  · exact no_X_denom_cleared_solution ha hkappa hq hcop heq
  · exact no_X_sq_denom_cleared_solution hkappa hq hsecond hcop heq
  · exact no_fixedPole_denom_cleared_solution hkappa hq hfixed hcop heq

theorem concrete_A_ne_zero : DoublingQuineNoGo.A ≠ 0 := by
  norm_num [DoublingQuineNoGo.A]

theorem concrete_D_ne_zero : DoublingQuineNoGo.D ≠ 0 := by
  norm_num [DoublingQuineNoGo.D]

theorem concrete_kappa_ne_zero : DoublingQuineNoGo.kappa ≠ 0 := by
  norm_num [DoublingQuineNoGo.kappa]

theorem concrete_b1_ne_zero : DoublingQuineNoGo.b1 ≠ 0 := by
  norm_num [DoublingQuineNoGo.b1]

theorem concrete_b2_ne_zero : DoublingQuineNoGo.b2 ≠ 0 := by
  norm_num [DoublingQuineNoGo.b2]

theorem concrete_second_residue_ne :
    DoublingQuineNoGo.A * DoublingQuineNoGo.kappa ^ 2 ≠
      DoublingQuineNoGo.D := by
  norm_num [DoublingQuineNoGo.A, DoublingQuineNoGo.D,
    DoublingQuineNoGo.kappa]

theorem concrete_fixed_residue_ne :
    2 * DoublingQuineNoGo.A * DoublingQuineNoGo.kappa ^ 2 ≠
      DoublingQuineNoGo.D := by
  norm_num [DoublingQuineNoGo.A, DoublingQuineNoGo.D,
    DoublingQuineNoGo.kappa]

/-- Concrete reduced-denominator form of the rational base-squaring no-go. -/
theorem no_concrete_reduced_cleared_solution :
    ¬ ∃ (N Q : ℚ[X]), Q ≠ 0 ∧ IsCoprime N Q ∧
      C DoublingQuineNoGo.A * N *
          squareScale DoublingQuineNoGo.kappa Q -
        C DoublingQuineNoGo.D * X ^ 2 *
          squareScale DoublingQuineNoGo.kappa N * Q =
      quadratic DoublingQuineNoGo.b0 DoublingQuineNoGo.b1
        DoublingQuineNoGo.b2 * Q *
          squareScale DoublingQuineNoGo.kappa Q := by
  exact no_reduced_cleared_solution concrete_A_ne_zero concrete_D_ne_zero
    concrete_kappa_ne_zero concrete_b1_ne_zero concrete_b2_ne_zero
    concrete_second_residue_ne concrete_fixed_residue_ne

/-- The polynomial base-squaring substitution is injective. -/
theorem squareScaleRingHom_injective {kappa : ℚ} (hkappa : kappa ≠ 0) :
    Function.Injective (squareScaleRingHom kappa) := by
  intro p q hpq
  by_contra hpqne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  apply squareScale_ne_zero hkappa hsub
  change squareScaleRingHom kappa (p - q) = 0
  rw [map_sub, hpq, sub_self]

/-- Base-squaring substitution on rational functions. -/
noncomputable def squareScaleRat (kappa : ℚ) (hkappa : kappa ≠ 0) :
    RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.mapRingHom (squareScaleRingHom kappa)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (squareScaleRingHom_injective hkappa))

theorem squareScaleRat_apply_num_denom
    (kappa : ℚ) (hkappa : kappa ≠ 0) (r : RatFunc ℚ) :
    squareScaleRat kappa hkappa r =
      algebraMap ℚ[X] (RatFunc ℚ) (squareScale kappa r.num) /
        algebraMap ℚ[X] (RatFunc ℚ) (squareScale kappa r.denom) := by
  let hφ : nonZeroDivisors ℚ[X] ≤
      (nonZeroDivisors ℚ[X]).comap (squareScaleRingHom kappa) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (squareScaleRingHom_injective hkappa)
  unfold squareScaleRat
  change RatFunc.map (squareScaleRingHom kappa) hφ r = _
  rw [RatFunc.map_apply]
  rfl

/-- Literal rational-function no-go, not merely a statement about a chosen
numerator/denominator presentation. -/
theorem no_rational_solution
    {a d kappa b0 b1 b2 : ℚ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hkappa : kappa ≠ 0)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (hsecond : a * kappa ^ 2 ≠ d)
    (hfixed : 2 * a * kappa ^ 2 ≠ d) :
    ¬ ∃ r : RatFunc ℚ,
      algebraMap ℚ[X] (RatFunc ℚ) (C a) * r -
          algebraMap ℚ[X] (RatFunc ℚ) (C d) * ratX ^ 2 *
            squareScaleRat kappa hkappa r =
        algebraMap ℚ[X] (RatFunc ℚ) (quadratic b0 b1 b2) := by
  rintro ⟨r, hr⟩
  let N := r.num
  let Q := r.denom
  have hQ : Q ≠ 0 := RatFunc.denom_ne_zero r
  have hscaleQ : squareScale kappa Q ≠ 0 :=
    squareScale_ne_zero hkappa hQ
  have hcop : IsCoprime N Q := r.isCoprime_num_denom
  have hr' := hr
  rw [squareScaleRat_apply_num_denom] at hr'
  nth_rewrite 1 [← RatFunc.num_div_denom r] at hr'
  simp only [ratX] at hr'
  have hQmap : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hQ
  have hscaleQmap :
      algebraMap ℚ[X] (RatFunc ℚ) (squareScale kappa Q) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hscaleQ
  have hdenmap : algebraMap ℚ[X] (RatFunc ℚ) r.denom ≠ 0 := by
    simpa only [Q] using hQmap
  have hscaledDenmap :
      algebraMap ℚ[X] (RatFunc ℚ) (squareScale kappa r.denom) ≠ 0 := by
    simpa only [Q] using hscaleQmap
  field_simp [hdenmap, hscaledDenmap] at hr'
  have hpoly :
      C a * N * squareScale kappa Q -
          C d * X ^ 2 * squareScale kappa N * Q =
        quadratic b0 b1 b2 * Q * squareScale kappa Q := by
    apply RatFunc.algebraMap_injective ℚ
    simp only [map_sub, map_mul, map_pow]
    dsimp only [N, Q]
    ring_nf at hr' ⊢
    exact hr'
  exact no_reduced_cleared_solution ha hd hkappa hb1 hb2
    hsecond hfixed ⟨N, Q, hQ, hcop, hpoly⟩

/-- The legal `g -> 2g` return route admits no rational-function self-writer
`F(g)=r(z_g)`.  Any surviving payload must be genuinely infinite and
nonrational. -/
theorem no_doubling_quine_rational :
    ¬ ∃ r : RatFunc ℚ,
      algebraMap ℚ[X] (RatFunc ℚ) (C DoublingQuineNoGo.A) * r -
          algebraMap ℚ[X] (RatFunc ℚ) (C DoublingQuineNoGo.D) * ratX ^ 2 *
            squareScaleRat DoublingQuineNoGo.kappa concrete_kappa_ne_zero r =
        algebraMap ℚ[X] (RatFunc ℚ)
          (quadratic DoublingQuineNoGo.b0 DoublingQuineNoGo.b1
            DoublingQuineNoGo.b2) := by
  exact no_rational_solution concrete_A_ne_zero concrete_D_ne_zero
    concrete_kappa_ne_zero concrete_b1_ne_zero concrete_b2_ne_zero
    concrete_second_residue_ne concrete_fixed_residue_ne

end DoublingQuineRationalNoGo
end KontoroC
