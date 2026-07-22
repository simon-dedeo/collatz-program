/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SuccessorQuineNoGo
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The denominator obstruction for a rational successor quine

This file isolates the missing algebraic step in the rational-function
version of the successor-quine no-go.  If a reduced denominator `Q` occurs
in a solution of

`A r(z) - D z² r(cz) = B(z)`,

then clearing denominators and reducing modulo `Q` gives

`Q ∣ Q(cz)`.

For nonzero rational `c` with `c ≠ 1`, this divisibility forces `Q` to have
at most one nonzero coefficient.  Thus every rational solution is already a
finite Laurent polynomial.  The finite Laurent case is ruled out in
`SuccessorQuineNoGo`.
-/

namespace KontoroC

namespace SuccessorQuineRationalNoGo

open Polynomial

/-- Scaling the variable of a polynomial: `p(z) ↦ p(cz)`. -/
noncomputable def scale (c : ℚ) (p : ℚ[X]) : ℚ[X] := p.comp (C c * X)

@[simp] theorem scale_coeff (c : ℚ) (p : ℚ[X]) (n : ℕ) :
    (scale c p).coeff n = p.coeff n * c ^ n := by
  simp [scale]

theorem scale_ne_zero {c : ℚ} (hc : c ≠ 0) {p : ℚ[X]} (hp : p ≠ 0) :
    scale c p ≠ 0 := by
  rw [scale, ne_eq, comp_C_mul_X_eq_zero_iff]
  · exact hp
  · simpa using hc

@[simp] theorem natDegree_scale {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    (scale c p).natDegree = p.natDegree := by
  rw [scale, natDegree_comp]
  simp [hc]

/-- A polynomial that divides its nontrivial variable scaling has singleton
support.  This is the finite-denominator form of the pole-orbit argument. -/
theorem support_subsingleton_of_dvd_scale
    {c : ℚ} (hcpos : 0 < c) (hc1 : c ≠ 1)
    {p : ℚ[X]} (hp : p ≠ 0) (hdiv : p ∣ scale c p) :
    ∀ ⦃i⦄, i ∈ p.support → ∀ ⦃j⦄, j ∈ p.support → i = j := by
  have hc : c ≠ 0 := ne_of_gt hcpos
  obtain ⟨t, ht⟩ := hdiv
  have hscale : scale c p ≠ 0 := scale_ne_zero hc hp
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    exact hscale ht
  have hdeg : t.natDegree = 0 := by
    have hd := congrArg Polynomial.natDegree ht
    rw [natDegree_scale hc, natDegree_mul hp ht0] at hd
    omega
  have htC : t = C (t.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  intro i hi j hj
  have hci : p.coeff i ≠ 0 := mem_support_iff.mp hi
  have hcj : p.coeff j ≠ 0 := mem_support_iff.mp hj
  have hiCoeff := congrArg (fun q : ℚ[X] ↦ q.coeff i) ht
  have hjCoeff := congrArg (fun q : ℚ[X] ↦ q.coeff j) ht
  rw [scale_coeff, htC] at hiCoeff hjCoeff
  simp only [coeff_mul_C] at hiCoeff hjCoeff
  have hipow : c ^ i = t.coeff 0 := by
    exact (mul_left_cancel₀ hci hiCoeff)
  have hjpow : c ^ j = t.coeff 0 := by
    exact (mul_left_cancel₀ hcj hjCoeff)
  exact (pow_right_injective₀ hcpos hc1)
    (hipow.trans hjpow.symm)

/-- The modular-denominator step after clearing a rational functional
equation.  Reducedness removes the numerator; a nonzero scalar coefficient
is a unit and also disappears. -/
theorem denom_dvd_scale_of_cleared_equation
    {a d c : ℚ} (ha : a ≠ 0)
    {N Q B : ℚ[X]} (hcop : IsCoprime N Q)
    (heq : C a * N * scale c Q - C d * X ^ 2 * scale c N * Q =
      B * Q * scale c Q) :
    Q ∣ scale c Q := by
  have hmain : Q ∣ C a * N * scale c Q := by
    have hright : Q ∣ B * Q * scale c Q := by
      refine ⟨B * scale c Q, ?_⟩
      ring
    have hshift : Q ∣ C d * X ^ 2 * scale c N * Q := by
      refine ⟨C d * X ^ 2 * scale c N, ?_⟩
      ring
    have hsum := dvd_add hright hshift
    convert hsum using 1
    calc
      C a * N * scale c Q =
          (C a * N * scale c Q - C d * X ^ 2 * scale c N * Q) +
            C d * X ^ 2 * scale c N * Q := by ring
      _ = B * Q * scale c Q + C d * X ^ 2 * scale c N * Q := by rw [heq]
  have hwithoutScalar : Q ∣ N * scale c Q := by
    obtain ⟨t, ht⟩ := hmain
    refine ⟨C (a⁻¹) * t, ?_⟩
    calc
      N * scale c Q = C (a⁻¹) * (C a * N * scale c Q) := by
        rw [← mul_assoc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1,
          one_mul]
      _ = C (a⁻¹) * (Q * t) := by rw [ht]
      _ = Q * (C (a⁻¹) * t) := by ring
  exact hcop.symm.dvd_of_dvd_mul_left hwithoutScalar

/-- A reduced denominator in the cleared successor-quine equation has at
most one nonzero coefficient.  This is the main rational obstruction, stated
without any `RatFunc` representation choices. -/
theorem reduced_denom_support_subsingleton
    {a d c : ℚ} (ha : a ≠ 0) (hcpos : 0 < c) (hc1 : c ≠ 1)
    {N Q B : ℚ[X]} (hQ : Q ≠ 0) (hcop : IsCoprime N Q)
    (heq : C a * N * scale c Q - C d * X ^ 2 * scale c N * Q =
      B * Q * scale c Q) :
    ∀ ⦃i⦄, i ∈ Q.support → ∀ ⦃j⦄, j ∈ Q.support → i = j := by
  apply support_subsingleton_of_dvd_scale hcpos hc1 hQ
  exact denom_dvd_scale_of_cleared_equation ha hcop heq

/-- Concrete scaling constant in RQ3 is strictly between zero and one. -/
theorem concrete_c_pos : 0 < SuccessorQuineNoGo.c := by
  norm_num [SuccessorQuineNoGo.c]

theorem concrete_c_ne_one : SuccessorQuineNoGo.c ≠ 1 := by
  norm_num [SuccessorQuineNoGo.c]

/-- Polynomial form of the quadratic forcing term. -/
noncomputable def quadratic (b0 b1 b2 : ℚ) : ℚ[X] :=
  C b0 + C b1 * X + C b2 * X ^ 2

/-- There is no reduced numerator/denominator pair satisfying the cleared
rational successor equation.  In particular, this theorem includes the
denominator argument rather than assuming that the putative solution was a
polynomial or Laurent polynomial. -/
theorem no_reduced_cleared_solution
    {a d c b0 b1 b2 : ℚ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hcpos : 0 < c) (hc1 : c ≠ 1)
    (hb1 : b1 ≠ 0) :
    ¬ ∃ (N Q : ℚ[X]), Q ≠ 0 ∧ IsCoprime N Q ∧
      C a * N * scale c Q - C d * X ^ 2 * scale c N * Q =
        quadratic b0 b1 b2 * Q * scale c Q := by
  rintro ⟨N, Q, hQ, hcop, heq⟩
  have hsupp := reduced_denom_support_subsingleton ha hcpos hc1 hQ hcop heq
  have hcard : Q.support.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    exact hsupp hi hj
  let k := Q.natDegree
  let q := Q.leadingCoeff
  have hq : q ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr hQ
  have hQshape : C q * X ^ k = Q :=
    C_mul_X_pow_eq_self hcard
  have hk : k = 0 := by
    by_contra hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hN0 : N.coeff 0 ≠ 0 := by
      intro hN0zero
      have hXN : X ∣ N := X_dvd_iff.mpr hN0zero
      have hXpow : (X : ℚ[X]) ∣ X ^ k := dvd_pow_self X hk0
      have hXQ : X ∣ Q := by
        rw [← hQshape]
        exact dvd_mul_of_dvd_right hXpow (C q)
      exact not_isUnit_X (hcop.isUnit_of_dvd' hXN hXQ)
    have hkcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff k) heq
    have hscaleQ : scale c Q = C (q * c ^ k) * X ^ k := by
      rw [← hQshape]
      ext n
      rw [scale_coeff, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases hn : n = k
      · subst n
        simp
      · simp [hn]
    have hfirst :
        (C a * N * (C (q * c ^ k) * X ^ k)).coeff k =
          a * N.coeff 0 * (q * c ^ k) := by
      rw [show C a * N * (C (q * c ^ k) * X ^ k) =
        (C a * N * C (q * c ^ k)) * X ^ k by ring,
        coeff_mul_X_pow']
      simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_mul_C, coeff_C_mul]
    have hshift :
        (C d * X ^ 2 * scale c N * (C q * X ^ k)).coeff k = 0 := by
      rw [show C d * X ^ 2 * scale c N * (C q * X ^ k) =
        (C d * scale c N * C q) * X ^ (k + 2) by ring]
      rw [coeff_mul_X_pow']
      simp [show ¬k + 2 ≤ k by omega]
    have hright :
        (quadratic b0 b1 b2 * (C q * X ^ k) *
          (C (q * c ^ k) * X ^ k)).coeff k = 0 := by
      rw [show quadratic b0 b1 b2 * (C q * X ^ k) *
          (C (q * c ^ k) * X ^ k) =
        (quadratic b0 b1 b2 * C q * C (q * c ^ k)) * X ^ (k + k) by ring]
      rw [coeff_mul_X_pow']
      simp [show ¬k + k ≤ k by omega]
    rw [hscaleQ, ← hQshape, coeff_sub, hfirst, hshift, hright,
      sub_zero] at hkcoeff
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hN0) hq)
      (pow_ne_zero k (ne_of_gt hcpos))) (by simpa [mul_assoc] using hkcoeff)
  have hQconst : Q = C q := by
    rw [← hQshape, hk, pow_zero, mul_one]
  have hreduced : C a * N - C d * X ^ 2 * scale c N =
      quadratic b0 b1 b2 * C q := by
    apply mul_right_cancel₀ (C_ne_zero.mpr hq)
    calc
      (C a * N - C d * X ^ 2 * scale c N) * C q =
          C a * N * C q - C d * X ^ 2 * scale c N * C q := by ring
      _ = quadratic b0 b1 b2 * C q * C q := by
        simpa [hQconst, scale] using heq
      _ = (quadratic b0 b1 b2 * C q) * C q := by ring
  have hcoeff1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hreduced
  have hshift1 : (C d * X ^ 2 * scale c N).coeff 1 = 0 := by
    rw [show C d * X ^ 2 * scale c N = (C d * scale c N) * X ^ 2 by ring,
      coeff_mul_X_pow']
    simp
  have hN1 : N.coeff 1 ≠ 0 := by
    intro hzero
    rw [coeff_sub, coeff_C_mul, hshift1, sub_zero] at hcoeff1
    simp [quadratic, hzero] at hcoeff1
    exact hcoeff1.elim hb1 hq
  have hNdeg : 1 ≤ N.natDegree := le_natDegree_of_ne_zero hN1
  let n := N.natDegree
  have hnlead : N.coeff n ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr (fun hN ↦ hN1 (hN ▸ coeff_zero 1))
  have htop := congrArg (fun p : ℚ[X] ↦ p.coeff (n + 2)) hreduced
  have hn2 : n + 2 ≠ 0 := by omega
  have hn21 : n + 2 ≠ 1 := by omega
  have hn22 : n + 2 ≠ 2 := by omega
  have hn0 : n ≠ 0 := by omega
  have hNhigh : N.coeff (n + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hshifttop :
      (C d * X ^ 2 * scale c N).coeff (n + 2) =
        d * (N.coeff n * c ^ n) := by
    rw [show C d * X ^ 2 * scale c N = (C d * scale c N) * X ^ 2 by ring,
      coeff_mul_X_pow]
    simp [scale_coeff]
  rw [coeff_sub, coeff_C_mul, hNhigh, hshifttop] at htop
  simp [quadratic] at htop
  have hb2coeff : (C b2).coeff n = 0 := by simp [coeff_C, hn0]
  rw [hb2coeff, zero_mul] at htop
  exact (mul_ne_zero hd (mul_ne_zero hnlead
    (pow_ne_zero n (ne_of_gt hcpos)))) (neg_eq_zero.mp htop)

/-- Concrete RQ3 has no reduced polynomial numerator/denominator
presentation. -/
theorem no_concrete_reduced_cleared_solution :
    ¬ ∃ (N Q : ℚ[X]), Q ≠ 0 ∧ IsCoprime N Q ∧
      C SuccessorQuineNoGo.A * N * scale SuccessorQuineNoGo.c Q -
          C SuccessorQuineNoGo.D * X ^ 2 *
            scale SuccessorQuineNoGo.c N * Q =
        quadratic SuccessorQuineNoGo.b0 SuccessorQuineNoGo.b1
          SuccessorQuineNoGo.b2 * Q * scale SuccessorQuineNoGo.c Q := by
  apply no_reduced_cleared_solution
  · norm_num [SuccessorQuineNoGo.A]
  · norm_num [SuccessorQuineNoGo.D]
  · exact concrete_c_pos
  · exact concrete_c_ne_one
  · norm_num [SuccessorQuineNoGo.b1]

/-- The polynomial substitution homomorphism `p(z) ↦ p(cz)`. -/
noncomputable def scaleRingHom (c : ℚ) : ℚ[X] →+* ℚ[X] :=
  Polynomial.compRingHom (C c * X)

@[simp] theorem scaleRingHom_apply (c : ℚ) (p : ℚ[X]) :
    scaleRingHom c p = scale c p := rfl

theorem scaleRingHom_injective {c : ℚ} (hc : c ≠ 0) :
    Function.Injective (scaleRingHom c) := by
  intro p q hpq
  by_contra hpqne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  apply scale_ne_zero hc hsub
  change scaleRingHom c (p - q) = 0
  rw [map_sub, hpq, sub_self]

/-- Substitution `r(z) ↦ r(cz)` on rational functions. -/
noncomputable def scaleRat (c : ℚ) (hc : c ≠ 0) : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.mapRingHom (scaleRingHom c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (scaleRingHom_injective hc))

theorem scaleRat_apply_num_denom (c : ℚ) (hc : c ≠ 0) (r : RatFunc ℚ) :
    scaleRat c hc r =
      algebraMap ℚ[X] (RatFunc ℚ) (scale c r.num) /
        algebraMap ℚ[X] (RatFunc ℚ) (scale c r.denom) := by
  let hφ : nonZeroDivisors ℚ[X] ≤
      (nonZeroDivisors ℚ[X]).comap (scaleRingHom c) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (scaleRingHom_injective hc)
  unfold scaleRat
  change RatFunc.map (scaleRingHom c) hφ r = _
  rw [RatFunc.map_apply]
  rfl

/-- The rational-function variable, embedded from the polynomial ring. -/
noncomputable def ratX : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) X

/-- Generic rational-function no-go.  This is the literal `ℚ(z)` statement,
not merely a theorem about a chosen numerator/denominator presentation. -/
theorem no_rational_solution
    {a d c b0 b1 b2 : ℚ}
    (ha : a ≠ 0) (hd : d ≠ 0) (hcpos : 0 < c) (hc1 : c ≠ 1)
    (hb1 : b1 ≠ 0) :
    ¬ ∃ r : RatFunc ℚ,
      algebraMap ℚ[X] (RatFunc ℚ) (C a) * r -
          algebraMap ℚ[X] (RatFunc ℚ) (C d) * ratX ^ 2 *
            scaleRat c (ne_of_gt hcpos) r =
        algebraMap ℚ[X] (RatFunc ℚ) (quadratic b0 b1 b2) := by
  rintro ⟨r, hr⟩
  let N := r.num
  let Q := r.denom
  have hQ : Q ≠ 0 := RatFunc.denom_ne_zero r
  have hscaleQ : scale c Q ≠ 0 := scale_ne_zero (ne_of_gt hcpos) hQ
  have hcop : IsCoprime N Q := r.isCoprime_num_denom
  have hr' := hr
  rw [scaleRat_apply_num_denom] at hr'
  nth_rewrite 1 [← RatFunc.num_div_denom r] at hr'
  simp only [ratX] at hr'
  have hQmap : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hQ
  have hscaleQmap : algebraMap ℚ[X] (RatFunc ℚ) (scale c Q) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hscaleQ
  have hdenmap : algebraMap ℚ[X] (RatFunc ℚ) r.denom ≠ 0 := by
    simpa [Q] using hQmap
  have hscaledDenmap :
      algebraMap ℚ[X] (RatFunc ℚ) (scale c r.denom) ≠ 0 := by
    simpa [Q] using hscaleQmap
  field_simp [hdenmap, hscaledDenmap] at hr'
  have hpoly :
      C a * N * scale c Q - C d * X ^ 2 * scale c N * Q =
        quadratic b0 b1 b2 * Q * scale c Q := by
    apply RatFunc.algebraMap_injective ℚ
    simp only [map_sub, map_mul, map_pow]
    dsimp [N, Q]
    ring_nf at hr' ⊢
    exact hr'
  exact no_reduced_cleared_solution ha hd hcpos hc1 hb1
    ⟨N, Q, hQ, hcop, hpoly⟩

/-- The corrected legal successor return route admits no rational-function
self-writer `F(g)=r(z_g)`. -/
theorem no_successor_quine_rational :
    ¬ ∃ r : RatFunc ℚ,
      algebraMap ℚ[X] (RatFunc ℚ) (C SuccessorQuineNoGo.A) * r -
          algebraMap ℚ[X] (RatFunc ℚ) (C SuccessorQuineNoGo.D) * ratX ^ 2 *
            scaleRat SuccessorQuineNoGo.c
              (ne_of_gt concrete_c_pos) r =
        algebraMap ℚ[X] (RatFunc ℚ)
          (quadratic SuccessorQuineNoGo.b0 SuccessorQuineNoGo.b1
            SuccessorQuineNoGo.b2) := by
  apply no_rational_solution
  · norm_num [SuccessorQuineNoGo.A]
  · norm_num [SuccessorQuineNoGo.D]
  · exact concrete_c_pos
  · exact concrete_c_ne_one
  · norm_num [SuccessorQuineNoGo.b1]

end SuccessorQuineRationalNoGo

end KontoroC
