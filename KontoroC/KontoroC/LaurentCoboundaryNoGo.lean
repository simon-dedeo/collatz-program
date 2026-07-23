/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodThree

/-!
# Finite homogeneous Laurent coboundaries cannot absorb the EC17 defect

An element `F : ℤ →₀ ℚ` represents the homogeneous Laurent polynomial

`sum_k F(k) * x^k * y^(-1-k)`.

The coefficient equation below is exactly the total-degree-two component of

`A*x^3*F(X*x,Y*y) - C*y^3*F(x,y)
  = 17*(D0*y^2 + D1*x*y + D2*x^2)`.

The proof uses only the least and greatest indices in the finite support.
This is QM67 in a coefficient-native representation; it does not claim that
an infinite series or a non-Laurent rational function is impossible.
-/

namespace KontoroC
namespace LaurentCoboundaryNoGo

/-- Scaling attached to the source coefficient with index `k-3`. -/
def advanceWeight (A X Y : ℚ) (k : ℤ) : ℚ :=
  A * X ^ (k - 3) * Y ^ (-1 - (k - 3))

theorem advanceWeight_ne_zero (A X Y : ℚ) (k : ℤ)
    (hA : A ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0) :
    advanceWeight A X Y k ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hA (zpow_ne_zero _ hX))
    (zpow_ne_zero _ hY)

/-- The three monomials on the quadratic right side, indexed by their
`x`-exponent. -/
def rhsCoeff (D0 D1 D2 : ℚ) (k : ℤ) : ℚ :=
  if k = 0 then 17 * D0
  else if k = 1 then 17 * D1
  else if k = 2 then 17 * D2
  else 0

def IsRhsIndex (k : ℤ) : Prop := k = 0 ∨ k = 1 ∨ k = 2

theorem rhsCoeff_eq_zero_of_not_index (D0 D1 D2 : ℚ) (k : ℤ)
    (hk : ¬ IsRhsIndex k) :
    rhsCoeff D0 D1 D2 k = 0 := by
  have h0 : k ≠ 0 := fun h => hk (Or.inl h)
  have h1 : k ≠ 1 := fun h => hk (Or.inr (Or.inl h))
  have h2 : k ≠ 2 := fun h => hk (Or.inr (Or.inr h))
  simp [rhsCoeff, h0, h1, h2]

/-- Exact coefficientwise meaning of the homogeneous function-field
coboundary equation QM66. -/
def Satisfies (F : ℤ →₀ ℚ) (A C X Y D0 D1 D2 : ℚ) : Prop :=
  ∀ k : ℤ,
    advanceWeight A X Y k * F (k - 3) - C * F k =
      rhsCoeff D0 D1 D2 k

/-- QM67: no nonzero finitely supported homogeneous Laurent potential solves
the period-three coboundary equation when its two leading multipliers and
both coordinate scales are nonzero. -/
theorem no_finite_homogeneous_potential
    (F : ℤ →₀ ℚ) (A C X Y D0 D1 D2 : ℚ)
    (hF : F ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0)
    (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : Satisfies F A C X Y D0 D1 D2) :
    False := by
  have hs : F.support.Nonempty := Finsupp.support_nonempty_iff.mpr hF
  let m : ℤ := F.support.min' hs
  let M : ℤ := F.support.max' hs
  have hm_mem : m ∈ F.support := by
    exact Finset.min'_mem F.support hs
  have hM_mem : M ∈ F.support := by
    exact Finset.max'_mem F.support hs
  have hFm : F m ≠ 0 := Finsupp.mem_support_iff.mp hm_mem
  have hFM : F M ≠ 0 := Finsupp.mem_support_iff.mp hM_mem
  have hm_rhs : IsRhsIndex m := by
    by_contra hm_not_rhs
    have hpred_not_mem : m - 3 ∉ F.support := by
      intro hpred
      have hmin := Finset.min'_le F.support (m - 3) hpred
      omega
    have hpred_zero : F (m - 3) = 0 := by
      by_contra hne
      exact hpred_not_mem (Finsupp.mem_support_iff.mpr hne)
    have h := heq m
    rw [rhsCoeff_eq_zero_of_not_index D0 D1 D2 m hm_not_rhs,
      hpred_zero] at h
    simp only [mul_zero, zero_sub] at h
    exact (mul_ne_zero hC hFm) (neg_eq_zero.mp h)
  have hm_nonneg : (0 : ℤ) ≤ m := by
    rcases hm_rhs with h | h | h <;> omega
  have hm_le_M : m ≤ M := Finset.min'_le F.support M hM_mem
  have hM_nonneg : (0 : ℤ) ≤ M := hm_nonneg.trans hm_le_M
  have hnext_not_mem : M + 3 ∉ F.support := by
    intro hnext
    have hmax := Finset.le_max' F.support (M + 3) hnext
    omega
  have hnext_zero : F (M + 3) = 0 := by
    by_contra hne
    exact hnext_not_mem (Finsupp.mem_support_iff.mpr hne)
  have hnext_not_rhs : ¬ IsRhsIndex (M + 3) := by
    simp only [IsRhsIndex]
    omega
  have h := heq (M + 3)
  rw [rhsCoeff_eq_zero_of_not_index D0 D1 D2 (M + 3) hnext_not_rhs,
    show M + 3 - 3 = M by omega, hnext_zero] at h
  simp only [mul_zero, sub_zero] at h
  exact (mul_ne_zero (advanceWeight_ne_zero A X Y (M + 3) hA hX hY) hFM) h

/-! ## All total-degree slices -/

/-- Scaling on the homogeneous input slice of total degree `d`. -/
def degreeAdvanceWeight (A X Y : ℚ) (d k : ℤ) : ℚ :=
  A * X ^ (k - 3) * Y ^ (d - (k - 3))

theorem degreeAdvanceWeight_ne_zero (A X Y : ℚ) (d k : ℤ)
    (hA : A ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0) :
    degreeAdvanceWeight A X Y d k ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hA (zpow_ne_zero _ hX))
    (zpow_ne_zero _ hY)

theorem degreeAdvanceWeight_neg_one (A X Y : ℚ) (k : ℤ) :
    degreeAdvanceWeight A X Y (-1) k = advanceWeight A X Y k := by
  rfl

/-- Every finitely supported homogeneous slice has trivial kernel.  Looking
three places beyond its greatest `x` exponent already gives the
contradiction. -/
theorem finite_homogeneous_kernel_eq_zero
    (f : ℤ →₀ ℚ) (A C X Y : ℚ) (d : ℤ)
    (hA : A ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : ∀ k : ℤ,
      degreeAdvanceWeight A X Y d k * f (k - 3) - C * f k = 0) :
    f = 0 := by
  by_contra hf
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  let M : ℤ := f.support.max' hs
  have hM_mem : M ∈ f.support := Finset.max'_mem f.support hs
  have hfM : f M ≠ 0 := Finsupp.mem_support_iff.mp hM_mem
  have hnext_not_mem : M + 3 ∉ f.support := by
    intro hnext
    have hmax := Finset.le_max' f.support (M + 3) hnext
    omega
  have hnext_zero : f (M + 3) = 0 := by
    by_contra hne
    exact hnext_not_mem (Finsupp.mem_support_iff.mpr hne)
  have h := heq (M + 3)
  rw [show M + 3 - 3 = M by omega, hnext_zero] at h
  simp only [mul_zero, sub_zero] at h
  exact (mul_ne_zero
    (degreeAdvanceWeight_ne_zero A X Y d (M + 3) hA hX hY) hfM) h

/-- A finite bivariate Laurent polynomial represented as a finite family of
finite homogeneous slices: outer index `d` is total degree and inner index
`k` is the `x` exponent. -/
abbrev FiniteLaurent := ℤ →₀ (ℤ →₀ ℚ)

/-- Coefficientwise full QM66.  The slice of input degree `d` contributes to
output degree `d+3`; only `d=-1` can meet the quadratic right side. -/
def FullSatisfies (F : FiniteLaurent) (A C X Y D0 D1 D2 : ℚ) : Prop :=
  ∀ (d k : ℤ),
    degreeAdvanceWeight A X Y d k * F d (k - 3) - C * F d k =
      if d = -1 then rhsCoeff D0 D1 D2 k else 0

/-- Every input degree other than `-1` is forced to vanish separately. -/
theorem slice_eq_zero_of_fullSatisfies
    (F : FiniteLaurent) (A C X Y D0 D1 D2 : ℚ)
    (hA : A ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : FullSatisfies F A C X Y D0 D1 D2)
    (d : ℤ) (hd : d ≠ -1) :
    F d = 0 := by
  apply finite_homogeneous_kernel_eq_zero (F d) A C X Y d hA hX hY
  intro k
  simpa [FullSatisfies, hd] using heq d k

/-- QM68: no finite bivariate Laurent potential satisfies QM66 when the
quadratic forcing is nonzero.  The degree-`-1` slice is excluded by QM67;
all other slices are independently kernel-free by the preceding theorem. -/
theorem no_finite_laurent_potential
    (F : FiniteLaurent) (A C X Y D0 D1 D2 : ℚ)
    (hA : A ≠ 0) (hC : C ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hD : D0 ≠ 0 ∨ D1 ≠ 0 ∨ D2 ≠ 0)
    (heq : FullSatisfies F A C X Y D0 D1 D2) :
    False := by
  let f : ℤ →₀ ℚ := F (-1)
  have hslice : Satisfies f A C X Y D0 D1 D2 := by
    intro k
    have h := heq (-1) k
    simpa [FullSatisfies, f, degreeAdvanceWeight_neg_one] using h
  have hf : f ≠ 0 := by
    intro hfzero
    rcases hD with hD0 | hD1 | hD2
    · have h := hslice 0
      rw [hfzero] at h
      simp [rhsCoeff] at h
      exact hD0 h
    · have h := hslice 1
      rw [hfzero] at h
      simp [rhsCoeff] at h
      exact hD1 h
    · have h := hslice 2
      rw [hfzero] at h
      simp [rhsCoeff] at h
      exact hD2 h
  exact no_finite_homogeneous_potential f A C X Y D0 D1 D2
    hf hA hC hX hY hslice

end LaurentCoboundaryNoGo
end KontoroC
