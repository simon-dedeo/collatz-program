/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SuccessorQuineNoGo

/-!
# No finite Laurent payload for the base-squaring return quine

The legal sign-negative return word `1 -> 1 -> g -> g -> 1` suggested the
nonlinear opcode update `g ↦ 2g`.  In the normalized variable

`z_g = 2^(23g+54) / 3^(17g+40)`

one has `z_(2g) = kappa * z_g^2`, where
`kappa = 3^40 / 2^54`.  A payload of the form `F(g)=f(z_g)` would have to
satisfy

`A f(z) - D z^2 f(kappa z^2) = b0+b1 z+b2 z^2`.

The coefficient at exponent one is nonzero.  Under the squaring substitution
it propagates through the infinite exponent orbit `j ↦ 2j+2`.  Therefore no
finitely supported Laurent series can solve the equation.  This closes the
first advertised nonlinear/base-squaring quine ansatz without any bounded
opcode search.  Rational and genuinely infinite Mahler payloads are not
excluded here.
-/

namespace KontoroC
namespace DoublingQuineNoGo

/-- Exponent transport induced by `z^2 f(kappa z^2)`. -/
def exponentStep (j : ℤ) : ℤ := 2 * j + 2

theorem exponentStep_injective : Function.Injective exponentStep := by
  intro i j h
  simp only [exponentStep] at h
  omega

/-- Orbit of the forced coefficient initially at exponent one. -/
def exponentOrbit : ℕ → ℤ
  | 0 => 1
  | n + 1 => exponentStep (exponentOrbit n)

theorem exponentOrbit_succ (n : ℕ) :
    exponentOrbit (n + 1) = 2 * exponentOrbit n + 2 := rfl

theorem exponentOrbit_lower_bound (n : ℕ) :
    (n : ℤ) + 1 ≤ exponentOrbit n := by
  induction n with
  | zero => norm_num [exponentOrbit]
  | succ n ih =>
      rw [exponentOrbit_succ, Nat.cast_succ]
      omega

/-- Coefficient action of `z^2 f(kappa*z^2)` on a finite Laurent series. -/
noncomputable def squareShift (kappa : ℚ) (r : ℤ →₀ ℚ) : ℤ →₀ ℚ :=
  r.sum fun j coefficient =>
    Finsupp.single (exponentStep j) (kappa ^ j * coefficient)

@[simp] theorem squareShift_apply_step (kappa : ℚ) (r : ℤ →₀ ℚ)
    (j : ℤ) :
    squareShift kappa r (exponentStep j) = kappa ^ j * r j := by
  classical
  rw [squareShift, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single j]
  · simp
  · intro i _hi hij
    have hstep : exponentStep i ≠ exponentStep j :=
      fun h => hij (exponentStep_injective h)
    simp [hstep]
  · intro hj
    simp

@[simp] theorem squareShift_apply_one (kappa : ℚ) (r : ℤ →₀ ℚ) :
    squareShift kappa r 1 = 0 := by
  classical
  rw [squareShift, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single 0]
  · simp [exponentStep]
  · intro i _hi _hi0
    have hstep : exponentStep i ≠ 1 := by
      simp only [exponentStep]
      omega
    simp [hstep]
  · intro hzero
    simp [exponentStep]

/-- Laurent coefficients of the quadratic forcing term. -/
noncomputable def forcing (b0 b1 b2 : ℚ) : ℤ →₀ ℚ :=
  Finsupp.single 0 b0 + Finsupp.single 1 b1 + Finsupp.single 2 b2

/-- Literal coefficient form of
`A*f(z)-D*z^2*f(kappa*z^2)=b0+b1*z+b2*z^2`. -/
def FunctionalCoefficientEquation
    (A D kappa b0 b1 b2 : ℚ) (r : ℤ →₀ ℚ) : Prop :=
  A • r = forcing b0 b1 b2 + D • squareShift kappa r

/-- The two coefficient equations needed from the base-squaring functional
equation: the forcing seeds exponent one, and every positive exponent is
transported to `2j+2`. -/
structure CoefficientLaw
    (A D kappa b1 : ℚ) (r : ℤ →₀ ℚ) : Prop where
  seed : A * r 1 = b1
  propagate : ∀ j : ℤ, 1 ≤ j →
    A * r (exponentStep j) = D * kappa ^ j * r j

/-- The full finite-Laurent functional equation implies the two coefficient
laws used by the infinite-support obstruction. -/
theorem coefficientLaw_of_functionalEquation
    {A D kappa b0 b1 b2 : ℚ} {r : ℤ →₀ ℚ}
    (heq : FunctionalCoefficientEquation A D kappa b0 b1 b2 r) :
    CoefficientLaw A D kappa b1 r := by
  constructor
  · have h := congrArg (fun f : ℤ →₀ ℚ => f 1) heq
    simpa [FunctionalCoefficientEquation, forcing] using h
  · intro j hj
    have h := congrArg (fun f : ℤ →₀ ℚ => f (exponentStep j)) heq
    have hstep0 : exponentStep j ≠ 0 := by simp [exponentStep]; omega
    have hstep1 : exponentStep j ≠ 1 := by simp [exponentStep]; omega
    have hstep2 : exponentStep j ≠ 2 := by simp [exponentStep]; omega
    simpa [FunctionalCoefficientEquation, forcing, hstep0, hstep1,
      hstep2, mul_assoc] using h

/-- A nonzero seed coefficient propagates to every point of the infinite
exponent orbit. -/
theorem coefficient_nonzero_on_orbit
    {A D kappa b1 : ℚ} (hD : D ≠ 0) (hkappa : kappa ≠ 0)
    (r : ℤ →₀ ℚ) (h : CoefficientLaw A D kappa b1 r)
    (hb1 : b1 ≠ 0) (n : ℕ) : r (exponentOrbit n) ≠ 0 := by
  induction n with
  | zero =>
      intro hr
      have hs := h.seed
      change r 1 = 0 at hr
      rw [hr, mul_zero] at hs
      exact hb1 hs.symm
  | succ n ih =>
      intro hr
      have hlower := exponentOrbit_lower_bound n
      have hp := h.propagate (exponentOrbit n) (by omega)
      have hr' : r (exponentStep (exponentOrbit n)) = 0 := by
        simpa only [exponentOrbit] using hr
      rw [hr', mul_zero] at hp
      have hkpow : kappa ^ exponentOrbit n ≠ 0 :=
        zpow_ne_zero _ hkappa
      exact (mul_ne_zero hD (mul_ne_zero hkpow ih))
        (by simpa [mul_assoc] using hp.symm)

/-- Generic finite-Laurent no-go for a base-squaring coefficient law. -/
theorem no_finiteLaurent_coefficientLaw
    {A D kappa b1 : ℚ}
    (hD : D ≠ 0) (hkappa : kappa ≠ 0) (hb1 : b1 ≠ 0) :
    ¬ ∃ r : ℤ →₀ ℚ, CoefficientLaw A D kappa b1 r := by
  rintro ⟨r, hlaw⟩
  have hr1 := coefficient_nonzero_on_orbit hD hkappa r hlaw hb1 0
  have hsne : r.support.Nonempty :=
    ⟨1, Finsupp.mem_support_iff.mpr (by simpa [exponentOrbit] using hr1)⟩
  let m : ℤ := r.support.max' hsne
  have hm_mem : m ∈ r.support := Finset.max'_mem _ _
  have hm_nonneg : 0 ≤ m := by
    have hm_one : 1 ≤ m :=
      Finset.le_max' _ 1 (Finsupp.mem_support_iff.mpr
        (by simpa [exponentOrbit] using hr1))
    omega
  let k : ℕ := m.toNat + 1
  have hmk : m < exponentOrbit k := by
    have hlower := exponentOrbit_lower_bound k
    have hmcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nonneg
    dsimp [k] at hlower ⊢
    omega
  have horbit_ne := coefficient_nonzero_on_orbit hD hkappa r hlaw hb1 k
  have horbit_mem : exponentOrbit k ∈ r.support :=
    Finsupp.mem_support_iff.mpr horbit_ne
  have hle : exponentOrbit k ≤ m := Finset.le_max' _ _ horbit_mem
  omega

/-- Generic no-go stated for the complete base-squaring functional equation,
not merely its extracted coefficient recurrence. -/
theorem no_finiteLaurent_functionalEquation
    {A D kappa b0 b1 b2 : ℚ}
    (hD : D ≠ 0) (hkappa : kappa ≠ 0) (hb1 : b1 ≠ 0) :
    ¬ ∃ r : ℤ →₀ ℚ,
      FunctionalCoefficientEquation A D kappa b0 b1 b2 r := by
  rintro ⟨r, heq⟩
  exact no_finiteLaurent_coefficientLaw hD hkappa hb1
    ⟨r, coefficientLaw_of_functionalEquation heq⟩

def A : ℚ := 3 ^ 114
def D : ℚ := 2 ^ 154
def kappa : ℚ := 3 ^ 40 / 2 ^ 54
def b1 : ℚ := 2 ^ 77
def b0 : ℚ := 3 ^ 57 + 2 ^ 77
def b2 : ℚ := 2 ^ 77

/-- The concrete `g ↦ 2g` return quine has no finite Laurent payload. -/
theorem no_doubling_quine_finiteLaurent :
    ¬ ∃ r : ℤ →₀ ℚ,
      FunctionalCoefficientEquation A D kappa b0 b1 b2 r := by
  apply no_finiteLaurent_functionalEquation
  · norm_num [D]
  · norm_num [kappa]
  · norm_num [b1]

end DoublingQuineNoGo
end KontoroC
