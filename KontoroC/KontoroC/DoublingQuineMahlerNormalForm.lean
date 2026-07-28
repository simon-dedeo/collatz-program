/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DoublingQuineRationalNoGo
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Canonical Mahler coordinates for the doubling return quine

The normalized variable used by the first base-squaring audit still carries a
coefficient in its substitution:

`z ↦ kappa * z^2`.

The standard Mahler coordinate is `x = kappa*z`.  If

`H(x) = x^2 * f(x/kappa)`,

then the original equation becomes the ordinary first-order `2`-Mahler
equation

`H(x) = Q(x) + lambda * H(x^2)`.

Moreover the opcode point is exactly

`x_g = (2^23/3^17)^g`,

so the legal update `g ↦ 2g` is literally `x ↦ x^2`.  Iterating the
equation splits every value into a finite particular prefix and one
homogeneous boundary term.  This is the precise standard-coordinate form of
the Archimedean boundary-amplitude gate: bounded/analytic behavior at zero
discards the final term, while an ordinary construction must retain it.

The file proves only exact algebra over `ℚ`.  It does not import a Mahler
transcendence theorem and does not construct an integer orbit.
-/

namespace KontoroC
namespace DoublingQuineMahlerNormalForm

open DoublingQuineNoGo

/-- The canonical `S`-unit coordinate ratio. -/
def alpha : ℚ := 2 ^ 23 / 3 ^ 17

/-- The original normalized opcode point. -/
def zPoint (g : ℕ) : ℚ :=
  2 ^ (23 * g + 54) / 3 ^ (17 * g + 40)

/-- The constant coefficient in the standard first-order Mahler equation. -/
def lambda : ℚ := D / (A * kappa ^ 2)

/-- The quadratic forcing before the standard coordinate change. -/
def forcingValue (z : ℚ) : ℚ := b0 + b1 * z + b2 * z ^ 2

/-- The forcing after `x=kappa*z` and `H(x)=x^2*f(x/kappa)`. -/
def standardForcing (x : ℚ) : ℚ :=
  x ^ 2 / A * forcingValue (x / kappa)

/-- Pointwise normalization of an arbitrary payload function. -/
def normalize (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  x ^ 2 * f (x / kappa)

/-- The original base-squaring functional equation, stated pointwise. -/
def OriginalEquation (f : ℚ → ℚ) : Prop :=
  ∀ z, A * f z - D * z ^ 2 * f (kappa * z ^ 2) = forcingValue z

/-- The canonical first-order `2`-Mahler equation. -/
def StandardEquation (H : ℚ → ℚ) : Prop :=
  ∀ x, H x = standardForcing x + lambda * H (x ^ 2)

theorem alpha_pos : 0 < alpha := by
  norm_num [alpha]

theorem alpha_lt_one : alpha < 1 := by
  norm_num [alpha]

theorem lambda_pos : 0 < lambda := by
  norm_num [lambda, A, D, kappa]

theorem lambda_lt_one : lambda < 1 := by
  norm_num [lambda, A, D, kappa]

theorem lambda_eq : lambda = 2 ^ 262 / 3 ^ 194 := by
  rw [show 262 = 154 + 2 * 54 by omega,
    show 194 = 114 + 2 * 40 by omega, pow_add, pow_add, pow_mul, pow_mul]
  simp only [lambda, A, D, kappa, div_pow]
  field_simp

theorem norm_alpha_padic :
    ‖(alpha : ℚ_[2])‖ = ((2 : ℝ)⁻¹) ^ 23 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [alpha, Rat.cast_div, Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofNat, norm_div, norm_pow, norm_pow, htwo, hthree, one_pow,
    div_one]

theorem norm_lambda_padic :
    ‖(lambda : ℚ_[2])‖ = ((2 : ℝ)⁻¹) ^ 262 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [lambda_eq, Rat.cast_div, Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofNat, norm_div, norm_pow, norm_pow, htwo, hthree, one_pow,
    div_one]

theorem kappa_mul_zPoint (g : ℕ) :
    kappa * zPoint g = alpha ^ g := by
  simp only [kappa, zPoint, alpha]
  rw [show (2 : ℚ) ^ (23 * g + 54) = 2 ^ (23 * g) * 2 ^ 54 by
      rw [pow_add],
    show (3 : ℚ) ^ (17 * g + 40) = 3 ^ (17 * g) * 3 ^ 40 by
      rw [pow_add],
    pow_mul, pow_mul, div_pow]
  field_simp

/-- In canonical coordinates the legal opcode doubling is exactly squaring. -/
theorem alphaPoint_double (g : ℕ) :
    alpha ^ (2 * g) = (alpha ^ g) ^ 2 := by
  rw [← pow_mul]
  congr 1
  omega

/-- The homemade equation is an ordinary first-order `2`-Mahler equation
after the canonical coordinate and gauge changes. -/
theorem standardEquation_of_original {f : ℚ → ℚ}
    (h : OriginalEquation f) : StandardEquation (normalize f) := by
  intro x
  have hkappa : kappa ≠ 0 := by norm_num [kappa]
  have hA : A ≠ 0 := by norm_num [A]
  have hx := h (x / kappa)
  simp only [OriginalEquation] at h
  simp only [normalize, standardForcing, lambda]
  simp only [forcingValue] at hx ⊢
  have harg : kappa * (x / kappa) ^ 2 = x ^ 2 / kappa := by
    field_simp
  rw [harg] at hx
  field_simp [hkappa, hA] at hx ⊢
  nlinarith

/-- Iterated squaring, kept separate so finite Mahler unrolling is syntactic. -/
def squareIter (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 => squareIter x n ^ 2

@[simp] theorem squareIter_zero (x : ℚ) : squareIter x 0 = x := rfl

@[simp] theorem squareIter_succ (x : ℚ) (n : ℕ) :
    squareIter x (n + 1) = squareIter x n ^ 2 := rfl

theorem squareIter_eq_pow (x : ℚ) (n : ℕ) :
    squareIter x n = x ^ (2 ^ n) := by
  induction n with
  | zero => simp [squareIter]
  | succ n ih =>
      rw [squareIter_succ, ih, ← pow_mul, pow_succ]

/-- Finite particular part of a first-order Mahler equation. -/
def particularPrefix (q : ℚ → ℚ) (c x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => q x + c * particularPrefix q c (x ^ 2) n

@[simp] theorem particularPrefix_zero (q : ℚ → ℚ) (c x : ℚ) :
    particularPrefix q c x 0 = 0 := rfl

@[simp] theorem particularPrefix_succ
    (q : ℚ → ℚ) (c x : ℚ) (n : ℕ) :
    particularPrefix q c x (n + 1) =
      q x + c * particularPrefix q c (x ^ 2) n := rfl

/-- Exact finite split into the particular Mahler prefix and the surviving
homogeneous boundary.  No convergence hypothesis is used. -/
theorem finite_boundary_split {H : ℚ → ℚ}
    (h : StandardEquation H) (x : ℚ) (N : ℕ) :
    H x = particularPrefix standardForcing lambda x N +
      lambda ^ N * H (squareIter x N) := by
  induction N generalizing x with
  | zero => simp [particularPrefix, squareIter]
  | succ N ih =>
      rw [h x, particularPrefix_succ, ih (x := x ^ 2)]
      have hsquare : squareIter (x ^ 2) N = squareIter x (N + 1) := by
        rw [squareIter_eq_pow, squareIter_eq_pow, ← pow_mul, pow_succ]
        simp [Nat.mul_comm]
      rw [hsquare, pow_succ]
      ring

/-- Differences of two solutions are pure homogeneous boundary terms. -/
theorem solution_difference_boundary
    {H₁ H₂ : ℚ → ℚ} (h₁ : StandardEquation H₁)
    (h₂ : StandardEquation H₂) (x : ℚ) (N : ℕ) :
    H₁ x - H₂ x =
      lambda ^ N * (H₁ (squareIter x N) - H₂ (squareIter x N)) := by
  rw [finite_boundary_split h₁ x N, finite_boundary_split h₂ x N]
  ring

/-- Along an opcode ray, the endpoint of the finite split is the opcode
`2^N*g`, with no residual homemade coordinate. -/
theorem squareIter_alphaPoint (g N : ℕ) :
    squareIter (alpha ^ g) N = alpha ^ (2 ^ N * g) := by
  rw [squareIter_eq_pow, ← pow_mul]
  simp [Nat.mul_comm]

/-- Concrete boundary split on the legal doubling-opcode ray. -/
theorem opcode_boundary_split {H : ℚ → ℚ}
    (h : StandardEquation H) (g N : ℕ) :
    H (alpha ^ g) =
      particularPrefix standardForcing lambda (alpha ^ g) N +
        lambda ^ N * H (alpha ^ (2 ^ N * g)) := by
  simpa only [squareIter_alphaPoint] using
    finite_boundary_split h (alpha ^ g) N

end DoublingQuineMahlerNormalForm
end KontoroC
