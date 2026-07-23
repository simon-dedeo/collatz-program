/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Exact rank of a three-mode geometric scalarization

The full-support scalar theta combination has coefficient multiplier
`s₀ + s₁ R^n + s₂ R^(2n)`.  Although this is one scalar sequence, its
three dilation modes do not collapse to a first-order problem.  We prove its
order-three recurrence, compute its `3 x 3` Hankel determinant, and rule out
every global recurrence of order at most two when that determinant is
nonzero.
-/

namespace KontoroC
namespace ThetaScalarRank

/-- The three-node moment sequence occurring in the scalarized theta
coefficients. -/
def moment {A : Type*} [CommRing A] (R s₀ s₁ s₂ : A) (n : ℕ) : A :=
  s₀ * 1 ^ n + s₁ * R ^ n + s₂ * (R ^ 2) ^ n

def characteristicExpr {A : Type*} [CommRing A] (R x : A) (n : ℕ) : A :=
  x ^ (n + 3) - (1 + R + R ^ 2) * x ^ (n + 2) +
    (R + R ^ 2 + R ^ 3) * x ^ (n + 1) - R ^ 3 * x ^ n

/-- The characteristic polynomial has roots `1`, `R`, and `R²`. -/
theorem geometric_characteristic {A : Type*} [CommRing A]
    (R x : A) (n : ℕ) :
    characteristicExpr R x n =
      x ^ n * ((x - 1) * (x - R) * (x - R ^ 2)) := by
  rw [characteristicExpr]
  rw [show n + 3 = n + 1 + 1 + 1 by omega,
    show n + 2 = n + 1 + 1 by omega]
  simp only [pow_succ]
  ring

/-- Exact order-three recurrence requested in QM126a. -/
theorem moment_recurrence {A : Type*} [CommRing A]
    (R s₀ s₁ s₂ : A) (n : ℕ) :
    moment R s₀ s₁ s₂ (n + 3) -
        (1 + R + R ^ 2) * moment R s₀ s₁ s₂ (n + 2) +
        (R + R ^ 2 + R ^ 3) * moment R s₀ s₁ s₂ (n + 1) -
        R ^ 3 * moment R s₀ s₁ s₂ n = 0 := by
  calc
    _ = s₀ * characteristicExpr R 1 n +
          s₁ * characteristicExpr R R n +
          s₂ * characteristicExpr R (R ^ 2) n := by
      simp only [moment, characteristicExpr]
      ring
    _ = 0 := by
      rw [geometric_characteristic, geometric_characteristic,
        geometric_characteristic]
      ring

def hankelThree {A : Type*} [CommRing A] (u : ℕ → A) :
    Matrix (Fin 3) (Fin 3) A :=
  fun i j => u ((i : ℕ) + (j : ℕ))

/-- Exact three-node moment determinant (QM126b). -/
theorem det_hankelThree_moment {A : Type*} [CommRing A]
    (R s₀ s₁ s₂ : A) :
    (hankelThree (moment R s₀ s₁ s₂)).det =
      s₀ * s₁ * s₂ * R ^ 2 * (R - 1) ^ 6 * (R + 1) ^ 2 := by
  rw [Matrix.det_fin_three]
  simp only [hankelThree, moment]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

/-- A global homogeneous recurrence with at most two previous terms. -/
def HasRecurrenceAtMostTwo {A : Type*} [CommRing A] (u : ℕ → A) : Prop :=
  ∃ a b : A, ∀ n, u (n + 2) = a * u (n + 1) + b * u n

/-- Every order-at-most-two sequence has singular `3 x 3` Hankel matrix. -/
theorem det_hankelThree_eq_zero_of_hasRecurrenceAtMostTwo
    {A : Type*} [CommRing A] {u : ℕ → A}
    (h : HasRecurrenceAtMostTwo u) :
    (hankelThree u).det = 0 := by
  obtain ⟨a, b, hrec⟩ := h
  let M := hankelThree u
  let c : Fin 3 → A := fun i => if (i : ℕ) = 0 then b
    else if (i : ℕ) = 1 then a else 0
  have hcol (k : Fin 3) :
      (∑ i, c i • M k i) = M k 2 := by
    fin_cases k <;>
      simp [c, M, hankelThree, hrec, Fin.sum_univ_succ] <;> ring
  have hupdate :
      M.updateCol 2 (fun k => ∑ i, c i • M k i) = M := by
    ext k j
    by_cases hj : j = 2
    · subst j
      simp only [Matrix.updateCol_self]
      exact hcol k
    · rw [Matrix.updateCol_ne hj]
  have hdet := Matrix.det_updateCol_sum M 2 c
  rw [hupdate] at hdet
  simpa [c] using hdet

/-- Nonzero moment determinant rules out every rank-one or rank-two scalar
recurrence. -/
theorem not_hasRecurrenceAtMostTwo_of_moment_factors_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] (R s₀ s₁ s₂ : A)
    (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hR : R ≠ 0) (hRm : R - 1 ≠ 0) (hRp : R + 1 ≠ 0) :
    ¬HasRecurrenceAtMostTwo (moment R s₀ s₁ s₂) := by
  intro hrec
  have hzero := det_hankelThree_eq_zero_of_hasRecurrenceAtMostTwo hrec
  rw [det_hankelThree_moment] at hzero
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hs₀ hs₁) hs₂)
          (pow_ne_zero _ hR))
        (pow_ne_zero _ hRm))
      (pow_ne_zero _ hRp) hzero

end ThetaScalarRank
end KontoroC
