/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.FiniteSystem

/-!
# Elementary finite nonlinear Perron lemmas

These are the order/homogeneity parts of nonlinear Perron theory that can be
proved directly in mathlib.  Existence of a positive eigenvector from strong
connectivity remains the nontrivial theorem still to formalize.
-/

namespace CleanLean.KL

open scoped BigOperators

section FiniteCone

variable {I : Type} [Finite I] [Nonempty I]

/-- Positive degree-one homogeneity on the nonnegative scalar cone. -/
def PosHomogeneous (F : (I → ℝ) → I → ℝ) : Prop :=
  ∀ (a : ℝ), 0 ≤ a → ∀ x, F (fun i => a * x i) = fun i => a * F x i

/-- A strictly positive nonlinear eigenpair. -/
def IsPositiveEigenpair (F : (I → ℝ) → I → ℝ)
    (x : I → ℝ) (r : ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ F x = fun i => r * x i

/-- Finite projective comparison: a nonnegative vector is dominated by a
strictly positive vector at a scalar for which equality holds somewhere. -/
theorem exists_tight_domination
    (x y : I → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 ≤ y i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ i : I,
      (∀ j, y j ≤ A * x j) ∧ y i = A * x i := by
  classical
  letI := Fintype.ofFinite I
  have huniv : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset I) (fun j => y j / x j) huniv
  refine ⟨y i / x i, div_nonneg (hy i) (hx i).le, i, ?_, ?_⟩
  · intro j
    have hratio := hmax j (Finset.mem_univ j)
    exact (div_le_iff₀ (hx j)).1 hratio
  · field_simp [ne_of_gt (hx i)]

/-- Positive eigenvectors of a monotone homogeneous finite-cone map all have
the same eigenvalue.  Eigenvectors themselves need not be unique. -/
theorem positiveEigenvalue_unique
    (F : (I → ℝ) → I → ℝ)
    (hmono : Monotone F) (hhom : PosHomogeneous F)
    {x y : I → ℝ} {r s : ℝ}
    (hx : IsPositiveEigenpair F x r)
    (hy : IsPositiveEigenpair F y s) : r = s := by
  rcases hx with ⟨hxpos, hxeig⟩
  rcases hy with ⟨hypos, hyeig⟩
  obtain ⟨A, hA0, i, hdom, htight⟩ :=
    exists_tight_domination y x hypos (fun j => (hxpos j).le)
  have hmap := hmono hdom
  rw [hhom A hA0 y, hxeig, hyeig] at hmap
  have hi := hmap i
  change r * x i ≤ A * (s * y i) at hi
  rw [htight] at hi
  have hyi : 0 < y i := hypos i
  have hApos : 0 < A := by
    by_contra hnot
    have hAz : A = 0 := le_antisymm (le_of_not_gt hnot) hA0
    rw [hAz, zero_mul] at htight
    linarith [hxpos i]
  have hrs : r ≤ s := by nlinarith [mul_pos hApos hyi]
  obtain ⟨B, hB0, j, hdom', htight'⟩ :=
    exists_tight_domination x y hxpos (fun q => (hypos q).le)
  have hmap' := hmono hdom'
  rw [hhom B hB0 x, hyeig, hxeig] at hmap'
  have hj := hmap' j
  change s * y j ≤ B * (r * x j) at hj
  rw [htight'] at hj
  have hxj : 0 < x j := hxpos j
  have hBpos : 0 < B := by
    by_contra hnot
    have hBz : B = 0 := le_antisymm (le_of_not_gt hnot) hB0
    rw [hBz, zero_mul] at htight'
    linarith [hypos j]
  have hsr : s ≤ r := by nlinarith [mul_pos hBpos hxj]
  exact le_antisymm hrs hsr

/-- A nonzero nonnegative subeigenvector forces the positive Perron
eigenvalue to be at least one. -/
theorem one_le_positiveEigenvalue_of_subeigenvector
    (F : (I → ℝ) → I → ℝ)
    (hmono : Monotone F) (hhom : PosHomogeneous F)
    {x y : I → ℝ} {r : ℝ}
    (hx : IsPositiveEigenpair F x r)
    (hy0 : ∀ i, 0 ≤ y i) (hyne : ∃ i, 0 < y i)
    (hsub : ∀ i, y i ≤ F y i) :
    1 ≤ r := by
  rcases hx with ⟨hxpos, hxeig⟩
  obtain ⟨A, hA0, i, hdom, htight⟩ := exists_tight_domination x y hxpos hy0
  have hApos : 0 < A := by
    obtain ⟨j, hyj⟩ := hyne
    have := hdom j
    nlinarith [hxpos j]
  have hmap := hmono hdom
  rw [hhom A hA0 x, hxeig] at hmap
  have hchain : y i ≤ A * (r * x i) := (hsub i).trans (hmap i)
  rw [htight] at hchain
  have hxi : 0 < x i := hxpos i
  nlinarith [mul_pos hApos hxi]

end FiniteCone

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

theorem fiberMin_const_mul (a : ℝ) (ha : 0 ≤ a)
    (c : S.State → ℝ) (r : S.Coarse) :
    S.fiberMin (fun m => a * c m) r = a * S.fiberMin c r := by
  simp only [fiberMin]
  rw [mul_min_of_nonneg _ _ ha, mul_min_of_nonneg _ _ ha]

theorem operator_monotone_map
    (w : Weights ℝ) (hw0 : 0 ≤ w.transport) (hw2 : 0 ≤ w.retarded)
    (hw8 : 0 ≤ w.advanced) : Monotone (S.operator w) := by
  intro c d h
  exact S.operator_mono w hw0 hw2 hw8 h

theorem operator_posHomogeneous (w : Weights ℝ) :
    PosHomogeneous (S.operator w) := by
  intro a ha c
  funext m
  rw [operator]
  rw [operator]
  rw [S.fiberMin_const_mul a ha]
  cases S.branch m <;> simp only <;> ring

end

end FiniteSystem

end CleanLean.KL
