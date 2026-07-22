/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeTypedInterface

/-!
# Exact algebra of the two-step phase swap

The phase-swap word restores signed chart separation by crossing the charts
at its internal boundary.  This file checks its exponent identities and the
general signed-area law.  It also records the adversarial qualification:
restoring separation does not cancel the strictly negative typed interface
tax of the internal public boundary.
-/

namespace KontoroC
namespace ChargePhaseSwap

/-- Total ternary exponent of a two-step public word with boundary opcodes
`m0,m1,m2` and recharge counts `h0,h1`. -/
def ternaryTotal (m₀ m₁ h₀ h₁ : ℕ) : ℕ :=
  114 * h₀ + 17 * m₀ + (114 * h₁ + 17 * m₁)

/-- Total binary exponent of the same word. -/
def binaryTotal (m₁ m₂ h₀ h₁ : ℕ) : ℕ :=
  154 * h₀ + 23 * m₁ + (154 * h₁ + 23 * m₂)

/-- The three boundary phases of the minimal swap word
`r -> L-r -> r+d`. -/
def boundaryPhase (L d r : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => r
  | ⟨1, _⟩ => L - r
  | ⟨2, _⟩ => r + d

/-- PS1, ternary half: the composite gain is independent of the moving
outer phase. -/
theorem ternaryTotal_phaseSwap {L r h₀ h₁ : ℕ} (hr : r ≤ L) :
    ternaryTotal r (L - r) h₀ h₁ =
      114 * (h₀ + h₁) + 17 * L := by
  simp only [ternaryTotal]
  omega

/-- PS1, binary half. -/
theorem binaryTotal_phaseSwap {L d r h₀ h₁ : ℕ} (hr : r ≤ L) :
    binaryTotal (L - r) (r + d) h₀ h₁ =
      154 * (h₀ + h₁) + 23 * (L + d) := by
  simp only [binaryTotal]
  omega

/-- Adjacent phase-swap words have signed boundary differences `(d,-d,d)`.
The statement uses integers so the internal chart crossing is visible rather
than truncated away. -/
theorem boundary_difference {L d r : ℕ} (hr : r + d ≤ L) (i : Fin 3) :
    (boundaryPhase L d (r + d) i : ℤ) -
        (boundaryPhase L d r i : ℤ) =
      if (i : ℕ) = 1 then -(d : ℤ) else (d : ℤ) := by
  fin_cases i <;> simp [boundaryPhase]
  all_goals omega

/-- PS2 in its algebraically minimal form.  Equal total `Q` and `P` give
the signed-area law after eliminating the total recharge difference. -/
theorem signed_area_law (d₀ dN internal rechargeDifference : ℤ)
    (hQ : 114 * rechargeDifference + 17 * (d₀ + internal) = 0)
    (hP : 154 * rechargeDifference + 23 * (internal + dN) = 0) :
    1311 * dN - 1309 * d₀ = -2 * internal := by
  linear_combination (57 : ℤ) * hP - (77 : ℤ) * hQ

/-- Total ternary exponent for a finite signed opcode/recharge word.  Signed
coordinates make comparison of two words direct. -/
def wordTernaryTotal (m h : ℕ → ℤ) (N : ℕ) : ℤ :=
  114 * ∑ i ∈ Finset.range N, h i +
    17 * ∑ i ∈ Finset.range N, m i

/-- Total binary exponent, using the target opcode of each step. -/
def wordBinaryTotal (m h : ℕ → ℤ) (N : ℕ) : ℤ :=
  154 * ∑ i ∈ Finset.range N, h i +
    23 * ∑ i ∈ Finset.range N, m (i + 1)

/-- PS2 stated for two actual finite opcode/recharge words with equal total
exponents, rather than merely for pre-simplified scalar equations. -/
theorem signed_area_law_of_equal_word_totals
    (m m' h h' : ℕ → ℤ) (N : ℕ) (hN : 0 < N)
    (hQ : wordTernaryTotal m h N = wordTernaryTotal m' h' N)
    (hP : wordBinaryTotal m h N = wordBinaryTotal m' h' N) :
    1311 * (m' N - m N) - 1309 * (m' 0 - m 0) =
      -2 * ∑ i ∈ Finset.Ico 1 N, (m' i - m i) := by
  let d : ℕ → ℤ := fun i => m' i - m i
  let e : ℕ → ℤ := fun i => h' i - h i
  let S : ℤ := ∑ i ∈ Finset.Ico 1 N, d i
  let E : ℤ := ∑ i ∈ Finset.range N, e i
  have hsource : (∑ i ∈ Finset.range N, d i) = d 0 + S := by
    have hs := Finset.sum_Ico_eq_sub d (show 1 ≤ N by omega)
    simp only [Finset.sum_range_one] at hs
    dsimp only [S]
    linarith
  have htarget : (∑ i ∈ Finset.range N, d (i + 1)) = S + d N := by
    have hs := Finset.sum_Ico_eq_sum_range d 1 (N + 1)
    have hsplit := Finset.sum_Ico_succ_top (show 1 ≤ N by omega) d
    rw [hs] at hsplit
    simp only [Nat.add_sub_cancel] at hsplit
    dsimp only [S]
    simpa [Nat.add_comm] using hsplit
  have hQzero : 114 * E + 17 * (d 0 + S) = 0 := by
    simp only [wordTernaryTotal] at hQ
    dsimp only [E, e, d]
    rw [← hsource]
    rw [show (∑ i ∈ Finset.range N, d i) =
        (∑ i ∈ Finset.range N, m' i) -
          (∑ i ∈ Finset.range N, m i) by
      simp [d, Finset.sum_sub_distrib]]
    simp only [Finset.sum_sub_distrib]
    linear_combination -hQ
  have hPzero : 154 * E + 23 * (S + d N) = 0 := by
    simp only [wordBinaryTotal] at hP
    dsimp only [E, e, d]
    rw [← htarget]
    rw [show (∑ i ∈ Finset.range N, d (i + 1)) =
        (∑ i ∈ Finset.range N, m' (i + 1)) -
          (∑ i ∈ Finset.range N, m (i + 1)) by
      simp [d, Finset.sum_sub_distrib]]
    simp only [Finset.sum_sub_distrib]
    linear_combination -hP
  have harea := signed_area_law (d 0) (d N) S E hQzero hPzero
  simpa [d, S] using harea

/-- Equal positive endpoint separation forces the sum of signed internal
separations to be negative.  A booster must therefore cross chart order. -/
theorem internal_eq_neg_endpoint_of_restored_separation
    (d internal rechargeDifference : ℤ)
    (hQ : 114 * rechargeDifference + 17 * (d + internal) = 0)
    (hP : 154 * rechargeDifference + 23 * (internal + d) = 0) :
    internal = -d := by
  have h := signed_area_law d d internal rechargeDifference hQ hP
  linarith

/-- The advertised smallest phase-swap delay line. -/
theorem smallest_boundary_shapes :
    (boundaryPhase 4 1 1 0, boundaryPhase 4 1 1 1, boundaryPhase 4 1 1 2) =
        (1, 3, 2) ∧
      (boundaryPhase 4 1 2 0, boundaryPhase 4 1 2 1, boundaryPhase 4 1 2 2) =
        (2, 2, 3) ∧
      (boundaryPhase 4 1 3 0, boundaryPhase 4 1 3 1, boundaryPhase 4 1 3 2) =
        (3, 1, 4) := by
  norm_num [boundaryPhase]

theorem smallest_composite_exponents :
    ternaryTotal 1 3 1 1 = 296 ∧
      binaryTotal 3 2 1 1 = 423 ∧
      ternaryTotal 2 2 1 1 = 296 ∧
      binaryTotal 2 3 1 1 = 423 := by
  norm_num [ternaryTotal, binaryTotal]

/-! ## Adversarial qualification -/

open ChargeTypedInterface

theorem internalTax_two (a d : ℕ → ℚ) :
    internalTax a d 2 = a 0 * d 1 := by
  norm_num [internalTax, prefixCoefficient]

/-- A two-step phase swap can restore its signed chart separation, but if it
consists of exact public steps then its sole internal boundary still pays a
strictly negative typed tax. -/
theorem two_step_public_tax_neg (g : PublicWord) (hg : g.length = 2) :
    g.typedTax < 0 := by
  exact g.typedTax_neg (by omega)

end ChargePhaseSwap
end KontoroC
