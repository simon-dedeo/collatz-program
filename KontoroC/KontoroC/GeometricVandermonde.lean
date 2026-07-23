/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Multiplicity

/-!
# Vandermonde determinants on a geometric grid

The active period-three ether reduction produces `3 * ν` Skolem roots on
one consecutive geometric grid.  This file records the exact determinant
factorization, including the multiplicity of every gap.  Unlike the fixed
three-point determinant, the gap product has quadratic multiplicity in `ν`.
-/

namespace KontoroC
namespace GeometricVandermonde

open Finset

/-- Product of geometric gaps grouped by their distance.  A gap of distance
`d` occurs `m-d` times among `m` consecutive points. -/
def gapProductSub {R : Type*} [CommRing R] (r : R) (m : ℕ) : R :=
  ∏ d ∈ Finset.Ico 1 m, (r ^ d - 1) ^ (m - d)

theorem gapProductSub_succ {R : Type*} [CommRing R] (r : R) (m : ℕ) :
    gapProductSub r (m + 1) =
      gapProductSub r m * ∏ d ∈ Finset.Icc 1 m, (r ^ d - 1) := by
  by_cases hm : m = 0
  · subst m
    simp [gapProductSub]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  rw [gapProductSub, gapProductSub, Finset.prod_Ico_succ_top hm1]
  rw [show m + 1 - m = 1 by omega, pow_one]
  rw [← Finset.prod_Ico_mul_eq_prod_Icc hm1]
  rw [← mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro d hd
  have hdlt : d < m := (Finset.mem_Ico.mp hd).2
  rw [show m + 1 - d = (m - d) + 1 by omega, pow_succ]

/-- Adding the last size by exposing the zero-index row leaves a shifted
geometric Vandermonde and one copy of every new gap. -/
theorem det_geometric_succ {R : Type*} [CommRing R]
    (α r : R) (m : ℕ) :
    (Matrix.vandermonde
      (fun i : Fin (m + 1) => α * r ^ (i : ℕ))).det =
      (∏ d ∈ Finset.Icc 1 m, α * (r ^ d - 1)) *
        (Matrix.vandermonde
          (fun i : Fin m => (α * r) * r ^ (i : ℕ))).det := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde]
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
  have hfirst :
      (∏ j : Fin m, (α * r ^ (j.succ : ℕ) - α * r ^ (0 : ℕ))) =
        ∏ d ∈ Finset.Icc 1 m, α * (r ^ d - 1) := by
    calc
      _ = ∏ j : Fin m, α * (r ^ ((j : ℕ) + 1) - 1) := by
        apply Finset.prod_congr rfl
        intro j _hj
        simp only [Fin.val_succ, pow_zero]
        ring
      _ = ∏ k ∈ Finset.range m, α * (r ^ (k + 1) - 1) :=
        Fin.prod_univ_eq_prod_range
          (fun k : ℕ => α * (r ^ (k + 1) - 1)) m
      _ = ∏ d ∈ Finset.Ico 1 (m + 1), α * (r ^ d - 1) := by
        rw [Finset.prod_Ico_eq_prod_range]
        simp only [Nat.add_sub_cancel, add_comm]
      _ = ∏ d ∈ Finset.Icc 1 m, α * (r ^ d - 1) := by
        rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [Fin.val_zero]
  rw [hfirst]
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  apply Finset.prod_congr rfl
  intro j _hj
  simp only [Fin.val_succ, pow_succ]
  ring

/-- Exact Vandermonde factorization for `m` consecutive geometric points
`alpha, alpha*r, ..., alpha*r^(m-1)` (QM123b). -/
theorem det_geometric {R : Type*} [CommRing R]
    (α r : R) (m : ℕ) :
    (Matrix.vandermonde (fun i : Fin m => α * r ^ (i : ℕ))).det =
      α ^ (m.choose 2) * r ^ (m.choose 3) * gapProductSub r m := by
  induction m generalizing α with
  | zero => simp [gapProductSub]
  | succ m ih =>
      rw [det_geometric_succ, ih]
      have hnew :
          (∏ d ∈ Finset.Icc 1 m, α * (r ^ d - 1)) =
            α ^ m * ∏ d ∈ Finset.Icc 1 m, (r ^ d - 1) := by
        rw [Finset.prod_mul_distrib]
        simp
      rw [hnew, mul_pow]
      rw [show (m + 1).choose 2 = m.choose 2 + m by
        rw [show m + 1 = m.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      rw [show (m + 1).choose 3 = m.choose 3 + m.choose 2 by
        rw [show m + 1 = m.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      rw [pow_add, pow_add, gapProductSub_succ]
      ring

/-! ## Cleared gap numerators and auxiliary-prime multiplicity -/

/-- Numerator of the grouped gap product for a rational ratio `u / v`, after
clearing the powers of `v`.  The order hypothesis `u ≤ v` makes natural
subtraction literal. -/
def gapNumerator (u v m : ℕ) : ℕ :=
  ∏ d ∈ Finset.Ico 1 m, (v ^ d - u ^ d) ^ (m - d)

/-- Total number of unordered pairs, expressed as the sum of gap
multiplicities. -/
theorem sum_gap_multiplicities (m : ℕ) :
    (∑ d ∈ Finset.Ico 1 m, (m - d)) = m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        simp
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      rw [Finset.sum_Ico_succ_top hm1]
      have hshift : ∀ d ∈ Finset.Ico 1 m,
          m + 1 - d = (m - d) + 1 := by
        intro d hd
        have hdlt := (Finset.mem_Ico.mp hd).2
        omega
      have hsum :
          (∑ d ∈ Finset.Ico 1 m, (m + 1 - d)) =
            ∑ d ∈ Finset.Ico 1 m, ((m - d) + 1) := by
        apply Finset.sum_congr rfl
        exact hshift
      rw [hsum, show m + 1 - m = 1 by omega]
      rw [Finset.sum_add_distrib, ih]
      have hone : (∑ _d ∈ Finset.Ico 1 m, 1) = m - 1 := by simp
      rw [hone]
      rw [show (m + 1).choose 2 = m.choose 2 + m by
        rw [show m + 1 = m.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      omega

theorem dvd_pow_sub_pow_of_dvd_sub {p u v d : ℕ}
    (huv : u ≤ v) (hp : p ∣ v - u) :
    p ∣ v ^ d - u ^ d := by
  have hmod : u ≡ v [MOD p] :=
    (Nat.modEq_iff_dvd' huv).2 hp
  have hpow := hmod.pow d
  exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left huv d)).1 hpow

/-- Every prime divisor of the base gap occurs in the cleared full-grid
numerator at least once per unordered pair (QM123c, in divisibility form). -/
theorem pow_choose_two_dvd_gapNumerator {p u v m : ℕ}
    (huv : u ≤ v) (hp : p ∣ v - u) :
    p ^ (m.choose 2) ∣ gapNumerator u v m := by
  rw [← sum_gap_multiplicities m,
    ← Finset.prod_pow_eq_pow_sum]
  unfold gapNumerator
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun d _hd =>
    pow_dvd_pow_of_dvd (dvd_pow_sub_pow_of_dvd_sub huv hp) (m - d))

theorem padicValNat_prod {p : ℕ} [Fact p.Prime]
    {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) =
      ∑ i ∈ s, padicValNat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (by simp)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (by simp [hi])
      have hprod : ∏ i ∈ s, f i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr hfs
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValNat.mul hfa hprod, ih hfs]

theorem padicValNat_gapNumerator {p u v m : ℕ} [Fact p.Prime]
    (huv : u < v) :
    padicValNat p (gapNumerator u v m) =
      ∑ d ∈ Finset.Ico 1 m,
        (m - d) * padicValNat p (v ^ d - u ^ d) := by
  rw [gapNumerator, padicValNat_prod]
  · apply Finset.sum_congr rfl
    intro d _hd
    rw [padicValNat.pow]
  · intro d hd
    apply pow_ne_zero
    have hdpos : 0 < d := (Finset.mem_Ico.mp hd).1
    exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left huv hdpos.ne')

/-- LTE summed over every geometric gap.  This is the exact valuation ledger
behind QM123d before specializing the active base to `729^K/256^K`. -/
theorem padicValNat_gapNumerator_of_lte {p u v m : ℕ}
    [Fact p.Prime] (hpodd : Odd p) (huv : u < v)
    (hp : p ∣ v - u) (hpv : ¬p ∣ v) :
    padicValNat p (gapNumerator u v m) =
      (m.choose 2) * padicValNat p (v - u) +
        ∑ d ∈ Finset.Ico 1 m,
          (m - d) * padicValNat p d := by
  rw [padicValNat_gapNumerator huv]
  calc
    (∑ d ∈ Finset.Ico 1 m,
        (m - d) * padicValNat p (v ^ d - u ^ d)) =
        ∑ d ∈ Finset.Ico 1 m,
          (m - d) * (padicValNat p (v - u) + padicValNat p d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [padicValNat.pow_sub_pow hpodd huv hp hpv]
      have hd1 := (Finset.mem_Ico.mp hd).1
      omega
    _ = ∑ d ∈ Finset.Ico 1 m,
          ((m - d) * padicValNat p (v - u) +
            (m - d) * padicValNat p d) := by
      simp only [Nat.mul_add]
    _ = (∑ d ∈ Finset.Ico 1 m, (m - d)) *
          padicValNat p (v - u) +
            ∑ d ∈ Finset.Ico 1 m,
              (m - d) * padicValNat p d := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [sum_gap_multiplicities]

end GeometricVandermonde
end KontoroC
