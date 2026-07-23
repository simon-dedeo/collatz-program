/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PublicPayloadConverse
import KontoroC.SlowRulerMahler

/-!
# The genuinely bivariate 17-ruler system

This file formalizes the elementary identities in QM154.  It deliberately
contains no multivariate Mahler value theorem.
-/

namespace KontoroC
namespace SelfWritingKL
namespace RankTwoRuler

open PublicTheta

/-- `A n = sum_{1 ≤ t ≤ n} 17^v17(t)`. -/
def placeSum (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, 17 ^ padicValNat 17 (t + 1)

@[simp] theorem placeSum_zero : placeSum 0 = 0 := by simp [placeSum]

theorem placeSum_succ (n : ℕ) :
    placeSum (n + 1) = placeSum n + 17 ^ padicValNat 17 (n + 1) := by
  simp [placeSum, Finset.sum_range_succ]

theorem padicVal_block_nonzero (n r : ℕ) (hr : 0 < r) (hr17 : r < 17) :
    padicValNat 17 (17 * n + r) = 0 := by
  rw [padicValNat.eq_zero_iff]
  exact Or.inr <| Or.inr <| by
    intro hdvd
    have hmod := Nat.dvd_iff_mod_eq_zero.mp hdvd
    have : r = 0 := by
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr17] using hmod
    omega

theorem padicVal_seventeen_mul_succ (n : ℕ) :
    padicValNat 17 (17 * (n + 1)) =
      1 + padicValNat 17 (n + 1) := by
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [padicValNat.mul (by norm_num : 17 ≠ 0) (by omega : n + 1 ≠ 0)]
  norm_num

/-- QM154a at a complete block boundary. -/
theorem placeSum_seventeen_mul (n : ℕ) :
    placeSum (17 * n) = 17 * placeSum n + 16 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 17 * (n + 1) = 17 * n + 17 by omega]
      repeat' rw [placeSum_succ]
      rw [ih]
      simp only [Nat.add_assoc]
      rw [show 17 * n + 17 = 17 * (n + 1) by omega,
        padicVal_seventeen_mul_succ]
      simp only [padicVal_block_nonzero n 1 (by omega) (by omega),
        padicVal_block_nonzero n 2 (by omega) (by omega),
        padicVal_block_nonzero n 3 (by omega) (by omega),
        padicVal_block_nonzero n 4 (by omega) (by omega),
        padicVal_block_nonzero n 5 (by omega) (by omega),
        padicVal_block_nonzero n 6 (by omega) (by omega),
        padicVal_block_nonzero n 7 (by omega) (by omega),
        padicVal_block_nonzero n 8 (by omega) (by omega),
        padicVal_block_nonzero n 9 (by omega) (by omega),
        padicVal_block_nonzero n 10 (by omega) (by omega),
        padicVal_block_nonzero n 11 (by omega) (by omega),
        padicVal_block_nonzero n 12 (by omega) (by omega),
        padicVal_block_nonzero n 13 (by omega) (by omega),
        padicVal_block_nonzero n 14 (by omega) (by omega),
        padicVal_block_nonzero n 15 (by omega) (by omega),
        padicVal_block_nonzero n 16 (by omega) (by omega),
        pow_zero, pow_add, pow_one]
      ring

/-- QM154a, including a partial final block. -/
theorem placeSum_block (n r : ℕ) (hr : r < 17) :
    placeSum (17 * n + r) = 17 * placeSum n + 16 * n + r := by
  induction r with
  | zero => simpa using placeSum_seventeen_mul n
  | succ r ih =>
      have hr' : r < 17 := by omega
      rw [show 17 * n + (r + 1) = (17 * n + r) + 1 by omega,
        placeSum_succ, ih hr',
        show 17 * n + r + 1 = 17 * n + (r + 1) by omega,
        padicVal_block_nonzero n (r + 1) (by omega) (by omega), pow_zero]
      omega

/-- Recursive base-17 digit form of QM154b.  Iterating this identity gives
the displayed weighted digit sum; unlike a fixed-width digit list, this form
has no trailing-zero convention. -/
theorem placeSum_digit_recursion (n : ℕ) :
    placeSum n =
      17 * placeSum (n / 17) + 16 * (n / 17) + n % 17 := by
  nth_rewrite 1 [← Nat.div_add_mod n 17]
  exact placeSum_block (n / 17) (n % 17) (Nat.mod_lt n (by omega))

def schedule (j n : ℕ) : ℕ :=
  j + 8 * 17 ^ padicValNat 17 (n + 1)

def a : ℚ := (2 : ℚ) ^ 15 / 3 ^ 11
def b : ℚ := (2 : ℚ) ^ 8 / 3 ^ 6
def c : ℚ := b ^ 8
def z (j : ℕ) : ℚ := a * b ^ j

theorem schedule_pos {j n : ℕ} (hj : 0 < j) : 0 < schedule j n := by
  simp [schedule, hj]

theorem branchSum_eq (j N : ℕ) :
    publicBranchSum (schedule j) N = j * N + 8 * placeSum N := by
  induction N with
  | zero => simp [publicBranchSum]
  | succ N ih =>
      rw [publicBranchSum_succ, ih, schedule, placeSum_succ, Nat.mul_succ]
      ring

/-- The inclusive public products are the bivariate place-value
coefficients from QM154c. -/
theorem prefixProduct_eq (j N : ℕ) :
    publicPrefixProduct (schedule j) N = c ^ placeSum N * z j ^ N := by
  rw [publicPrefixProduct_factor, branchSum_eq]
  simp only [a, b, c, z]
  rw [pow_add, pow_mul, pow_mul]
  ring

noncomputable def termAt (C Z : ℚ_[2]) (n : ℕ) : ℚ_[2] :=
  C ^ placeSum n * Z ^ n

noncomputable def valueAt (C Z : ℚ_[2]) : ℚ_[2] :=
  ∑' n, termAt C Z n

theorem termAt_summable (C Z : ℚ_[2]) (hC : ‖C‖ ≤ 1) (hZ : ‖Z‖ < 1) :
    Summable (termAt C Z) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have hbound : ∀ n : ℕ, ‖termAt C Z n‖ ≤ ‖Z‖ ^ n := by
    intro n
    rw [termAt, norm_mul, norm_pow, norm_pow]
    have hc : ‖C‖ ^ placeSum n ≤ 1 := pow_le_one₀ (norm_nonneg C) hC
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg Z) n) hc
  exact squeeze_zero_norm hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg Z) hZ)

theorem termAt_block (C Z : ℚ_[2]) (n : ℕ) (r : ZMod 17) :
    termAt C Z (r.val + 17 * n) =
      (C * Z) ^ r.val *
        termAt (C ^ 17) (C ^ 16 * Z ^ 17) n := by
  unfold termAt
  rw [show r.val + 17 * n = 17 * n + r.val by omega,
    placeSum_block n r.val r.val_lt, pow_add, pow_add, pow_add,
    pow_mul, pow_mul, pow_mul, mul_pow, mul_pow]
  ring

/-- QM154c as an identity of convergent `Q_2` series. -/
theorem valueAt_functional (C Z : ℚ_[2]) (hC : ‖C‖ ≤ 1) (hZ : ‖Z‖ < 1) :
    valueAt C Z = SlowRuler.P17 (C * Z) *
      valueAt (C ^ 17) (C ^ 16 * Z ^ 17) := by
  have hs := termAt_summable C Z hC hZ
  have hCnext : ‖C ^ 17‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg C) hC
  have hZnext : ‖C ^ 16 * Z ^ 17‖ < 1 := by
    rw [norm_mul, norm_pow, norm_pow]
    have hc16 : ‖C‖ ^ 16 ≤ 1 := pow_le_one₀ (norm_nonneg C) hC
    have hz17 : ‖Z‖ ^ 17 < 1 := pow_lt_one₀ (norm_nonneg Z) hZ (by norm_num)
    exact (mul_le_mul_of_nonneg_right hc16
      (pow_nonneg (norm_nonneg Z) 17)).trans_lt (by simpa using hz17)
  have hsnext := termAt_summable (C ^ 17) (C ^ 16 * Z ^ 17) hCnext hZnext
  rw [valueAt, Nat.sumByResidueClasses hs 17]
  simp_rw [termAt_block]
  calc
    (∑ r : ZMod 17,
        ∑' n : ℕ, (C * Z) ^ r.val *
          termAt (C ^ 17) (C ^ 16 * Z ^ 17) n) =
        ∑ r : ZMod 17, (C * Z) ^ r.val *
          valueAt (C ^ 17) (C ^ 16 * Z ^ 17) := by
      apply Finset.sum_congr rfl
      intro r _
      exact hsnext.tsum_mul_left ((C * Z) ^ r.val)
    _ = SlowRuler.P17 (C * Z) *
        valueAt (C ^ 17) (C ^ 16 * Z ^ 17) := by
      simp only [SlowRuler.P17, Finset.sum_mul]

noncomputable def value (j : ℕ) : ℚ_[2] :=
  valueAt (c : ℚ_[2]) (z j : ℚ_[2])

theorem termAt_specialization (j n : ℕ) :
    termAt (c : ℚ_[2]) (z j : ℚ_[2]) n =
      (publicPrefixProduct (schedule j) n : ℚ_[2]) := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (prefixProduct_eq j n)
  simpa only [termAt, Rat.cast_mul, Rat.cast_pow] using h.symm

/-- The public specialization in QM154c. -/
theorem value_eq_one_add_padicSum (j : ℕ) (hj : 0 < j) :
    value j = 1 + padicSum (schedule j) := by
  have heq : (fun n => termAt (c : ℚ_[2]) (z j : ℚ_[2]) n) =
      fun n => (publicPrefixProduct (schedule j) n : ℚ_[2]) := by
    funext n
    exact termAt_specialization j n
  rw [value, valueAt, heq]
  have htail : Summable (fun n : ℕ =>
      (publicPrefixProduct (schedule j) (n + 1) : ℚ_[2])) := by
    change Summable (padicTerm (schedule j))
    exact padicTerm_summable (schedule j) (fun n => schedule_pos hj)
  have hsum := (summable_nat_add_iff
    (f := fun n : ℕ =>
      (publicPrefixProduct (schedule j) n : ℚ_[2])) 1).mp htail
  have hsplit := hsum.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, publicPrefixProduct_zero] at hsplit
  have htailValue : (∑' n : ℕ,
      (publicPrefixProduct (schedule j) (n + 1) : ℚ_[2])) =
      padicSum (schedule j) := by rfl
  rw [htailValue] at hsplit
  exact hsplit.symm

/-- The Jordan-type parameter update in QM154d. -/
noncomputable def transform (s : ℚ_[2] × ℚ_[2]) : ℚ_[2] × ℚ_[2] :=
  (s.1 ^ 17, s.1 ^ 16 * s.2 ^ 17)

def jordanExponent (k : ℕ) : ℕ := 16 * k * 17 ^ (k - 1)

theorem jordanExponent_succ (k : ℕ) :
    17 ^ k * 16 + jordanExponent k * 17 =
      jordanExponent (k + 1) := by
  cases k with
  | zero => simp [jordanExponent]
  | succ k =>
      simp only [jordanExponent]
      rw [show k + 1 - 1 = k by omega,
        show k + 1 + 1 - 1 = k + 1 by omega, pow_succ]
      ring

/-- Exact iterate formula in QM154d.  The linear factor in `k` is the
signature of the defective Jordan block. -/
theorem transform_iterate (C Z : ℚ_[2]) (k : ℕ) :
    (transform^[k]) (C, Z) =
      (C ^ (17 ^ k), C ^ jordanExponent k * Z ^ (17 ^ k)) := by
  induction k with
  | zero => simp [jordanExponent]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [transform]
      apply Prod.ext
      · simp only [pow_mul, pow_succ]
      · simp only [mul_pow]
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_assoc,
          ← pow_add, jordanExponent_succ, pow_succ]

theorem transform_preserves_norms {C Z : ℚ_[2]}
    (hC : ‖C‖ ≤ 1) (hZ : ‖Z‖ < 1) :
    ‖(transform (C, Z)).1‖ ≤ 1 ∧ ‖(transform (C, Z)).2‖ < 1 := by
  simp only [transform, norm_pow, norm_mul]
  constructor
  · exact pow_le_one₀ (norm_nonneg C) hC
  · have hc16 : ‖C‖ ^ 16 ≤ 1 := pow_le_one₀ (norm_nonneg C) hC
    have hz17 : ‖Z‖ ^ 17 < 1 := pow_lt_one₀ (norm_nonneg Z) hZ (by norm_num)
    exact (mul_le_mul_of_nonneg_right hc16
      (pow_nonneg (norm_nonneg Z) 17)).trans_lt (by simpa using hz17)

theorem transform_iterate_norms (C Z : ℚ_[2])
    (hC : ‖C‖ ≤ 1) (hZ : ‖Z‖ < 1) (k : ℕ) :
    ‖((transform^[k]) (C, Z)).1‖ ≤ 1 ∧
      ‖((transform^[k]) (C, Z)).2‖ < 1 := by
  induction k with
  | zero => simpa using And.intro hC hZ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact transform_preserves_norms ih.1 ih.2

noncomputable def factor (s : ℚ_[2] × ℚ_[2]) : ℚ_[2] :=
  SlowRuler.P17 (s.1 * s.2)

noncomputable def factorProduct (s : ℚ_[2] × ℚ_[2]) (k : ℕ) : ℚ_[2] :=
  ∏ i ∈ Finset.range k, factor ((transform^[i]) s)

theorem factor_transform_iterate (C Z : ℚ_[2]) (k : ℕ) :
    factor ((transform^[k]) (C, Z)) =
      SlowRuler.P17
        (C ^ (17 ^ k + jordanExponent k) * Z ^ (17 ^ k)) := by
  rw [transform_iterate]
  simp only [factor, ← mul_assoc, ← pow_add]

/-- Finite exact product form of QM154d, retaining the convergent tail. -/
theorem valueAt_iterated (C Z : ℚ_[2])
    (hC : ‖C‖ ≤ 1) (hZ : ‖Z‖ < 1) (k : ℕ) :
    valueAt C Z = factorProduct (C, Z) k *
      valueAt (((transform^[k]) (C, Z)).1)
        (((transform^[k]) (C, Z)).2) := by
  induction k with
  | zero => simp [factorProduct]
  | succ k ih =>
      have hnorm := transform_iterate_norms C Z hC hZ k
      have hfun := valueAt_functional
        (((transform^[k]) (C, Z)).1)
        (((transform^[k]) (C, Z)).2) hnorm.1 hnorm.2
      rw [ih]
      simp only [factorProduct, Finset.prod_range_succ]
      change _ =
        ((∏ i ∈ Finset.range k, factor ((transform^[i]) (C, Z))) *
            factor ((transform^[k]) (C, Z))) * _
      rw [hfun, Function.iterate_succ_apply']
      simp only [factor, transform]
      ring

/-- Formal exponent vectors of the specialized rational parameters. -/
def cExponent : ℤ × ℤ := (64, -48)
def zExponent (j : ℕ) : ℤ × ℤ := (15 + 8 * (j : ℤ), -11 - 6 * (j : ℤ))

def exponentDet (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- QM154e: every specialization has multiplicative rank two. -/
theorem exponentDet_eq_sixteen (j : ℕ) :
    exponentDet cExponent (zExponent j) = 16 := by
  simp only [exponentDet, cExponent, zExponent]
  ring

end RankTwoRuler
end SelfWritingKL
end KontoroC
