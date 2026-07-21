/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.BallPressureAutomaton
import CleanLean.KL.KLWeights

/-!
# Exact upper bounds for pressure-automaton edge weights

The ball automaton uses rational upper bounds for the three real KL
coefficients on a rational interval of `lambda` values.  This file turns the
portable integer-power comparisons into bounds for the true irrational
coefficients involving `alpha = log_2 3`.
-/

namespace CleanLean.KL

/-- A closed rational parameter interval. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

/-- Executable check that adjacent entries tile without gaps or overlaps. -/
def RatInterval.isChain : List RatInterval → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first.hi = second.lo) && RatInterval.isChain (second :: rest)

/-- Exact S4 predicate for a finite interval tiling. -/
def checkRatIntervalCover (outerLo outerHi : ℚ)
    (pieces : List RatInterval) : Bool :=
  decide (pieces ≠ [] ∧
    (∀ piece ∈ pieces, 1 < piece.lo ∧ piece.lo ≤ piece.hi ∧ piece.hi ≤ 2) ∧
    pieces.head?.map RatInterval.lo = some outerLo ∧
    pieces.getLast?.map RatInterval.hi = some outerHi ∧
    RatInterval.isChain pieces = true)

theorem checkRatIntervalCover_eq_true_iff (outerLo outerHi : ℚ)
    (pieces : List RatInterval) :
    checkRatIntervalCover outerLo outerHi pieces = true ↔
      (pieces ≠ [] ∧
        (∀ piece ∈ pieces,
          1 < piece.lo ∧ piece.lo ≤ piece.hi ∧ piece.hi ≤ 2) ∧
        pieces.head?.map RatInterval.lo = some outerLo ∧
        pieces.getLast?.map RatInterval.hi = some outerHi ∧
        RatInterval.isChain pieces = true) := by
  simp [checkRatIntervalCover]

/-- Executable S3 predicate for one rational parameter interval.  The branch
fields of `w` include the `1/3` fiber-average factor, hence the factors of
three below. -/
def checkBallWeightUpperData (lo hi : ℚ) (w : BallEdgeWeights)
    (P Q : ℕ) : Bool :=
  decide
    (1 < lo ∧ lo ≤ hi ∧ hi ≤ 2 ∧ Q ≤ P ∧ P ≤ 2 * Q ∧
      0 ≤ w.transport ∧ 0 ≤ w.retarded ∧ 0 ≤ w.advanced ∧
      1 ≤ w.transport * lo ^ 2 ∧
      1 ≤ (3 * w.retarded) ^ Q * lo ^ (2 * Q - P) ∧
      hi ^ (P - Q) ≤ (3 * w.advanced) ^ Q)

theorem checkBallWeightUpperData_eq_true_iff
    (lo hi : ℚ) (w : BallEdgeWeights) (P Q : ℕ) :
    checkBallWeightUpperData lo hi w P Q = true ↔
      (1 < lo ∧ lo ≤ hi ∧ hi ≤ 2 ∧ Q ≤ P ∧ P ≤ 2 * Q ∧
        0 ≤ w.transport ∧ 0 ≤ w.retarded ∧ 0 ≤ w.advanced ∧
        1 ≤ w.transport * lo ^ 2 ∧
        1 ≤ (3 * w.retarded) ^ Q * lo ^ (2 * Q - P) ∧
        hi ^ (P - Q) ≤ (3 * w.advanced) ^ Q) := by
  simp [checkBallWeightUpperData]

/-- Taking a positive `Q`-th root in the upper-bound direction for the
retarded exponent. -/
theorem rpow_div_sub_two_le_of_mul_pow
    {x lam : ℝ} {P Q : ℕ}
    (hx : 0 ≤ x) (hlam : 0 < lam) (hQ : 0 < Q) (hP : P ≤ 2 * Q)
    (hcross : 1 ≤ x ^ Q * lam ^ (2 * Q - P)) :
    lam ^ ((P : ℝ) / Q - 2) ≤ x := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hE : ((2 * Q - P : ℕ) : ℝ) = 2 * (Q : ℝ) - P := by
    rw [Nat.cast_sub hP]
    norm_num
  have hpow : lam ^ ((P : ℝ) - 2 * Q) ≤ x ^ Q := by
    rw [show (P : ℝ) - 2 * Q = -((2 * Q - P : ℕ) : ℝ) by
      rw [hE]
      ring]
    rw [Real.rpow_neg hlam.le]
    have hdiv : 1 / lam ^ (2 * Q - P) ≤ x ^ Q :=
      (div_le_iff₀ (pow_pos hlam _)).2 (by simpa [mul_comm] using hcross)
    simpa [one_div] using hdiv
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hlam.le _) hx hQR).mp
  calc
    (lam ^ ((P : ℝ) / Q - 2)) ^ (Q : ℝ) =
        lam ^ (((P : ℝ) / Q - 2) * Q) :=
      (Real.rpow_mul hlam.le _ _).symm
    _ = lam ^ ((P : ℝ) - 2 * Q) := by
      congr 1
      field_simp
    _ ≤ x ^ Q := hpow
    _ = x ^ (Q : ℝ) := (Real.rpow_natCast x Q).symm

/-- The corresponding positive-root lemma for the advanced exponent. -/
theorem rpow_div_sub_one_le_of_pow
    {x lam : ℝ} {P Q : ℕ}
    (hx : 0 ≤ x) (hlam : 0 ≤ lam) (hQ : 0 < Q) (hP : Q ≤ P)
    (hpow : lam ^ (P - Q) ≤ x ^ Q) :
    lam ^ ((P : ℝ) / Q - 1) ≤ x := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hlam _) hx hQR).mp
  calc
    (lam ^ ((P : ℝ) / Q - 1)) ^ (Q : ℝ) =
        lam ^ (((P : ℝ) / Q - 1) * Q) :=
      (Real.rpow_mul hlam _ _).symm
    _ = lam ^ ((P - Q : ℕ) : ℝ) := by
      congr 1
      rw [Nat.cast_sub hP]
      field_simp
    _ = lam ^ (P - Q) := Real.rpow_natCast lam (P - Q)
    _ ≤ x ^ Q := hpow
    _ = x ^ (Q : ℝ) := (Real.rpow_natCast x Q).symm

/-- Soundness of a checked pressure-weight interval.  The returned branch
bounds include the factor three which is divided out on each of the three
ball-refinement edges. -/
theorem klWeights_le_of_checkBallWeightUpperData
    (lo hi : ℚ) (w : BallEdgeWeights) (P Q : ℕ)
    (hQ : 0 < Q) (halpha : checkAlphaUpper P Q = true)
    (hcheck : checkBallWeightUpperData lo hi w P Q = true)
    {lam : ℝ} (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ (hi : ℝ)) :
    (klWeights lam).transport ≤ (w.transport : ℝ) ∧
      (klWeights lam).retarded ≤ (3 * w.retarded : ℚ) ∧
      (klWeights lam).advanced ≤ (3 * w.advanced : ℚ) := by
  rcases (checkBallWeightUpperData_eq_true_iff lo hi w P Q).1 hcheck with
    ⟨hlo1, hlohi, hhi2, hQP, hP2, hwT, hw2, hw8, htransport,
      hretarded, hadvanced⟩
  have hloR : (1 : ℝ) < lo := by exact_mod_cast hlo1
  have hloPos : (0 : ℝ) < lo := zero_lt_one.trans hloR
  have hlamPos : 0 < lam := hloPos.trans_le hlam.1
  have hhiR : (1 : ℝ) < hi := hloR.trans_le (by exact_mod_cast hlohi)
  have hhiNonneg : (0 : ℝ) ≤ hi := (zero_lt_one.trans hhiR).le
  have halphaR : alpha ≤ (P : ℝ) / Q :=
    (alpha_lt_div_of_check hQ halpha).le
  have halphaTwo : alpha - 2 ≤ 0 := by linarith [alpha_lt_two]
  have halphaOne : 0 ≤ alpha - 1 := by linarith [one_lt_alpha]
  constructor
  · change lam ^ (-2 : ℝ) ≤ (w.transport : ℝ)
    calc
      lam ^ (-2 : ℝ) ≤ (lo : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hloPos hlam.1 (by norm_num)
      _ = 1 / (lo : ℝ) ^ 2 := by
        rw [Real.rpow_neg hloPos.le]
        simp [one_div]
      _ ≤ (w.transport : ℝ) := by
        rw [div_le_iff₀ (pow_pos hloPos 2)]
        exact_mod_cast htransport
  constructor
  · change lam ^ (alpha - 2) ≤ ((3 * w.retarded : ℚ) : ℝ)
    calc
      lam ^ (alpha - 2) ≤ (lo : ℝ) ^ (alpha - 2) :=
        Real.rpow_le_rpow_of_nonpos hloPos hlam.1 halphaTwo
      _ ≤ (lo : ℝ) ^ ((P : ℝ) / Q - 2) :=
        Real.rpow_le_rpow_of_exponent_le hloR.le (by linarith)
      _ ≤ ((3 * w.retarded : ℚ) : ℝ) := by
        apply rpow_div_sub_two_le_of_mul_pow
          (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℚ) ≤ 3) hw2))
          hloPos hQ hP2
        exact_mod_cast hretarded
  · change lam ^ (alpha - 1) ≤ ((3 * w.advanced : ℚ) : ℝ)
    calc
      lam ^ (alpha - 1) ≤ (hi : ℝ) ^ (alpha - 1) :=
        Real.rpow_le_rpow hlamPos.le hlam.2 halphaOne
      _ ≤ (hi : ℝ) ^ ((P : ℝ) / Q - 1) :=
        Real.rpow_le_rpow_of_exponent_le hhiR.le (by linarith)
      _ ≤ ((3 * w.advanced : ℚ) : ℝ) := by
        apply rpow_div_sub_one_le_of_pow
          (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℚ) ≤ 3) hw8))
          hhiNonneg hQ hQP
        exact_mod_cast hadvanced

end CleanLean.KL
