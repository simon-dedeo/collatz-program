/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.TernaryColdMean
import CleanLean.KL.SoftHardTransfer

/-!
# The softened finite KL operator and its hard-min sandwich

The branch minimum in a finite KL system is replaced by the ternary power
mean of order `-beta`.  On positive vectors the resulting operator lies
between the literal hard-min operator and `3^(1/beta)` times that operator.
Combined with `SoftHardTransfer`, a soft subeigenvalue strictly larger than
that factor is an exact hard-min feasibility certificate.
-/

namespace CleanLean.KL

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- Cold power mean of the three values in a refinement fiber. -/
def coldFiberMean (beta : ℝ) (c : S.State → ℝ) (r : S.Coarse) : ℝ :=
  ternaryColdMean beta (fun i => c (S.fiber r i))

/-- Finite KL operator with its branch minimum replaced by a cold power mean. -/
def coldOperator (beta : ℝ) (w : Weights ℝ)
    (c : S.State → ℝ) (m : S.State) : ℝ :=
  w.transport * c (S.transport m) +
    match S.branch m with
    | .retarded => w.retarded * S.coldFiberMean beta c (S.refinementTarget m)
    | .neutral => 0
    | .advanced => w.advanced * S.coldFiberMean beta c (S.refinementTarget m)

private theorem min3_fiber_eq_fiberMin
    (c : S.State → ℝ) (r : S.Coarse) :
    min3 (fun i => c (S.fiber r i)) = S.fiberMin c r := by
  rfl

private theorem fiberMin_pos
    (c : S.State → ℝ) (hc : ∀ q, 0 < c q) (r : S.Coarse) :
    0 < S.fiberMin c r := by
  simp only [fiberMin]
  exact lt_min (hc _) (lt_min (hc _) (hc _))

theorem fiberMin_le_coldFiberMean
    {beta : ℝ} (hbeta : 0 < beta)
    (c : S.State → ℝ) (hc : ∀ q, 0 < c q) (r : S.Coarse) :
    S.fiberMin c r ≤ S.coldFiberMean beta c r := by
  rw [← min3_fiber_eq_fiberMin]
  exact min3_le_ternaryColdMean hbeta (fun i => hc _)

theorem coldFiberMean_le_factor_mul_fiberMin
    {beta : ℝ} (hbeta : 0 < beta)
    (c : S.State → ℝ) (hc : ∀ q, 0 < c q) (r : S.Coarse) :
    S.coldFiberMean beta c r ≤
      3 ^ (1 / beta) * S.fiberMin c r := by
  rw [← min3_fiber_eq_fiberMin]
  exact ternaryColdMean_le_three_rpow_mul_min3 hbeta (fun i => hc _)

/-- Literal lower half of the soft/hard operator sandwich. -/
theorem operator_le_coldOperator
    {beta : ℝ} (hbeta : 0 < beta)
    (w : Weights ℝ) (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced)
    (c : S.State → ℝ) (hc : ∀ q, 0 < c q) :
    ∀ m, S.operator w c m ≤ S.coldOperator beta w c m := by
  intro m
  cases hb : S.branch m with
  | retarded =>
      simp only [operator, coldOperator, hb]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (S.fiberMin_le_coldFiberMean hbeta c hc _) hret)
  | neutral => simp [operator, coldOperator, hb]
  | advanced =>
      simp only [operator, coldOperator, hb]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (S.fiberMin_le_coldFiberMean hbeta c hc _) hadv)

/-- Literal upper half of the soft/hard operator sandwich. -/
theorem coldOperator_le_factor_mul_operator
    {beta : ℝ} (hbeta : 0 < beta)
    (w : Weights ℝ) (hwt : 0 ≤ w.transport)
    (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced)
    (c : S.State → ℝ) (hc : ∀ q, 0 < c q) :
    ∀ m, S.coldOperator beta w c m ≤
      3 ^ (1 / beta) * S.operator w c m := by
  let C : ℝ := 3 ^ (1 / beta)
  have hC : 1 ≤ C :=
    Real.one_le_rpow (by norm_num) (div_nonneg zero_le_one hbeta.le)
  intro m
  have htransport : 0 ≤ w.transport * c (S.transport m) :=
    mul_nonneg hwt (hc _).le
  cases hb : S.branch m with
  | retarded =>
      simp only [coldOperator, operator, hb]
      have hmean := S.coldFiberMean_le_factor_mul_fiberMin hbeta c hc
        (S.refinementTarget m)
      have hbranch := mul_le_mul_of_nonneg_left hmean hret
      have hbranch0 : 0 ≤ w.retarded * S.fiberMin c (S.refinementTarget m) :=
        mul_nonneg hret (S.fiberMin_pos c hc _).le
      change w.transport * c (S.transport m) +
          w.retarded * S.coldFiberMean beta c (S.refinementTarget m) ≤
        C * (w.transport * c (S.transport m) +
          w.retarded * S.fiberMin c (S.refinementTarget m))
      have hscale : 0 ≤ (C - 1) * (w.transport * c (S.transport m)) :=
        mul_nonneg (sub_nonneg.mpr hC) htransport
      nlinarith
  | neutral =>
      simp only [coldOperator, operator, hb, add_zero]
      change w.transport * c (S.transport m) ≤
        C * (w.transport * c (S.transport m))
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) htransport]
  | advanced =>
      simp only [coldOperator, operator, hb]
      have hmean := S.coldFiberMean_le_factor_mul_fiberMin hbeta c hc
        (S.refinementTarget m)
      have hbranch := mul_le_mul_of_nonneg_left hmean hadv
      have hbranch0 : 0 ≤ w.advanced * S.fiberMin c (S.refinementTarget m) :=
        mul_nonneg hadv (S.fiberMin_pos c hc _).le
      change w.transport * c (S.transport m) +
          w.advanced * S.coldFiberMean beta c (S.refinementTarget m) ≤
        C * (w.transport * c (S.transport m) +
          w.advanced * S.fiberMin c (S.refinementTarget m))
      have hscale : 0 ≤ (C - 1) * (w.transport * c (S.transport m)) :=
        mul_nonneg (sub_nonneg.mpr hC) htransport
      nlinarith

end

end FiniteSystem

namespace ResidueSystem

noncomputable section

/-- A certified cold-power-mean subeigenvalue above `3^(1/beta)` is already
an exact feasibility witness for the literal hard-min KL system. -/
theorem levelFeasible_of_coldSubeigen
    (k : ℕ) (lam beta r : ℝ)
    (x : State k → ℝ)
    (hlam : 0 ≤ lam) (hbeta : 0 < beta) (hx : ∀ s, 0 < x s)
    (hr : 3 ^ (1 / beta) < r)
    (hsoft : ∀ s, r * x s ≤
      (system k).coldOperator beta (klWeights lam) x s) :
    LevelFeasible k lam := by
  apply levelFeasible_of_softSubeigen_domination
    k lam r (3 ^ (1 / beta))
      ((system k).coldOperator beta (klWeights lam)) x hx
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact hr
  · exact hsoft
  · exact (system k).coldOperator_le_factor_mul_operator hbeta
      (klWeights lam)
      (Real.rpow_nonneg hlam _)
      (Real.rpow_nonneg hlam _)
      (Real.rpow_nonneg hlam _) x hx

/-- Fully concrete fixed-temperature handoff.  For a parameter sequence
tending to two, positive cold subeigenvectors at arbitrary witness levels,
with factors above `3^(1/beta)`, imply almost-linear predecessor counting. -/
theorem almostLinearPredecessorCounting_of_coldSubeigen_sequence
    (mu beta r : ℕ → ℝ) (level : ℕ → ℕ)
    (x : (n : ℕ) → State (level n) → ℝ)
    (hmu : Filter.Tendsto mu Filter.atTop (nhds 2))
    (hmuLower : ∀ n, 1 < mu n)
    (hmuUpper : ∀ n, mu n ≤ 2)
    (hlevel : ∀ n, 2 ≤ level n)
    (hbeta : ∀ n, 0 < beta n)
    (hx : ∀ n s, 0 < x n s)
    (hr : ∀ n, 3 ^ (1 / beta n) < r n)
    (hsoft : ∀ n s, r n * x n s ≤
      (system (level n)).coldOperator (beta n) (klWeights (mu n)) (x n) s) :
    CleanLean.Collatz.AlmostLinearPredecessorCounting := by
  apply almostLinearPredecessorCounting_of_sparse_feasible_sequence
    mu level hmu hmuLower hmuUpper hlevel
  intro n
  exact levelFeasible_of_coldSubeigen
    (level n) (mu n) (beta n) (r n) (x n)
      (by linarith [hmuLower n]) (hbeta n) (hx n) (hr n) (hsoft n)

end

end ResidueSystem

end CleanLean.KL
