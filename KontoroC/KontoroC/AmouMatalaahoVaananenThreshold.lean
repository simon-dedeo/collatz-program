/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The 2007 p-adic threshold misses the period-three EC17 parameter

Amou--Matala-aho--Väänänen's effective sufficient condition, specialized to
the three-value, first-derivative-free case, introduces `0 < δ < 1` and a
positive real optimization variable `ρ`.  This file proves uniformly that
its quotient `B/A` is below `13/12`, whereas the period-three logarithmic
parameter is above `13/12`.

This is a citation-boundary audit, not a period-three impossibility theorem:
it proves that this published sufficient criterion cannot supply the missing
linear-independence result at the EC17 parameter.
-/

namespace KontoroC
namespace AmouMatalaahoVaananenThreshold

/-- The specialized source constant for `m=3`, `s=1`. -/
noncomputable def sourceK (δ : ℝ) : ℝ :=
  9 / 2 + ((4 - δ) ^ 3 - 27) / (6 * δ)

noncomputable def sourceA (δ ρ : ℝ) : ℝ :=
  ρ ^ 2 / 2 + 3 * ρ + sourceK δ

noncomputable def sourceB (δ ρ : ℝ) : ℝ :=
  ρ ^ 2 / 2 + (4 - δ) * ρ

/-- The correction in `sourceK` is strictly positive throughout the source's
admissible auxiliary-parameter interval. -/
theorem nine_halves_lt_sourceK {δ : ℝ} (hδpos : 0 < δ) (hδlt : δ < 1) :
    (9 : ℝ) / 2 < sourceK δ := by
  have hfactor :
      (4 - δ) ^ 3 - 27 =
        (1 - δ) * ((4 - δ) ^ 2 + 3 * (4 - δ) + 9) := by
    ring
  have hfirst : 0 < 1 - δ := by linarith
  have hsecond : 0 < (4 - δ) ^ 2 + 3 * (4 - δ) + 9 := by
    nlinarith [sq_nonneg (4 - δ)]
  have hnum : 0 < (4 - δ) ^ 3 - 27 := by
    rw [hfactor]
    exact mul_pos hfirst hsecond
  have hden : 0 < 6 * δ := by positivity
  have hquot : 0 < ((4 - δ) ^ 3 - 27) / (6 * δ) :=
    div_pos hnum hden
  simp only [sourceK]
  linarith

/-- Abstract algebraic heart of the threshold estimate.  Only the lower
bound `K>9/2` is needed from the paper's more elaborate constant. -/
theorem sourceB_div_sourceA_lt_thirteen_twelfths_of_K
    {δ ρ K : ℝ} (hδpos : 0 < δ) (hδlt : δ < 1)
    (hρpos : 0 < ρ) (hK : (9 : ℝ) / 2 < K) :
    (ρ ^ 2 / 2 + (4 - δ) * ρ) /
        (ρ ^ 2 / 2 + 3 * ρ + K) < (13 : ℝ) / 12 := by
  let A : ℝ := ρ ^ 2 / 2 + 3 * ρ + K
  let B : ℝ := ρ ^ 2 / 2 + (4 - δ) * ρ
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith [sq_nonneg ρ]
  have hdiff : 0 < 13 * A - 12 * B := by
    by_cases hlarge : (3 : ℝ) / 4 ≤ δ
    · have hcoefficient : 0 ≤ 12 * δ - 9 := by linarith
      have hterm : 0 ≤ (12 * δ - 9) * ρ :=
        mul_nonneg hcoefficient hρpos.le
      dsimp only [A, B]
      nlinarith [sq_nonneg ρ]
    · have hsmall : δ < (3 : ℝ) / 4 := lt_of_not_ge hlarge
      let a : ℝ := 9 - 12 * δ
      have ha_pos : 0 < a := by dsimp only [a]; linarith
      have ha_lt : a < 9 := by dsimp only [a]; linarith
      have ha_sq_lt : a * a < 81 := by
        have hproduct : 0 < (9 - a) * (9 + a) := by positivity
        nlinarith
      dsimp only [A, B]
      have hsquare : 0 ≤ (ρ - a) ^ 2 := sq_nonneg (ρ - a)
      dsimp only [a] at hsquare ha_sq_lt
      nlinarith
  apply (div_lt_div_iff₀ hA (by norm_num : (0 : ℝ) < 12)).2
  dsimp only [A, B] at hdiff ⊢
  nlinarith

/-- Uniform specialization to the literal source constant. -/
theorem sourceB_div_sourceA_lt_thirteen_twelfths
    {δ ρ : ℝ} (hδpos : 0 < δ) (hδlt : δ < 1) (hρpos : 0 < ρ) :
    sourceB δ ρ / sourceA δ ρ < (13 : ℝ) / 12 := by
  exact sourceB_div_sourceA_lt_thirteen_twelfths_of_K
    hδpos hδlt hρpos (nine_halves_lt_sourceK hδpos hδlt)

/-- Logarithmic parameter of the three-value EC17 specialization. -/
noncomputable def periodThreeLambda : ℝ :=
  3 * Real.log 3 / (4 * Real.log 2)

/-- The exact integer separator `2^13 < 3^9` puts the EC17 parameter above
`13/12`; no numerical approximation to logarithms is used. -/
theorem thirteen_twelfths_lt_periodThreeLambda :
    (13 : ℝ) / 12 < periodThreeLambda := by
  have hpowers : (2 : ℝ) ^ 13 < (3 : ℝ) ^ 9 := by norm_num
  have hlogpowers : Real.log ((2 : ℝ) ^ 13) < Real.log ((3 : ℝ) ^ 9) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) hpowers
  rw [Real.log_pow, Real.log_pow] at hlogpowers
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 4 * Real.log 2 := by positivity
  rw [periodThreeLambda]
  apply (lt_div_iff₀ hden).2
  norm_num [div_eq_mul_inv] at hlogpowers ⊢
  nlinarith

theorem periodThreeLambda_pos : 0 < periodThreeLambda :=
  (by norm_num : (0 : ℝ) < 13 / 12).trans
    thirteen_twelfths_lt_periodThreeLambda

/-- Final falsification endpoint: for no admissible `δ,ρ` does the effective
2007 sufficient inequality hold at the period-three parameter. -/
theorem not_periodThreeLambda_lt_source_threshold
    {δ ρ : ℝ} (hδpos : 0 < δ) (hδlt : δ < 1) (hρpos : 0 < ρ) :
    ¬ |periodThreeLambda| < sourceB δ ρ / sourceA δ ρ := by
  rw [abs_of_pos periodThreeLambda_pos]
  exact not_lt_of_ge
    ((sourceB_div_sourceA_lt_thirteen_twelfths hδpos hδlt hρpos).trans
      thirteen_twelfths_lt_periodThreeLambda).le

end AmouMatalaahoVaananenThreshold
end KontoroC
