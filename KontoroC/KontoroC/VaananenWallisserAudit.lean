/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.StandardTwoRailTheta
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kernel-checked application data for the Väänänen--Wallisser obstruction

This file does **not** reprove the 1989 p-adic linear-independence theorem.
It formalizes the elementary seams in its application to the standard
two-rail partial-theta candidate:

* the coefficientwise change of notation;
* the two strict inequalities in the theorem's size hypothesis;
* the final implication from irrationality of the Lean-defined candidate to
  nonexistence of an ordinary normalized payload stream.

Thus the external citation is isolated to one proposition about one explicit
`Q_2` value; no numerical approximation or hidden axiom is used here.
-/

namespace KontoroC

namespace NormalizedStandardPayloadStream

/-- Exponent `n(n+1)/2`, written without natural-number division. -/
def vaananenExponent (n : ℕ) : ℕ := n.choose 2 + n

/-- The rational `n`th term of
`f_(3/2)(2^12/3^8)` in Väänänen--Wallisser notation. -/
def vaananenTerm (n : ℕ) : ℚ :=
  ((2 : ℚ) / 3) ^ vaananenExponent n *
    ((2 : ℚ) ^ 12 / (3 : ℚ) ^ 8) ^ n

/-- Exact coefficientwise parameter substitution.  The partial-theta defect
term is `23/3^8` times the cited paper's theta-function term. -/
theorem thetaTerm_eq_scaled_vaananenTerm (n : ℕ) :
    thetaTerm n = (23 / (3 : ℚ) ^ 8) * vaananenTerm n := by
  have htwo : n.choose 2 + 13 * n =
      (n.choose 2 + n) + 12 * n := by omega
  have hthree : (n + 1).choose 2 + 8 * (n + 1) =
      (n.choose 2 + n) + 8 * n + 8 := by
    rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
    simp
    omega
  simp only [thetaTerm, terminalTwoExponent, thetaThreeExponent,
    terminalThreeExponent, quadraticExponent, vaananenTerm,
    vaananenExponent]
  rw [htwo, hthree]
  simp only [div_pow, pow_add]
  ring_nf
  rw [show (6561 : ℚ) = (3 : ℚ) ^ 8 by norm_num,
    show (4096 : ℚ) = (2 : ℚ) ^ 12 by norm_num]
  simp only [inv_pow]
  rw [← pow_mul, ← pow_mul]
  rw [show 8 * n = n * 8 by omega, show 12 * n = n * 12 by omega]
  rw [show n * 9 = n + n * 8 by omega,
    show n * 13 = n + n * 12 by omega, pow_add, pow_add]
  ring

/-- The first exact integer inequality behind the logarithmic separator. -/
theorem three_pow_five_lt_two_pow_eight : 3 ^ 5 < 2 ^ 8 := by
  norm_num

/-- The Väänänen--Wallisser size parameter lies below the exact rational
separator `3/8`; no floating-point logarithms occur. -/
theorem log_size_parameter_lt_three_eighths :
    1 - Real.log 2 / Real.log 3 < (3 : ℝ) / 8 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 8 := by norm_num
  have hlogpow : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
    Real.strictMonoOn_log
      (show 0 < (3 : ℝ) ^ 5 by positivity)
      (show 0 < (2 : ℝ) ^ 8 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hratio : (5 : ℝ) / 8 < Real.log 2 / Real.log 3 := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 8) hlog3).2
    simpa [mul_comm] using hlogpow
  nlinarith

/-- The second exact integer inequality behind the square-root separator. -/
theorem five_mul_four_sq_lt_nine_sq : 5 * 4 ^ 2 < 9 ^ 2 := by
  norm_num

/-- The rational separator `3/8` lies below the theorem's golden-ratio
threshold. -/
theorem three_eighths_lt_golden_threshold :
    (3 : ℝ) / 8 < (3 - √5) / 2 := by
  have hsqrt_nonneg : 0 ≤ √(5 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (√(5 : ℝ)) ^ 2 = 5 := by norm_num
  have hsqrt_lt : √(5 : ℝ) < 9 / 4 := by
    nlinarith [five_mul_four_sq_lt_nine_sq]
  nlinarith

/-- The complete strict size inequality used in the one-argument,
zero-derivative application. -/
theorem vaananenWallisser_size_condition :
    1 - Real.log 2 / Real.log 3 < (3 - √5) / 2 :=
  lt_trans log_size_parameter_lt_three_eighths
    three_eighths_lt_golden_threshold

/-- Being outside the image of `ℚ` in `ℚ_[2]`. -/
def IsPadicIrrational (x : ℚ_[2]) : Prop :=
  ∀ q : ℚ, x ≠ (q : ℚ_[2])

/-- Exact endpoint for the cited external theorem: irrationality of the
Lean-defined candidate excludes every ordinary normalized stream. -/
theorem no_stream_of_candidate_irrational
    (hirr : IsPadicIrrational padicThetaCandidate) :
    ¬Nonempty NormalizedStandardPayloadStream := by
  apply no_stream_of_candidate_avoids_positiveNaturals
  intro u _hu heq
  exact hirr u heq

end NormalizedStandardPayloadStream

end KontoroC
