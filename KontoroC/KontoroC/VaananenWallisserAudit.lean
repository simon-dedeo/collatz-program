/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.StandardTwoRailTheta
import KontoroC.VaananenWallisserCore
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

/-- The rational scaling constant between the two series. -/
def vaananenScale : ℚ := 23 / 3 ^ 8

/-- The cited theta-function term embedded in `ℚ_[2]`. -/
noncomputable def padicVaananenTerm (n : ℕ) : ℚ_[2] :=
  (vaananenTerm n : ℚ_[2])

theorem padicThetaTerm_eq_scaled_vaananenTerm (n : ℕ) :
    padicThetaTerm n =
      (vaananenScale : ℚ_[2]) * padicVaananenTerm n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (thetaTerm_eq_scaled_vaananenTerm n)
  simpa [padicThetaTerm, padicVaananenTerm, vaananenScale,
    Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

theorem padic_vaananenScale_ne_zero : (vaananenScale : ℚ_[2]) ≠ 0 := by
  norm_num [vaananenScale]

/-- Summability of the paper's series, derived from the already established
summability of the scaled defect series. -/
theorem padicVaananenTerm_summable : Summable padicVaananenTerm := by
  let c : ℚ_[2] := vaananenScale
  have hs := padicThetaTerm_summable.mul_left c⁻¹
  refine hs.congr ?_
  intro n
  rw [padicThetaTerm_eq_scaled_vaananenTerm]
  dsimp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ padic_vaananenScale_ne_zero, one_mul]

/-- The exact `ℚ_[2]` value to which the external theorem applies. -/
noncomputable def padicVaananenSum : ℚ_[2] :=
  ∑' n, padicVaananenTerm n

/-- The project-specific series is definitionally the generic theta series
from `VaananenWallisserCore` at the paper's original rational argument. -/
theorem padicVaananenTerm_eq_coreThetaTerm (n : ℕ) :
    padicVaananenTerm n =
      VaananenWallisser.thetaTerm
        ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
        ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) n := by
  simp [padicVaananenTerm, vaananenTerm, vaananenExponent,
    VaananenWallisser.thetaTerm, VaananenWallisser.exponent,
    Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  norm_num

theorem padicVaananenSum_eq_coreThetaSum :
    padicVaananenSum =
      VaananenWallisser.thetaSum
        ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
        ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) := by
  apply tsum_congr
  exact padicVaananenTerm_eq_coreThetaTerm

/-- In `Q_2`, the paper parameter `q=3/2` has norm two. -/
theorem norm_padic_threeHalves :
    ‖(((3 : ℚ) / 2 : ℚ) : ℚ_[2])‖ = 2 := by
  rw [Rat.cast_div, norm_div]
  have h3 : ‖((3 : ℚ) : ℚ_[2])‖ = 1 := by
    rw [show ((3 : ℚ) : ℚ_[2]) = (3 : ℚ_[2]) by norm_num]
    exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h2 : ‖((2 : ℚ) : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using (Padic.norm_p (p := 2))
  rw [h3, h2]
  norm_num

/-- Every intermediate argument from the original point through its eighth
`q`-shift remains in the closed 2-adic unit ball. -/
theorem norm_padic_vaananen_shift_le_one (j : ℕ) (hj : j < 9) :
    ‖((((3 : ℚ) / 2 : ℚ) : ℚ_[2]) ^ j *
      (((4096 : ℚ) / 6561 : ℚ) : ℚ_[2]))‖ ≤ 1 := by
  rw [norm_mul, norm_pow, norm_padic_threeHalves]
  have ha : ‖(((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])‖ =
      (2 : ℝ) ^ (-12 : ℤ) := by
    rw [show (4096 : ℚ) / 6561 = 2 ^ 12 / 3 ^ 8 by norm_num,
      Rat.cast_div, Rat.cast_pow, Rat.cast_pow, norm_div, norm_pow, norm_pow]
    have h3 : ‖((3 : ℚ) : ℚ_[2])‖ = 1 := by
      rw [show ((3 : ℚ) : ℚ_[2]) = (3 : ℚ_[2]) by norm_num]
      exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    have h2 : ‖((2 : ℚ) : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
      simpa using (Padic.norm_p (p := 2))
    rw [h2, h3]
    norm_num
  rw [ha]
  have hj' : j ≤ 8 := by omega
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  omega

theorem padic_vaananen_intermediate_summable (j : ℕ) (hj : j < 9) :
    Summable (VaananenWallisser.thetaTerm
      ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
      ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]) ^ j *
        (((4096 : ℚ) / 6561 : ℚ) : ℚ_[2]))) := by
  apply VaananenWallisser.thetaTerm_summable_of_norm
  · rw [norm_padic_threeHalves]
    norm_num
  · exact norm_padic_vaananen_shift_le_one j hj

/-- Eight exact functional-equation steps move the original argument
`4096/6561` to the auxiliary-prime unit `16`. -/
theorem thetaSum_sixteen_affine :
    VaananenWallisser.thetaSum
      ((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) (16 : ℚ_[2]) =
      (((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) ^ ((8 : ℕ).choose 2) *
        ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) ^ 8) *
          padicVaananenSum +
        VaananenWallisser.thetaShiftOffset
          ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
          ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) 8 := by
  have h := VaananenWallisser.thetaSum_pow_shift_affine
    ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
    ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) (by norm_num) 8
    (fun j hj => padic_vaananen_intermediate_summable j (by omega))
  rw [← padicVaananenSum_eq_coreThetaSum] at h
  convert h using 1 <;> norm_num

/-- Equality of the completed 2-adic sums, not merely of finite
coefficients. -/
theorem padicThetaSum_eq_scaled_vaananenSum :
    padicThetaSum =
      (vaananenScale : ℚ_[2]) * padicVaananenSum := by
  have hv := padicVaananenTerm_summable.hasSum.mul_left
    (vaananenScale : ℚ_[2])
  have hfun :
      (fun n => (vaananenScale : ℚ_[2]) * padicVaananenTerm n) =
        padicThetaTerm := by
    funext n
    exact (padicThetaTerm_eq_scaled_vaananenTerm n).symm
  rw [hfun] at hv
  exact padicThetaTerm_summable.hasSum.unique hv

/-- The research-note candidate is the negative rational multiple of the
literal Väänänen--Wallisser series value. -/
theorem padicThetaCandidate_eq_scaled_vaananenSum :
    padicThetaCandidate =
      -(vaananenScale : ℚ_[2]) * padicVaananenSum := by
  rw [padicThetaCandidate, padicThetaSum_eq_scaled_vaananenSum]
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

/-- Irrationality at the auxiliary-prime unit argument `16` implies
irrationality at the project's original argument.  The eight functional
equations express the shifted value as a rational affine function of the
original one, so a rational original value would force a rational shifted
value. -/
theorem padicVaananenSum_irrational_of_sixteen_irrational
    (hirr : IsPadicIrrational
      (VaananenWallisser.thetaSum
        ((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) (16 : ℚ_[2]))) :
    IsPadicIrrational padicVaananenSum := by
  let a : ℚ := ((3 : ℚ) / 2) ^ ((8 : ℕ).choose 2) *
    ((4096 : ℚ) / 6561) ^ 8
  let b : ℚ := VaananenWallisser.thetaShiftOffset
    ((3 : ℚ) / 2) ((4096 : ℚ) / 6561) 8
  have hb :
      (b : ℚ_[2]) =
        VaananenWallisser.thetaShiftOffset
          ((((3 : ℚ) / 2 : ℚ) : ℚ_[2]))
          ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) 8 := by
    simpa [b] using
      (VaananenWallisser.map_thetaShiftOffset
        (algebraMap ℚ ℚ_[2]) ((3 : ℚ) / 2) ((4096 : ℚ) / 6561) 8)
  have ha :
      (a : ℚ_[2]) =
        (((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) ^ ((8 : ℕ).choose 2) *
          ((((4096 : ℚ) / 6561 : ℚ) : ℚ_[2])) ^ 8) := by
    simp [a, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hrel :
      VaananenWallisser.thetaSum
        ((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) (16 : ℚ_[2]) =
        (a : ℚ_[2]) * padicVaananenSum + (b : ℚ_[2]) := by
    rw [thetaSum_sixteen_affine, ha, hb]
  intro r hr
  apply hirr (a * r + b)
  rw [Rat.cast_add, Rat.cast_mul, hrel, hr]

/-- The exact logical bridge from the 1989 paper's stated conclusion to the
project's citation seam.  Since `f_q(0)=1`, linear independence of
`f_q(0), f_q(α)` over `ℚ` is precisely p-adic irrationality of `f_q(α)`.
This theorem guards against silently replacing the paper's conclusion by a
nearby but inequivalent proposition. -/
theorem isPadicIrrational_iff_linearIndependent_one (x : ℚ_[2]) :
    IsPadicIrrational x ↔
      LinearIndependent ℚ ![(1 : ℚ_[2]), x] := by
  rw [LinearIndependent.pair_iff' (one_ne_zero : (1 : ℚ_[2]) ≠ 0)]
  simp only [IsPadicIrrational, ne_eq, Rat.smul_one_eq_cast]
  constructor
  · intro h q heq
    exact h q heq.symm
  · intro h q heq
    exact h q heq.symm

/-- A nonzero rational rescaling preserves p-adic irrationality, specialized
to the exact scale and sign occurring here. -/
theorem padicThetaCandidate_irrational_of_vaananenSum_irrational
    (hirr : IsPadicIrrational padicVaananenSum) :
    IsPadicIrrational padicThetaCandidate := by
  intro q heq
  apply hirr (-q / vaananenScale)
  rw [Rat.cast_div, Rat.cast_neg]
  apply (eq_div_iff padic_vaananenScale_ne_zero).2
  rw [padicThetaCandidate_eq_scaled_vaananenSum] at heq
  linear_combination -heq

/-- Exact endpoint for the cited external theorem: irrationality of the
Lean-defined candidate excludes every ordinary normalized stream. -/
theorem no_stream_of_candidate_irrational
    (hirr : IsPadicIrrational padicThetaCandidate) :
    ¬Nonempty NormalizedStandardPayloadStream := by
  apply no_stream_of_candidate_avoids_positiveNaturals
  intro u _hu heq
  exact hirr u heq

/-- Final citation seam: the published irrationality statement about its own
theta-series value directly rules out the standard payload stream. -/
theorem no_stream_of_vaananenSum_irrational
    (hirr : IsPadicIrrational padicVaananenSum) :
    ¬Nonempty NormalizedStandardPayloadStream :=
  no_stream_of_candidate_irrational
    (padicThetaCandidate_irrational_of_vaananenSum_irrational hirr)

/-- Citation endpoint after auxiliary-prime normalization: it is enough to
prove irrationality of the theta value at `16`.  The checked eight-step
functional-equation bridge then returns to the project's original value. -/
theorem no_stream_of_sixteen_theta_irrational
    (hirr : IsPadicIrrational
      (VaananenWallisser.thetaSum
        ((((3 : ℚ) / 2 : ℚ) : ℚ_[2])) (16 : ℚ_[2]))) :
    ¬Nonempty NormalizedStandardPayloadStream :=
  no_stream_of_vaananenSum_irrational
    (padicVaananenSum_irrational_of_sixteen_irrational hirr)

/-- Citation endpoint in the literal language of Väänänen--Wallisser:
their linear-independence conclusion for `1` and the displayed theta value
implies nonexistence of the normalized stream. -/
theorem no_stream_of_vaananen_pair_linearIndependent
    (hli : LinearIndependent ℚ
      ![(1 : ℚ_[2]), padicVaananenSum]) :
    ¬Nonempty NormalizedStandardPayloadStream :=
  no_stream_of_vaananenSum_irrational
    ((isPadicIrrational_iff_linearIndependent_one padicVaananenSum).2 hli)

end NormalizedStandardPayloadStream

end KontoroC
