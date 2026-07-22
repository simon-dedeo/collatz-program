/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.StandardTwoRail
import KontoroC.MersenneShadow
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite partial-theta identity for the standard schedule

After removing the forced factor three, the standard payload recurrence is

`2^(t+13) U(t+1) = 3^(t+8) U(t) + 23`.

This file proves its exact finite unrolling.  It makes no irrationality claim
about the limiting 2-adic partial-theta value.
-/

namespace KontoroC

open MersennePacketRenewal

/-- A normalized all-level payload sequence for the standard schedule.  This
is a necessary arithmetic projection of an exact standard gate program. -/
structure NormalizedStandardPayloadStream where
  payload : ℕ → ℕ
  payload_pos : ∀ t, 0 < payload t
  recurrence : ∀ t,
    2 ^ (t + 13) * payload (t + 1) =
      3 ^ (t + 8) * payload t + 23

namespace NormalizedStandardPayloadStream

open Filter Topology

/-- Backward multiplier at normalized level `t`. -/
def backwardCoeff (t : ℕ) : ℚ :=
  (2 : ℚ) ^ (t + 13) / (3 : ℚ) ^ (t + 8)

/-- Constant defect at normalized level `t`. -/
def backwardDefect (t : ℕ) : ℚ :=
  23 / (3 : ℚ) ^ (t + 8)

theorem step_backward (g : NormalizedStandardPayloadStream) (t : ℕ) :
    (g.payload t : ℚ) =
      backwardCoeff t * g.payload (t + 1) - backwardDefect t := by
  have h :
      (2 : ℚ) ^ (t + 13) * g.payload (t + 1) =
        (3 : ℚ) ^ (t + 8) * g.payload t + 23 := by
    exact_mod_cast g.recurrence t
  dsimp [backwardCoeff, backwardDefect]
  have hthree : (3 : ℚ) ^ (t + 8) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Mathlib-native form of the quadratic exponent
`n(n+2*c-1)/2`: `choose n 2 + c*n`. -/
def quadraticExponent (c n : ℕ) : ℕ :=
  n.choose 2 + c * n

theorem quadraticExponent_succ (c n : ℕ) :
    quadraticExponent c (n + 1) = quadraticExponent c n + n + c := by
  simp only [quadraticExponent]
  rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
  simp
  ring

/-- Terminal numerator exponent `n(n+25)/2`. -/
def terminalTwoExponent (n : ℕ) : ℕ := quadraticExponent 13 n

/-- Terminal denominator exponent `n(n+15)/2`. -/
def terminalThreeExponent (n : ℕ) : ℕ := quadraticExponent 8 n

/-- Denominator exponent `(n+1)(n+16)/2` of the `n`th defect term. -/
def thetaThreeExponent (n : ℕ) : ℕ := terminalThreeExponent (n + 1)

@[simp] theorem terminalTwoExponent_succ (n : ℕ) :
    terminalTwoExponent (n + 1) = terminalTwoExponent n + n + 13 :=
  quadraticExponent_succ 13 n

@[simp] theorem terminalThreeExponent_succ (n : ℕ) :
    terminalThreeExponent (n + 1) =
      terminalThreeExponent n + n + 8 :=
  quadraticExponent_succ 8 n

/-- One positive rational defect term in the partial-theta expansion. -/
def thetaTerm (n : ℕ) : ℚ :=
  23 * (2 : ℚ) ^ terminalTwoExponent n /
    (3 : ℚ) ^ thetaThreeExponent n

def thetaPartial (n : ℕ) : ℚ :=
  ∑ t ∈ Finset.range n, thetaTerm t

/-- Closed product of the first `n` backward coefficients. -/
theorem backwardPrefixProduct_eq (n : ℕ) :
    backwardPrefixProduct backwardCoeff n =
      (2 : ℚ) ^ terminalTwoExponent n /
        (3 : ℚ) ^ terminalThreeExponent n := by
  induction n with
  | zero => simp [backwardPrefixProduct, terminalTwoExponent,
      terminalThreeExponent, quadraticExponent]
  | succ n ih =>
      rw [backwardPrefixProduct, ih]
      simp only [backwardCoeff, terminalTwoExponent_succ,
        terminalThreeExponent_succ, pow_add]
      ring

/-- The generic accumulated defect is exactly the displayed partial-theta
truncation. -/
theorem backwardPrefixDefect_eq (n : ℕ) :
    backwardPrefixDefect backwardCoeff backwardDefect n = thetaPartial n := by
  induction n with
  | zero => simp [backwardPrefixDefect, thetaPartial]
  | succ n ih =>
      rw [backwardPrefixDefect, ih, backwardPrefixProduct_eq]
      simp only [thetaPartial, Finset.sum_range_succ]
      congr 1
      simp only [thetaTerm, backwardDefect, thetaThreeExponent,
        terminalThreeExponent_succ]
      ring

/-- Exact finite identity underlying the partial-theta candidate.  The final
term is retained; no Archimedean or 2-adic limit has been taken. -/
theorem finite_theta_identity (g : NormalizedStandardPayloadStream) (n : ℕ) :
    (g.payload 0 : ℚ) =
      (2 : ℚ) ^ terminalTwoExponent n * g.payload n /
          (3 : ℚ) ^ terminalThreeExponent n -
        thetaPartial n := by
  have h := backward_affine_unroll
    (y := fun t => (g.payload t : ℚ))
    (a := backwardCoeff) (b := backwardDefect)
    (fun t => g.step_backward t) n
  rw [backwardPrefixProduct_eq, backwardPrefixDefect_eq] at h
  calc
    (g.payload 0 : ℚ) =
        ((2 : ℚ) ^ terminalTwoExponent n /
            (3 : ℚ) ^ terminalThreeExponent n) * g.payload n -
          thetaPartial n := h
    _ = (2 : ℚ) ^ terminalTwoExponent n * g.payload n /
          (3 : ℚ) ^ terminalThreeExponent n - thetaPartial n := by ring

theorem le_terminalTwoExponent (n : ℕ) : n ≤ terminalTwoExponent n := by
  simp only [terminalTwoExponent, quadraticExponent]
  omega

/-- The positive partial-theta term embedded in `ℚ₂`. -/
noncomputable def padicThetaTerm (n : ℕ) : ℚ_[2] :=
  (thetaTerm n : ℚ_[2])

theorem norm_padicThetaTerm (n : ℕ) :
    ‖padicThetaTerm n‖ =
      ((2 : ℝ)⁻¹) ^ terminalTwoExponent n := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have htwentythree : ‖(23 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [padicThetaTerm, thetaTerm, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat,
    Rat.cast_ofNat, norm_div, norm_mul, norm_pow, norm_pow,
    htwo, hthree, htwentythree, one_mul, one_pow, div_one]

theorem norm_padicThetaTerm_le (n : ℕ) :
    ‖padicThetaTerm n‖ ≤ ((2 : ℝ)⁻¹) ^ n := by
  rw [norm_padicThetaTerm]
  exact pow_le_pow_of_le_one (by positivity) (by norm_num)
    (le_terminalTwoExponent n)

theorem padicThetaTerm_tendsto_zero :
    Tendsto padicThetaTerm atTop (𝓝 0) := by
  apply squeeze_zero_norm norm_padicThetaTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicThetaTerm_summable : Summable padicThetaTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using padicThetaTerm_tendsto_zero

noncomputable def padicThetaSum : ℚ_[2] :=
  ∑' n, padicThetaTerm n

noncomputable def padicThetaPartial (n : ℕ) : ℚ_[2] :=
  ∑ t ∈ Finset.range n, padicThetaTerm t

theorem padicThetaPartial_tendsto_sum :
    Tendsto padicThetaPartial atTop (𝓝 padicThetaSum) := by
  change Tendsto (fun n => ∑ t ∈ Finset.range n, padicThetaTerm t)
    atTop (𝓝 padicThetaSum)
  simpa only [padicThetaSum] using
    padicThetaTerm_summable.hasSum.tendsto_sum_nat

theorem cast_thetaPartial (n : ℕ) :
    (thetaPartial n : ℚ_[2]) = padicThetaPartial n := by
  simp only [thetaPartial, padicThetaPartial, padicThetaTerm]
  push_cast
  rfl

/-- Terminal term in the finite identity, interpreted 2-adically. -/
noncomputable def padicTerminal
    (g : NormalizedStandardPayloadStream) (n : ℕ) : ℚ_[2] :=
  (2 : ℚ_[2]) ^ terminalTwoExponent n * g.payload n /
    (3 : ℚ_[2]) ^ terminalThreeExponent n

theorem norm_padicTerminal_le
    (g : NormalizedStandardPayloadStream) (n : ℕ) :
    ‖g.padicTerminal n‖ ≤ ((2 : ℝ)⁻¹) ^ n := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hpayload : ‖(g.payload n : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.payload n))
  rw [padicTerminal, norm_div, norm_mul, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]
  calc
    ((2 : ℝ)⁻¹) ^ terminalTwoExponent n * ‖(g.payload n : ℚ_[2])‖ ≤
        ((2 : ℝ)⁻¹) ^ terminalTwoExponent n * 1 :=
      mul_le_mul_of_nonneg_left hpayload (by positivity)
    _ = ((2 : ℝ)⁻¹) ^ terminalTwoExponent n := by ring
    _ ≤ ((2 : ℝ)⁻¹) ^ n :=
      pow_le_pow_of_le_one (by positivity) (by norm_num)
        (le_terminalTwoExponent n)

theorem padicTerminal_tendsto_zero
    (g : NormalizedStandardPayloadStream) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

/-- The exact rational truncation transported into `ℚ₂`. -/
theorem padic_finite_theta_identity
    (g : NormalizedStandardPayloadStream) (n : ℕ) :
    (g.payload 0 : ℚ_[2]) = g.padicTerminal n - padicThetaPartial n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.finite_theta_identity n)
  simpa [padicTerminal, cast_thetaPartial, Rat.cast_sub, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Any ordinary normalized stream forces the independently defined
partial-theta sum to equal the negative of its initial payload. -/
theorem padicThetaSum_eq_negative_payload
    (g : NormalizedStandardPayloadStream) :
    padicThetaSum = -(g.payload 0 : ℚ_[2]) := by
  have heq : padicThetaPartial = fun n =>
      g.padicTerminal n - (g.payload 0 : ℚ_[2]) := by
    funext n
    have h := g.padic_finite_theta_identity n
    linear_combination h
  have hlim : Tendsto padicThetaPartial atTop
      (𝓝 (-(g.payload 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  exact tendsto_nhds_unique padicThetaPartial_tendsto_sum hlim

/-- The candidate in the sign convention of the research note. -/
noncomputable def padicThetaCandidate : ℚ_[2] :=
  -padicThetaSum

theorem padicThetaCandidate_eq_payload
    (g : NormalizedStandardPayloadStream) :
    padicThetaCandidate = (g.payload 0 : ℚ_[2]) := by
  rw [padicThetaCandidate, g.padicThetaSum_eq_negative_payload]
  simp

/-- Arithmetic obstruction endpoint: if the partial-theta candidate is not
an embedded positive natural, no normalized standard payload stream exists. -/
theorem no_stream_of_candidate_avoids_positiveNaturals
    (havoid : ∀ u : ℕ, 0 < u →
      padicThetaCandidate ≠ (u : ℚ_[2])) :
    ¬Nonempty NormalizedStandardPayloadStream := by
  rintro ⟨g⟩
  exact havoid (g.payload 0) (g.payload_pos 0)
    g.padicThetaCandidate_eq_payload

end NormalizedStandardPayloadStream

end KontoroC
