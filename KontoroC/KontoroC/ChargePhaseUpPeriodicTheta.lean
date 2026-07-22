/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePhaseUpTheta

/-!
# Periodic phase-up jump words split into finitely many theta series

This file starts the extension of the fixed-jump obstruction to a nonempty
finite word of positive jumps repeated forever.  It proves the exact
cycle-shift laws for the public-cofactor backward coefficients and the pure
algebra which splits the resulting series by positions in the period.

The final multi-value Väänänen--Wallisser linear-independence theorem remains
an external citation, just as in `ChargePhaseUpTheta`.
-/

namespace KontoroC

open MersennePacketRenewal

namespace PeriodicPhaseUp

/-- One nonempty finite word of positive jump sizes. -/
structure JumpWord where
  period : ℕ
  period_pos : 0 < period
  jump : Fin period → ℕ
  jump_pos : ∀ r, 0 < jump r

namespace JumpWord

def cycleSum (W : JumpWord) : ℕ := ∑ r, W.jump r

def prefixSum (W : JumpWord) (r : Fin W.period) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin W.period => (i : ℕ) < r), W.jump i

theorem cycleSum_pos (W : JumpWord) : 0 < W.cycleSum := by
  let r : Fin W.period := ⟨0, W.period_pos⟩
  have hr := W.jump_pos r
  have hle : W.jump r ≤ W.cycleSum := by
    simp only [cycleSum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  omega

def phase (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  m₀ + 4 * (n * W.cycleSum + W.prefixSum r)

def targetPhase (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  W.phase m₀ n r + 4 * W.jump r

def recharge (W : JumpWord) (r : Fin W.period) : ℕ :=
  FixedJumpPhaseUp.recharge (W.jump r)

def binaryExponent (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  154 * W.recharge r + 23 * W.targetPhase m₀ n r

def ternaryExponent (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℕ :=
  114 * W.recharge r + 17 * W.phase m₀ n r

def backwardCoeff (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℚ :=
  (2 : ℚ) ^ W.binaryExponent m₀ n r /
    (3 : ℚ) ^ W.ternaryExponent m₀ n r

def backwardDefect (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) : ℚ :=
  -(FixedJumpPhaseUp.gap (W.jump r) : ℚ) /
    (3 : ℚ) ^ W.ternaryExponent m₀ n r

def cycleRatio (W : JumpWord) : ℚ :=
  (2 : ℚ) ^ (92 * W.cycleSum) / (3 : ℚ) ^ (68 * W.cycleSum)

def defectRatio (W : JumpWord) : ℚ :=
  1 / (3 : ℚ) ^ (68 * W.cycleSum)

theorem phase_cycle_shift (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.phase m₀ (n + 1) r = W.phase m₀ n r + 4 * W.cycleSum := by
  simp only [phase]
  ring

theorem targetPhase_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.targetPhase m₀ (n + 1) r =
      W.targetPhase m₀ n r + 4 * W.cycleSum := by
  rw [targetPhase, targetPhase, W.phase_cycle_shift]
  ring

theorem binaryExponent_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.binaryExponent m₀ (n + 1) r =
      W.binaryExponent m₀ n r + 92 * W.cycleSum := by
  simp only [binaryExponent, W.targetPhase_cycle_shift]
  ring

theorem ternaryExponent_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.ternaryExponent m₀ (n + 1) r =
      W.ternaryExponent m₀ n r + 68 * W.cycleSum := by
  simp only [ternaryExponent, W.phase_cycle_shift]
  ring

/-- At a fixed position in the jump word, advancing one whole period
multiplies the backward coefficient by one common rational ratio. -/
theorem backwardCoeff_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ (n + 1) r =
      W.cycleRatio * W.backwardCoeff m₀ n r := by
  rw [backwardCoeff, backwardCoeff, W.binaryExponent_cycle_shift,
    W.ternaryExponent_cycle_shift]
  simp only [cycleRatio, pow_add]
  ring

/-- The signed defect has its own common cycle multiplier. -/
theorem backwardDefect_cycle_shift
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ (n + 1) r =
      W.defectRatio * W.backwardDefect m₀ n r := by
  rw [backwardDefect, backwardDefect, W.ternaryExponent_cycle_shift]
  simp only [defectRatio, pow_add]
  ring

theorem backwardCoeff_cycle_closed
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ n r =
      W.cycleRatio ^ n * W.backwardCoeff m₀ 0 r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [W.backwardCoeff_cycle_shift m₀ n r, ih, pow_succ]
      ring

theorem backwardDefect_cycle_closed
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ n r =
      W.defectRatio ^ n * W.backwardDefect m₀ 0 r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [W.backwardDefect_cycle_shift m₀ n r, ih, pow_succ]
      ring

def cycleCoeff (W : JumpWord) (m₀ n : ℕ) : ℚ :=
  ∏ r, W.backwardCoeff m₀ n r

theorem cycleCoeff_closed (W : JumpWord) (m₀ n : ℕ) :
    W.cycleCoeff m₀ n =
      W.cycleRatio ^ (n * W.period) * W.cycleCoeff m₀ 0 := by
  simp only [cycleCoeff, W.backwardCoeff_cycle_closed m₀ n]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_fin, ← pow_mul]

theorem cycleRatio_ne_zero (W : JumpWord) : W.cycleRatio ≠ 0 := by
  apply div_ne_zero <;> positivity

theorem defectRatio_ne_zero (W : JumpWord) : W.defectRatio ≠ 0 := by
  simp [defectRatio]

theorem backwardCoeff_ne_zero
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardCoeff m₀ n r ≠ 0 := by
  apply div_ne_zero <;> positivity

theorem backwardDefect_ne_zero
    (W : JumpWord) (m₀ n : ℕ) (r : Fin W.period) :
    W.backwardDefect m₀ n r ≠ 0 := by
  apply div_ne_zero
  · exact neg_ne_zero.mpr (by
      exact_mod_cast (FixedJumpPhaseUp.gap_pos (W.jump r)).ne')
  · positivity

theorem cycleCoeff_ne_zero (W : JumpWord) (m₀ n : ℕ) :
    W.cycleCoeff m₀ n ≠ 0 := by
  simp only [cycleCoeff, Finset.prod_ne_zero_iff]
  intro r _
  exact W.backwardCoeff_ne_zero m₀ n r

end JumpWord

/-! ## Pure residue-class theta decomposition -/

/-- Algebraic data left after splitting a periodic coefficient schedule by
positions in its period.  `ratio` is the common coefficient multiplier per
cycle, `defectRatio` is the common defect multiplier, and `cycleCoeff` is the
product of the coefficients in cycle zero. -/
structure ThetaResidueData (p : ℕ) where
  ratio : ℚ
  defectRatio : ℚ
  cycleCoeff : ℚ
  prefixScale : Fin p → ℚ

namespace ThetaResidueData

def weightedTerm {p : ℕ} (D : ThetaResidueData p)
    (r : Fin p) (n : ℕ) : ℚ :=
  D.prefixScale r *
    (D.ratio ^ p) ^ n.choose 2 *
    (D.cycleCoeff * D.ratio ^ (r : ℕ) * D.defectRatio) ^ n

def parameterInverse {p : ℕ} (D : ThetaResidueData p) : ℚ :=
  D.ratio ^ p

def argument {p : ℕ} (D : ThetaResidueData p) (r : Fin p) : ℚ :=
  (D.cycleCoeff * D.ratio ^ (r : ℕ) * D.defectRatio) /
    D.parameterInverse

def vaananenExponent (n : ℕ) : ℕ := n.choose 2 + n

def vaananenTerm {p : ℕ} (D : ThetaResidueData p)
    (r : Fin p) (n : ℕ) : ℚ :=
  D.parameterInverse ^ vaananenExponent n * D.argument r ^ n

/-- Each residue-class subsequence is exactly one rational multiple of the
paper-normalized theta series, coefficient by coefficient. -/
theorem weightedTerm_eq_scaled_vaananenTerm {p : ℕ}
    (D : ThetaResidueData p) (hratio : D.ratio ≠ 0)
    (r : Fin p) (n : ℕ) :
    D.weightedTerm r n = D.prefixScale r * D.vaananenTerm r n := by
  simp only [weightedTerm, vaananenTerm, vaananenExponent, argument,
    parameterInverse, pow_add, div_pow]
  field_simp [pow_ne_zero _ hratio]

/-- The theta arguments at two period positions differ only by the
corresponding power of the common one-cycle ratio. -/
theorem argument_cross_ratio {p : ℕ} (D : ThetaResidueData p)
    (r s : Fin p) :
    D.argument r * D.ratio ^ (s : ℕ) =
      D.argument s * D.ratio ^ (r : ℕ) := by
  simp only [argument, parameterInverse]
  ring

theorem argument_ne_zero {p : ℕ} (D : ThetaResidueData p)
    (hratio : D.ratio ≠ 0) (hdefect : D.defectRatio ≠ 0)
    (hcycle : D.cycleCoeff ≠ 0) (r : Fin p) : D.argument r ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero hcycle (pow_ne_zero _ hratio)) hdefect
  · exact pow_ne_zero _ hratio

end ThetaResidueData

end PeriodicPhaseUp

end KontoroC
