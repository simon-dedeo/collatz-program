/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ExactCertificate

/-!
# Integer-scaled KL certificate format

This mirrors the arithmetic acceptance path documented in
`docs/FOR_CLEAN_LEAN.md`.  It deliberately excludes SHA-256 and NPY parsing;
those are transport concerns, while this file specifies and proves sound the
integer inequalities after a vector has been decoded.
-/

namespace CleanLean.KL

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- Integer data used by the large streamed KL certificates. -/
structure ScaledCertificate where
  lambdaNum : ℕ
  lambdaScale : ℕ
  retardedNum : ℕ
  advancedNum : ℕ
  weightScale : ℕ
  valueScale : ℕ
  value : S.State → ℕ

namespace ScaledCertificate

variable {S}

/-- Minimum of the three scaled integer values in one refinement fiber. -/
def fiberMinValue (d : S.ScaledCertificate) (r : S.Coarse) : ℕ :=
  min (d.value (S.fiber r 0))
    (min (d.value (S.fiber r 1)) (d.value (S.fiber r 2)))

/-- Common-denominator form of the left side of a KL row. -/
def rowLhs (d : S.ScaledCertificate) (m : S.State) : ℕ :=
  d.value m * d.lambdaNum ^ 2 * d.weightScale

/-- Common-denominator form of the right side of a KL row. -/
def rowRhs (d : S.ScaledCertificate) (m : S.State) : ℕ :=
  d.value (S.transport m) * d.lambdaScale ^ 2 * d.weightScale +
    match S.branch m with
    | .retarded => d.retardedNum * d.lambdaNum ^ 2 * d.fiberMinValue (S.refinementTarget m)
    | .neutral => 0
    | .advanced => d.advancedNum * d.lambdaNum ^ 2 * d.fiberMinValue (S.refinementTarget m)

/-- Exact integer proposition checked by the streaming verifier. -/
def Valid (d : S.ScaledCertificate) : Prop :=
  0 < d.lambdaNum ∧ 0 < d.lambdaScale ∧ 0 < d.weightScale ∧
    0 < d.valueScale ∧
    (∀ m, d.valueScale ≤ d.value m) ∧
    ∀ m, d.rowLhs m ≤ d.rowRhs m

/-- Executable finite checker for decoded scaled data. -/
def check (d : S.ScaledCertificate) : Bool :=
  decide
    (0 < d.lambdaNum ∧ 0 < d.lambdaScale ∧ 0 < d.weightScale ∧
      0 < d.valueScale ∧
      (∀ m ∈ (Finset.univ : Finset S.State), d.valueScale ≤ d.value m) ∧
      ∀ m ∈ (Finset.univ : Finset S.State), d.rowLhs m ≤ d.rowRhs m)

theorem check_eq_true_iff (d : S.ScaledCertificate) :
    d.check = true ↔ d.Valid := by
  simp [check, Valid]

/-- Rational weights represented by the integer certificate. -/
def weightsRat (d : S.ScaledCertificate) : Weights ℚ where
  transport := (d.lambdaScale : ℚ) ^ 2 / (d.lambdaNum : ℚ) ^ 2
  retarded := (d.retardedNum : ℚ) / d.weightScale
  advanced := (d.advancedNum : ℚ) / d.weightScale

/-- Rational vector represented by the integer certificate. -/
def valuesRat (d : S.ScaledCertificate) : S.State → ℚ :=
  fun m => (d.value m : ℚ) / d.valueScale

theorem fiberMin_valuesRat (d : S.ScaledCertificate) (r : S.Coarse) :
    S.fiberMin d.valuesRat r = (d.fiberMinValue r : ℚ) / d.valueScale := by
  simp [FiniteSystem.fiberMin, valuesRat, fiberMinValue,
    min_div_div_right, Nat.cast_min]

private def commonDenom (d : S.ScaledCertificate) : ℚ :=
  (d.valueScale : ℚ) * (d.lambdaNum : ℚ) ^ 2 * d.weightScale

theorem valuesRat_eq_rowLhs_div (d : S.ScaledCertificate) (m : S.State)
    (hA : 0 < d.lambdaNum) (hW : 0 < d.weightScale) :
    d.valuesRat m = (d.rowLhs m : ℚ) / d.commonDenom := by
  simp [valuesRat, rowLhs, commonDenom]
  field_simp
  ring

theorem operatorRat_eq_rowRhs_div (d : S.ScaledCertificate) (m : S.State)
    (hA : 0 < d.lambdaNum) (hW : 0 < d.weightScale) :
    S.operatorRat d.weightsRat d.valuesRat m =
      (d.rowRhs m : ℚ) / d.commonDenom := by
  rw [operatorRat]
  rw [fiberMin_valuesRat]
  cases hb : S.branch m <;>
    simp [weightsRat, valuesRat, rowRhs, commonDenom, hb] <;>
    field_simp <;> ring

/-- Soundness of the exact integer row format.  Bounds proving that the two
branch numerators lie below the true irrational KL weights are a separate
analytic obligation. -/
theorem feasibleRat_of_valid (d : S.ScaledCertificate) (hd : d.Valid) :
    S.FeasibleRat d.weightsRat d.valuesRat := by
  rcases hd with ⟨hA, hL, hW, hC, hnorm, hrows⟩
  constructor
  · intro m
    have hCQ : (0 : ℚ) < d.valueScale := by exact_mod_cast hC
    rw [valuesRat, le_div_iff₀ hCQ]
    simpa using (show (d.valueScale : ℚ) ≤ d.value m by exact_mod_cast hnorm m)
  · intro m
    rw [valuesRat_eq_rowLhs_div d m hA hW,
      operatorRat_eq_rowRhs_div d m hA hW]
    have hden : 0 ≤ d.commonDenom := by
      simp [commonDenom]
      positivity
    apply div_le_div_of_nonneg_right _ hden
    exact_mod_cast hrows m

/-- End-to-end soundness after the finite Boolean checker accepts. -/
theorem feasibleRat_of_check (d : S.ScaledCertificate) (hcheck : d.check = true) :
    S.FeasibleRat d.weightsRat d.valuesRat :=
  feasibleRat_of_valid d ((check_eq_true_iff d).1 hcheck)

end ScaledCertificate

end

end FiniteSystem

end CleanLean.KL
