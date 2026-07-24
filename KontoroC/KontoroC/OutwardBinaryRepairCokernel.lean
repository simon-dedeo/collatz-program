/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import KontoroC.OutwardFrozenTernaryResidue

/-!
# Exact solution-or-cokernel certificates for binary repair tables

A finite replayed macro-effect table should be treated as exact linear
algebra over `F_2`, not as a rank heuristic.  For any requested repair target,
either the columns synthesize it, or a dual functional annihilates every
available column and detects the target.

The generic separation theorem below works over any field and uses mathlib's
audited dual separation for a vector outside a subspace.  The matrix theorem
then exposes the certificate column-by-column, and the final specialization
uses `ZMod 2`.

This certifies the finite additive surrogate only.  A solution vector does
not prove that the selected literal first-passage macros compose, preserve
positivity, or have zero ordinary carry; those semantic obligations remain
separate.
-/

namespace KontoroC
namespace OutwardBinaryRepairCokernel

variable {FieldType Domain Codomain Macro Obligation : Type*}

/-- Algebraic alternative for one linear repair map.  Failure produces an
exact dual obstruction, not merely a rank deficit. -/
theorem linearRepair_or_cokernelWitness
    [Field FieldType]
    [AddCommGroup Domain] [Module FieldType Domain]
    [AddCommGroup Codomain] [Module FieldType Codomain]
    (repair : Domain →ₗ[FieldType] Codomain) (target : Codomain) :
    (∃ coefficients, repair coefficients = target) ∨
      ∃ obstruction : Codomain →ₗ[FieldType] FieldType,
        (∀ coefficients, obstruction (repair coefficients) = 0) ∧
        obstruction target ≠ 0 := by
  by_cases htarget : target ∈ repair.range
  · exact Or.inl (LinearMap.mem_range.mp htarget)
  · obtain ⟨obstruction, hdetects, hannihilates⟩ :=
      repair.range.exists_dual_map_eq_bot_of_notMem htarget inferInstance
    refine Or.inr ⟨obstruction, ?_, hdetects⟩
    intro coefficients
    have hmem : obstruction (repair coefficients) ∈
        repair.range.map obstruction := by
      exact ⟨repair coefficients, ⟨coefficients, rfl⟩, rfl⟩
    rw [hannihilates] at hmem
    simpa using hmem

/-- Matrix form.  Either a coefficient vector synthesizes `target`, or one
linear functional kills every matrix column and is nonzero on `target`. -/
theorem matrixRepair_or_columnCokernel
    [Field FieldType]
    [Fintype Macro] [DecidableEq Macro]
    (effects : Matrix Obligation Macro FieldType)
    (target : Obligation → FieldType) :
    (∃ coefficients : Macro → FieldType,
      effects.mulVec coefficients = target) ∨
      ∃ obstruction : (Obligation → FieldType) →ₗ[FieldType] FieldType,
        (∀ choice, obstruction (fun obligation ↦ effects obligation choice) = 0) ∧
        obstruction target ≠ 0 := by
  rcases linearRepair_or_cokernelWitness effects.mulVecLin target with
      hsolution | ⟨obstruction, hannihilates, hdetects⟩
  · obtain ⟨coefficients, hcoefficients⟩ := hsolution
    exact Or.inl ⟨coefficients, by simpa using hcoefficients⟩
  · refine Or.inr ⟨obstruction, ?_, hdetects⟩
    intro choice
    have hcolumn := hannihilates (Pi.single choice 1)
    change obstruction (effects.col choice) = 0
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hcolumn

/-- The exact binary repair/cokernel dichotomy used by the proposed CEGIS
matrix worker. -/
theorem binaryRepair_or_cokernel
    [Fintype Macro] [DecidableEq Macro]
    (effects : Matrix Obligation Macro (ZMod 2))
    (target : Obligation → ZMod 2) :
    (∃ coefficients : Macro → ZMod 2,
      effects.mulVec coefficients = target) ∨
      ∃ obstruction : (Obligation → ZMod 2) →ₗ[ZMod 2] ZMod 2,
        (∀ choice, obstruction (fun obligation ↦ effects obligation choice) = 0) ∧
        obstruction target ≠ 0 :=
  matrixRepair_or_columnCokernel effects target

/-- A supplied cokernel witness immediately refutes every proposed repair
coefficient vector.  This is the small replay theorem a certificate checker
can invoke after evaluating the functional on columns and target. -/
theorem no_matrixRepair_of_columnCokernel
    [Field FieldType]
    [Fintype Macro]
    (effects : Matrix Obligation Macro FieldType)
    (target : Obligation → FieldType)
    (obstruction : (Obligation → FieldType) →ₗ[FieldType] FieldType)
    (hcolumns : ∀ choice,
      obstruction (fun obligation ↦ effects obligation choice) = 0)
    (htarget : obstruction target ≠ 0) :
    ¬∃ coefficients : Macro → FieldType,
      effects.mulVec coefficients = target := by
  rintro ⟨coefficients, hcoefficients⟩
  apply htarget
  have hrangeLe : LinearMap.range effects.mulVecLin ≤
      LinearMap.ker obstruction := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro column ⟨choice, rfl⟩
    apply LinearMap.mem_ker.mpr
    change obstruction (fun obligation ↦ effects obligation choice) = 0
    exact hcolumns choice
  have htargetRange : target ∈ LinearMap.range effects.mulVecLin := by
    exact ⟨coefficients, by simpa using hcoefficients⟩
  exact LinearMap.mem_ker.mp (hrangeLe htargetRange)

end OutwardBinaryRepairCokernel
end KontoroC
