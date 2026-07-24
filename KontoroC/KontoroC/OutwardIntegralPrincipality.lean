/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardPolicyLiftCohomology
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Integral principality gates for outward valuation charts

A collection of branchwise slope jumps comes from one integral affine
correction only if its integer system `A * a = b` is solvable over `ℤ`.
Solvability over `ℚ`, `ℝ`, or a fitted finite table is weaker.  This file
provides two exact interfaces:

* the class of `b` in the cokernel of the integer matrix is the complete
  (abstract) obstruction;
* a left obstruction after mapping to any commutative ring, especially
  `ZMod modulus`, is a small proof-carrying certificate of non-solvability.

The modular certificate detects invariant-factor torsion missed by an
ordinary integer left-kernel test: for example, parity detects the failure of
`2 * a = 1` although the integer left kernel is zero.

This is a finite algebraic preflight only.  Passing it does not prove that a
potential is coercive, that its inequalities hold for every literal
first-passage macro, or that an ordinary infinite execution exists.
-/

namespace KontoroC
namespace OutwardIntegralPrincipality

variable {Row Column RingType : Type*}

/-- The claimed jumps are the integer image of one correction vector. -/
def IntegerPrincipal
    [Fintype Column]
    (A : Matrix Row Column ℤ) (b : Row → ℤ) : Prop :=
  ∃ a : Column → ℤ, A.mulVec a = b

/-- The complete abstract obstruction: the class of `b` in the cokernel of
the integer matrix. -/
def cokernelClass
    [Fintype Column]
    (A : Matrix Row Column ℤ) (b : Row → ℤ) :
    (Row → ℤ) ⧸ LinearMap.range A.mulVecLin :=
  (LinearMap.range A.mulVecLin).mkQ b

/-- Integral principality is exactly vanishing of the cokernel class. -/
theorem integerPrincipal_iff_cokernelClass_eq_zero
    [Fintype Column]
    (A : Matrix Row Column ℤ) (b : Row → ℤ) :
    IntegerPrincipal A b ↔ cokernelClass A b = 0 := by
  rw [IntegerPrincipal, cokernelClass, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

/-- Exact semantic dichotomy.  The right branch is complete, but the quotient
class is an abstract object rather than the compact certificate expected from
a Smith-normal-form worker. -/
theorem integerPrincipal_or_nonzero_cokernelClass
    [Fintype Column]
    (A : Matrix Row Column ℤ) (b : Row → ℤ) :
    IntegerPrincipal A b ∨ cokernelClass A b ≠ 0 := by
  by_cases hprincipal : IntegerPrincipal A b
  · exact Or.inl hprincipal
  · exact Or.inr fun hzero ↦
      hprincipal ((integerPrincipal_iff_cokernelClass_eq_zero A b).mpr hzero)

/-- A left vector over a commutative ring which kills every matrix column but
detects the target. -/
def IsLeftObstruction
    [CommRing RingType] [Fintype Row] [Fintype Column]
    (A : Matrix Row Column RingType) (b : Row → RingType)
    (witness : Row → RingType) : Prop :=
  Matrix.vecMul witness A = 0 ∧ dotProduct witness b ≠ 0

/-- Soundness of a supplied left obstruction over any commutative ring.  A
field hypothesis is intentionally unnecessary, so composite invariant-factor
moduli are valid. -/
theorem no_ringSolution_of_leftObstruction
    [CommRing RingType] [Fintype Row] [Fintype Column]
    (A : Matrix Row Column RingType) (b : Row → RingType)
    (witness : Row → RingType)
    (hobstruction : IsLeftObstruction A b witness) :
    ¬ ∃ a : Column → RingType, A.mulVec a = b := by
  rintro ⟨a, ha⟩
  apply hobstruction.2
  rw [← ha, Matrix.dotProduct_mulVec, hobstruction.1]
  simp [dotProduct]

/-- An obstruction after applying a ring homomorphism to the integer system.
This packages reduction modulo an arbitrary modulus as well as other exact
coefficient maps. -/
def IsMappedLeftObstruction
    [CommRing RingType] [Fintype Row] [Fintype Column]
    (mapCoefficients : ℤ →+* RingType)
    (A : Matrix Row Column ℤ) (b : Row → ℤ)
    (witness : Row → RingType) : Prop :=
  IsLeftObstruction (A.map mapCoefficients)
    (mapCoefficients ∘ b) witness

/-- Every mapped left obstruction refutes an integer correction. -/
theorem no_integerPrincipal_of_mappedLeftObstruction
    [CommRing RingType] [Fintype Row] [Fintype Column]
    (mapCoefficients : ℤ →+* RingType)
    (A : Matrix Row Column ℤ) (b : Row → ℤ)
    (witness : Row → RingType)
    (hobstruction :
      IsMappedLeftObstruction mapCoefficients A b witness) :
    ¬IntegerPrincipal A b := by
  intro hprincipal
  obtain ⟨a, ha⟩ := hprincipal
  apply no_ringSolution_of_leftObstruction
    (A.map mapCoefficients) (mapCoefficients ∘ b) witness hobstruction
  refine ⟨mapCoefficients ∘ a, funext fun row ↦ ?_⟩
  rw [← RingHom.map_mulVec]
  exact congrArg mapCoefficients (congrFun ha row)

/-- Worker-facing invariant-factor certificate: reduce the integer system
modulo `modulus`, then provide a left vector which kills all reduced columns
and detects the reduced target. -/
def IsModularObstruction
    [Fintype Row] [Fintype Column]
    (modulus : ℕ) (A : Matrix Row Column ℤ) (b : Row → ℤ)
    (witness : Row → ZMod modulus) : Prop :=
  IsMappedLeftObstruction (Int.castRingHom (ZMod modulus)) A b witness

/-- Soundness of a supplied modular nonprincipality certificate. -/
theorem no_integerPrincipal_of_modularObstruction
    [Fintype Row] [Fintype Column]
    (modulus : ℕ) (A : Matrix Row Column ℤ) (b : Row → ℤ)
    (witness : Row → ZMod modulus)
    (hobstruction : IsModularObstruction modulus A b witness) :
    ¬IntegerPrincipal A b :=
  no_integerPrincipal_of_mappedLeftObstruction
    (Int.castRingHom (ZMod modulus)) A b witness hobstruction

/-- A modular certificate also proves that the complete integer cokernel class
is nonzero. -/
theorem cokernelClass_ne_zero_of_modularObstruction
    [Fintype Row] [Fintype Column]
    (modulus : ℕ) (A : Matrix Row Column ℤ) (b : Row → ℤ)
    (witness : Row → ZMod modulus)
    (hobstruction : IsModularObstruction modulus A b witness) :
    cokernelClass A b ≠ 0 := by
  intro hzero
  exact no_integerPrincipal_of_modularObstruction
    modulus A b witness hobstruction
      ((integerPrincipal_iff_cokernelClass_eq_zero A b).mpr hzero)

end OutwardIntegralPrincipality
end KontoroC
