/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardKernelDecoderGap

/-!
# A Jacobian tangent is not a second ordinary solution

For a finite algebraic selector model, a nonzero Jacobian kernel detects a
nontrivial infinitesimal tangent.  It does **not** by itself prove that the
ordinary solution set has two points.  The elementary equation `x^2 = 0`
over the rationals is the exact counterexample: its only rational solution is
zero, while its linearization at zero is the zero map and hence has a nonzero
kernel.

This distinction matters for architecture CEGIS.  A tangent witness can
reject a claim of infinitesimal or reduced-scheme rigidity, but cannot reject
uniqueness of a literal integer/rational selector without an independently
extracted second ordinary point.  Conversely, a trivial tangent does not
construct a solution, a next-precision lift, or an ordinary first-passage
orbit.
-/

namespace KontoroC
namespace OutwardJacobianRigidityGap

/-- One specified point is the unique ordinary point in a target fiber. -/
def HasUniqueFiberPoint {Point Value : Type*}
    (system : Point → Value) (target : Value) (base : Point) : Prop :=
  system base = target ∧
    ∀ point, system point = target → point = base

/-- The declared linearization has a nonzero tangent vector in its kernel. -/
def HasNonzeroLinearizedTangent
    {FieldType Source Target : Type*}
    [Semiring FieldType]
    [AddCommMonoid Source] [Module FieldType Source]
    [AddCommMonoid Target] [Module FieldType Target]
    (jacobian : Source →ₗ[FieldType] Target) : Prop :=
  ∃ tangent, tangent ≠ 0 ∧ jacobian tangent = 0

/-- The elementary selector equation used to separate ordinary uniqueness
from infinitesimal rigidity. -/
def squareSystem (x : ℚ) : ℚ := x ^ 2

/-- Its linearization at zero is the zero linear map. -/
def squareJacobianAtZero : ℚ →ₗ[ℚ] ℚ := 0

/-- The rational fiber `x^2 = 0` has exactly one ordinary point. -/
theorem squareSystem_hasUniqueZero :
    HasUniqueFiberPoint squareSystem 0 0 := by
  constructor
  · norm_num [squareSystem]
  · intro x hx
    dsimp [squareSystem] at hx
    exact sq_eq_zero_iff.mp hx

/-- Nevertheless the exact linearization at that point has a nonzero kernel. -/
theorem squareJacobianAtZero_hasNonzeroTangent :
    HasNonzeroLinearizedTangent squareJacobianAtZero := by
  refine ⟨1, by norm_num, ?_⟩
  rfl

/-- The absence of a linear term is visible in the exact displacement
identity: every perturbation starts at quadratic order. -/
theorem squareSystem_displacement_is_quadratic (parameter tangent : ℚ) :
    squareSystem (0 + parameter * tangent) =
      parameter ^ 2 * tangent ^ 2 := by
  simp [squareSystem]
  ring

/-- Kernel-checked counterexample to the invalid implication “nonzero
Jacobian tangent implies a second ordinary solution.” -/
theorem nonzeroTangent_does_not_imply_secondOrdinaryPoint :
    ¬ (HasNonzeroLinearizedTangent squareJacobianAtZero →
      ∃ x : ℚ, x ≠ 0 ∧ squareSystem x = 0) := by
  intro himplication
  obtain ⟨x, hxne, hxzero⟩ :=
    himplication squareJacobianAtZero_hasNonzeroTangent
  have hx : x = 0 := squareSystem_hasUniqueZero.2 x hxzero
  exact hxne hx

/-- Both facts coexist: the ordinary fiber is a singleton and its declared
linearization has a nonzero tangent. -/
theorem uniqueOrdinaryPoint_and_nonzeroTangent :
    HasUniqueFiberPoint squareSystem 0 0 ∧
      HasNonzeroLinearizedTangent squareJacobianAtZero :=
  ⟨squareSystem_hasUniqueZero,
    squareJacobianAtZero_hasNonzeroTangent⟩

end OutwardJacobianRigidityGap
end KontoroC
