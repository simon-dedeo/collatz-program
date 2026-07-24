/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardShadowPathLift
import Mathlib.GroupTheory.Torsion

/-!
# A finite group coordinate cannot carry recharge drift

Any additive map from a finite additive group into a torsion-free additive
group is zero.  In particular a finite abelian group recovered from a bounded
recharge table cannot itself supply a nonzero integer height increment.  A
successful architecture needs a separate cocycle or unbounded extension, and
that extra coordinate must still be connected to literal first-passage
semantics.
-/

namespace KontoroC
namespace OutwardFiniteGroupDriftNoGo

variable {G A : Type*}

/-- General torsion-versus-torsion-free obstruction. Commutativity of the
finite source is not needed. -/
theorem finite_addGroup_hom_torsionFree_eq_zero
    [AddGroup G] [Finite G] [AddGroup A] [IsAddTorsionFree A]
    (f : G →+ A) : f = 0 := by
  ext g
  obtain ⟨n, hnpos, hng⟩ :=
    (is_add_torsion_of_finite g).exists_nsmul_eq_zero
  apply IsAddTorsionFree.nsmul_right_injective (Nat.ne_of_gt hnpos)
  change n • f g = n • (0 : A)
  rw [← f.map_nsmul, hng]
  simp

/-- Integer-valued specialization used by recharge-height proposals. -/
theorem finite_addGroup_hom_int_eq_zero
    [AddGroup G] [Finite G] (height : G →+ ℤ) :
    height = 0 :=
  finite_addGroup_hom_torsionFree_eq_zero height

/-- Every value of a homomorphic integer height on a finite group vanishes. -/
theorem finite_addGroup_hom_int_apply_eq_zero
    [AddGroup G] [Finite G] (height : G →+ ℤ) (g : G) :
    height g = 0 := by
  rw [finite_addGroup_hom_int_eq_zero height]
  rfl

/-- Therefore translation by any finite group element has zero homomorphic
integer increment at every state. -/
theorem finite_group_translation_has_zero_int_drift
    [AddGroup G] [Finite G] (height : G →+ ℤ) (step state : G) :
    height (state + step) - height state = 0 := by
  rw [height.map_add, finite_addGroup_hom_int_apply_eq_zero height step]
  simp

/-- A claimed strictly positive homomorphic recharge increment on a finite
group is impossible. -/
theorem no_positive_homomorphic_int_drift
    [AddGroup G] [Finite G] (height : G →+ ℤ) (step : G) :
    ¬0 < height step := by
  rw [finite_addGroup_hom_int_apply_eq_zero height step]
  exact lt_irrefl 0

end OutwardFiniteGroupDriftNoGo
end KontoroC
