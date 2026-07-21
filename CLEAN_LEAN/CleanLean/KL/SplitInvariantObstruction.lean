/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.EliminationTree

/-!
# Splitting need not preserve the assignment-specific principal invariant

This finite positive constant-valued countermodel checks a second gap in the
printed KL induction.  An outer minimum initially avoids a principal node, so
all old critical assignments satisfy the principal-bound invariant.  Replacing
one inner leaf by a locally valid KL-shaped split lowers that alternative,
makes it critical, and exposes a violated inherited principal bound.

The construction is abstract: it refutes the generic invariant-preservation
inference, not a claim that these constants arise from a concrete KL solution.
-/

namespace CleanLean.KL.SplitInvariantObstruction

open EliminationTree

abbrev Index := Fin 8

/-- Positive constant functions with values `P,L,X,B,T,C0,C1,C2` equal to
`5,9,1,8,2,3,3,3`.  An explicit decision tree makes closed evaluations
kernel-reducible. -/
def φ (i : Index) (_ : ℝ) : ℝ :=
  if i = 0 then 5
  else if i = 1 then 9
  else if i = 2 then 1
  else if i = 3 then 8
  else if i = 4 then 2
  else 3

def label (i : Index) : PrincipalLabel Index := ⟨i, 0⟩

def P : PrincipalLabel Index := label 0
def L : PrincipalLabel Index := label 1
def X : PrincipalLabel Index := label 2
def B : PrincipalLabel Index := label 3
def T : PrincipalLabel Index := label 4
def C0 : PrincipalLabel Index := label 5
def C1 : PrincipalLabel Index := label 6
def C2 : PrincipalLabel Index := label 7

/-- The old inactive left alternative has value `L+X=10` below principal
label `P=5`; the competing right leaf has value eight. -/
def oldLeft : EliminationTree Index :=
  .principal P (.add (.leaf L) (.leaf X))

def oldTree : EliminationTree Index :=
  .inf oldLeft (.leaf B)

/-- A KL-shaped local split with value `T + min(C0,C1,C2) = 2+3=5`. -/
def splitBody : EliminationTree Index :=
  .add (.leaf T) (.inf (.leaf C0) (.inf (.leaf C1) (.leaf C2)))

def splitL : EliminationTree Index := .principal L splitBody

/-- After replacing `L=9` by the locally valid split of value five, the left
alternative has value six and becomes the unique outer minimum. -/
def newLeft : EliminationTree Index :=
  .principal P (.add splitL (.leaf X))

def newTree : EliminationTree Index :=
  .inf newLeft (.leaf B)

theorem φ_pos : ∀ i y, 0 < φ i y := by
  intro i y
  fin_cases i <;> norm_num [φ, Fin.ext_iff]

theorem φ_mono (i : Index) : Monotone (φ i) := by
  intro x y hxy
  rfl

theorem tree_values :
    oldLeft.eval φ 0 = 10 ∧ oldTree.eval φ 0 = 8 ∧
    splitBody.eval φ 0 = 5 ∧ splitL.eval φ 0 = 5 ∧
    newLeft.eval φ 0 = 6 ∧ newTree.eval φ 0 = 6 := by
  norm_num [oldLeft, oldTree, splitBody, splitL, newLeft, newTree,
    EliminationTree.eval, PrincipalLabel.value, P, L, X, B, T, C0, C1, C2,
    label, φ, Fin.ext_iff]

/-- The substituted split is locally valid at `L`: its body value five is at
most the old leaf value nine. -/
theorem splitL_locallyValid : splitL.LocallyValid φ 0 := by
  norm_num [splitL, splitBody, EliminationTree.LocallyValid,
    EliminationTree.eval, PrincipalLabel.value, L, T, C0, C1, C2, label, φ,
    Fin.ext_iff]

/-- Every old critical assignment selects the right leaf and therefore avoids
the violated but inactive principal node. -/
theorem every_old_critical_respects :
    ∀ A : Assignment oldTree,
      A.IsCritical φ 0 → A.RespectsPrincipalBounds φ 0 := by
  intro A hA
  cases A with
  | infLeft leftA =>
      norm_num [oldTree, oldLeft, EliminationTree.eval, Assignment.IsCritical,
        PrincipalLabel.value, P, L, X, B, label, φ, Fin.ext_iff] at hA
  | infRight rightA =>
      cases rightA
      simp [Assignment.RespectsPrincipalBounds]

def splitBodyAssignment : Assignment splitBody :=
  .add (.principalLeaf T) (.infLeft (.principalLeaf C0))

def newLeftAssignment : Assignment newLeft :=
  .principalNode (.add (.principalNode splitBodyAssignment) (.principalLeaf X))

def newAssignment : Assignment newTree :=
  .infLeft newLeftAssignment

theorem newAssignment_critical : newAssignment.IsCritical φ 0 := by
  norm_num [newAssignment, newLeftAssignment, splitBodyAssignment, newTree,
    newLeft, splitL, splitBody, EliminationTree.eval, Assignment.IsCritical,
    PrincipalLabel.value, P, L, X, B, T, C0, C1, C2, label, φ, Fin.ext_iff]

/-- The newly activated assignment selects total value six below `P=5`, so
the inherited principal bound fails. -/
theorem newAssignment_violates_principal_bound :
    ¬newAssignment.RespectsPrincipalBounds φ 0 := by
  norm_num [newAssignment, newLeftAssignment, splitBodyAssignment,
    Assignment.RespectsPrincipalBounds, Assignment.selectedEval,
    PrincipalLabel.value, P, L, X, T, C0, label, φ, Fin.ext_iff]

/-- Exact countermodel to the generic split-preservation inference used by the
printed induction. -/
theorem split_time_invariant_preservation_fails :
    (∀ A : Assignment oldTree,
      A.IsCritical φ 0 → A.RespectsPrincipalBounds φ 0) ∧
    splitL.LocallyValid φ 0 ∧
    ∃ A : Assignment newTree,
      A.IsCritical φ 0 ∧ ¬A.RespectsPrincipalBounds φ 0 := by
  exact ⟨every_old_critical_respects, splitL_locallyValid,
    newAssignment, newAssignment_critical,
    newAssignment_violates_principal_bound⟩

end CleanLean.KL.SplitInvariantObstruction
