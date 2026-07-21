/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CycleCertificate

/-!
# Small exact regression examples

These `native_decide` regression examples ensure that the Lean definitions
agree with the independent Python compiler on the motivating finite word, and
that the trivial cycle is accepted as a cycle but rejected by the separate
nontriviality gate.  They are tests, not premises of any soundness theorem.
-/

namespace KontoroC

theorem example199_legal : WordLegal 199 [1, 1, 2, 2] := by native_decide

theorem example199_endpoint : runWord 199 [1, 1, 2, 2] = 253 := by native_decide

theorem example199_affineOffset : affineOffset [1, 1, 2, 2] = 73 := by decide

def trivialCycleArtifact : CycleArtifact where
  word := [2]
  seed := 1
  orbit := [1]
  affineConstant := 1
  totalHalvings := 2
  acceleratedSteps := 1
  ordinarySteps := 3

theorem trivialCycleArtifact_check : trivialCycleArtifact.check = true := by native_decide

theorem trivialCycleArtifact_not_nontrivial :
    trivialCycleArtifact.checkNontrivial = false := by native_decide

end KontoroC
