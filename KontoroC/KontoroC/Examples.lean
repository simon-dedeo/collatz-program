/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CycleCertificate
import KontoroC.SignedController
import KontoroC.MersenneShadow

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

/-! The strongest finite phase-shadow regression supplied by the worker.
It is deliberately kept here, outside every soundness dependency. -/

def phaseShadowWord0 : List ℕ := shadowMacroWord [2, 1] 1 2
def phaseShadowWord1 : List ℕ := shadowMacroWord [1, 2] 2 3
def phaseShadowWord2 : List ℕ := shadowMacroWord [2, 1] 3 1
def phaseShadowWord3 : List ℕ := shadowMacroWord [2, 1] 4 1

theorem phaseShadowFiniteChain :
    WordLegal 53403857 phaseShadowWord0 ∧
    runWord 53403857 phaseShadowWord0 = 15019835 ∧
    WordLegal 15019835 phaseShadowWord1 ∧
    runWord 15019835 phaseShadowWord1 = 2376185 ∧
    WordLegal 2376185 phaseShadowWord2 ∧
    runWord 2376185 phaseShadowWord2 = 1691641 ∧
    WordLegal 1691641 phaseShadowWord3 ∧
    runWord 1691641 phaseShadowWord3 = 1354843 := by
  native_decide

/-- The finite chain cannot renew at level five near either phase of the
controller through `-5` and `-7`. -/
theorem phaseShadowFiniteChain_not_levelFive_aligned :
    ¬(8 : ℤ) ^ 5 ∣ (1354843 : ℤ) - (-5) ∧
    ¬(8 : ℤ) ^ 5 ∣ (1354843 : ℤ) - (-7) := by
  norm_num

/-! The strongest growing finite `-1` shadow regression currently emitted by
`search_mersenne_shadow.py`.  It is again a test, not an infinite witness. -/

theorem mersenneShadowFiniteChain :
    WordLegal 24017279 (mersenneMacroWord 7 4) ∧
    runWord 24017279 (mersenneMacroWord 7 4) = 25647359 ∧
    WordLegal 25647359 (mersenneMacroWord 8 3) ∧
    runWord 25647359 (mersenneMacroWord 8 3) = 82164223 ∧
    WordLegal 82164223 (mersenneMacroWord 9 1) ∧
    runWord 82164223 (mersenneMacroWord 9 1) = 1579334395 := by
  native_decide

/-- The three outward macrosteps do not renew the `-1` coordinate at level
ten, so they cannot be promoted to `MersenneShadowOrbit`. -/
theorem mersenneShadowFiniteChain_not_levelTen_aligned :
    ¬(2 : ℤ) ^ 10 ∣ (1579334395 : ℤ) + 1 := by
  norm_num

/-! Constant-extra seed-stability regression requested by the worker. -/

theorem mersenneConstantExtraFiniteChain :
    WordLegal 121 (mersenneMacroWord 1 1) ∧
    runWord 121 (mersenneMacroWord 1 1) = 91 ∧
    WordLegal 91 (mersenneMacroWord 2 1) ∧
    runWord 91 (mersenneMacroWord 2 1) = 103 ∧
    WordLegal 103 (mersenneMacroWord 3 1) ∧
    runWord 103 (mersenneMacroWord 3 1) = 175 ∧
    WordLegal 175 (mersenneMacroWord 4 1) ∧
    runWord 175 (mersenneMacroWord 4 1) = 445 := by
  native_decide

/-- Constant extra `e=1` also fails its next required shadow coordinate. -/
theorem mersenneConstantExtraFiniteChain_not_levelFive_aligned :
    ¬(2 : ℤ) ^ 5 ∣ (445 : ℤ) + 1 := by
  norm_num

end KontoroC
