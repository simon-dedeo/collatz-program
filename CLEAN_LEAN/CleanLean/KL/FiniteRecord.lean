/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CriticalParameter

/-!
# A small end-to-end KL certificate

This three-state level-2 certificate is intentionally tiny enough to evaluate
inside Lean.  It exercises the same integer row format and irrational-weight
soundness theorem used by the large streamed GPU certificates.
-/

namespace CleanLean.KL

namespace FiniteRecord

def certificateK2Value (s : ResidueSystem.State 2) : ℕ :=
  match s.val with
  | 0 => 178
  | 1 => 100
  | _ => 170

/-- A level-2 certificate at `lambda = 4/3`, with lower branch weights
`17/20` and `23/20`.  Coordinates `0,1,2` correspond to residue classes
`2,5,8 (mod 9)`. -/
def certificateK2 :
    (ResidueSystem.system 2).ScaledCertificate where
  lambdaNum := 4
  lambdaScale := 3
  retardedNum := 17
  advancedNum := 23
  weightScale := 20
  valueScale := 100
  value := certificateK2Value

theorem certificateK2_rows : certificateK2.check = true := by
  decide

theorem certificateK2_alpha : checkAlphaLower 3 2 = true := by
  decide

theorem certificateK2_weights :
    checkBranchWeightLowerData 4 3 17 23 20 3 2 = true := by
  decide

/-- End-to-end result: the true irrational level-2 KL system is feasible at
`lambda = 4/3`. -/
theorem levelFeasible_four_thirds : LevelFeasible 2 (4 / 3 : ℝ) := by
  apply levelFeasible_of_scaledCertificate 2 3 2 certificateK2
  · exact certificateK2_rows
  · norm_num
  · norm_num [certificateK2]
  · exact certificateK2_alpha
  · simpa [certificateK2] using certificateK2_weights

theorem four_thirds_le_criticalLambda :
    (4 / 3 : ℝ) ≤ criticalLambda 2 := by
  apply le_criticalLambda_of_feasible
  · constructor <;> norm_num
  · exact levelFeasible_four_thirds

end FiniteRecord

end CleanLean.KL
