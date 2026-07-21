/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CountingTransfer
import CleanLean.KL.FiniteRecordK12Chunks

/-!
# The exact level-12 KL record

The generated block theorems check all 177,147 scaled coordinates using
kernel reduction.  This file sends the assembled exact certificate through
the irrational-weight soundness theorem and the concrete KL counting bridge.
-/

namespace CleanLean.KL

namespace FiniteRecordK12

theorem certificate_rows : certificate.check = true := by
  exact (certificate.check_eq_true_iff).2
    (certificate_valid_of_allChunks allChunksValid)

set_option maxHeartbeats 0 in
-- Exact reduction compares the two large rational powers defining `alpha`.
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem certificate_alpha : checkAlphaLower 50508 31867 = true := by
  decide

set_option maxHeartbeats 0 in
-- Exact reduction checks both irrational branch-weight lower bounds.
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem certificate_weights :
    checkBranchWeightLowerData
      18064231 10000000
      782366571504816 1413285047434102 1000000000000000
      50508 31867 = true := by
  decide

/-- The exact level-12 KL system is feasible at the certified rational
parameter. -/
theorem levelFeasible :
    LevelFeasible 12 (18064231 / 10000000 : ℝ) := by
  apply levelFeasible_of_scaledCertificate
    12 50508 31867 certificate
  · exact certificate_rows
  · norm_num
  · norm_num [certificate]
  · exact certificate_alpha
  · simpa [certificate] using certificate_weights

/-- Unconditional predecessor-counting exponent obtained from the exact
level-12 certificate. -/
theorem hasPredecessorExponent_record
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    HasPredecessorExponent a
      (klExponent (18064231 / 10000000 : ℝ)) := by
  exact hasPredecessorExponent_of_levelFeasible (k := 12)
    (by norm_num) (by norm_num) (by norm_num) levelFeasible ha ha3

end FiniteRecordK12

end CleanLean.KL
