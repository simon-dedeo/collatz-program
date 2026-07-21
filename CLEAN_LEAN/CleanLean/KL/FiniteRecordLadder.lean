/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.StrictLift
import CleanLean.KL.FiniteRecordK12

/-!
# An unconditional infinite strict feasibility ladder

The exact level-12 certificate and the qualitative adjacent strict-lift theorem
combine to produce a strictly increasing exact feasible parameter at every
later level.  The choices made through continuity are noncomputable, and no
uniform increment is asserted.  In particular, this theorem does not say that
the ladder tends to two.
-/

namespace CleanLean.KL

/-- Starting from the exact level-12 record, there is an infinite strictly
increasing ladder of exact KL-feasible parameters below two. -/
theorem exists_strict_feasible_ladder_from_k12 :
    ∃ lam : ℕ → ℝ,
      lam 0 = (18064231 / 10000000 : ℝ) ∧
      (∀ n, LevelFeasible (12 + n) (lam n)) ∧
      (∀ n, lam n < lam (n + 1)) ∧
      ∀ n, lam n < 2 := by
  exact ResidueSystem.exists_strict_feasible_ladder
    12 (by norm_num) (18064231 / 10000000 : ℝ)
      (by norm_num) (by norm_num) FiniteRecordK12.levelFeasible

/-- Every finite number of strict adjacent improvements exists above the
level-12 record. -/
theorem exists_later_feasible_gt_k12 (n : ℕ) (hn : 0 < n) :
    ∃ lam : ℝ,
      (18064231 / 10000000 : ℝ) < lam ∧
      lam < 2 ∧ LevelFeasible (12 + n) lam := by
  obtain ⟨seq, hzero, hfeas, hmono, htwo⟩ :=
    exists_strict_feasible_ladder_from_k12
  refine ⟨seq n, ?_, htwo n, hfeas n⟩
  rw [← hzero]
  exact (strictMono_nat_of_lt_succ hmono) hn

/-- Non-numerical but unconditional strict improvement of the level-12
predecessor exponent.  The theorem asserts existence of a larger real
exponent; it does not provide a decimal certificate for that exponent. -/
theorem exists_predecessorExponent_gt_k12
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ gamma : ℝ,
      klExponent (18064231 / 10000000 : ℝ) < gamma ∧
      HasPredecessorExponent a gamma := by
  obtain ⟨lam, hlam, hlam2, hfeas⟩ :=
    exists_later_feasible_gt_k12 1 (by norm_num)
  refine ⟨klExponent lam, ?_, ?_⟩
  · unfold klExponent
    exact (Real.strictMonoOn_logb (b := (2 : ℝ)) (by norm_num))
      (by norm_num) (lt_trans (by norm_num) hlam) hlam
  · exact hasPredecessorExponent_of_levelFeasible
      (k := 13) (by norm_num) (lt_trans (by norm_num) hlam) hlam2.le
        (by simpa using hfeas) ha ha3

end CleanLean.KL
