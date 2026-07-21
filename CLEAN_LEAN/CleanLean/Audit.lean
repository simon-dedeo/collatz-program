/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Relational
import CleanLean.Collatz.Syracuse
import CleanLean.KL.FiniteSystem
import CleanLean.KL.WeightedTail

/-!
# Trust-boundary audit

These commands make Lean report the axioms used by the principal proved
specification theorems during a build.
-/

#print axioms CleanLean.Collatz.conjecture_iff_relational
#print axioms CleanLean.Collatz.conjecture_iff_syracuse
#print axioms CleanLean.Collatz.conjecture_of_descent
#print axioms CleanLean.KL.FiniteSystem.operator_mono
#print axioms CleanLean.KL.weightedDefect_le_tail
