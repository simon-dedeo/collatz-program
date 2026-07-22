/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.Glider

/-!
# A glider tail is enough

Search constructions often have a finite irregular prefix before an exact
strictly outward regime begins.  The Collatz counterexample only needs the
tail; this module packages the index shift once and for all.
-/

namespace KontoroC

structure EventualMacroGlider where
  state : ℕ → ℕ
  word : ℕ → List ℕ
  tailStart : ℕ
  start_large : 4 < state tailStart
  word_nonempty : ∀ t, tailStart ≤ t → word t ≠ []
  legal : ∀ t, tailStart ≤ t → WordLegal (state t) (word t)
  transition : ∀ t, tailStart ≤ t →
    runWord (state t) (word t) = state (t + 1)
  grows : ∀ t, tailStart ≤ t → state t < state (t + 1)

namespace EventualMacroGlider

/-- Shift the exact outward tail to time zero. -/
def toMacroGlider (g : EventualMacroGlider) : MacroGlider where
  state := fun t => g.state (g.tailStart + t)
  word := fun t => g.word (g.tailStart + t)
  start_large := by simpa using g.start_large
  word_nonempty := fun t => g.word_nonempty _ (Nat.le_add_right _ _)
  legal := fun t => g.legal _ (Nat.le_add_right _ _)
  transition := fun t => by
    have h := g.transition (g.tailStart + t) (Nat.le_add_right _ _)
    simpa [Nat.add_assoc] using h
  grows := fun t => by
    have h := g.grows (g.tailStart + t) (Nat.le_add_right _ _)
    simpa [Nat.add_assoc] using h

/-- End-to-end soundness: an exact outward tail disproves the standard
positive Collatz conjecture, regardless of its finite prefix. -/
theorem not_conjecture (g : EventualMacroGlider) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end EventualMacroGlider

end KontoroC
