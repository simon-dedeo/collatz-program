/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardOrdinaryRootDichotomy

/-!
# Direct bridge from a literal recharge orbit to first-passage infinity

Construction workers naturally describe a candidate dispatcher by an
explicit sequence of positive boundary charges and a word list realizing
each successor step.  The invariant bridge is more general, but making every
worker reconstruct the range predicate obscures a small semantic seam.

This file supplies the direct adapter.  A sequence whose every successor is
connected by a `RechargeMacro` is strictly increasing, escapes at least
linearly in macro time, executes arbitrarily many literal first-passage
blocks, and reaches the existing conditional Syracuse and Collatz endpoints.
Variable positive macro lengths are handled by `OutwardInvariantBridge`.

Everything remains conditional: no such orbit is constructed here.
-/

namespace KontoroC
namespace OutwardLiteralMacroOrbit

open OutwardCodeCompactness OutwardInvariantBridge OutwardOddSlice
  OutwardCodeCounterexample
open CleanLean.Collatz

/-- The boundary charge of a literal recharge-macro orbit strictly increases
at every macro step. -/
theorem orbit_strictMono
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    StrictMono charge :=
  strictMono_nat_of_lt_succ fun n ↦ (hmacro n).lt

/-- Quantitative escape: after `n` macros the charge has risen by at least
`n`.  Individual macros may contain several first-passage blocks and may
increase it by much more. -/
theorem orbit_linear_escape
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (n : ℕ) :
    charge 0 + n ≤ charge n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : charge n < charge (n + 1) := (hmacro n).lt
      omega

/-- Hence the charge sequence of a literal macro orbit is unbounded. -/
theorem orbit_unbounded
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    ∀ bound, ∃ n, bound < charge n := by
  intro bound
  refine ⟨bound + 1, ?_⟩
  have hlarge := orbit_linear_escape charge words hmacro (bound + 1)
  omega

/-- An explicit literal recharge orbit is the range-closed invariant needed
by the general bridge, and therefore supplies infinite first-passage
execution from its ordinary initial boundary. -/
theorem orbit_gives_infiniteExecution
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    InfiniteExecution FirstPassageCode (3 * charge 0 - 1) := by
  let I : ℕ → Prop := fun H ↦ ∃ n, charge n = H
  apply invariant_gives_infiniteExecution I (charge 0)
  · exact (hmacro 0).source_pos
  · exact ⟨0, rfl⟩
  · intro H hH
    obtain ⟨n, rfl⟩ := hH
    exact ⟨charge (n + 1), words n, hmacro n, ⟨n + 1, rfl⟩⟩

/-- Direct Syracuse endpoint for a literal recharge orbit. -/
theorem orbit_gives_not_syracuseReachesOne
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    ¬ SyracuseReachesOne (3 * charge 0 - 1) := by
  exact not_syracuseReachesOne_of_infiniteExecution
    (fun _ hw ↦ hw.1)
    (orbit_gives_infiniteExecution charge words hmacro)

/-- Direct standard unaccelerated Collatz endpoint for a literal recharge
orbit. -/
theorem orbit_gives_not_collatz
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    ¬ CleanLean.Collatz.Conjecture := by
  exact not_conjecture_of_infiniteExecution
    (fun _ hw ↦ hw.1)
    (orbit_gives_infiniteExecution charge words hmacro)

end OutwardLiteralMacroOrbit
end KontoroC
