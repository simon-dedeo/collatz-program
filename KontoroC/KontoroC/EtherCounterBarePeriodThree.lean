/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterBareGlue
import KontoroC.EtherCounterPeriodThree

/-!
# Bare affine period-three schedules

This file upgrades the zero-carry construction endpoint from a generic EC17
orbit to the literal period-three `Ray` used by the surrounding theory.
-/

namespace KontoroC
namespace EtherCounterBarePeriodThree

open EtherCounterBareGlue EtherCounterStateNoRepeat

/-- An affine three-phase branch schedule, without any assumed core orbit. -/
structure Schedule where
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  cycleGain : ℕ
  cycleGain_pos : 0 < cycleGain
  branch_zero : ∀ q, branch (3 * q) = branch 0 + cycleGain * q
  branch_one : ∀ q, branch (3 * q + 1) = branch 1 + cycleGain * q
  branch_two : ∀ q, branch (3 * q + 2) = branch 2 + cycleGain * q

namespace Schedule

/-- Restrict an affine schedule to the tail beginning at cycle `Q0`. -/
def tail (S : Schedule) (Q0 : ℕ) : Schedule where
  branch t := S.branch (3 * Q0 + t)
  branch_pos t := S.branch_pos _
  cycleGain := S.cycleGain
  cycleGain_pos := S.cycleGain_pos
  branch_zero q := by
    rw [show 3 * Q0 + 3 * q = 3 * (Q0 + q) by ring,
      S.branch_zero]
    change S.branch 0 + S.cycleGain * (Q0 + q) =
      S.branch (3 * Q0) + S.cycleGain * q
    rw [S.branch_zero]
    ring
  branch_one q := by
    rw [show 3 * Q0 + (3 * q + 1) = 3 * (Q0 + q) + 1 by ring,
      S.branch_one]
    change S.branch 1 + S.cycleGain * (Q0 + q) =
      S.branch (3 * Q0 + 1) + S.cycleGain * q
    rw [S.branch_one]
    ring
  branch_two q := by
    rw [show 3 * Q0 + (3 * q + 2) = 3 * (Q0 + q) + 2 by ring,
      S.branch_two]
    change S.branch 2 + S.cycleGain * (Q0 + q) =
      S.branch (3 * Q0 + 2) + S.cycleGain * q
    rw [S.branch_two]
    ring

theorem tail_branch (S : Schedule) (Q0 t : ℕ) :
    (S.tail Q0).branch t = S.branch (3 * Q0 + t) := rfl

/-- An EC17 orbit on this bare schedule is exactly a period-three ray. -/
def toRay (S : Schedule) (g : EtherCounterStateNoRepeat.Orbit)
    (hbranch : g.branch = S.branch) : EtherCounterPeriodThree.Ray where
  toOrbit := g
  cycleGain := S.cycleGain
  cycleGain_pos := S.cycleGain_pos
  branch_zero q := by rw [hbranch]; exact S.branch_zero q
  branch_one q := by rw [hbranch]; exact S.branch_one q
  branch_two q := by rw [hbranch]; exact S.branch_two q

theorem toRay_core (S : Schedule) (g : EtherCounterStateNoRepeat.Orbit)
    (hbranch : g.branch = S.branch) (t : ℕ) :
    (S.toRay g hbranch).core t = g.core t := rfl

/-- End-to-end construction theorem in the project's strongest semantic
type: an eventual exact-zero carry tail on a positive affine three-phase
schedule constructs a literal period-three `Ray` tail. -/
theorem exists_tailRay_of_eventualZeroCarryChain
    (S : Schedule) (boundary image : ℕ → ℕ) (Q0 : ℕ)
    (hboundary : ∀ q, 0 < boundary q)
    (haffine : ∀ q ≥ Q0,
      2 ^ threeStepBinaryMass S.branch (3 * q) * image q =
        3 ^ threeStepTernaryMass S.branch (3 * q) * boundary q +
          threeStepDefect (S.branch (3 * q)) (S.branch (3 * q + 1))
            (S.branch (3 * q + 2)))
    (hzero : ∀ q ≥ Q0, boundary (q + 1) = image q) :
    ∃ g : EtherCounterPeriodThree.Ray,
      g.cycleGain = S.cycleGain ∧
        (∀ t, g.branch t = S.branch (3 * Q0 + t)) ∧
          ∀ q, g.core (3 * q) = boundary (Q0 + q) := by
  obtain ⟨orbit, hbranch, hcore⟩ :=
    exists_tailOrbit_of_eventualZeroCarryChain S.branch boundary image Q0
      S.branch_pos hboundary haffine hzero
  have hbranchEq : orbit.branch = (S.tail Q0).branch := by
    funext t
    exact hbranch t
  let ray := (S.tail Q0).toRay orbit hbranchEq
  refine ⟨ray, rfl, ?_, ?_⟩
  · intro t
    exact hbranch t
  · intro q
    exact hcore q

end Schedule

end EtherCounterBarePeriodThree
end KontoroC
