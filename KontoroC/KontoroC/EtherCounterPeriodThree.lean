/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterStateNoRepeat

/-!
# Literal period-three EC17 composition

This file derives the three phase defect in one cycle directly from the
natural EC17 balance.  No theta-value theorem or function-field surrogate is
used.  The result is the exact arithmetic identity QM65.
-/

namespace KontoroC
namespace EtherCounterPeriodThree

open EtherCounterStateNoRepeat

/-- A positive EC17 orbit whose branch schedule has three affine phases and
positive cycle gain. -/
structure Ray extends EtherCounterStateNoRepeat.Orbit where
  cycleGain : ℕ
  cycleGain_pos : 0 < cycleGain
  branch_zero : ∀ q, branch (3 * q) = branch 0 + cycleGain * q
  branch_one : ∀ q, branch (3 * q + 1) = branch 1 + cycleGain * q
  branch_two : ∀ q, branch (3 * q + 2) = branch 2 + cycleGain * q

namespace Ray

def binaryScale (g : Ray) : ℕ := 2 ^ (8 * g.cycleGain)
def ternaryScale (g : Ray) : ℕ := 3 ^ (6 * g.cycleGain)

def binaryPhase0 (g : Ray) : ℕ := 2 ^ (8 * g.branch 1 + 15)
def binaryPhase1 (g : Ray) : ℕ := 2 ^ (8 * g.branch 2 + 15)
/-- The third binary phase reads the next cycle's phase-zero branch. -/
def binaryPhase2 (g : Ray) : ℕ :=
  2 ^ (8 * (g.branch 0 + g.cycleGain) + 15)

def ternaryPhase0 (g : Ray) : ℕ := 3 ^ (6 * g.branch 0 + 11)
def ternaryPhase1 (g : Ray) : ℕ := 3 ^ (6 * g.branch 1 + 11)
def ternaryPhase2 (g : Ray) : ℕ := 3 ^ (6 * g.branch 2 + 11)

/-- The literal balance rewritten through the public factor definitions. -/
theorem factor_balance (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.binaryFactor t * g.core (t + 1) =
      g.ternaryFactor t * g.core t + 17 := by
  simpa [EtherCounterStateNoRepeat.Orbit.binaryFactor,
    EtherCounterStateNoRepeat.Orbit.ternaryFactor] using g.balance t

/-- Three literal EC17 steps composed before imposing any periodic law. -/
theorem compose_three (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.binaryFactor t * g.binaryFactor (t + 1) * g.binaryFactor (t + 2) *
        g.core (t + 3) =
      g.ternaryFactor t * g.ternaryFactor (t + 1) *
          g.ternaryFactor (t + 2) * g.core t +
        17 * (g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by
  have h0 := factor_balance g t
  have h1 : g.binaryFactor (t + 1) * g.core (t + 2) =
      g.ternaryFactor (t + 1) * g.core (t + 1) + 17 := by
    simpa only [show t + 1 + 1 = t + 2 by omega] using factor_balance g (t + 1)
  have h2 : g.binaryFactor (t + 2) * g.core (t + 3) =
      g.ternaryFactor (t + 2) * g.core (t + 2) + 17 := by
    simpa only [show t + 2 + 1 = t + 3 by omega] using factor_balance g (t + 2)
  calc
    g.binaryFactor t * g.binaryFactor (t + 1) * g.binaryFactor (t + 2) *
          g.core (t + 3) =
        g.binaryFactor t * g.binaryFactor (t + 1) *
          (g.ternaryFactor (t + 2) * g.core (t + 2) + 17) := by
      rw [← h2]
      ring
    _ = g.binaryFactor t * g.ternaryFactor (t + 2) *
          (g.binaryFactor (t + 1) * g.core (t + 2)) +
        17 * (g.binaryFactor t * g.binaryFactor (t + 1)) := by ring
    _ = g.binaryFactor t * g.ternaryFactor (t + 2) *
          (g.ternaryFactor (t + 1) * g.core (t + 1) + 17) +
        17 * (g.binaryFactor t * g.binaryFactor (t + 1)) := by
      rw [h1]
    _ = g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) *
          (g.binaryFactor t * g.core (t + 1)) +
        17 * (g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by ring
    _ = g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) *
          (g.ternaryFactor t * g.core t + 17) +
        17 * (g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by
      rw [h0]
    _ = _ := by ring

theorem binaryFactor_zero (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q) = g.binaryPhase0 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 1 = 3 * q + 1 by rfl, g.branch_one q]
  rw [show 8 * (g.branch 1 + g.cycleGain * q) + 15 =
      (8 * g.branch 1 + 15) + (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem binaryFactor_one (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q + 1) =
      g.binaryPhase1 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 1 + 1 = 3 * q + 2 by omega, g.branch_two q]
  rw [show 8 * (g.branch 2 + g.cycleGain * q) + 15 =
      (8 * g.branch 2 + 15) + (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem binaryFactor_two (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q + 2) =
      g.binaryPhase2 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 2 + 1 = 3 * (q + 1) by ring, g.branch_zero (q + 1)]
  rw [show 8 * (g.branch 0 + g.cycleGain * (q + 1)) + 15 =
      (8 * (g.branch 0 + g.cycleGain) + 15) +
        (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_zero (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q) =
      g.ternaryPhase0 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_zero q]
  rw [show 6 * (g.branch 0 + g.cycleGain * q) + 11 =
      (6 * g.branch 0 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_one (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q + 1) =
      g.ternaryPhase1 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_one q]
  rw [show 6 * (g.branch 1 + g.cycleGain * q) + 11 =
      (6 * g.branch 1 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_two (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q + 2) =
      g.ternaryPhase2 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_two q]
  rw [show 6 * (g.branch 2 + g.cycleGain * q) + 11 =
      (6 * g.branch 2 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

/-- QM65: the exact three-phase composition.  The three defect monomials
are `Y^(2q)`, `(XY)^q`, and `X^(2q)` respectively. -/
theorem cycle_balance (g : Ray) (q : ℕ) :
    (g.binaryPhase0 * g.binaryPhase1 * g.binaryPhase2) *
        g.binaryScale ^ (3 * q) * g.core (3 * q + 3) =
      (g.ternaryPhase0 * g.ternaryPhase1 * g.ternaryPhase2) *
          g.ternaryScale ^ (3 * q) * g.core (3 * q) +
        17 * (g.ternaryPhase1 * g.ternaryPhase2 *
            g.ternaryScale ^ (2 * q) +
          g.binaryPhase0 * g.ternaryPhase2 *
            (g.binaryScale * g.ternaryScale) ^ q +
          g.binaryPhase0 * g.binaryPhase1 *
            g.binaryScale ^ (2 * q)) := by
  have h := compose_three g.toOrbit (3 * q)
  rw [g.binaryFactor_zero q, g.binaryFactor_one q, g.binaryFactor_two q,
    g.ternaryFactor_zero q, g.ternaryFactor_one q, g.ternaryFactor_two q] at h
  have hX3 : g.binaryScale ^ (3 * q) = (g.binaryScale ^ q) ^ 3 := by
    rw [show 3 * q = q * 3 by omega, pow_mul]
  have hY3 : g.ternaryScale ^ (3 * q) = (g.ternaryScale ^ q) ^ 3 := by
    rw [show 3 * q = q * 3 by omega, pow_mul]
  have hX2 : g.binaryScale ^ (2 * q) = (g.binaryScale ^ q) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul]
  have hY2 : g.ternaryScale ^ (2 * q) = (g.ternaryScale ^ q) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul]
  rw [hX3, hY3, hX2, hY2, mul_pow]
  convert h using 1 <;> ring

end Ray
end EtherCounterPeriodThree
end KontoroC
