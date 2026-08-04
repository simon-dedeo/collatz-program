/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineBinaryCounterNoGo
import KontoroC.ValuationWord
import Mathlib.Tactic.Ring

/-!
# A literal counter/fuel boost cell

This semantic companion is intentionally separate from the small algebra-only
`AffineBinaryCounterNoGo` module.  Import this file only when the literal
accelerated-Collatz replay is needed.
-/

namespace KontoroC
namespace AffineBinaryCounterNoGo

/-- A two-coordinate affine encoding. -/
def CounterFuelEncoding (A B : ℤ) (counter fuel offset : ℤ) : ℤ :=
  A * counter + B * fuel + offset

/-- Exact counter/fuel decrement algebra.  The second coordinate absorbs the
scale mismatch, but another round requires a fresh source fuel cylinder. -/
theorem counterFuel_decrement_balance
    (S O : ℕ) (counter u offset gamma : ℤ) :
    let A : ℤ := (2 : ℤ) ^ S
    let C : ℤ := (3 : ℤ) ^ O
    let B : ℤ := C - A
    let delta : ℤ := B * (A * gamma - offset) - A ^ 2
    ResetBalance S O delta
      (CounterFuelEncoding A B counter (A * u) offset)
      (CounterFuelEncoding A B (counter - 1)
        (counter + C * u + gamma) offset) := by
  dsimp [ResetBalance, CounterFuelEncoding]
  ring

def concreteSource (counter fuel : ℕ) : ℕ :=
  16 * counter + 176 * fuel + 7

def concreteAfterOne (counter fuel : ℕ) : ℕ :=
  24 * counter + 264 * fuel + 11

def concreteAfterTwo (counter fuel : ℕ) : ℕ :=
  36 * counter + 396 * fuel + 17

def concreteEndpoint (counter fuel : ℕ) : ℕ :=
  27 * counter + 297 * fuel + 13

/-- One linked cell literally executes `[1,1,2]`, decreases the counter, and
lands in the same source chart. -/
theorem concrete_counterFuel_cell (counter fuel nextFuel : ℕ)
    (hcounter : 0 < counter)
    (hlink : 16 * nextFuel = counter + 27 * fuel + 2) :
    WordLegal (concreteSource counter fuel) [1, 1, 2] ∧
      runWord (concreteSource counter fuel) [1, 1, 2] =
        concreteSource (counter - 1) nextFuel := by
  have hsourcePos : 0 < concreteSource counter fuel := by
    simp [concreteSource]
  have hsourceOdd : concreteSource counter fuel % 2 = 1 := by
    simp only [concreteSource]
    omega
  have hfirstOdd : concreteAfterOne counter fuel % 2 = 1 := by
    simp only [concreteAfterOne]
    omega
  have hsecondOdd : concreteAfterTwo counter fuel % 2 = 1 := by
    simp only [concreteAfterTwo]
    omega
  have hendEq : concreteEndpoint counter fuel =
      concreteSource (counter - 1) nextFuel := by
    simp only [concreteEndpoint, concreteSource]
    omega
  have hendOdd : concreteEndpoint counter fuel % 2 = 1 := by
    rw [hendEq]
    simp only [concreteSource]
    omega
  have hstep1 : LegalInstruction (concreteSource counter fuel) 1 ∧
      oddStep (concreteSource counter fuel) = concreteAfterOne counter fuel := by
    apply legalInstruction_of_step_equation hsourcePos hsourceOdd hfirstOdd
    simp [concreteSource, concreteAfterOne]
    ring
  have hstep2 : LegalInstruction (concreteAfterOne counter fuel) 1 ∧
      oddStep (concreteAfterOne counter fuel) = concreteAfterTwo counter fuel := by
    apply legalInstruction_of_step_equation (by simp [concreteAfterOne])
      hfirstOdd hsecondOdd
    simp [concreteAfterOne, concreteAfterTwo]
    ring
  have hstep3 : LegalInstruction (concreteAfterTwo counter fuel) 2 ∧
      oddStep (concreteAfterTwo counter fuel) = concreteEndpoint counter fuel := by
    apply legalInstruction_of_step_equation (by simp [concreteAfterTwo])
      hsecondOdd hendOdd
    simp [concreteAfterTwo, concreteEndpoint]
    ring
  constructor
  · simp only [WordLegal]
    exact ⟨hstep1.1, hstep1.2 ▸ hstep2.1,
      hstep1.2 ▸ hstep2.2 ▸ hstep3.1, trivial⟩
  · simp only [runWord]
    rw [hstep1.2, hstep2.2, hstep3.2, hendEq]

/-- Every concrete cell is a strict boost. -/
theorem concrete_counterFuel_outward (counter fuel : ℕ) :
    concreteSource counter fuel < concreteEndpoint counter fuel := by
  simp only [concreteSource, concreteEndpoint]
  omega

end AffineBinaryCounterNoGo
end KontoroC
