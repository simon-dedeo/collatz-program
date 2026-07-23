/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterAperiodic
import KontoroC.EtherCounterStateNoRepeat

/-!
# The self-writing KL/EC17 coordinate

This file packages the exact one-coordinate recurrence found in the returning
ether-glider audit.  An `Orbit` is still a hypothesis: the definitions do not
assert that an infinite accepted execution, an ordinary initial address, or a
Collatz counterexample exists.

The useful conclusions are semantic.  Every supplied self-writing orbit is
an exact positive EC17 orbit, its public payload grows strictly, and its
branch schedule cannot be eventually periodic.
-/

namespace KontoroC
namespace SelfWritingKL

def Z (q : ℕ) : ℕ := 494251421 + 495976448 * q
def W (q : ℕ) : ℕ := 83499104 + 83790531 * q

/-- SW1, including both the constant and slope identities. -/
theorem determinant_identity (q : ℕ) :
    3 ^ 11 * Z q + 17 = 2 ^ 20 * W q := by
  simp [Z, W]
  ring

/-- A hypothetical infinite execution of the deterministic self-writing
coordinate.  `z_factor` records the current ternary branch and `w_factor`
records the next binary branch.  Requiring the next `z_factor` is exactly the
fixed return cylinder; it is not inferred from a finite computation. -/
structure Orbit where
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  payload : ℕ → ℕ
  z_factor : ∀ t,
    Z (payload t) = 3 ^ (6 * branch t) * core t
  w_factor : ∀ t,
    W (payload t) = 2 ^ (8 * branch (t + 1) - 5) * core (t + 1)

namespace Orbit

/-- SW1 turns every accepted self-writing step into the literal EC17
balance. -/
theorem balance (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
      3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
  have hnext := o.branch_pos (t + 1)
  calc
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
        2 ^ 20 *
          (2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1)) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ = 2 ^ 20 * W (o.payload t) := by rw [o.w_factor]
    _ = 3 ^ 11 * Z (o.payload t) + 17 :=
      (determinant_identity (o.payload t)).symm
    _ = 3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
      rw [o.z_factor, ← mul_assoc, ← pow_add]
      congr 3
      omega

/-- Forgetting the packet coordinate gives precisely the universal positive
EC17 orbit used by the existing obstruction library. -/
def toEC17 (o : Orbit) : EtherCounterStateNoRepeat.Orbit where
  branch := o.branch
  branch_pos := o.branch_pos
  core := o.core
  core_pos := o.core_pos
  balance := o.balance

/-- In zero-based indexing the same object is the exact ternary-core orbit
of the autonomous ether-counter development. -/
def toTernaryCore (o : Orbit) : EtherCounterAperiodic.TernaryCoreOrbit where
  level t := o.branch t - 1
  core := o.core
  core_pos := o.core_pos
  balance t := by
    have ht := o.branch_pos t
    have ht1 := o.branch_pos (t + 1)
    rw [show 8 * (o.branch (t + 1) - 1) + 23 =
        8 * o.branch (t + 1) + 15 by omega,
      show 6 * (o.branch t - 1) + 17 =
        6 * o.branch t + 11 by omega]
    exact o.balance t

/-- Reinsert the forced factor `3` and the dyadic public register.  This is
the converse normalization needed to reuse the audited periodic-schedule
obstruction. -/
def ternaryCoreToNormalized (o : EtherCounterAperiodic.TernaryCoreOrbit) :
    EtherCounterAperiodic.NormalizedOrbit where
  level := o.level
  value := fun t => 2 ^ (8 * o.level t + 3) * (3 * o.core t)
  oddPart := fun t => 3 * o.core t
  value_pos t := Nat.mul_pos (pow_pos (by omega) _)
    (Nat.mul_pos (by omega) (o.core_pos t))
  factor t := rfl
  transition t := by
    calc
      2 ^ 20 *
          (2 ^ (8 * o.level (t + 1) + 3) * (3 * o.core (t + 1))) =
          3 * (2 ^ (8 * o.level (t + 1) + 23) * o.core (t + 1)) := by
        rw [show 8 * o.level (t + 1) + 23 =
          20 + (8 * o.level (t + 1) + 3) by omega, pow_add]
        ring
      _ = 3 * (3 ^ (6 * o.level t + 17) * o.core t + 17) := by
        rw [o.balance]
      _ = 3 ^ (6 * o.level t + 17) * (3 * o.core t) + 51 := by ring

def toNormalized (o : Orbit) : EtherCounterAperiodic.NormalizedOrbit :=
  ternaryCoreToNormalized o.toTernaryCore

/-- Every accepted step is outward in the public self-writing coordinate.
This is a theorem about a supplied exact orbit, not evidence that one exists. -/
theorem payload_strictMono (o : Orbit) : StrictMono o.payload := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hfirst :
      3 ^ 11 * Z (o.payload t) <
        2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
    calc
      3 ^ 11 * Z (o.payload t) =
          3 ^ (6 * o.branch t + 11) * o.core t := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
      _ < 2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
        rw [o.balance]
        omega
  have hsecond :
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
        3 ^ 11 * Z (o.payload (t + 1)) := by
    calc
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
          3 ^ (6 * o.branch (t + 1) + 11) * o.core (t + 1) :=
        Nat.mul_lt_mul_of_pos_right
          (EtherCounterStateNoRepeat.Orbit.binary_lt_ternary_at_branch
            (o.branch (t + 1))) (o.core_pos (t + 1))
      _ = 3 ^ 11 * Z (o.payload (t + 1)) := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
  have hz : Z (o.payload t) < Z (o.payload (t + 1)) := by
    apply (Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ 11)).mp
    exact hfirst.trans hsecond
  simp [Z] at hz
  omega

/-- The self-writing map does not rescue a finite or ultimately periodic
branch dispatcher.  Any infinite accepted execution must use a genuinely
aperiodic schedule. -/
theorem branch_not_eventually_periodic (o : Orbit) (K p : ℕ) (hp : 0 < p) :
    ¬ EtherCounterAperiodic.EventuallyPeriodicFrom o.branch K p := by
  intro hperiodic
  apply o.toNormalized.branch_not_eventually_periodic K p hp
  intro k
  simpa [toNormalized, ternaryCoreToNormalized, toTernaryCore] using
    congrArg (fun n => n - 1) (hperiodic k)

end Orbit
end SelfWritingKL
end KontoroC
