/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PublicPayloadTheta
import KontoroC.EtherCounterGeometricMahler

/-!
# The two-place pressure gate for public-payload schedules

This file isolates the natural-number kernel of QM151c--e.  The analytic
work needed to produce a gate from a rational lattice hit is deliberately
kept separate: once the two inequalities in `NaturalPressureGate` are
available, everything below is exact arithmetic.
-/

namespace KontoroC
namespace SelfWritingKL
namespace PublicPressure

/-- Common ternary denominator exponent after `N` public branches. -/
def denominatorExponent (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  11 * N + 6 * publicBranchSum m N

/-- Dyadic exponent in the product of the first `N` public multipliers. -/
def valuationExponent (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  15 * N + 8 * publicBranchSum m N

/-- The amount by which the next dyadic exponent clears the universal
`65/41` ternary budget.  Grouped subtraction is intentional: writing a
chain of natural subtractions would express a different statement. -/
def freshExcess (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  41 * valuationExponent m (N + 1) -
    65 * denominatorExponent m N

/-- The exact natural-valued gate obtained from the first omitted term.
`A` is the numerator of the finite real partial sum over the common
denominator `3^D`. -/
def NaturalPressureGate (K D V A : ℕ) : Prop :=
  2 ^ V ≤ K * 3 ^ D + A ∧
    K * 3 ^ D + A < (K + 1) * 3 ^ D

theorem separator_power (D : ℕ) :
    3 ^ (41 * D) ≤ 2 ^ (65 * D) := by
  have hbase : 3 ^ 41 ≤ 2 ^ 65 :=
    (EtherCounterAperiodic.TernaryCoreOrbit.three_pow_41_lt_two_pow_65).le
  have hpow := Nat.pow_le_pow_left hbase D
  rw [pow_mul, pow_mul]
  exact hpow

/-- QM151d, in its reusable kernel form. -/
theorem powered_pressure_gate
    {K D V A : ℕ} (hgate : NaturalPressureGate K D V A) :
    2 ^ (41 * V) < (K + 1) ^ 41 * 2 ^ (65 * D) := by
  have hp : (2 ^ V) ^ 41 < ((K + 1) * 3 ^ D) ^ 41 :=
    Nat.pow_lt_pow_left (lt_of_le_of_lt hgate.1 hgate.2) (by norm_num)
  rw [mul_pow] at hp
  have hpExp : 2 ^ (41 * V) < (K + 1) ^ 41 * 3 ^ (41 * D) := by
    rw [Nat.mul_comm 41 V, pow_mul, Nat.mul_comm 41 D, pow_mul]
    exact hp
  have hsep := separator_power D
  exact hpExp.trans_le (Nat.mul_le_mul_left ((K + 1) ^ 41) hsep)

/-- Cancellation form of QM151e.  It avoids all schedule-specific algebra
and is the useful endpoint for future growth sieves. -/
theorem fresh_excess_power_lt
    {K D V A : ℕ} (hgate : NaturalPressureGate K D V A)
    (hbudget : 65 * D ≤ 41 * V) :
    2 ^ (41 * V - 65 * D) < (K + 1) ^ 41 := by
  have hp := powered_pressure_gate hgate
  have hsplit : 65 * D + (41 * V - 65 * D) = 41 * V :=
    Nat.add_sub_of_le hbudget
  rw [← hsplit, pow_add, mul_comm ((K + 1) ^ 41) (2 ^ (65 * D))] at hp
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ (65 * D))).mp hp

theorem freshExcess_formula (m : ℕ → ℕ) (N : ℕ) :
    freshExcess m N =
      328 * m N + 615 - (62 * publicBranchSum m N + 100 * N) := by
  unfold freshExcess valuationExponent denominatorExponent
  rw [publicBranchSum_succ]
  omega

/-- Schedule-specialized pressure conclusion. -/
theorem schedule_fresh_excess_power_lt
    {m : ℕ → ℕ} {K A N : ℕ}
    (hgate : NaturalPressureGate K (denominatorExponent m N)
      (valuationExponent m (N + 1)) A)
    (hbudget : 65 * denominatorExponent m N ≤
      41 * valuationExponent m (N + 1)) :
    2 ^ freshExcess m N < (K + 1) ^ 41 := by
  exact fresh_excess_power_lt hgate hbudget

/-- A single over-budget branch already rules out a pressure gate for the
fixed ordinary endpoint `K`. -/
theorem no_gate_of_excess_power_ge
    {m : ℕ → ℕ} {K A N : ℕ}
    (hbudget : 65 * denominatorExponent m N ≤
      41 * valuationExponent m (N + 1))
    (hexcess : (K + 1) ^ 41 ≤ 2 ^ freshExcess m N) :
    ¬ NaturalPressureGate K (denominatorExponent m N)
      (valuationExponent m (N + 1)) A := by
  intro hgate
  exact (not_lt_of_ge hexcess)
    (schedule_fresh_excess_power_lt hgate hbudget)

end PublicPressure
end SelfWritingKL
end KontoroC
