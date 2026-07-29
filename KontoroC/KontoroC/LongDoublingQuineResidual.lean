/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongDoublingQuineRationalNoGo
import Mathlib.NumberTheory.PowModTotient

/-!
# The hidden residual register of a long doubling return

The forced low dyadic block is not merely an obstruction.  Extract it as a
new integer register

`A F(g) = b0 + 2^(77+P(g)) U(g)`.

For a long return with `k` high-opcode transitions, the exact macro equation
then becomes another affine integer return on `U`.  At the first affordable
length `k=6`, its real slope is the small positive surplus

`102 log₂ 3 - 161 = 0.666...`,

rather than the original large scales.  This is the correct coordinate in
which to seek a self-writing carry mechanism.

There is a second useful hack.  The condition that `F` recovered from `U` is
an integer is a congruence modulo the *fixed* number `A=3^114`.  If the base
opcode freezes the phase of `2^(23g)` modulo `A`, opcode doubling preserves
that phase forever.  Thus the integrality gate for every residual register on
the ray is one stationary ternary residue class, not a changing family.

This module proves both facts exactly.  It constructs no orbit.
-/

namespace KontoroC
namespace LongDoublingQuineResidual

open LongDoublingQuineThreshold

def L (g : ℕ) : ℕ := 77 + P g
def E (j g : ℕ) : ℕ := 77 + j * P g
def residualShift (j g : ℕ) : ℕ := E j g + L (2 * g)

/-- Exact residual-register equation extracted from a legal long return with
`j+1` high-opcode transitions. -/
theorem residual_balance {j g F Fnext U Unext : ℕ}
    (hbalance : 3 ^ R (j + 1) g * F =
      defect (j + 1) g + 2 ^ S (j + 1) g * Fnext)
    (hF : A * F = b0 + 2 ^ L g * U)
    (hFnext : A * Fnext = b0 + 2 ^ L (2 * g) * Unext) :
    A * 3 ^ ((j + 1) * Q g) * U =
      A * forcingTail g (j + 1) + 2 ^ E j g * b0 +
        2 ^ residualShift j g * Unext := by
  have hfactor := balance_factor hbalance
  have hsub : A * F - b0 = 2 ^ L g * U := by
    rw [hF]
    omega
  rw [hsub] at hfactor
  have hcancel :
      3 ^ ((j + 1) * Q g) * U =
        forcingTail g (j + 1) + 2 ^ E j g * Fnext := by
    apply Nat.mul_left_cancel (show 0 < 2 ^ L g by positivity)
    simpa only [L, E, mul_assoc, mul_left_comm, mul_comm] using hfactor
  calc
    A * 3 ^ ((j + 1) * Q g) * U =
        A * (forcingTail g (j + 1) + 2 ^ E j g * Fnext) := by
          rw [← hcancel]
          ring
    _ = A * forcingTail g (j + 1) + 2 ^ E j g * (A * Fnext) := by
          ring
    _ = A * forcingTail g (j + 1) +
        2 ^ E j g * (b0 + 2 ^ L (2 * g) * Unext) := by rw [hFnext]
    _ = A * forcingTail g (j + 1) + 2 ^ E j g * b0 +
        2 ^ residualShift j g * Unext := by
          rw [residualShift, pow_add]
          ring

theorem L_eq (g : ℕ) : L g = 131 + 23 * g := by
  simp only [L, P]
  omega

/-- At `k=6` (so `j=5`), the residual output shift has slope `161`. -/
theorem residualShift_five_eq (g : ℕ) :
    residualShift 5 g = 478 + 161 * g := by
  simp only [residualShift, E, L, P]
  omega

/-- The residual numerator has ternary exponent `354+102g`. -/
theorem residualTernary_six_eq (g : ℕ) :
    114 + 6 * Q g = 354 + 102 * g := by
  simp only [Q]
  omega

set_option exponentiation.threshold 200 in
theorem residual_six_has_positive_slope : 2 ^ 161 < 3 ^ 102 := by norm_num

/-- The base of the surviving slow residual growth. -/
def residualBase : ℚ := 3 ^ 102 / 2 ^ 161

set_option exponentiation.threshold 200 in
theorem three_halves_lt_residualBase : (3 : ℚ) / 2 < residualBase := by
  norm_num [residualBase]

set_option exponentiation.threshold 200 in
theorem residualBase_lt_eight_fifths : residualBase < (8 : ℚ) / 5 := by
  norm_num [residualBase]

/-- The fixed ternary integrality gate for a residual payload. -/
def ResidualGate (g U : ℕ) : Prop := A ∣ b0 + 2 ^ L g * U

def frozenResidualGate (U : ℕ) : Prop := A ∣ b0 + 2 ^ 131 * U

/-- If the dyadic opcode phase is frozen at the base, doubling preserves it
at every depth. -/
theorem phase_on_doubling_ray {base : ℕ}
    (hphase : 2 ^ (23 * base) ≡ 1 [MOD A]) (n : ℕ) :
    2 ^ (23 * (base * 2 ^ n)) ≡ 1 [MOD A] := by
  have hp := hphase.pow (2 ^ n)
  rw [one_pow] at hp
  rw [← pow_mul] at hp
  have hexp : 23 * (base * 2 ^ n) = (23 * base) * 2 ^ n := by ring
  rw [hexp]
  exact hp

/-- On a phase-frozen opcode ray, all changing integrality gates become the
same residue class modulo `3^114`. -/
theorem residualGate_iff_frozen {base : ℕ}
    (hphase : 2 ^ (23 * base) ≡ 1 [MOD A]) (n U : ℕ) :
    ResidualGate (base * 2 ^ n) U ↔ frozenResidualGate U := by
  have hray := phase_on_doubling_ray hphase n
  have hpow : 2 ^ L (base * 2 ^ n) ≡ 2 ^ 131 [MOD A] := by
    rw [L_eq, pow_add]
    exact (Nat.ModEq.rfl.mul hray)
  have hsum : b0 + 2 ^ L (base * 2 ^ n) * U ≡
      b0 + 2 ^ 131 * U [MOD A] :=
    Nat.ModEq.rfl.add (hpow.mul Nat.ModEq.rfl)
  exact hsum.dvd_iff (dvd_refl A)

/-- Euler's exponent for the fixed ternary gate. -/
def phasePeriod : ℕ := 2 * 3 ^ 113

theorem totient_A : A.totient = phasePeriod := by
  rw [A, Nat.totient_prime_pow Nat.prime_three (by norm_num)]
  simp only [phasePeriod]
  ring

theorem phase_of_period_dvd {base : ℕ}
    (hdiv : phasePeriod ∣ 23 * base) :
    2 ^ (23 * base) ≡ 1 [MOD A] := by
  have heuler : 2 ^ A.totient ≡ 1 [MOD A] :=
    Nat.ModEq.pow_totient (by
      simp only [A]
      exact (Nat.Coprime.pow_right 114 (by norm_num : Nat.Coprime 2 3)))
  rw [totient_A] at heuler
  obtain ⟨m, hm⟩ := hdiv
  rw [hm, pow_mul]
  simpa using heuler.pow m

/-- One explicit (enormous) base opcode freezes the ternary phase forever. -/
def phaseBase : ℕ := phasePeriod

theorem phaseBase_spec : 2 ^ (23 * phaseBase) ≡ 1 [MOD A] := by
  apply phase_of_period_dvd
  exact dvd_mul_left _ _

theorem phaseBase_all_gates (n U : ℕ) :
    ResidualGate (phaseBase * 2 ^ n) U ↔ frozenResidualGate U :=
  residualGate_iff_frozen phaseBase_spec n U

end LongDoublingQuineResidual
end KontoroC
