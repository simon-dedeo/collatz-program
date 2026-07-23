/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PeriodicAffineChartNoGo

/-!
# The first two YAH restorative edges cannot form an alternating cycle

The verified first restorative register instruction is

`256 * R₁ = 3^6 * R₀ + 1`.

The next research-side candidate has arithmetic instruction

`2048 * R₂ = 3^10 * R₁ + 8`.

Even if the second output were proved to identify with the first chart input,
alternating these two edges forever would be impossible for positive natural
registers.  Their period product has numerator `3^16`, denominator `2^19`,
and a nonnegative gain.  The numerator and denominator are coprime and the
composite slope is strictly expanding, so the generic denominator-growth gate
applies.

This theorem does not audit the word-level construction of the second edge,
and it does not exclude a third chart, a nontrivial coordinate conjugacy, or
an aperiodic route.
-/

namespace KontoroC
namespace YahTwoRestorativeCycleNoGo

open PeriodicAffineChartNoGo

def edgeNumerator : ℕ → ℕ
  | 0 => 3 ^ 6
  | _ => 3 ^ 10

def edgeDenominator : ℕ → ℕ
  | 0 => 2 ^ 8
  | _ => 2 ^ 11

def edgeGain : ℕ → ℕ
  | 0 => 1
  | _ => 8

/-- Package an alleged alternating execution of the two restorative maps as
a period-two affine chart orbit. -/
def alternatingOrbit (register : ℕ → ℕ)
    (hpos : ∀ n, 0 < register n)
    (hfirst : ∀ t,
      2 ^ 8 * register (2 * t + 1) = 3 ^ 6 * register (2 * t) + 1)
    (hsecond : ∀ t,
      2 ^ 11 * register (2 * t + 2) = 3 ^ 10 * register (2 * t + 1) + 8) :
    PeriodicAffineChartOrbit 2 edgeNumerator edgeDenominator edgeGain where
  value := register
  value_pos := hpos
  balance t i hi := by
    interval_cases i
    · simpa [edgeNumerator, edgeDenominator, edgeGain] using hfirst t
    · simpa [edgeNumerator, edgeDenominator, edgeGain, Nat.add_assoc] using
        hsecond t

theorem composite_numerator :
    ChargeBouncerPeriodicNoGo.prefixProduct edgeNumerator 2 = 3 ^ 16 := by
  norm_num [ChargeBouncerPeriodicNoGo.prefixProduct, edgeNumerator, pow_add]

theorem composite_denominator :
    ChargeBouncerPeriodicNoGo.prefixProduct edgeDenominator 2 = 2 ^ 19 := by
  norm_num [ChargeBouncerPeriodicNoGo.prefixProduct, edgeDenominator, pow_add]

/-- The direct two-chart closure is impossible even under the strongest
favorable assumption that both word-level edges and their chart
identifications are exact. -/
theorem no_alternating_restorative_cycle (register : ℕ → ℕ)
    (hpos : ∀ n, 0 < register n)
    (hfirst : ∀ t,
      2 ^ 8 * register (2 * t + 1) = 3 ^ 6 * register (2 * t) + 1)
    (hsecond : ∀ t,
      2 ^ 11 * register (2 * t + 2) = 3 ^ 10 * register (2 * t + 1) + 8) :
    False := by
  let o := alternatingOrbit register hpos hfirst hsecond
  apply o.impossible
  · rw [composite_numerator, composite_denominator]
    exact (by norm_num : Nat.Coprime (3 ^ 16) (2 ^ 19))
  · rw [composite_denominator]
    norm_num
  · rw [composite_numerator, composite_denominator]
    norm_num

end YahTwoRestorativeCycleNoGo
end KontoroC
