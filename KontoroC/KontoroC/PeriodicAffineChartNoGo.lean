/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerPeriodicNoGo

/-!
# Generic obstruction to a periodic affine chart cycle

A future multi-chart proposal may list a finite period of register updates

`Bᵢ * R(next) = Aᵢ * R(current) + Gᵢ`.

This file is independent of the charge-bouncer semantics.  It folds any such
period into one affine update using the already verified finite elimination
lemma.  If the composite numerator and denominator are coprime, the
denominator is nontrivial, and the composite slope is expanding, no infinite
positive natural register orbit exists.

The theorem does not reject an aperiodic dispatcher or a composite with a
nonexpanding slope.  It is a ready-made gate for any claimed finite chart
cycle whose edge sequence itself repeats.
-/

namespace KontoroC
namespace PeriodicAffineChartNoGo

open ChargeBouncerPeriodicNoGo

/-- An infinite positive register execution obtained by repeating one fixed
finite schedule of affine chart edges. -/
structure PeriodicAffineChartOrbit
    (period : ℕ) (A B G : ℕ → ℕ) where
  value : ℕ → ℕ
  value_pos : ∀ n, 0 < value n
  balance : ∀ t i, i < period →
    B i * value (period * t + i + 1) =
      A i * value (period * t + i) + G i

variable {period : ℕ} {A B G : ℕ → ℕ}

/-- Sampling once per period produces the single composite affine-gain
orbit. -/
def PeriodicAffineChartOrbit.collapsed
    (o : PeriodicAffineChartOrbit period A B G) :
    PositiveAffineGainOrbit (prefixProduct A period)
      (prefixProduct B period) (prefixGain A B G period) where
  value t := o.value (period * t)
  value_pos t := o.value_pos (period * t)
  balance t := by
    let x : ℕ → ℕ := fun i => o.value (period * t + i)
    have hlocal : ∀ i, i < period →
        B i * x (i + 1) = A i * x i + G i := by
      intro i hi
      simpa [x, Nat.add_assoc] using o.balance t i hi
    have hfold := prefix_balance A B G x period hlocal
    change prefixProduct B period * o.value (period * (t + 1)) =
      prefixProduct A period * o.value (period * t) +
        prefixGain A B G period
    simpa [x, show period * (t + 1) = period * t + period by ring]
      using hfold

/-- Universal periodic-chart obstruction in terms of the three composite
checks a concrete proposed cycle must discharge. -/
theorem PeriodicAffineChartOrbit.impossible
    (o : PeriodicAffineChartOrbit period A B G)
    (hcop : (prefixProduct A period).Coprime (prefixProduct B period))
    (hdenom : 1 < prefixProduct B period)
    (hexpand : prefixProduct B period < prefixProduct A period) : False := by
  exact o.collapsed.impossible hcop hdenom hexpand

theorem no_periodicAffineChartOrbit
    (hcop : (prefixProduct A period).Coprime (prefixProduct B period))
    (hdenom : 1 < prefixProduct B period)
    (hexpand : prefixProduct B period < prefixProduct A period) :
    ¬ Nonempty (PeriodicAffineChartOrbit period A B G) := by
  rintro ⟨o⟩
  exact o.impossible hcop hdenom hexpand

/-- A termwise expanding positive schedule automatically has an expanding
composite.  This wrapper leaves only coprimality and the nontrivial
denominator to check. -/
theorem PeriodicAffineChartOrbit.impossible_of_termwise_expanding
    (o : PeriodicAffineChartOrbit period A B G)
    (hperiod : 0 < period)
    (hBpos : ∀ i, 0 < B i)
    (hedge : ∀ i, i < period → B i < A i)
    (hcop : (prefixProduct A period).Coprime (prefixProduct B period))
    (hdenom : 1 < prefixProduct B period) : False := by
  apply o.impossible hcop hdenom
  exact prefixProduct_lt A B hperiod hBpos hedge

end PeriodicAffineChartNoGo
end KontoroC
