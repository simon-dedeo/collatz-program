/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardResonance
import KontoroC.YahRechargeAddressNoGo

/-!
# The shallow power-charge Hensel tower is not an ordinary exponent

The exact power-charge worker observes a unique compatible dyadic tower of
parameters for which the first `010111` recharge has larger and larger drain.
This file records the essential adversarial conclusion: compatible finite
residues may define a 2-adic exponent, but they cannot eventually stabilize
to one natural exponent.
-/

namespace KontoroC
namespace OutwardPowerChargeNoGo

/-- The positive integer whose 2-adic valuation controls the shallow drain
for `C = 12 + 16*n`. -/
def shallowDrainNumerator (n : ℕ) : ℕ :=
  3 ^ (14 + 16 * n) + 7

theorem shallowDrainNumerator_pos (n : ℕ) :
    0 < shallowDrainNumerator n := by
  simp [shallowDrainNumerator]

/-- Any address family funding drain depth `6+k` at stage `k` must change
arbitrarily late.  This consumes exact divisibility statements only; the
worker's Hensel lifting algorithm is not trusted. -/
theorem no_eventually_constant_shallowDrain_address
    (address : ℕ → ℕ)
    (hdeep : ∀ k, 2 ^ (6 + k) ∣ shallowDrainNumerator (address k)) :
    ¬∃ n k₀ : ℕ, ∀ k, k₀ ≤ k → address k = n := by
  apply YahRechargeAddressNoGo.no_eventually_constant_deep_addresses
    shallowDrainNumerator address shallowDrainNumerator_pos
  intro k
  exact (Nat.pow_dvd_pow 2 (by omega : k ≤ 6 + k)).trans (hdeep k)

/-- In particular no single ordinary exponent has unbounded shallow-drain
depth, even though a compatible 2-adic exponent tower can have every finite
depth. -/
theorem no_ordinary_unbounded_shallowDrain_exponent :
    ¬∃ n : ℕ, ∀ k, 2 ^ (6 + k) ∣ shallowDrainNumerator n := by
  rintro ⟨n, hn⟩
  let address : ℕ → ℕ := fun _ => n
  apply no_eventually_constant_shallowDrain_address address
    (by intro k; exact hn k)
  exact ⟨n, 0, by intro k _hk; rfl⟩

/-- The same statement in the worker's displayed exponent coordinate
`C=12+16*n`. -/
theorem no_ordinary_unbounded_shallowDrain_C :
    ¬∃ C n : ℕ, C = 12 + 16 * n ∧
      ∀ k, 2 ^ (6 + k) ∣ 3 ^ (C + 2) + 7 := by
  rintro ⟨C, n, rfl, hdeep⟩
  apply no_ordinary_unbounded_shallowDrain_exponent
  refine ⟨n, ?_⟩
  intro k
  have hexponent : 12 + 16 * n + 2 = 14 + 16 * n := by omega
  simpa only [shallowDrainNumerator, hexponent] using hdeep k

end OutwardPowerChargeNoGo
end KontoroC
