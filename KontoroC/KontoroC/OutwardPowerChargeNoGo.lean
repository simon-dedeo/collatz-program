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

/-! ## Direct pure-power return -/

/-- The exponential equation forced by a direct shallow-branch return to a
pure power has no solutions.  The proof is elementary: reduction modulo
three makes the binary exponent even, after which difference of squares
forces the exceptional identity `3^2 + 7 = 2^4`, incompatible with the
displayed exponents. -/
theorem no_direct_purePower_return_equation (n a : ℕ) :
    3 ^ (14 + 16 * n) + 7 ≠ 2 ^ (a + 6) := by
  intro heq
  have hcast := congrArg (fun z : ℕ => (z : ZMod 3)) heq
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_ofNat] at hcast
  have hpowTwo : ((2 : ZMod 3) ^ (a + 6)) = 1 := by
    have hzero : (3 : ZMod 3) = 0 := by decide
    have hseven : (7 : ZMod 3) = 1 := by decide
    rw [hzero, zero_pow (by omega : 14 + 16 * n ≠ 0), hseven,
      zero_add] at hcast
    exact hcast.symm
  have hpowNeg : ((-1 : ZMod 3) ^ (a + 6)) = 1 := by
    rw [show (2 : ZMod 3) = -1 by decide] at hpowTwo
    exact hpowTwo
  have heven : Even (a + 6) :=
    (neg_one_pow_eq_one_iff_even
      (by decide : (-1 : ZMod 3) ≠ 1)).mp hpowNeg
  obtain ⟨d, hd⟩ := heven
  let X := 2 ^ d
  let Y := 3 ^ (7 + 8 * n)
  have htwo : 2 ^ (a + 6) = X ^ 2 := by
    dsimp [X]
    rw [hd, pow_add, pow_two]
  have hthree : 3 ^ (14 + 16 * n) = Y ^ 2 := by
    dsimp [Y]
    rw [show 14 + 16 * n = (7 + 8 * n) + (7 + 8 * n) by omega,
      pow_add, pow_two]
  rw [hthree, htwo] at heq
  have hYX : Y < X := by nlinarith
  let p := X - Y
  have hp : 0 < p := by exact Nat.sub_pos_of_lt hYX
  have hX : X = p + Y := by
    dsimp [p]
    omega
  rw [hX] at heq
  have hprod : p * (p + 2 * Y) = 7 := by nlinarith
  have hpDvd : p ∣ 7 := ⟨p + 2 * Y, hprod.symm⟩
  have hpLe : p ≤ 7 := Nat.le_of_dvd (by norm_num) hpDvd
  have hYlarge : 3 < Y := by
    dsimp [Y]
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 3)
      (show 1 < 7 + 8 * n by omega)
    norm_num at h ⊢
    exact h
  interval_cases p <;> norm_num at hprod <;> omega

end OutwardPowerChargeNoGo
end KontoroC
