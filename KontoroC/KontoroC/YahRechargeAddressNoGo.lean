/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahPacketRecharge

/-!
# Deep recharge addresses cannot stabilize to an ordinary coordinate

QM13 produces compatible dyadic congruence classes for packet coordinates.
Those classes may converge in the two-adics, but an address sequence giving
unbounded recharge cannot eventually become one fixed natural number.  If it
did, one fixed positive integer would be divisible by arbitrarily high powers
of two.

This is deliberately a no-go about address stabilization, not about the
existence of each finite-depth address.  It pinpoints why isolated discrete
logarithms do not yet assemble into an ordinary orbit.
-/

namespace KontoroC
namespace YahRechargeAddressNoGo

open YahPacketRecharge

/-- A sequence whose image has dyadic divisibility depth at least its index
cannot eventually stabilize whenever the image values are positive. -/
theorem no_eventually_constant_deep_addresses
    (target address : ℕ → ℕ)
    (hpositive : ∀ q, 0 < target q)
    (hdeep : ∀ K, 2 ^ K ∣ target (address K)) :
    ¬∃ q₀ K₀ : ℕ, ∀ K, K₀ ≤ K → address K = q₀ := by
  rintro ⟨q₀, K₀, hstable⟩
  let X := target q₀
  let K := K₀ + X
  have hK : K₀ ≤ K := by simp [K]
  have haddress : address K = q₀ := hstable K hK
  have hdiv : 2 ^ K ∣ X := by
    simpa [X, haddress] using hdeep K
  have hX : 0 < X := hpositive q₀
  have hle : 2 ^ K ≤ X := Nat.le_of_dvd hX hdiv
  have hpow : 2 ^ X ≤ 2 ^ K := by
    apply Nat.pow_le_pow_right (by omega)
    simp [K]
  exact (not_lt_of_ge (hpow.trans hle)) X.lt_two_pow_self

def phaseZeroTarget (s q : ℕ) : ℕ :=
  3 * (9 ^ q * packetScale s) + 37

def phaseOneTarget (s q : ℕ) : ℕ :=
  9 ^ q * packetScale s + 15

def phaseThreeTarget (s q : ℕ) : ℕ :=
  9 ^ q * packetScale s + 31

/-- A QM13 phase-zero address chosen to give arbitrarily increasing gains
cannot eventually be a fixed ordinary `q`. -/
theorem phaseZero_addresses_not_eventually_constant (s : ℕ) (address : ℕ → ℕ)
    (hdeep : ∀ g, 2 ^ (g + 6) ∣ phaseZeroTarget s (address g)) :
    ¬∃ q₀ g₀ : ℕ, ∀ g, g₀ ≤ g → address g = q₀ := by
  apply no_eventually_constant_deep_addresses (phaseZeroTarget s) address
  · intro q
    simp [phaseZeroTarget]
  · intro g
    exact (Nat.pow_dvd_pow 2 (by omega : g ≤ g + 6)).trans (hdeep g)

/-- The same obstruction for phase one. -/
theorem phaseOne_addresses_not_eventually_constant (s : ℕ) (address : ℕ → ℕ)
    (hdeep : ∀ g, 2 ^ (g + 5) ∣ phaseOneTarget s (address g)) :
    ¬∃ q₀ g₀ : ℕ, ∀ g, g₀ ≤ g → address g = q₀ := by
  apply no_eventually_constant_deep_addresses (phaseOneTarget s) address
  · intro q
    simp [phaseOneTarget]
  · intro g
    exact (Nat.pow_dvd_pow 2 (by omega : g ≤ g + 5)).trans (hdeep g)

/-- The same obstruction for phase three. -/
theorem phaseThree_addresses_not_eventually_constant (s : ℕ) (address : ℕ → ℕ)
    (hdeep : ∀ g, 2 ^ (g + 7) ∣ phaseThreeTarget s (address g)) :
    ¬∃ q₀ g₀ : ℕ, ∀ g, g₀ ≤ g → address g = q₀ := by
  apply no_eventually_constant_deep_addresses (phaseThreeTarget s) address
  · intro q
    simp [phaseThreeTarget]
  · intro g
    exact (Nat.pow_dvd_pow 2 (by omega : g ≤ g + 7)).trans (hdeep g)

end YahRechargeAddressNoGo
end KontoroC
