/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.RouterRecurrence

/-!
# The minimal break-off counter recurrence

The public router recurrence can be encoded by two exact factorizations of a
single growing counter `k`.  This file uses proof-carrying factorization
witnesses rather than executable valuations.  No infinite orbit is supplied.
-/

namespace KontoroC

/-- An infinite orbit of the radix break-off counter.  The two factorizations
are

`k = 2^j * u`, and `8*k = 3^(r+2) * H + 1`.

The handoff fields identify the next ternary registers with the current
binary registers. -/
structure BreakoffCounterOrbit where
  k : ℕ → ℕ
  j : ℕ → ℕ
  u : ℕ → ℕ
  r : ℕ → ℕ
  H : ℕ → ℕ
  k_pos : ∀ t, 0 < k t
  u_pos : ∀ t, 0 < u t
  H_pos : ∀ t, 0 < H t
  u_odd : ∀ t, Odd (u t)
  H_odd : ∀ t, Odd (H t)
  binary_factor : ∀ t, k t = 2 ^ j t * u t
  ternary_factor : ∀ t, 8 * k t = 3 ^ (r t + 2) * H t + 1
  next_r : ∀ t, r (t + 1) = j t
  next_H : ∀ t, H (t + 1) = u t
  start_large : 4 < minusOneState (3 * H 0) (r 0 + 1)

namespace BreakoffCounterOrbit

/-- The advertised break-off equation follows from the next ternary
factorization and register handoff. -/
theorem breakoff_equation (g : BreakoffCounterOrbit) (t : ℕ) :
    8 * g.k (t + 1) = 3 ^ (g.j t + 2) * g.u t + 1 := by
  rw [g.ternary_factor (t + 1), g.next_r t, g.next_H t]

/-- Every counter value automatically lies in the class `8 mod 9`. -/
theorem k_mod_nine (g : BreakoffCounterOrbit) (t : ℕ) :
    g.k t % 9 = 8 := by
  have hdiv : 9 ∣ 3 ^ (g.r t + 2) * g.H t := by
    refine ⟨3 ^ g.r t * g.H t, ?_⟩
    rw [show g.r t + 2 = 2 + g.r t by omega, pow_add]
    norm_num
    ring
  obtain ⟨q, hq⟩ := hdiv
  have hmod : (8 * g.k t) % 9 = 1 := by
    rw [g.ternary_factor t, hq]
    simp [Nat.add_mod]
  rw [Nat.mul_mod] at hmod
  norm_num at hmod
  have hkmod := Nat.mod_lt (g.k t) (by omega : 0 < 9)
  omega

/-- The break-off counter is strictly increasing at every step. -/
theorem k_strictly_grows (g : BreakoffCounterOrbit) (t : ℕ) :
    g.k t < g.k (t + 1) := by
  have hcoeff := twoPow_add_three_lt_threePow_add_two (g.j t)
  have hmul : 2 ^ (g.j t + 3) * g.u t <
      3 ^ (g.j t + 2) * g.u t :=
    (Nat.mul_lt_mul_right (g.u_pos t)).2 hcoeff
  have hleft : 8 * g.k t = 2 ^ (g.j t + 3) * g.u t := by
    rw [g.binary_factor t,
      show g.j t + 3 = 3 + g.j t by omega, pow_add]
    norm_num
    ring
  have hright := g.breakoff_equation t
  omega

/-- The two counter factorizations generate the public router payload
recurrence with `P=3H`. -/
def toInfiniteRouterPayloadRecurrence (g : BreakoffCounterOrbit) :
    InfiniteRouterPayloadRecurrence where
  railLength := g.r
  payload t := 3 * g.H t
  payload_pos t := Nat.mul_pos (by omega) (g.H_pos t)
  payload_odd t := (by norm_num : Odd 3).mul (g.H_odd t)
  recurrence t := by
    rw [g.next_r t, g.next_H t]
    calc
      2 ^ (g.j t + 3) * (3 * g.u t) =
          24 * (2 ^ g.j t * g.u t) := by
        rw [show g.j t + 3 = 3 + g.j t by omega, pow_add]
        norm_num
        ring
      _ = 24 * g.k t := by rw [g.binary_factor t]
      _ = 3 * (8 * g.k t) := by ring
      _ = 3 * (3 ^ (g.r t + 2) * g.H t + 1) := by
        rw [g.ternary_factor t]
      _ = 3 ^ (g.r t + 2) * (3 * g.H t) + 3 := by ring
  start_large := g.start_large

/-- Main endpoint: any infinite positive proof-carrying break-off orbit
refutes the literal standard Collatz conjecture. -/
theorem not_conjecture (g : BreakoffCounterOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toInfiniteRouterPayloadRecurrence.not_conjecture

end BreakoffCounterOrbit

end KontoroC
