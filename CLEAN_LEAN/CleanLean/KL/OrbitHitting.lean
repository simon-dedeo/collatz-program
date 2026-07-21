/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.NumberTheory.Multiplicity

/-!
# The first hit of `2` by the backward four-orbit of `-1`

The charged-Lyapunov no-go discussion needs more than the fact that
multiplication by four is cyclic modulo powers of three: it needs the exact
position of the residue `2` in that cycle.  This file proves the arithmetic
statement using the lifting-the-exponent theorem already in mathlib.
-/

namespace CleanLean.KL

/-- The orbit hit `2 * 4^t = -1 (mod 3^J)`, written without signed modular
arithmetic. -/
def OrbitHit (J t : ℕ) : Prop := 3 ^ J ∣ 2 * 4 ^ t + 1

/-- The odd-prime LTE specialization used throughout the orbit calculation. -/
theorem padicValNat_two_pow_add_one {n : ℕ} (hn : Odd n) :
    padicValNat 3 (2 ^ n + 1) = 1 + padicValNat 3 n := by
  simpa using
    (padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
      (odd_two_mul_add_one 1) (by norm_num) (by norm_num) hn)

/-- Rewriting the Collatz-shaped power as one power of two. -/
theorem two_mul_four_pow (t : ℕ) : 2 * 4 ^ t = 2 ^ (2 * t + 1) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]
  ring

/-- An orbit hit at precision `3^J` is equivalent to divisibility of the odd
exponent by `3^(J-1)`. -/
theorem orbitHit_iff_exponent_dvd {J t : ℕ} (hJ : 1 ≤ J) :
    OrbitHit J t ↔ 3 ^ (J - 1) ∣ 2 * t + 1 := by
  have hnOdd : Odd (2 * t + 1) := odd_two_mul_add_one t
  have hpowNe : 2 ^ (2 * t + 1) + 1 ≠ 0 := by positivity
  rw [OrbitHit, two_mul_four_pow]
  rw [padicValNat_dvd_iff_le hpowNe, padicValNat_two_pow_add_one hnOdd]
  rw [padicValNat_dvd_iff_le (by omega : 2 * t + 1 ≠ 0)]
  omega

/-- Powers of three are odd. -/
theorem odd_three_pow (n : ℕ) : Odd (3 ^ n) := by
  exact (odd_two_mul_add_one 1).pow

/-- The candidate first hitting time has the expected odd exponent. -/
theorem twice_orbitHitTime_add_one (J : ℕ) :
    2 * ((3 ^ J - 1) / 2) + 1 = 3 ^ J := by
  obtain ⟨q, hq⟩ := odd_three_pow J
  rw [hq]
  omega

/-- The explicit time `(3^(J-1)-1)/2` really hits `-1` modulo `3^J`. -/
theorem orbitHit_at_explicit_time {J : ℕ} (hJ : 1 ≤ J) :
    OrbitHit J ((3 ^ (J - 1) - 1) / 2) := by
  rw [orbitHit_iff_exponent_dvd hJ, twice_orbitHitTime_add_one]

/-- No earlier nonnegative time hits. -/
theorem explicit_time_le_of_orbitHit {J t : ℕ} (hJ : 1 ≤ J)
    (hit : OrbitHit J t) :
    (3 ^ (J - 1) - 1) / 2 ≤ t := by
  have hdvd : 3 ^ (J - 1) ∣ 2 * t + 1 :=
    (orbitHit_iff_exponent_dvd hJ).mp hit
  have hpos : 0 < 2 * t + 1 := by omega
  have hle : 3 ^ (J - 1) ≤ 2 * t + 1 := Nat.le_of_dvd hpos hdvd
  have heq := twice_orbitHitTime_add_one (J - 1)
  omega

/-- Exact first-hitting-time theorem. -/
theorem orbitHit_first_time {J : ℕ} (hJ : 1 ≤ J) :
    OrbitHit J ((3 ^ (J - 1) - 1) / 2) ∧
      ∀ t, OrbitHit J t → (3 ^ (J - 1) - 1) / 2 ≤ t :=
  ⟨orbitHit_at_explicit_time hJ, fun _ hit => explicit_time_le_of_orbitHit hJ hit⟩

/-- From precision three onward, the first hitting time is at least the
precision. -/
theorem precision_le_explicit_time {J : ℕ} (hJ : 3 ≤ J) :
    J ≤ (3 ^ (J - 1) - 1) / 2 := by
  have hpow : 2 * J + 1 ≤ 3 ^ (J - 1) := by
    induction J, hJ using Nat.le_induction with
    | base => norm_num
    | succ J hJ ih =>
        have hsub : J + 1 - 1 = (J - 1) + 1 := by omega
        rw [hsub, pow_succ]
        nlinarith
  have heq := twice_orbitHitTime_add_one (J - 1)
  omega

/-- Thus the depth-`J` truncation consisting of times `0,...,J-1` does not
contain the residue `2`, for every `J >= 3`.  This is the exact charge-location
fact missing from the all-level marginal-cycle no-go argument. -/
theorem no_orbitHit_before_precision {J t : ℕ} (hJ : 3 ≤ J) (ht : t < J) :
    ¬OrbitHit J t := by
  intro hit
  have hfirst := explicit_time_le_of_orbitHit (by omega : 1 ≤ J) hit
  have hprecision := precision_le_explicit_time hJ
  omega

end CleanLean.KL
