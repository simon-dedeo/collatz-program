/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.RouterRecurrence

/-!
# Congruence skeleton of the autonomous router recurrence

Every interior reduced state of an infinite router recurrence lies in one of
two residue classes modulo 24.  This is a necessary invariant, not an
existence theorem for an infinite orbit.
-/

namespace KontoroC

theorem three_pow_two_mul_mod_eight (k : ℕ) :
    3 ^ (2 * k) % 8 = 1 := by
  have hbase : 3 ^ 2 ≡ 1 [MOD 8] := by norm_num
  have hp := hbase.pow k
  apply Nat.mod_eq_of_modEq
  · simpa [pow_mul] using hp
  · norm_num

theorem three_pow_two_mul_add_one_mod_eight (k : ℕ) :
    3 ^ (2 * k + 1) % 8 = 3 := by
  have hbase : 3 ^ 2 ≡ 1 [MOD 8] := by norm_num
  have hp := (hbase.pow k).mul (Nat.ModEq.rfl : 3 ≡ 3 [MOD 8])
  apply Nat.mod_eq_of_modEq
  · simpa [pow_mul, pow_add] using hp
  · norm_num

theorem two_pow_two_mul_mod_three (k : ℕ) :
    2 ^ (2 * k) % 3 = 1 := by
  have hbase : 2 ^ 2 ≡ 1 [MOD 3] := by norm_num
  have hp := hbase.pow k
  apply Nat.mod_eq_of_modEq
  · simpa [pow_mul] using hp
  · norm_num

theorem two_pow_two_mul_add_one_mod_three (k : ℕ) :
    2 ^ (2 * k + 1) % 3 = 2 := by
  have hbase : 2 ^ 2 ≡ 1 [MOD 3] := by norm_num
  have hp := (hbase.pow k).mul (Nat.ModEq.rfl : 2 ≡ 2 [MOD 3])
  apply Nat.mod_eq_of_modEq
  · simpa [pow_mul, pow_add] using hp
  · norm_num

/-- Incoming and outgoing reduced recurrence equations force one of two
modulo-24 classes according to the parity of the current rail length. -/
theorem reduced_router_state_mod_twentyFour
    (rPrev r rNext HPrev H HNext : ℕ)
    (hin : 2 ^ (r + 3) * H = 3 ^ (rPrev + 2) * HPrev + 1)
    (hout : 2 ^ (rNext + 3) * HNext = 3 ^ (r + 2) * H + 1) :
    (Even r → H % 24 = 23) ∧ (Odd r → H % 24 = 13) := by
  constructor
  · rintro ⟨k, rfl⟩
    have hin' : 2 ^ (k * 2 + 3) * H =
        3 ^ (rPrev + 2) * HPrev + 1 := by
      rw [show k * 2 = k + k by omega]
      exact hin
    have hout' : 2 ^ (rNext + 3) * HNext =
        3 ^ (k * 2 + 2) * H + 1 := by
      rw [show k * 2 = k + k by omega]
      exact hout
    have hpow8 : 3 ^ (k * 2 + 2) % 8 = 1 := by
      simpa [show k * 2 + 2 = 2 * (k + 1) by omega] using
        three_pow_two_mul_mod_eight (k + 1)
    have hout8 : (3 ^ (k * 2 + 2) * H + 1) % 8 = 0 := by
      rw [← hout']
      rw [show rNext + 3 = 3 + rNext by omega, pow_add]
      simp [Nat.mul_mod]
    rw [Nat.add_mod, Nat.mul_mod, hpow8] at hout8
    norm_num at hout8
    have hH8 : H % 8 = 7 := by omega
    have hpow3 : 2 ^ (k * 2 + 3) % 3 = 2 := by
      simpa [show k * 2 + 3 = 2 * (k + 1) + 1 by omega] using
        two_pow_two_mul_add_one_mod_three (k + 1)
    have hin3 : (2 ^ (k * 2 + 3) * H) % 3 = 1 := by
      rw [hin']
      rw [show rPrev + 2 = (rPrev + 1) + 1 by omega, pow_succ]
      simp [Nat.add_mod, Nat.mul_mod]
    rw [Nat.mul_mod, hpow3] at hin3
    norm_num at hin3
    have hH3 : H % 3 = 2 := by omega
    have h24lt : H % 24 < 24 := Nat.mod_lt _ (by omega)
    have hto8 := Nat.mod_mod_of_dvd H (by norm_num : 8 ∣ 24)
    have hto3 := Nat.mod_mod_of_dvd H (by norm_num : 3 ∣ 24)
    omega
  · rintro ⟨k, rfl⟩
    have hin' : 2 ^ (k * 2 + 1 + 3) * H =
        3 ^ (rPrev + 2) * HPrev + 1 := by
      rw [show k * 2 = 2 * k by omega]
      exact hin
    have hout' : 2 ^ (rNext + 3) * HNext =
        3 ^ (k * 2 + 1 + 2) * H + 1 := by
      rw [show k * 2 = 2 * k by omega]
      exact hout
    have hpow8 : 3 ^ (k * 2 + 1 + 2) % 8 = 3 := by
      simpa [show k * 2 + 1 + 2 = 2 * (k + 1) + 1 by omega] using
        three_pow_two_mul_add_one_mod_eight (k + 1)
    have hout8 : (3 ^ (k * 2 + 1 + 2) * H + 1) % 8 = 0 := by
      rw [← hout']
      rw [show rNext + 3 = 3 + rNext by omega, pow_add]
      simp [Nat.mul_mod]
    rw [Nat.add_mod, Nat.mul_mod, hpow8] at hout8
    norm_num at hout8
    have hH8 : H % 8 = 5 := by omega
    have hpow3 : 2 ^ (k * 2 + 1 + 3) % 3 = 1 := by
      simpa [show k * 2 + 1 + 3 = 2 * (k + 2) by omega] using
        two_pow_two_mul_mod_three (k + 2)
    have hin3 : (2 ^ (k * 2 + 1 + 3) * H) % 3 = 1 := by
      rw [hin']
      rw [show rPrev + 2 = (rPrev + 1) + 1 by omega, pow_succ]
      simp [Nat.add_mod, Nat.mul_mod]
    rw [Nat.mul_mod, hpow3] at hin3
    norm_num at hin3
    have hH3 : H % 3 = 1 := by omega
    have h24lt : H % 24 < 24 := Nat.mod_lt _ (by omega)
    have hto8 := Nat.mod_mod_of_dvd H (by norm_num : 8 ∣ 24)
    have hto3 := Nat.mod_mod_of_dvd H (by norm_num : 3 ∣ 24)
    omega

end KontoroC
