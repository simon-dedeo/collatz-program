/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerDecoder
import KontoroC.RouterCongruence

/-!
# Quadratic two-rail closure and the mod-eight obstruction

This file checks the inexpensive universal algebra behind the quadratic
two-rail proposal.  It proves closure of `x²+d*u²` under the recharge
scalings and rules out `d=1` at an accepted endpoint.  It does not construct
a coupled integral bouncer transition.
-/

namespace KontoroC

namespace ChargeQuadraticNorm

/-- The homogeneous quadratic two-rail data type. -/
def quadraticNorm (d x u : ℕ) : ℕ := x ^ 2 + d * u ^ 2

/-- The `2^154` recharge coefficient is the square of `2^77`. -/
theorem two_recharge_closed (d h t v : ℕ) :
    (2 ^ 154) ^ h * quadraticNorm d t v =
      quadraticNorm d (2 ^ (77 * h) * t) (2 ^ (77 * h) * v) := by
  have hpow : (2 ^ 154) ^ h = (2 ^ (77 * h)) ^ 2 := by
    rw [← pow_mul]
    rw [show 154 * h = (77 * h) * 2 by omega]
    rw [pow_mul]
  rw [hpow]
  simp only [quadraticNorm]
  ring

/-- The `3^114` recharge coefficient is the square of `3^57`. -/
theorem three_recharge_closed (d h t v : ℕ) :
    (3 ^ 114) ^ h * quadraticNorm d t v =
      quadraticNorm d (3 ^ (57 * h) * t) (3 ^ (57 * h) * v) := by
  have hpow : (3 ^ 114) ^ h = (3 ^ (57 * h)) ^ 2 := by
    rw [← pow_mul]
    rw [show 114 * h = (57 * h) * 2 by omega]
    rw [pow_mul]
  rw [hpow]
  simp only [quadraticNorm]
  ring

/-- The mod-eight residue forced by the accepted input valuation. -/
theorem mod_eight_eq_seven_of_twoPowTwentyThree_dvd_succ
    {y : ℕ} (hy : 2 ^ 23 ∣ y + 1) : y % 8 = 7 := by
  have h8pow : 8 ∣ 2 ^ 23 := by norm_num
  obtain ⟨k, hk⟩ := h8pow.trans hy
  omega

/-- Every accepted fixed-form bouncer input is `7 mod 8`. -/
theorem accepted_input_mod_eight (s : ChargeBouncerStep) :
    s.input % 8 = 7 := by
  have hpow : 2 ^ (23 * s.defectOpcode) ∣ s.input + 1 := by
    rw [← s.input_opcode_readback]
    exact pow_padicValNat_dvd
  have hsmall : 2 ^ 23 ∣ 2 ^ (23 * s.defectOpcode) := by
    apply Nat.pow_dvd_pow
    have hm := s.defectOpcode_pos
    omega
  exact mod_eight_eq_seven_of_twoPowTwentyThree_dvd_succ (hsmall.trans hpow)

/-- Removing the even recharge power of three preserves the forced residue
of an accepted output endpoint. -/
theorem accepted_output_quotient_mod_eight
    {h q : ℕ} (hout : 2 ^ 23 ∣ 3 ^ (114 * h) * q + 1) :
    q % 8 = 7 := by
  have hy : (3 ^ (114 * h) * q) % 8 = 7 :=
    mod_eight_eq_seven_of_twoPowTwentyThree_dvd_succ hout
  have hthree : 3 ^ (114 * h) % 8 = 1 := by
    rw [show 114 * h = 2 * (57 * h) by omega]
    exact three_pow_two_mul_mod_eight (57 * h)
  rw [Nat.mul_mod, hthree] at hy
  simpa using hy

/-- A natural square has residue `0`, `1`, or `4` modulo eight. -/
theorem square_mod_eight (x : ℕ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  rw [pow_two, Nat.mul_mod]
  have hx : x % 8 < 8 := Nat.mod_lt _ (by omega)
  interval_cases h : x % 8 <;> norm_num

/-- In particular, the tempting sum-of-two-squares type cannot occupy an
accepted endpoint, whose residue would have to be seven modulo eight. -/
theorem sum_two_squares_not_mod_eight_seven (x u : ℕ) :
    (x ^ 2 + u ^ 2) % 8 ≠ 7 := by
  intro hseven
  rw [Nat.add_mod] at hseven
  rcases square_mod_eight x with hx | hx | hx <;>
    rcases square_mod_eight u with hu | hu | hu <;>
      rw [hx, hu] at hseven <;> norm_num at hseven

theorem no_accepted_sum_two_squares
    {y x u : ℕ} (hy : 2 ^ 23 ∣ y + 1) (hrep : y = x ^ 2 + u ^ 2) : False := by
  have hseven := mod_eight_eq_seven_of_twoPowTwentyThree_dvd_succ hy
  rw [hrep] at hseven
  exact sum_two_squares_not_mod_eight_seven x u hseven

end ChargeQuadraticNorm

end KontoroC
