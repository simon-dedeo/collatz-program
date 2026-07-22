/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeQuadraticNorm
import KontoroC.ChargePowerQuine

/-!
# Normalized opcode recurrence for quadratic charge types

This file records the universal algebra behind the selected `d=31` norm
type.  It deliberately separates a norm identity or one accepted step from
the still-open existence of a second step or an infinite chain.
-/

namespace KontoroC

namespace ChargeNormOpcode

open ChargePowerQuine

/-- Integral quadratic norm, allowing signed coordinates. -/
def quadraticNormInt (d x u : ℤ) : ℤ := x ^ 2 + d * u ^ 2

/-- Multiplication in `Z[sqrt(-d)]`, stated as a norm identity. -/
theorem quadraticNormInt_mul (d x u t v : ℤ) :
    quadraticNormInt d (x * t - d * u * v) (x * v + u * t) =
      quadraticNormInt d x u * quadraticNormInt d t v := by
  simp only [quadraticNormInt]
  ring

/-- Odd public-register factor `C-D`. -/
def registerOdd : ℤ := C - D

theorem registerOdd_spec : registerOdd = 120751555 := by
  norm_num [registerOdd, C, D]

/-- DO3: the public register factor is a principal `N_31` norm. -/
theorem registerOdd_is_norm_thirtyOne :
    quadraticNormInt 31 7706 1407 = registerOdd := by
  norm_num [quadraticNormInt, registerOdd, C, D]

private theorem seven_inert_mod_five
    (x u : ZMod 5) (h : x ^ 2 + 7 * u ^ 2 = 0) : x = 0 ∧ u = 0 := by
  revert x u
  decide

private theorem seven_inert_mod_nineteen
    (x u : ZMod 19) (h : x ^ 2 + 7 * u ^ 2 = 0) : x = 0 ∧ u = 0 := by
  revert x u
  decide

/-- DO1 at the first inert register prime for `d=7`. -/
theorem five_dvd_coordinates_of_five_dvd_norm_seven
    {x u : ℤ} (h : (5 : ℤ) ∣ quadraticNormInt 7 x u) :
    (5 : ℤ) ∣ x ∧ (5 : ℤ) ∣ u := by
  have hz : ((quadraticNormInt 7 x u : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  have hi := seven_inert_mod_five (x : ZMod 5) (u : ZMod 5)
    (by simpa [quadraticNormInt] using hz)
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi.2⟩

/-- DO1 at the second inert register prime for `d=7`. -/
theorem nineteen_dvd_coordinates_of_nineteen_dvd_norm_seven
    {x u : ℤ} (h : (19 : ℤ) ∣ quadraticNormInt 7 x u) :
    (19 : ℤ) ∣ x ∧ (19 : ℤ) ∣ u := by
  have hz : ((quadraticNormInt 7 x u : ℤ) : ZMod 19) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  have hi := seven_inert_mod_nineteen (x : ZMod 19) (u : ZMod 19)
    (by simpa [quadraticNormInt] using hz)
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi.2⟩

private theorem prime_sq_dvd_norm_of_dvd_coordinates
    {p d x u : ℤ} (hx : p ∣ x) (hu : p ∣ u) :
    p ^ 2 ∣ quadraticNormInt d x u := by
  rcases hx with ⟨a, rfl⟩
  rcases hu with ⟨b, rfl⟩
  refine ⟨a ^ 2 + d * b ^ 2, ?_⟩
  simp only [quadraticNormInt]
  ring

theorem twentyFive_dvd_norm_seven_of_five_dvd
    {x u : ℤ} (h : (5 : ℤ) ∣ quadraticNormInt 7 x u) :
    (25 : ℤ) ∣ quadraticNormInt 7 x u := by
  have hc := five_dvd_coordinates_of_five_dvd_norm_seven h
  exact prime_sq_dvd_norm_of_dvd_coordinates hc.1 hc.2

theorem threeSixtyOne_dvd_norm_seven_of_nineteen_dvd
    {x u : ℤ} (h : (19 : ℤ) ∣ quadraticNormInt 7 x u) :
    (361 : ℤ) ∣ quadraticNormInt 7 x u := by
  have hc := nineteen_dvd_coordinates_of_nineteen_dvd_norm_seven h
  exact prime_sq_dvd_norm_of_dvd_coordinates hc.1 hc.2

/-- Integral geometric quotient `(C^m-D^m)/(C-D)`. -/
def opcodeDebris : ℕ → ℤ
  | 0 => 0
  | n + 1 => C ^ n + D * opcodeDebris n

theorem opcodeDebris_factor (m : ℕ) :
    registerOdd * opcodeDebris m = C ^ m - D ^ m := by
  induction m with
  | zero => simp [opcodeDebris]
  | succ n ih =>
      simp only [opcodeDebris]
      calc
        registerOdd * (C ^ n + D * opcodeDebris n) =
            C ^ (n + 1) - D ^ (n + 1) +
              D * (registerOdd * opcodeDebris n - (C ^ n - D ^ n)) := by
                dsimp [registerOdd]
                rw [pow_succ, pow_succ]
                ring
        _ = C ^ (n + 1) - D ^ (n + 1) := by rw [ih]; ring

/-- CP5 at the scalar level: defect debris composes by an exact Lucas law.
Consequently a word of defect-only blocks contains only the sum of its
opcodes; any nontrivial programming content must use recharge decorations. -/
theorem opcodeDebris_add (m n : ℕ) :
    opcodeDebris (m + n) =
      C ^ n * opcodeDebris m + D ^ m * opcodeDebris n := by
  apply mul_left_cancel₀ (by norm_num [registerOdd, C, D] : registerOdd ≠ 0)
  calc
    registerOdd * opcodeDebris (m + n) = C ^ (m + n) - D ^ (m + n) :=
      opcodeDebris_factor (m + n)
    _ = C ^ n * (C ^ m - D ^ m) + D ^ m * (C ^ n - D ^ n) := by
      rw [pow_add]
      ring
    _ = registerOdd *
        (C ^ n * opcodeDebris m + D ^ m * opcodeDebris n) := by
      rw [← opcodeDebris_factor m, ← opcodeDebris_factor n]
      ring

/-- If both payload sides vanish modulo `n`, the collision forces the two
opcode coefficients to agree modulo `n`. -/
theorem collision_forces_coefficient_modEq
    {n : ℤ} {m h : ℕ} {y q : ℤ}
    (hy : n ∣ y) (hq : n ∣ q)
    (hcollision : C ^ m * (y + 1) = D ^ m * (1 + B ^ h * q)) :
    C ^ m ≡ D ^ m [ZMOD n] := by
  rcases hy with ⟨a, rfl⟩
  rcases hq with ⟨b, rfl⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨C ^ m * a - D ^ m * B ^ h * b, ?_⟩
  linear_combination -hcollision

/-- The ratio `C/D` has exact order five modulo `5²`. -/
theorem five_dvd_opcode_of_coefficient_modEq
    {m : ℕ} (h : C ^ m ≡ D ^ m [ZMOD (25 : ℤ)]) : 5 ∣ m := by
  have heq : ((C ^ m : ℤ) : ZMod 25) = ((D ^ m : ℤ) : ZMod 25) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact Int.modEq_iff_dvd.mp h
  push_cast at heq
  have hc : (C : ZMod 25) = 13 := by decide
  have hd : (D : ZMod 25) = 8 := by decide
  rw [hc, hd] at heq
  have hr : (11 : ZMod 25) ^ m = 1 := by
    calc
      (11 : ZMod 25) ^ m = ((13 : ZMod 25) * 22) ^ m :=
        congrArg (fun z : ZMod 25 => z ^ m) (by decide)
      _ = (13 : ZMod 25) ^ m * 22 ^ m := by rw [mul_pow]
      _ = (8 : ZMod 25) ^ m * 22 ^ m := by rw [heq]
      _ = ((8 : ZMod 25) * 22) ^ m := (mul_pow _ _ _).symm
      _ = 1 := by rw [show (8 : ZMod 25) * 22 = 1 by decide, one_pow]
  rw [Nat.dvd_iff_mod_eq_zero]
  let q := m / 5
  let r := m % 5
  change r = 0
  have hm : m = 5 * q + r := by dsimp [q, r]; omega
  have hrlt : r < 5 := by dsimp [r]; omega
  rw [hm, pow_add, pow_mul] at hr
  have horderBase : (11 : ZMod 25) ^ 5 = 1 := by decide
  rw [horderBase, one_pow, one_mul] at hr
  have horder : ∀ k : Fin 5, (11 : ZMod 25) ^ k.val = 1 → k.val = 0 := by
    decide
  exact horder ⟨r, hrlt⟩ hr

/-- The ratio `C/D` has exact order nineteen modulo `19²`. -/
theorem nineteen_dvd_opcode_of_coefficient_modEq
    {m : ℕ} (h : C ^ m ≡ D ^ m [ZMOD (361 : ℤ)]) : 19 ∣ m := by
  have heq : ((C ^ m : ℤ) : ZMod 361) = ((D ^ m : ℤ) : ZMod 361) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact Int.modEq_iff_dvd.mp h
  push_cast at heq
  have hc : (C : ZMod 361) = 355 := by decide
  have hd : (D : ZMod 361) = 51 := by decide
  rw [hc, hd] at heq
  have hr : (191 : ZMod 361) ^ m = 1 := by
    calc
      (191 : ZMod 361) ^ m = ((355 : ZMod 361) * 269) ^ m :=
        congrArg (fun z : ZMod 361 => z ^ m) (by decide)
      _ = (355 : ZMod 361) ^ m * 269 ^ m := by rw [mul_pow]
      _ = (51 : ZMod 361) ^ m * 269 ^ m := by rw [heq]
      _ = ((51 : ZMod 361) * 269) ^ m := (mul_pow _ _ _).symm
      _ = 1 := by rw [show (51 : ZMod 361) * 269 = 1 by decide, one_pow]
  rw [Nat.dvd_iff_mod_eq_zero]
  let q := m / 19
  let r := m % 19
  change r = 0
  have hm : m = 19 * q + r := by dsimp [q, r]; omega
  have hrlt : r < 19 := by dsimp [r]; omega
  rw [hm, pow_add, pow_mul] at hr
  have horderBase : (191 : ZMod 361) ^ 19 = 1 := by decide
  rw [horderBase, one_pow, one_mul] at hr
  have horder : ∀ k : Fin 19,
      (191 : ZMod 361) ^ k.val = 1 → k.val = 0 := by
    decide
  exact horder ⟨r, hrlt⟩ hr

/-- Concrete opcode tax contributed by the inert prime five for `d=7`. -/
theorem five_dvd_opcode_of_norm_seven_collision
    {m h : ℕ} {x u t v : ℤ}
    (hy : (5 : ℤ) ∣ quadraticNormInt 7 x u)
    (hq : (5 : ℤ) ∣ quadraticNormInt 7 t v)
    (hcollision : C ^ m * (quadraticNormInt 7 x u + 1) =
      D ^ m * (1 + B ^ h * quadraticNormInt 7 t v)) :
    5 ∣ m := by
  apply five_dvd_opcode_of_coefficient_modEq
  exact collision_forces_coefficient_modEq
    (twentyFive_dvd_norm_seven_of_five_dvd hy)
    (twentyFive_dvd_norm_seven_of_five_dvd hq) hcollision

/-- Concrete opcode tax contributed by the inert prime nineteen for `d=7`. -/
theorem nineteen_dvd_opcode_of_norm_seven_collision
    {m h : ℕ} {x u t v : ℤ}
    (hy : (19 : ℤ) ∣ quadraticNormInt 7 x u)
    (hq : (19 : ℤ) ∣ quadraticNormInt 7 t v)
    (hcollision : C ^ m * (quadraticNormInt 7 x u + 1) =
      D ^ m * (1 + B ^ h * quadraticNormInt 7 t v)) :
    19 ∣ m := by
  apply nineteen_dvd_opcode_of_coefficient_modEq
  exact collision_forces_coefficient_modEq
    (threeSixtyOne_dvd_norm_seven_of_nineteen_dvd hy)
    (threeSixtyOne_dvd_norm_seven_of_nineteen_dvd hq) hcollision

/-- The full `d=7` opcode tax from the two inert public-register primes. -/
theorem ninetyFive_dvd_opcode_of_norm_seven_register_collision
    {m h : ℕ} {x u t v : ℤ}
    (hy : registerOdd ∣ quadraticNormInt 7 x u)
    (hq : registerOdd ∣ quadraticNormInt 7 t v)
    (hcollision : C ^ m * (quadraticNormInt 7 x u + 1) =
      D ^ m * (1 + B ^ h * quadraticNormInt 7 t v)) :
    95 ∣ m := by
  have hfiveR : (5 : ℤ) ∣ registerOdd := by
    norm_num [registerOdd, C, D]
  have hnineteenR : (19 : ℤ) ∣ registerOdd := by
    norm_num [registerOdd, C, D]
  have hfive := five_dvd_opcode_of_norm_seven_collision
    (hfiveR.trans hy) (hfiveR.trans hq) hcollision
  have hnineteen := nineteen_dvd_opcode_of_norm_seven_collision
    (hnineteenR.trans hy) (hnineteenR.trans hq) hcollision
  exact (by norm_num : Nat.Coprime 5 19).mul_dvd_of_dvd_of_dvd
    hfive hnineteen

/-- Algebraic DO4 before expanding `A,B,C,D` into powers of two and three. -/
theorem normalized_payload_recurrence
    {m h g : ℕ} {y q r r' : ℤ}
    (hy : y = A ^ g * registerOdd * r)
    (hq : q = registerOdd * r')
    (hcollision : C ^ m * (y + 1) = D ^ m * (1 + B ^ h * q)) :
    D ^ m * B ^ h * r' = C ^ m * A ^ g * r + opcodeDebris m := by
  have hfactor := opcodeDebris_factor m
  have hscaled : registerOdd * (D ^ m * B ^ h * r') =
      registerOdd * (C ^ m * A ^ g * r + opcodeDebris m) := by
    rw [hy, hq] at hcollision
    linear_combination -hcollision - hfactor
  exact mul_left_cancel₀ (by norm_num [registerOdd, C, D]) hscaled

/-- DO4 in its literal power-of-two/power-of-three form. -/
theorem normalized_payload_recurrence_powers
    {m h g : ℕ} {y q r r' : ℤ}
    (hy : y = A ^ g * registerOdd * r)
    (hq : q = registerOdd * r')
    (hcollision : C ^ m * (y + 1) = D ^ m * (1 + B ^ h * q)) :
    (2 : ℤ) ^ (23 * m + 154 * h) * r' =
      (3 : ℤ) ^ (17 * m + 114 * g) * r + opcodeDebris m := by
  have hrec := normalized_payload_recurrence hy hq hcollision
  simpa [A, B, C, D, pow_add, pow_mul, mul_assoc] using hrec

/-- The normalized recurrence extracted directly from an accepted semantic
step.  The coordinate residuals may be signed, but the public input and odd
quotient are the actual natural fields of `s`. -/
theorem accepted_step_normalized_payload_recurrence
    (s : ChargeBouncerStep) {g : ℕ} {r r' : ℤ}
    (hy : (s.input : ℤ) = A ^ g * registerOdd * r)
    (hq : (s.oddPart : ℤ) = registerOdd * r') :
    (2 : ℤ) ^ (23 * s.defectOpcode + 154 * s.rechargeCount) * r' =
      (3 : ℤ) ^ (17 * s.defectOpcode + 114 * g) * r +
        opcodeDebris s.defectOpcode := by
  have hcollision :
      C ^ s.defectOpcode * ((s.input : ℤ) + 1) =
        D ^ s.defectOpcode * (1 + B ^ s.rechargeCount * (s.oddPart : ℤ)) := by
    have hs := congrArg (fun n : ℕ ↦ (n : ℤ)) s.rearranged
    simpa [B, C, D, pow_mul] using hs
  exact normalized_payload_recurrence_powers hy hq hcollision

/-- A collision length of 153 cannot contain even the shortest positive
defect and positive recharge blocks.  This is the arithmetic reason the first
recorded `N_31` transition is not a two-step chain. -/
theorem no_positive_defect_recharge_at_153
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) :
    23 * m + 154 * h ≠ 153 := by
  omega

end ChargeNormOpcode

end KontoroC
