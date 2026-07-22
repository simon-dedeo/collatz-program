/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeStatePowerRoth

/-!
# The hidden fixed-divisor register

This file formalizes necessary algebra for the hidden `F`-adic register behind
public-state 23rd-power transitions.  It does not construct an ordinary
Collatz transition or an infinite orbit.
-/

namespace KontoroC

namespace ChargeHiddenRegister

open ChargePowerQuine ChargeStatePowerQuine

/-- Taylor tail after the constant and linear terms of `Q(-1+u)`. -/
def cofactorTaylorTail (u : ℤ) : ℤ :=
  1771 - 8855 * u + 33649 * u ^ 2 - 100947 * u ^ 3 +
    245157 * u ^ 4 - 490314 * u ^ 5 + 817190 * u ^ 6 -
    1144066 * u ^ 7 + 1352078 * u ^ 8 - 1352078 * u ^ 9 +
    1144066 * u ^ 10 - 817190 * u ^ 11 + 490314 * u ^ 12 -
    245157 * u ^ 13 + 100947 * u ^ 14 - 33649 * u ^ 15 +
    8855 * u ^ 16 - 1771 * u ^ 17 + 253 * u ^ 18 - 23 * u ^ 19 +
    u ^ 20

set_option maxHeartbeats 10000000 in
-- Expanding both fixed degree-22 polynomials requires substantial normalization.
/-- Exact Taylor expansion `Q(-1+u)=23-253u+u²R(u)`. -/
theorem plusCofactor_at_negOne_add (u : ℤ) :
    plusCofactor (-1 + u) = 23 - 253 * u + u ^ 2 * cofactorTaylorTail u := by
  norm_num [plusCofactor, cofactorTaylorTail, Finset.sum_range_succ]
  ring

/-- The first-order Taylor approximation is exact modulo `F²`. -/
theorem fixedDivisor_sq_dvd_cofactor_taylor_error (d w : ℤ) :
    F ^ 2 ∣ plusCofactor (-1 + F * d * w) -
      (23 - 253 * F * d * w) := by
  rw [plusCofactor_at_negOne_add]
  refine ⟨(d * w) ^ 2 * cofactorTaylorTail (F * d * w), ?_⟩
  ring

private theorem dvd_of_sq_dvd_mul_self
    {f x : ℤ} (hf : f ≠ 0) (h : f ^ 2 ∣ f * x) : f ∣ x := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ hf
  calc
    f * x = f ^ 2 * k := hk
    _ = f * (f * k) := by ring

/-- HF3: the first nonlinear carry forced by the cofactor collision balance. -/
theorem collision_first_carry
    {m : ℕ} {w v delta : ℤ}
    (hv : v = w + F * delta)
    (hbal : w * plusCofactor (-1 + F * D ^ m * w) =
      v * plusCofactor (-1 + F * C ^ m * v)) :
    F ∣ delta - 11 * (C ^ m - D ^ m) * w ^ 2 := by
  let qs : ℤ := 23 - 253 * F * D ^ m * w
  let qz : ℤ := 23 - 253 * F * C ^ m * v
  have hQsDvd := fixedDivisor_sq_dvd_cofactor_taylor_error (D ^ m) w
  have hQzDvd := fixedDivisor_sq_dvd_cofactor_taylor_error (C ^ m) v
  have hQs : plusCofactor (-1 + F * D ^ m * w) ≡ qs [ZMOD F ^ 2] := by
    exact ((Int.modEq_iff_dvd.mpr hQsDvd).symm)
  have hQz : plusCofactor (-1 + F * C ^ m * v) ≡ qz [ZMOD F ^ 2] := by
    exact ((Int.modEq_iff_dvd.mpr hQzDvd).symm)
  have hleft := (Int.ModEq.refl w).mul hQs
  have hright := (Int.ModEq.refl v).mul hQz
  have hbalMod : w * plusCofactor (-1 + F * D ^ m * w) ≡
      v * plusCofactor (-1 + F * C ^ m * v) [ZMOD F ^ 2] := by
    rw [hbal]
  have happrox : w * qs ≡ v * qz [ZMOD F ^ 2] :=
    hleft.symm.trans (hbalMod.trans hright)
  have hraw : F ^ 2 ∣ v * qz - w * qs :=
    Int.modEq_iff_dvd.mp happrox
  let target : ℤ := delta - 11 * (C ^ m - D ^ m) * w ^ 2
  have hrem : F ^ 2 ∣ (v * qz - w * qs) - F * 23 * target := by
    refine ⟨-506 * C ^ m * w * delta - 253 * F * C ^ m * delta ^ 2, ?_⟩
    dsimp [qs, qz, target]
    rw [hv]
    ring
  have hscaled : F ^ 2 ∣ F * (23 * target) := by
    simpa only [sub_sub_cancel, mul_assoc] using dvd_sub hraw hrem
  have htwentyThree : F ∣ 23 * target :=
    dvd_of_sq_dvd_mul_self (by norm_num [F, chargeFixedDivisor]) hscaled
  exact fixedDivisor_isCoprime_twentyThree.dvd_of_dvd_mul_left htwentyThree

/-- The geometric quotient `(A^ell-B^ell)/(A-B)`, defined integrally. -/
def geomS : ℕ → ℤ
  | 0 => 0
  | n + 1 => A ^ n + B * geomS n

theorem geomS_factor (ell : ℕ) :
    (A - B) * geomS ell = A ^ ell - B ^ ell := by
  induction ell with
  | zero => simp [geomS]
  | succ n ih =>
      simp only [geomS]
      calc
        (A - B) * (A ^ n + B * geomS n) =
            A ^ (n + 1) - B ^ (n + 1) +
              B * ((A - B) * geomS n - (A ^ n - B ^ n)) := by
                rw [pow_succ, pow_succ]
                ring
        _ = A ^ (n + 1) - B ^ (n + 1) := by rw [ih]; ring

theorem A_modEq_B : A ≡ B [ZMOD F] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-5, ?_⟩
  linear_combination -A_sub_B

/-- At the register precision, the geometric quotient is its repeated root
value `ell * B^(ell-1)`. -/
theorem geomS_modEq (n : ℕ) :
    geomS (n + 1) ≡ ((n + 1 : ℕ) : ℤ) * B ^ n [ZMOD F] := by
  induction n with
  | zero => simp [geomS]
  | succ n ih =>
      have hp := A_modEq_B.pow (n + 1)
      have hm := (Int.ModEq.refl B).mul ih
      have hadd := hp.add hm
      convert hadd using 1 <;>
        simp [geomS, Nat.cast_succ, pow_succ, mul_assoc, mul_comm,
          add_comm, add_left_comm] <;> ring

theorem fixedDivisor_dvd_geomS_sub
    {ell : ℕ} (hell : 0 < ell) :
    F ∣ geomS ell - (ell : ℤ) * B ^ (ell - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  have h := geomS_modEq n
  rw [Int.modEq_iff_dvd] at h
  exact dvd_neg.mp (by simpa using h)

/-- Exact output relation HF4. -/
theorem hidden_output_identity
    {ell m m' : ℕ} {s' t v w' : ℤ}
    (hs' : s' = A ^ ell * t)
    (hin : B ^ ell * t + 1 = C ^ m * F * v)
    (hout : s' + 1 = D ^ m' * F * w') :
    D ^ m' * w' = C ^ m * v + 5 * geomS ell * t := by
  have hdiff : D ^ m' * F * w' - C ^ m * F * v =
      (A ^ ell - B ^ ell) * t := by
    rw [← hout, ← hin, hs']
    ring
  have hfactor := geomS_factor ell
  rw [A_sub_B] at hfactor
  have hcommon : F * (D ^ m' * w') =
      F * (C ^ m * v + 5 * geomS ell * t) := by
    linear_combination hdiff - t * hfactor
  exact mul_left_cancel₀ (by norm_num [F, chargeFixedDivisor]) hcommon

/-- First-digit form HF5 as a modular equality. -/
theorem hidden_first_digit_modEq
    {ell m m' : ℕ} {t v w w' : ℤ}
    (hell : 0 < ell)
    (hvw : v ≡ w [ZMOD F])
    (hz : B ^ ell * t ≡ -1 [ZMOD F])
    (hstep : D ^ m' * w' = C ^ m * v + 5 * geomS ell * t) :
    B * D ^ m' * w' ≡ B * C ^ m * w - 5 * (ell : ℤ) [ZMOD F] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  have hS := geomS_modEq n
  have hSt := (hS.mul_left B).mul_right t
  have hzEll := hz.mul_left ((n + 1 : ℕ) : ℤ)
  have hStNeg : B * geomS (n + 1) * t ≡ -((n + 1 : ℕ) : ℤ) [ZMOD F] := by
    apply hSt.trans
    simpa [pow_succ, Nat.cast_succ, mul_assoc, mul_comm, mul_left_comm] using hzEll
  have hvTerm := hvw.mul_left (B * C ^ m)
  have hfive := hStNeg.mul_left 5
  have hadd := hvTerm.add hfive
  have hadd' : B * (C ^ m * v + 5 * geomS (n + 1) * t) ≡
      B * C ^ m * w - 5 * ((n + 1 : ℕ) : ℤ) [ZMOD F] := by
    convert hadd using 1 <;> ring
  have hstepMod : B * D ^ m' * w' ≡
      B * (C ^ m * v + 5 * geomS (n + 1) * t) [ZMOD F] := by
    rw [← hstep]
    simp [mul_assoc]
  exact hstepMod.trans hadd'

theorem fixedDivisor_dvd_hidden_first_digit
    {ell m m' : ℕ} {t v w w' : ℤ}
    (hell : 0 < ell)
    (hvw : v ≡ w [ZMOD F])
    (hz : B ^ ell * t ≡ -1 [ZMOD F])
    (hstep : D ^ m' * w' = C ^ m * v + 5 * geomS ell * t) :
    F ∣ B * D ^ m' * w' - (B * C ^ m * w - 5 * (ell : ℤ)) := by
  have h := hidden_first_digit_modEq hell hvw hz hstep
  rw [Int.modEq_iff_dvd] at h
  exact dvd_neg.mp (by simpa using h)

theorem fixedDivisor_isCoprime_five : IsCoprime F (5 : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  norm_num [F, chargeFixedDivisor]

/-- Multiplication by five is a bijection on residue classes modulo `F`,
expressed without choosing a modular inverse. -/
theorem five_register_write_exists_unique (rhs : ℤ) :
    ∃ ell : ℤ, 5 * ell ≡ rhs [ZMOD F] ∧
      ∀ ell' : ℤ, 5 * ell' ≡ rhs [ZMOD F] → ell' ≡ ell [ZMOD F] := by
  rcases fixedDivisor_isCoprime_five with ⟨a, b, hab⟩
  have hex : 5 * (b * rhs) ≡ rhs [ZMOD F] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨a * rhs, ?_⟩
    calc
      rhs - 5 * (b * rhs) = (a * F + b * 5) * rhs - 5 * (b * rhs) := by
        rw [hab, one_mul]
      _ = F * (a * rhs) := by ring
  refine ⟨b * rhs, ?_, ?_⟩
  · exact hex
  · intro ell' hell'
    have hfive : 5 * ell' ≡ 5 * (b * rhs) [ZMOD F] :=
      hell'.trans hex.symm
    rw [Int.modEq_iff_dvd] at hfive ⊢
    have hmul : F ∣ 5 * (b * rhs - ell') := by
      convert hfive using 1 <;> ring
    exact fixedDivisor_isCoprime_five.dvd_of_dvd_mul_left hmul

/-- HF6: every desired first hidden-register output has one recharge class
modulo `F`.  This is a residue-class statement only; it does not assert that
the class realizes the exact Collatz valuation decoder. -/
theorem hidden_recharge_class_exists_unique
    (m m' : ℕ) (r r' : ℤ) :
    ∃ ell : ℤ,
      5 * ell ≡ B * (C ^ m * r - D ^ m' * r') [ZMOD F] ∧
      ∀ ell' : ℤ,
        5 * ell' ≡ B * (C ^ m * r - D ^ m' * r') [ZMOD F] →
          ell' ≡ ell [ZMOD F] :=
  five_register_write_exists_unique _

end ChargeHiddenRegister

end KontoroC
