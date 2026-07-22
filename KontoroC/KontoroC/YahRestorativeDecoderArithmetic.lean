/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRestorativeLoopNoGo

/-!
# Arithmetic of the first YAH restorative decoder chart

This file checks the arithmetic part of QM26--QM30.  It deliberately does not
identify the returned word with the original decoder chart; the preceding
separation theorem proves that such an identification is impossible.
-/

namespace KontoroC
namespace YahRestorativeDecoderArithmetic

open YahRechargeRegister YahLiftDecoderArithmetic

def restorativeIndex (u : ℕ) : ℕ := 91 + 256 * u

def restorativeExponent (u : ℕ) : ℕ :=
  decoderExponent (restorativeIndex u)

def incomingRegister (u : ℕ) : ℕ :=
  decoderRegister (restorativeIndex u)

def returnedRegister (u : ℕ) : ℕ :=
  (3 ^ 6 * incomingRegister u + 1) / 2 ^ 8

theorem restorativeExponent_eq (u : ℕ) :
    restorativeExponent u = 11665 + 32768 * u := by
  simp [restorativeExponent, restorativeIndex, decoderExponent]
  ring

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
private theorem base_rhs_mod :
    (41 * 9 ^ 11665 + 15) % 786432 = 463872 := by
  decide

set_option maxRecDepth 100000 in
private theorem incomingRegister_base_mod : incomingRegister 0 % 256 = 151 := by
  have hvalue := decoderRegister_value 91
  change decoderRegister 91 % 256 = 151
  change 3072 * decoderRegister 91 = 41 * 9 ^ 11665 + 15 at hvalue
  have hmod := congrArg (fun n : ℕ => n % 786432) hvalue
  rw [base_rhs_mod] at hmod
  have hfactor : (3072 * decoderRegister 91) % 786432 =
      3072 * (decoderRegister 91 % 256) :=
    Nat.mul_mod_mul_left 3072 (decoderRegister 91) 256
  rw [hfactor] at hmod
  omega

/-- Restricting the original decoder isometry to `t=91+256u` adds exactly
eight powers of two to parameter differences. -/
theorem incomingRegister_sub_val (u t : ℕ) (hut : u < t) :
    padicValNat 2 (incomingRegister t - incomingRegister u) =
      8 + padicValNat 2 (t - u) := by
  have hindex : restorativeIndex u < restorativeIndex t := by
    simp only [restorativeIndex]
    omega
  have hv := decoderRegister_sub_val
    (restorativeIndex u) (restorativeIndex t) hindex
  have hsub : restorativeIndex t - restorativeIndex u = 256 * (t - u) := by
    simp only [restorativeIndex]
    omega
  rw [hsub, show 256 = 2 ^ 8 by norm_num,
    padicValNat.mul (by positivity) (Nat.sub_ne_zero_of_lt hut),
    padicValNat.prime_pow] at hv
  simpa only [incomingRegister] using hv

theorem incomingRegister_strictMono : StrictMono incomingRegister := by
  intro u t hut
  apply decoderRegister_strictMono
  simp only [restorativeIndex]
  omega

/-- QM27's source cylinder, proved for every lift rather than sampled. -/
theorem incomingRegister_mod (u : ℕ) : incomingRegister u % 256 = 151 := by
  by_cases hu : u = 0
  · simpa [hu] using incomingRegister_base_mod
  · have hu_pos : 0 < u := Nat.pos_of_ne_zero hu
    have hmono := incomingRegister_strictMono hu_pos
    have hdiffne : incomingRegister u - incomingRegister 0 ≠ 0 :=
      Nat.sub_ne_zero_of_lt hmono
    have hval := incomingRegister_sub_val 0 u hu_pos
    have hdvd : 2 ^ 8 ∣ incomingRegister u - incomingRegister 0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiffne).2 (by omega)
    have hmodzero := (Nat.dvd_iff_mod_eq_zero.mp hdvd)
    norm_num only [Nat.reducePow] at hmodzero
    have hsplit := Nat.sub_add_cancel hmono.le
    rw [← hsplit, Nat.add_mod, hmodzero, incomingRegister_base_mod]

theorem restorative_numerator_dvd (u : ℕ) :
    2 ^ 8 ∣ 3 ^ 6 * incomingRegister u + 1 := by
  let q := incomingRegister u / 256
  have hsplit := Nat.mod_add_div (incomingRegister u) 256
  rw [incomingRegister_mod] at hsplit
  refine ⟨430 + 729 * q, ?_⟩
  dsimp [q]
  omega

/-- Division-free form of the restorative register update. -/
theorem returnedRegister_balance (u : ℕ) :
    2 ^ 8 * returnedRegister u = 3 ^ 6 * incomingRegister u + 1 := by
  exact Nat.mul_div_cancel' (restorative_numerator_dvd u)

theorem returnedRegister_pos (u : ℕ) : 0 < returnedRegister u := by
  have h := returnedRegister_balance u
  have hin := decoderRegister_pos (restorativeIndex u)
  change 0 < incomingRegister u at hin
  norm_num only [Nat.reducePow] at h
  omega

theorem returnedRegister_strictMono : StrictMono returnedRegister := by
  intro u t hut
  have hin := incomingRegister_strictMono hut
  have hu := returnedRegister_balance u
  have ht := returnedRegister_balance t
  norm_num only [Nat.reducePow] at hu ht
  omega

theorem returnedRegister_sub_balance (u t : ℕ) (hut : u < t) :
    2 ^ 8 * (returnedRegister t - returnedRegister u) =
      3 ^ 6 * (incomingRegister t - incomingRegister u) := by
  have hout := returnedRegister_strictMono hut
  have hin := incomingRegister_strictMono hut
  have hu := returnedRegister_balance u
  have ht := returnedRegister_balance t
  norm_num only [Nat.reducePow] at hu ht ⊢
  omega

/-- QM30: the new register is again a two-adic isometry in its free
parameter. -/
theorem returnedRegister_sub_val (u t : ℕ) (hut : u < t) :
    padicValNat 2 (returnedRegister t - returnedRegister u) =
      padicValNat 2 (t - u) := by
  have hout := returnedRegister_strictMono hut
  have hin := incomingRegister_strictMono hut
  have hv := YahBattery.padicVal_of_twoPow_balance
    (k := 8)
    (E := returnedRegister t - returnedRegister u)
    (A := 3 ^ 6)
    (X := incomingRegister t - incomingRegister u)
    (Nat.sub_pos_of_lt hout) (by positivity) (Nat.sub_pos_of_lt hin)
    (by norm_num) (returnedRegister_sub_balance u t hut)
  have hsource := incomingRegister_sub_val u t hut
  omega

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
private theorem base_rhs_mod_512 :
    (41 * 9 ^ 11665 + 15) % 1572864 = 1250304 := by
  decide

set_option maxRecDepth 100000 in
private theorem incomingRegister_base_mod_512 :
    incomingRegister 0 % 512 = 407 := by
  have hvalue := decoderRegister_value 91
  change decoderRegister 91 % 512 = 407
  change 3072 * decoderRegister 91 = 41 * 9 ^ 11665 + 15 at hvalue
  have hmod := congrArg (fun n : ℕ => n % 1572864) hvalue
  rw [base_rhs_mod_512] at hmod
  have hfactor : (3072 * decoderRegister 91) % 1572864 =
      3072 * (decoderRegister 91 % 512) :=
    Nat.mul_mod_mul_left 3072 (decoderRegister 91) 512
  rw [hfactor] at hmod
  omega

private theorem returnedRegister_base_parity : returnedRegister 0 % 2 = 1 := by
  have hsplit := Nat.mod_add_div (incomingRegister 0) 512
  rw [incomingRegister_base_mod_512] at hsplit
  have hbalance := returnedRegister_balance 0
  norm_num only [Nat.reducePow] at hbalance
  omega

private theorem returnedRegister_step_odd (u : ℕ) :
    (returnedRegister (u + 1) - returnedRegister u) % 2 = 1 := by
  have hv := returnedRegister_sub_val u (u + 1) (by omega)
  have hout := returnedRegister_strictMono (show u < u + 1 by omega)
  have hdiff : returnedRegister (u + 1) - returnedRegister u ≠ 0 :=
    Nat.sub_ne_zero_of_lt hout
  have hv0 : padicValNat 2
      (returnedRegister (u + 1) - returnedRegister u) = 0 := by
    simpa [padicValNat.eq_zero_of_not_dvd] using hv
  have hnotdvd : ¬2 ∣ returnedRegister (u + 1) - returnedRegister u := by
    rcases (padicValNat.eq_zero_iff.mp hv0) with h | h | h
    · norm_num at h
    · exact (hdiff h).elim
    · exact h
  rw [Nat.dvd_iff_mod_eq_zero] at hnotdvd
  have hlt := Nat.mod_lt
    (returnedRegister (u + 1) - returnedRegister u) (by omega : 0 < 2)
  omega

theorem returnedRegister_parity (u : ℕ) :
    returnedRegister u % 2 = (u + 1) % 2 := by
  induction u with
  | zero => exact returnedRegister_base_parity
  | succ u ih =>
      have hlt := returnedRegister_strictMono (show u < u + 1 by omega)
      have hsplit := Nat.sub_add_cancel hlt.le
      have hodd := returnedRegister_step_odd u
      omega

end YahRestorativeDecoderArithmetic
end KontoroC
