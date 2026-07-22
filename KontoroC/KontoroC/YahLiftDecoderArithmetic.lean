/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRegisterDrainNoGo

/-!
# Arithmetic core of the first YAH lift-register decoder

At charge `K=5`, use the phase-one address `q(t)=17+128t`.  This file defines
the stripped register from the already verified normalized recharge register
and proves its division-free value equation and low-bit decoder law.

The word-level lasso identities and the claimed return from the bit-one chart
are separate obligations.
-/

namespace KontoroC
namespace YahLiftDecoderArithmetic

open YahRechargeRegister

def decoderExponent (t : ℕ) : ℕ := 17 + 128 * t

/-- Nine times this quantity is the `K=5` normalized register. -/
def decoderRegister (t : ℕ) : ℕ := normalizedRegister 5 17 t / 9

theorem decoder_base_dvd : 2 ^ 10 ∣ rawRegister 5 17 0 := by
  norm_num [rawRegister]

theorem decoder_raw_dvd (t : ℕ) : 2 ^ 10 ∣ rawRegister 5 17 t := by
  simpa using rawRegister_dvd_of_base 5 17 t decoder_base_dvd

theorem nine_dvd_raw (t : ℕ) : 9 ∣ rawRegister 5 17 t := by
  refine ⟨123 * 9 ^ (16 + 128 * t) + 5, ?_⟩
  simp only [rawRegister]
  rw [show 17 + 2 ^ (5 + 2) * t = (16 + 128 * t) + 1 by
    norm_num
    omega]
  rw [pow_succ]
  ring

theorem nine_dvd_normalized (t : ℕ) :
    9 ∣ normalizedRegister 5 17 t := by
  have htwo := decoder_raw_dvd t
  have hnine := nine_dvd_raw t
  have hcop : Nat.Coprime 9 (2 ^ 10) := by norm_num
  have hproduct : 9 * 2 ^ 10 ∣ rawRegister 5 17 t :=
    hcop.mul_dvd_of_dvd_of_dvd hnine htwo
  exact (Nat.dvd_div_iff_mul_dvd htwo).2 hproduct

theorem normalized_eq_nine_mul_decoderRegister (t : ℕ) :
    normalizedRegister 5 17 t = 9 * decoderRegister t := by
  exact (Nat.mul_div_cancel' (nine_dvd_normalized t)).symm

/-- QM20, with no division in the proposition. -/
theorem decoderRegister_value (t : ℕ) :
    3 * 2 ^ 10 * decoderRegister t =
      41 * 9 ^ decoderExponent t + 15 := by
  have hraw := Nat.mul_div_cancel' (decoder_raw_dvd t)
  change 2 ^ 10 * normalizedRegister 5 17 t = rawRegister 5 17 t at hraw
  rw [normalized_eq_nine_mul_decoderRegister] at hraw
  simp only [rawRegister] at hraw
  simp only [decoderExponent]
  norm_num at hraw ⊢
  omega

private theorem normalized_strict (t : ℕ) :
    normalizedRegister 5 17 t < normalizedRegister 5 17 (t + 1) := by
  have hsub := rawRegister_sub 5 17 t (t + 1) (by omega)
  have hfactor : 0 < 9 ^ (2 ^ (5 + 2) * ((t + 1) - t)) - 1 := by
    norm_num
  have hsubpos : 0 < rawRegister 5 17 (t + 1) - rawRegister 5 17 t := by
    rw [hsub]
    exact Nat.mul_pos (by positivity) hfactor
  have hrawlt : rawRegister 5 17 t < rawRegister 5 17 (t + 1) := by omega
  have ht := Nat.mul_div_cancel' (decoder_raw_dvd t)
  have hs := Nat.mul_div_cancel' (decoder_raw_dvd (t + 1))
  change 2 ^ 10 * normalizedRegister 5 17 t = rawRegister 5 17 t at ht
  change 2 ^ 10 * normalizedRegister 5 17 (t + 1) =
    rawRegister 5 17 (t + 1) at hs
  norm_num at ht hs
  omega

private theorem normalized_step_odd (t : ℕ) :
    (normalizedRegister 5 17 (t + 1) -
      normalizedRegister 5 17 t) % 2 = 1 := by
  have hv := normalizedRegister_isometry_of_base 5 17 t (t + 1)
    (by omega) decoder_base_dvd
  have hv0 : padicValNat 2
      (normalizedRegister 5 17 (t + 1) -
        normalizedRegister 5 17 t) = 0 := by
    simpa [padicValNat.eq_zero_of_not_dvd] using hv
  have hdiff : normalizedRegister 5 17 (t + 1) -
      normalizedRegister 5 17 t ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (normalized_strict t)
  have hnotdvd : ¬ 2 ∣
      normalizedRegister 5 17 (t + 1) -
        normalizedRegister 5 17 t := by
    rcases (padicValNat.eq_zero_iff.mp hv0) with h | h | h
    · norm_num at h
    · exact (hdiff h).elim
    · exact h
  rw [Nat.dvd_iff_mod_eq_zero] at hnotdvd
  have hlt := Nat.mod_lt
    (normalizedRegister 5 17 (t + 1) - normalizedRegister 5 17 t)
    (by omega : 0 < 2)
  omega

theorem normalizedRegister_parity (t : ℕ) :
    normalizedRegister 5 17 t % 2 = t % 2 := by
  induction t with
  | zero => norm_num [normalizedRegister, rawRegister]
  | succ t ih =>
      have hlt := normalized_strict t
      have hsplit := Nat.sub_add_cancel hlt.le
      have hodd := normalized_step_odd t
      omega

/-- QM21: the physical register exposes exactly the low bit of the free lift
parameter. -/
theorem decoderRegister_parity (t : ℕ) :
    decoderRegister t % 2 = t % 2 := by
  have hnine := normalized_eq_nine_mul_decoderRegister t
  have hparity := normalizedRegister_parity t
  omega

theorem decoderRegister_pos (t : ℕ) : 0 < decoderRegister t := by
  have hvalue := decoderRegister_value t
  have hrhs : 0 < 41 * 9 ^ decoderExponent t + 15 := by positivity
  norm_num only [Nat.reducePow] at hvalue
  omega

/-- The original decoder registers form a strictly increasing discrete
chart. -/
theorem decoderRegister_strictMono : StrictMono decoderRegister := by
  intro s t hst
  have hexp : decoderExponent s < decoderExponent t := by
    simp only [decoderExponent]
    omega
  have hpow : 9 ^ decoderExponent s < 9 ^ decoderExponent t :=
    Nat.pow_lt_pow_right (by omega) hexp
  have hs := decoderRegister_value s
  have ht := decoderRegister_value t
  norm_num only [Nat.reducePow] at hs ht
  omega

/-- The stripped decoder register retains the full two-adic isometry of the
normalized recharge register. -/
theorem decoderRegister_sub_val (u t : ℕ) (hut : u < t) :
    padicValNat 2 (decoderRegister t - decoderRegister u) =
      padicValNat 2 (t - u) := by
  have hv := normalizedRegister_isometry_of_base 5 17 u t hut
    decoder_base_dvd
  have hu := normalized_eq_nine_mul_decoderRegister u
  have ht := normalized_eq_nine_mul_decoderRegister t
  have hmono := decoderRegister_strictMono hut
  have hsub : normalizedRegister 5 17 t - normalizedRegister 5 17 u =
      9 * (decoderRegister t - decoderRegister u) := by
    rw [hu, ht]
    omega
  have hdiff : decoderRegister t - decoderRegister u ≠ 0 :=
    Nat.sub_ne_zero_of_lt hmono
  rw [hsub, padicValNat.mul (by norm_num) hdiff,
    padicValNat.eq_zero_of_not_dvd (by norm_num), zero_add] at hv
  exact hv

end YahLiftDecoderArithmetic
end KontoroC
