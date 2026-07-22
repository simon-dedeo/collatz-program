/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahFiniteAmplifier

/-!
# The YAH recharge lift is a lossless dyadic register

This file proves QM18 from mathlib's lifting-the-exponent theorem.  The raw
register is

`3 * (41 * 9^(q₀ + 2^(K+2)t) + 15)`.

If its base address is divisible by `2^(K+5)`, every lift is divisible by the
same power.  After normalization, the exact dyadic valuation of the
difference between two outputs is the valuation of the difference between
their lift parameters.
-/

namespace KontoroC
namespace YahRechargeRegister

/-- The specialized LTE calculation behind the register. -/
theorem nine_pow_twoPow_mul_sub_one_val (K d : ℕ) (hd : 0 < d) :
    padicValNat 2 (9 ^ (2 ^ (K + 2) * d) - 1) =
      K + 5 + padicValNat 2 d := by
  let n := 2 ^ (K + 2) * d
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hneven : Even n := by
    rw [even_iff_two_dvd]
    dsimp [n]
    exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega)) d
  have hLTE := padicValNat.pow_two_sub_one
    (x := 9) (n := n) (by omega) (by norm_num) hn hneven
  have h10 : padicValNat 2 10 = 1 := by
    rw [show 10 = 2 ^ 1 * 5 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    norm_num [padicValNat.eq_zero_of_not_dvd]
  have h8 : padicValNat 2 8 = 3 := by
    rw [show 8 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  norm_num only at hLTE
  rw [h10, h8] at hLTE
  have hvaln : padicValNat 2 n = K + 2 + padicValNat 2 d := by
    dsimp [n]
    rw [padicValNat.mul (by positivity) hd.ne', padicValNat.prime_pow]
  dsimp [n] at hLTE hvaln
  omega

def rawRegister (K q₀ t : ℕ) : ℕ :=
  3 * (41 * 9 ^ (q₀ + 2 ^ (K + 2) * t) + 15)

def normalizedRegister (K q₀ t : ℕ) : ℕ :=
  rawRegister K q₀ t / 2 ^ (K + 5)

theorem rawRegister_mono (K q₀ : ℕ) : Monotone (rawRegister K q₀) := by
  intro u t hut
  dsimp [rawRegister]
  have he : q₀ + 2 ^ (K + 2) * u ≤ q₀ + 2 ^ (K + 2) * t :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hut) _
  have hp := Nat.pow_le_pow_right (by omega : 0 < 9) he
  omega

theorem rawRegister_sub (K q₀ u t : ℕ) (hut : u < t) :
    rawRegister K q₀ t - rawRegister K q₀ u =
      (3 * 41 * 9 ^ (q₀ + 2 ^ (K + 2) * u)) *
        (9 ^ (2 ^ (K + 2) * (t - u)) - 1) := by
  let L := 2 ^ (K + 2)
  have ht : t = u + (t - u) := by omega
  have hexp : q₀ + L * t = (q₀ + L * u) + L * (t - u) := by
    nth_rewrite 1 [ht]
    ring
  have hmono := rawRegister_mono K q₀ hut.le
  apply (Nat.sub_eq_iff_eq_add' hmono).2
  dsimp [rawRegister]
  dsimp [L] at hexp
  rw [hexp, pow_add]
  let Q := 9 ^ (2 ^ (K + 2) * (t - u))
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ (by omega)
  have hQsplit : Q = (Q - 1) + 1 := (Nat.sub_add_cancel hQ).symm
  change 3 * (41 * (9 ^ (q₀ + 2 ^ (K + 2) * u) * Q) + 15) = _
  rw [hQsplit]
  ring

theorem rawRegister_sub_val (K q₀ u t : ℕ) (hut : u < t) :
    padicValNat 2 (rawRegister K q₀ t - rawRegister K q₀ u) =
      K + 5 + padicValNat 2 (t - u) := by
  rw [rawRegister_sub K q₀ u t hut]
  let A := 3 * 41 * 9 ^ (q₀ + 2 ^ (K + 2) * u)
  let X := 9 ^ (2 ^ (K + 2) * (t - u)) - 1
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have htu : 0 < t - u := by omega
  have hexppos : 0 < 2 ^ (K + 2) * (t - u) :=
    Nat.mul_pos (by positivity) htu
  have hpow : 1 < 9 ^ (2 ^ (K + 2) * (t - u)) :=
    one_lt_pow₀ (by omega) hexppos.ne'
  have hX : X ≠ 0 := by dsimp [X]; omega
  rw [padicValNat.mul hA hX]
  have hpowodd : 9 ^ (q₀ + 2 ^ (K + 2) * u) % 2 = 1 := by
    norm_num [Nat.pow_mod]
  have hAodd : ¬2 ∣ A := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [A]
    omega
  rw [padicValNat.eq_zero_of_not_dvd hAodd, zero_add]
  exact nine_pow_twoPow_mul_sub_one_val K (t - u) htu

/-- Every lift remains integral once the base recharge address is integral. -/
theorem rawRegister_dvd_of_base (K q₀ t : ℕ)
    (hbase : 2 ^ (K + 5) ∣ rawRegister K q₀ 0) :
    2 ^ (K + 5) ∣ rawRegister K q₀ t := by
  by_cases ht : t = 0
  · simpa [ht] using hbase
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hv := rawRegister_sub_val K q₀ 0 t htpos
    have hdiffne : rawRegister K q₀ t - rawRegister K q₀ 0 ≠ 0 := by
      rw [rawRegister_sub K q₀ 0 t htpos]
      apply Nat.mul_ne_zero (by positivity)
      apply Nat.sub_ne_zero_of_lt
      apply one_lt_pow₀ (by omega)
      exact (Nat.mul_pos (by positivity) htpos).ne'
    have hdiff : 2 ^ (K + 5) ∣
        rawRegister K q₀ t - rawRegister K q₀ 0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by omega) hdiffne).mpr (by omega)
    have hadd := hdiff.add hbase
    have hmono := rawRegister_mono K q₀ (Nat.zero_le t)
    simpa [Nat.sub_add_cancel hmono] using hadd

private theorem normalizedRegister_sub_eq_quotient (K q₀ u t : ℕ)
    (hut : u < t)
    (hu : 2 ^ (K + 5) ∣ rawRegister K q₀ u)
    (ht : 2 ^ (K + 5) ∣ rawRegister K q₀ t) :
    normalizedRegister K q₀ t - normalizedRegister K q₀ u =
      (rawRegister K q₀ t - rawRegister K q₀ u) / 2 ^ (K + 5) := by
  let P := 2 ^ (K + 5)
  have hP : 0 < P := by dsimp [P]; positivity
  have hmono := rawRegister_mono K q₀ hut.le
  have hdivu : P ∣ rawRegister K q₀ u := by simpa [P] using hu
  have hdivt : P ∣ rawRegister K q₀ t := by simpa [P] using ht
  have heu : P * (rawRegister K q₀ u / P) = rawRegister K q₀ u :=
    Nat.mul_div_cancel' hdivu
  have het : P * (rawRegister K q₀ t / P) = rawRegister K q₀ t :=
    Nat.mul_div_cancel' hdivt
  have hregmono : rawRegister K q₀ u / P ≤ rawRegister K q₀ t / P :=
    Nat.div_le_div_right hmono
  have hmul : P * (rawRegister K q₀ t / P - rawRegister K q₀ u / P) =
      rawRegister K q₀ t - rawRegister K q₀ u := by
    rw [Nat.mul_sub_left_distrib, heu, het]
  dsimp [normalizedRegister]
  dsimp [P] at hmul ⊢
  rw [← hmul, Nat.mul_div_cancel_left _ hP]

/-- QM18: the normalized recharge register preserves the exact dyadic
distance between two distinct lift parameters. -/
theorem normalizedRegister_sub_val (K q₀ u t : ℕ) (hut : u < t)
    (hu : 2 ^ (K + 5) ∣ rawRegister K q₀ u)
    (ht : 2 ^ (K + 5) ∣ rawRegister K q₀ t) :
    padicValNat 2
        (normalizedRegister K q₀ t - normalizedRegister K q₀ u) =
      padicValNat 2 (t - u) := by
  rw [normalizedRegister_sub_eq_quotient K q₀ u t hut hu ht]
  have hv := rawRegister_sub_val K q₀ u t hut
  have hdiffne : rawRegister K q₀ t - rawRegister K q₀ u ≠ 0 := by
    rw [rawRegister_sub K q₀ u t hut]
    apply Nat.mul_ne_zero (by positivity)
    apply Nat.sub_ne_zero_of_lt
    apply one_lt_pow₀ (by omega)
    exact (Nat.mul_pos (by positivity) (by omega : 0 < t - u)).ne'
  have hdvd : 2 ^ (K + 5) ∣
      rawRegister K q₀ t - rawRegister K q₀ u :=
    (Nat.pow_dvd_iff_le_padicValNat (by omega) hdiffne).mpr (by omega)
  rw [padicValNat.div_pow hdvd, hv]
  omega

/-- The convenient base-address wrapper: one QM15 divisibility hypothesis
makes the whole normalized lift an isometry. -/
theorem normalizedRegister_isometry_of_base (K q₀ u t : ℕ) (hut : u < t)
    (hbase : 2 ^ (K + 5) ∣ rawRegister K q₀ 0) :
    padicValNat 2
        (normalizedRegister K q₀ t - normalizedRegister K q₀ u) =
      padicValNat 2 (t - u) := by
  exact normalizedRegister_sub_val K q₀ u t hut
    (rawRegister_dvd_of_base K q₀ u hbase)
    (rawRegister_dvd_of_base K q₀ t hbase)

end YahRechargeRegister
end KontoroC
