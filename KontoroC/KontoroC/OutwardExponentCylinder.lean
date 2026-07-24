/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardPowerChargeNoGo

/-!
# The first outward exponent cylinder

This file formalizes the symbolic content of QM160.  It contains no finite
exponent scan and makes no infinite-orbit claim.
-/

namespace KontoroC
namespace OutwardExponentCylinder

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardFirstPassage OutwardBoundaryRenewal

def shallowWord : List Bool :=
  [false, true, false, true, true, true]

theorem shallowWord_length : shallowWord.length = 6 := rfl

theorem shallowWord_oddCount : shallowWord.count true = 4 := rfl

/-- Literal canonical execution of the shallow first-passage word. -/
theorem shallow_base_executes : Executes shallowWord 18 26 := by
  simp only [shallowWord, Executes]
  exact ⟨9, by norm_num,
    ⟨14, by norm_num,
    ⟨7, by norm_num,
    ⟨11, by norm_num,
    ⟨17, by norm_num,
    ⟨26, by norm_num, by norm_num⟩⟩⟩⟩⟩⟩

theorem shallowWord_firstPassage : FirstPassage shallowWord := by
  constructor
  · norm_num [shallowWord, WordOutward]
  · intro u hu
    have hlen : u.length < shallowWord.length := properPrefix_length_lt hu
    have hprefix := hu.1
    rw [List.prefix_iff_eq_take] at hprefix
    rw [hprefix]
    interval_cases u.length <;> norm_num [shallowWord, WordOutward] at hlen ⊢

/-- A natural source executes `010111` exactly when it lies in the dyadic
cylinder `18 mod 64`. -/
theorem exists_shallow_execution_iff_source_modEq (source : ℕ) :
    (∃ target, Executes shallowWord source target) ↔
      source ≡ 18 [MOD 64] := by
  constructor
  · rintro ⟨target, hexec⟩
    simpa [shallowWord_length] using
      (OutwardCylinderRenewal.executes_source_modEq shallowWord
        hexec shallow_base_executes)
  · intro hmod
    have hresidue : source % 64 = 18 := by
      simpa [Nat.ModEq] using hmod
    have hle : 18 ≤ source := by
      have := Nat.mod_le source 64
      omega
    have hdiv : 64 ∣ source - 18 :=
      (Nat.modEq_iff_dvd' hle).1 hmod.symm
    obtain ⟨t, ht⟩ := hdiv
    have hsource : source = 18 + 64 * t := by omega
    refine ⟨26 + 81 * t, ?_⟩
    rw [hsource]
    simpa [shallowWord_length, shallowWord_oddCount] using
      (executes_shift shallowWord shallow_base_executes t)

/-- Multiplication by `3` modulo `64` has period sixteen. -/
theorem three_pow_succ_mod64_period (C : ℕ) :
    3 ^ (C + 1) ≡ 3 ^ (C % 16 + 1) [MOD 64] := by
  let r := C % 16
  let q := C / 16
  have hC : C = r + 16 * q := by
    dsimp [r, q]
    omega
  have hperiod : 3 ^ 16 ≡ 1 [MOD 64] := by norm_num
  have hpow := hperiod.pow q
  have hmul := (Nat.ModEq.refl 64 (3 ^ (r + 1))).mul hpow
  rw [hC]
  simpa [pow_add, pow_mul, mul_assoc] using hmul

/-- QM160a, legality clause: among pure ternary charges, `010111` is legal
exactly on the exponent class `12 mod 16`. -/
theorem exists_shallow_power_execution_iff (C : ℕ) :
    (∃ target, Executes shallowWord (3 * 3 ^ C - 1) target) ↔
      C % 16 = 12 := by
  rw [exists_shallow_execution_iff_source_modEq]
  constructor
  · intro hsource
    have hsourceAdd := hsource.add_right 1
    have hpos : 1 ≤ 3 * 3 ^ C := by positivity
    have hpow : 3 ^ (C + 1) ≡ 19 [MOD 64] := by
      simpa [Nat.sub_add_cancel hpos, pow_succ, mul_comm] using hsourceAdd
    have hresidue : 3 ^ (C % 16 + 1) ≡ 19 [MOD 64] :=
      (three_pow_succ_mod64_period C).symm.trans hpow
    let r := C % 16
    have hr : r < 16 := Nat.mod_lt _ (by omega)
    change 3 ^ (r + 1) ≡ 19 [MOD 64] at hresidue
    change r = 12
    interval_cases r <;> norm_num [Nat.ModEq] at hresidue ⊢
  · intro hC
    have hpow : 3 ^ (C + 1) ≡ 19 [MOD 64] := by
      have hperiod := three_pow_succ_mod64_period C
      rw [hC] at hperiod
      exact hperiod.trans (by norm_num)
    have hsourceAdd : (3 * 3 ^ C - 1) + 1 ≡ 18 + 1 [MOD 64] := by
      have hpos : 1 ≤ 3 * 3 ^ C := by positivity
      simpa [Nat.sub_add_cancel hpos, pow_succ, mul_comm] using hpow
    exact Nat.ModEq.add_right_cancel' 1 hsourceAdd

/-- The exact boundary error in the shallow word is `63`. -/
theorem shallowWord_boundaryError : boundaryError shallowWord = 63 := by
  norm_num [shallowWord, boundaryError, rawDefect, programData,
    accumulate, initialData, ParityData.step]

/-- The fixed multiplier between adjacent points of the exponent cylinder. -/
def shallowGenerator : ℕ := 3 ^ 16

/-- QM160b.  The exact two-adic separation of exponent addresses is linear
in the address precision.  This is an application of LTE, not a finite
valuation table. -/
theorem shallowGenerator_twoPow_sub_one_val (k : ℕ) :
    padicValNat 2 (shallowGenerator ^ (2 ^ k) - 1) = 6 + k := by
  cases k with
  | zero =>
      norm_num [shallowGenerator, padicValNat.eq_zero_of_not_dvd,
        padicValNat.mul, padicValNat.prime_pow]
  | succ k =>
      let n := 2 ^ (k + 1)
      have hn : n ≠ 0 := by dsimp [n]; positivity
      have hneven : Even n := by
        rw [even_iff_two_dvd]
        dsimp [n]
        exact dvd_pow (dvd_refl 2) (by omega)
      have hLTE := padicValNat.pow_two_sub_one
        (x := shallowGenerator) (n := n) (by
          norm_num [shallowGenerator]) (by
          norm_num [shallowGenerator]) hn hneven
      have hplus : padicValNat 2 (shallowGenerator + 1) = 1 := by
        norm_num [shallowGenerator, padicValNat.eq_zero_of_not_dvd,
          padicValNat.mul, padicValNat.prime_pow]
      have hminus : padicValNat 2 (shallowGenerator - 1) = 6 := by
        norm_num [shallowGenerator, padicValNat.eq_zero_of_not_dvd,
          padicValNat.mul, padicValNat.prime_pow]
      have hnval : padicValNat 2 n = k + 1 := by
        dsimp [n]
        rw [padicValNat.prime_pow]
      norm_num only at hLTE
      rw [hplus, hminus, hnval] at hLTE
      simpa [n] using hLTE

/-- The numerator whose extra dyadic valuation is the shallow drain depth. -/
def shallowAddressValue (n : ℕ) : ℕ :=
  3 ^ (14 + 16 * n) + 7

/-- Moving an exponent address by `2^k` has an exact multiplicative
difference. -/
theorem shallowAddressValue_add_twoPow_sub (n k : ℕ) :
    shallowAddressValue (n + 2 ^ k) - shallowAddressValue n =
      3 ^ (14 + 16 * n) * (shallowGenerator ^ (2 ^ k) - 1) := by
  have hexponent :
      14 + 16 * (n + 2 ^ k) = (14 + 16 * n) + 16 * 2 ^ k := by omega
  have hbase :
      3 ^ (14 + 16 * (n + 2 ^ k)) =
        3 ^ (14 + 16 * n) * shallowGenerator ^ (2 ^ k) := by
    rw [hexponent, pow_add, ← pow_mul]
    rfl
  have hone : 1 ≤ shallowGenerator ^ (2 ^ k) := by positivity
  simp only [shallowAddressValue, hbase]
  rw [Nat.add_sub_add_right]
  exact Nat.mul_sub_left_distrib _ _ _

/-- The preceding address difference has precisely the valuation required
for a one-bit Hensel lift. -/
theorem shallowAddressValue_gap_val (n k : ℕ) :
    padicValNat 2
        (shallowAddressValue (n + 2 ^ k) - shallowAddressValue n) =
      6 + k := by
  rw [shallowAddressValue_add_twoPow_sub]
  have hleft : 3 ^ (14 + 16 * n) ≠ 0 := by positivity
  have hright : shallowGenerator ^ (2 ^ k) - 1 ≠ 0 := by
    have hg : 1 < shallowGenerator := by norm_num [shallowGenerator]
    have he : 0 < 2 ^ k := by positivity
    have hp : 1 < shallowGenerator ^ (2 ^ k) :=
      one_lt_pow₀ hg he.ne'
    omega
  rw [padicValNat.mul hleft hright,
    shallowGenerator_twoPow_sub_one_val]
  have hodd : padicValNat 2 (3 ^ (14 + 16 * n)) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod]
  rw [hodd]
  omega

/-- QM160c, local Hensel clause.  If `n` is a solution at precision `k`,
then exactly one of its two children `n` and `n + 2^k` is a solution at the
next precision.  This is the symbolic uniqueness statement used by the
finite worker. -/
theorem shallowAddressValue_unique_child (n k : ℕ)
    (hroot : 2 ^ (6 + k) ∣ shallowAddressValue n) :
    (2 ^ (7 + k) ∣ shallowAddressValue n) ↔
      ¬ (2 ^ (7 + k) ∣ shallowAddressValue (n + 2 ^ k)) := by
  let p := 2 ^ (6 + k)
  let x := shallowAddressValue n
  let y := shallowAddressValue (n + 2 ^ k)
  have hxy : x ≤ y := by
    dsimp [x, y, shallowAddressValue]
    gcongr
    omega
  have hgapNe : y - x ≠ 0 := by
    have hv := shallowAddressValue_gap_val n k
    dsimp [x, y]
    intro hzero
    rw [hzero] at hv
    simp at hv
  have hgapDvd : p ∣ y - x := by
    apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hgapNe).2
    dsimp [p]
    rw [shallowAddressValue_gap_val]
  have hgapNotNext : ¬ 2 ^ (7 + k) ∣ y - x := by
    intro hdvd
    have hv := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hgapNe).1 hdvd
    rw [shallowAddressValue_gap_val] at hv
    omega
  have hxroot : p ∣ x := by simpa [p, x] using hroot
  have hyroot : p ∣ y := by
    have hsum : y = x + (y - x) := (Nat.add_sub_of_le hxy).symm
    rw [hsum]
    exact dvd_add hxroot hgapDvd
  obtain ⟨u, hu⟩ := hxroot
  obtain ⟨v, hv⟩ := hyroot
  have hp : 0 < p := by dsimp [p]; positivity
  have huv : u ≤ v := by
    apply (Nat.mul_le_mul_left p).mp
    simpa [hu, hv, mul_comm] using hxy
  have hgapFactor : y - x = p * (v - u) := by
    rw [hu, hv, Nat.mul_sub_left_distrib]
  have hdiffOdd : ¬ 2 ∣ v - u := by
    intro heven
    obtain ⟨q, hq⟩ := heven
    apply hgapNotNext
    refine ⟨q, ?_⟩
    rw [hgapFactor, hq]
    dsimp [p]
    rw [show 7 + k = (6 + k) + 1 by omega, pow_succ]
    ring
  have hparity : (2 ∣ u) ↔ ¬ (2 ∣ v) := by
    simp only [Nat.dvd_iff_mod_eq_zero] at hdiffOdd ⊢
    omega
  have hxnext : (2 ^ (7 + k) ∣ x) ↔ 2 ∣ u := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have := hq
      rw [hu, show 7 + k = (6 + k) + 1 by omega, pow_succ] at this
      dsimp [p] at this
      exact Nat.eq_of_mul_eq_mul_left hp (by simpa [mul_assoc] using this)
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hu, hq, show 7 + k = (6 + k) + 1 by omega, pow_succ]
      dsimp [p]
      ring
  have hynext : (2 ^ (7 + k) ∣ y) ↔ 2 ∣ v := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have := hq
      rw [hv, show 7 + k = (6 + k) + 1 by omega, pow_succ] at this
      dsimp [p] at this
      exact Nat.eq_of_mul_eq_mul_left hp (by simpa [mul_assoc] using this)
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hv, hq, show 7 + k = (6 + k) + 1 by omega, pow_succ]
      dsimp [p]
      ring
  simpa [x, y, hxnext, hynext] using hparity

/-- The canonical nested address selected one bit at a time by the exact
Hensel test.  This definition computes with arbitrary precision and contains
no bounded search table. -/
def shallowRootAddress : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      if 2 ^ (7 + k) ∣ shallowAddressValue (shallowRootAddress k) then
        shallowRootAddress k
      else
        shallowRootAddress k + 2 ^ k

theorem shallowRootAddress_step (k : ℕ) :
    shallowRootAddress (k + 1) = shallowRootAddress k ∨
      shallowRootAddress (k + 1) = shallowRootAddress k + 2 ^ k := by
  simp only [shallowRootAddress]
  split <;> simp_all

/-- Every recursively selected address satisfies the required precision. -/
theorem shallowRootAddress_spec (k : ℕ) :
    2 ^ (6 + k) ∣ shallowAddressValue (shallowRootAddress k) := by
  induction k with
  | zero =>
      norm_num [shallowRootAddress, shallowAddressValue]
  | succ k ih =>
      simp only [shallowRootAddress]
      split_ifs with hnext
      · exact hnext
      · have htoggle := shallowAddressValue_unique_child
          (shallowRootAddress k) k ih
        have hsurvives :
            2 ^ (7 + k) ∣
              shallowAddressValue (shallowRootAddress k + 2 ^ k) := by
          by_contra hfail
          exact hnext (htoggle.mpr hfail)
        simpa [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using
          hsurvives

/-- The canonical representative really lies in `[0,2^k)`. -/
theorem shallowRootAddress_lt (k : ℕ) : shallowRootAddress k < 2 ^ k := by
  induction k with
  | zero => norm_num [shallowRootAddress]
  | succ k ih =>
      rcases shallowRootAddress_step k with h | h <;> rw [h]
      · have hp : 2 ^ k < 2 ^ (k + 1) := by
          rw [pow_succ]
          positivity
        omega
      · rw [pow_succ]
        omega

/-- The canonical address is the unique representative below `2^k` at
precision `k`.  Together with `shallowRootAddress_spec`, this is the full
finite-level uniqueness assertion in QM160c. -/
theorem shallowRootAddress_unique (k n : ℕ) (hn : n < 2 ^ k)
    (hroot : 2 ^ (6 + k) ∣ shallowAddressValue n) :
    n = shallowRootAddress k := by
  induction k generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      simpa [this, shallowRootAddress]
  | succ k ih =>
      have hnextRoot : 2 ^ (7 + k) ∣ shallowAddressValue n := by
        simpa [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using
          hroot
      have hnBound : n < 2 ^ k + 2 ^ k := by
        simpa [pow_succ] using hn
      by_cases hlow : n < 2 ^ k
      · have hcurrent : 2 ^ (6 + k) ∣ shallowAddressValue n :=
          dvd_trans (pow_dvd_pow 2 (by omega)) hnextRoot
        have hnEq : n = shallowRootAddress k := ih n hlow hcurrent
        have hselected :
            shallowRootAddress (k + 1) = shallowRootAddress k := by
          simp [shallowRootAddress, ← hnEq, hnextRoot]
        rw [hnEq, hselected]
      · let m := n - 2 ^ k
        have hm : m < 2 ^ k := by dsimp [m]; omega
        have hnEq : n = m + 2 ^ k := by dsimp [m]; omega
        have hgapNe :
            shallowAddressValue (m + 2 ^ k) - shallowAddressValue m ≠ 0 := by
          intro hzero
          have hv := shallowAddressValue_gap_val m k
          rw [hzero] at hv
          simp at hv
        have hgapDvd :
            2 ^ (6 + k) ∣
              shallowAddressValue (m + 2 ^ k) - shallowAddressValue m := by
          apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hgapNe).2
          rw [shallowAddressValue_gap_val]
        have hupperCurrent :
            2 ^ (6 + k) ∣ shallowAddressValue (m + 2 ^ k) :=
          dvd_trans (pow_dvd_pow 2 (by omega)) (by simpa [hnEq] using hnextRoot)
        have hmCurrent : 2 ^ (6 + k) ∣ shallowAddressValue m := by
          have hsub := Nat.dvd_sub hupperCurrent hgapDvd
          have hmono : shallowAddressValue m ≤
              shallowAddressValue (m + 2 ^ k) := by
            dsimp [shallowAddressValue]
            gcongr
            omega
          simpa [Nat.sub_sub_self hmono] using hsub
        have hmEq : m = shallowRootAddress k := ih m hm hmCurrent
        have htoggle := shallowAddressValue_unique_child
          (shallowRootAddress k) k (shallowRootAddress_spec k)
        have hupperNext :
            2 ^ (7 + k) ∣
              shallowAddressValue (shallowRootAddress k + 2 ^ k) := by
          simpa [hmEq] using (show
            2 ^ (7 + k) ∣ shallowAddressValue (m + 2 ^ k) by
              simpa [hnEq] using hnextRoot)
        have hlowerNot :
            ¬ 2 ^ (7 + k) ∣ shallowAddressValue (shallowRootAddress k) := by
          intro hlower
          exact (htoggle.mp hlower) hupperNext
        have hselected : shallowRootAddress (k + 1) =
            shallowRootAddress k + 2 ^ k := by
          simp [shallowRootAddress, hlowerNot]
        rw [hnEq, hmEq, hselected]

/-- The integral charge parameter produced by the shallow exponent
cylinder.  Integrality is proved below on the legal exponent class. -/
def shallowRecharge (C : ℕ) : ℕ :=
  9 * (3 ^ (C + 2) + 7) / 64

/-- QM160a, exact recharge clause.  On its legal exponent class the word
lands at boundary state `3 * K - 1`, with the advertised closed formula for
`K`. -/
theorem shallow_power_executes_formula {C : ℕ} (hC : C % 16 = 12) :
    Executes shallowWord (3 * 3 ^ C - 1) (3 * shallowRecharge C - 1) := by
  have hCge : 12 ≤ C := by
    have hle := Nat.mod_le C 16
    omega
  have hmod : 3 * 3 ^ C - 1 ≡ 18 [MOD 64] :=
    (exists_shallow_execution_iff_source_modEq _).1
      ((exists_shallow_power_execution_iff C).2 hC)
  have hsourceLe : 18 ≤ 3 * 3 ^ C - 1 := by
    have hp : 3 ^ 12 ≤ 3 ^ C := Nat.pow_le_pow_right (by omega) hCge
    norm_num at hp ⊢
    omega
  have hdiv : 64 ∣ (3 * 3 ^ C - 1) - 18 :=
    (Nat.modEq_iff_dvd' hsourceLe).1 hmod.symm
  obtain ⟨t, ht⟩ := hdiv
  have hsource : 3 * 3 ^ C - 1 = 18 + 64 * t := by omega
  have hsourcePos : 1 ≤ 3 * 3 ^ C := by positivity
  have hpow : 3 ^ (C + 1) = 19 + 64 * t := by
    rw [pow_succ]
    omega
  have hnumerator : 3 ^ (C + 2) + 7 = 64 * (1 + 3 * t) := by
    rw [show C + 2 = (C + 1) + 1 by omega, pow_succ, hpow]
    ring
  have hK : shallowRecharge C = 9 * (1 + 3 * t) := by
    simp [shallowRecharge, hnumerator]
  have htarget : 3 * shallowRecharge C - 1 = 26 + 81 * t := by
    rw [hK]
    omega
  rw [hsource, htarget]
  simpa [shallowWord_length, shallowWord_oddCount] using
    (executes_shift shallowWord shallow_base_executes t)

/-- QM160d in subtraction-free form.  The three affine equations are the
incoming exponent presentation, one recharge, and its forced drain. -/
theorem exponent_child_composition
    {A B C D H S O e K a R : ℕ}
    (hinput : 2 ^ D * H = 3 ^ (C + A) + B)
    (hrecharge : 2 ^ S * K = 3 ^ O * H + e)
    (hdrain : 2 ^ a * R = 3 ^ a * K) :
    2 ^ (D + S + a) * R =
      3 ^ (C + (A + O + a)) +
        3 ^ a * (3 ^ O * B + e * 2 ^ D) := by
  calc
    2 ^ (D + S + a) * R =
        2 ^ (D + S) * (2 ^ a * R) := by rw [pow_add]; ring
    _ = 2 ^ (D + S) * (3 ^ a * K) := by rw [hdrain]
    _ = 2 ^ D * 3 ^ a * (2 ^ S * K) := by
      rw [pow_add]
      ring
    _ = 2 ^ D * 3 ^ a * (3 ^ O * H + e) := by rw [hrecharge]
    _ = 3 ^ (O + a) * (2 ^ D * H) + 3 ^ a * (e * 2 ^ D) := by
      rw [pow_add]
      ring
    _ = 3 ^ (O + a) * (3 ^ (C + A) + B) +
        3 ^ a * (e * 2 ^ D) := by rw [hinput]
    _ = 3 ^ (C + (A + O + a)) +
        3 ^ a * (3 ^ O * B + e * 2 ^ D) := by
      rw [show C + (A + O + a) = (C + A) + (O + a) by omega,
        pow_add, pow_add]
      ring

end OutwardExponentCylinder
end KontoroC
