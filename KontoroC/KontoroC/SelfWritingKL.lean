/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterAperiodic
import KontoroC.EtherCounterStateNoRepeat
import KontoroC.KLDyadicReset

/-!
# The self-writing KL/EC17 coordinate

This file packages the exact one-coordinate recurrence found in the returning
ether-glider audit.  An `Orbit` is still a hypothesis: the definitions do not
assert that an infinite accepted execution, an ordinary initial address, or a
Collatz counterexample exists.

The useful conclusions are semantic.  Every supplied self-writing orbit is
an exact positive EC17 orbit, its public payload grows strictly, and its
branch schedule cannot be eventually periodic.
-/

namespace KontoroC
namespace SelfWritingKL

def Z (q : ℕ) : ℕ := 494251421 + 495976448 * q
def W (q : ℕ) : ℕ := 83499104 + 83790531 * q
/-- The `Z` rail after dividing out the invariant collision factor on
payloads of the form `17*r`. -/
def Zbar (r : ℕ) : ℕ := 29073613 + 495976448 * r
/-- The `W` rail after dividing out the same factor. -/
def Wbar (r : ℕ) : ℕ := 4911712 + 83790531 * r
/-- Positive affine defect of the complete target-`m` payload cylinder.  The
division by `473` is exact for positive branches; this is proved below. -/
def branchDelta (m : ℕ) : ℕ :=
  (3 ^ (6 * m) * 83499104 - 2 ^ (8 * m - 5) * 494251421) / 473
def coreModulus : ℕ := 473 * 3 ^ 11
def returnModulus : ℕ := 2 ^ 20

/-- SW1, including both the constant and slope identities. -/
theorem determinant_identity (q : ℕ) :
    3 ^ 11 * Z q + 17 = 2 ^ 20 * W q := by
  simp [Z, W]
  ring

/-- First coefficientwise identity in QM146a. -/
theorem Z_seventeen_mul (r : ℕ) : Z (17 * r) = 17 * Zbar r := by
  simp [Z, Zbar]
  ring

/-- Second coefficientwise identity in QM146a. -/
theorem W_seventeen_mul (r : ℕ) : W (17 * r) = 17 * Wbar r := by
  simp [W, Wbar]
  ring

/-- The determinant identity on the divided collision slice has defect one. -/
theorem reduced_determinant_identity (r : ℕ) :
    3 ^ 11 * Zbar r + 1 = 2 ^ 20 * Wbar r := by
  simp [Zbar, Wbar]
  ring

/-- For every positive target branch the unscaled affine defect is strictly
positive.  The proof reduces it to the universal outward coefficient
inequality `2^(8m+15) < 3^(6m+11)`. -/
theorem branchDelta_raw_positive {m : ℕ} (hm : 0 < m) :
    2 ^ (8 * m - 5) * 494251421 < 3 ^ (6 * m) * 83499104 := by
  have hcoeff :=
    EtherCounterStateNoRepeat.Orbit.binary_lt_ternary_at_branch m
  have hscaled := Nat.mul_lt_mul_of_pos_right hcoeff
    (by norm_num : 0 < 494251421)
  have hdet : 3 ^ 11 * 494251421 + 17 = 2 ^ 20 * 83499104 := by
    simpa [Z, W] using determinant_identity 0
  apply (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ 20)).mp
  calc
    2 ^ 20 * (2 ^ (8 * m - 5) * 494251421) =
        2 ^ (8 * m + 15) * 494251421 := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ < 3 ^ (6 * m + 11) * 494251421 := hscaled
    _ < 3 ^ (6 * m) * (3 ^ 11 * 494251421 + 17) := by
      rw [pow_add]
      have hpos : 0 < 3 ^ (6 * m) := by positivity
      nlinarith
    _ = 2 ^ 20 * (3 ^ (6 * m) * 83499104) := by
      rw [hdet]
      ring

/-- Resonance modulo `473` makes the raw branch defect divisible by `473`
at every positive height. -/
theorem branchDelta_raw_modEq {m : ℕ} (hm : 0 < m) :
    Nat.ModEq 473
      (2 ^ (8 * m - 5) * 494251421)
      (3 ^ (6 * m) * 83499104) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk]
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 8 * (k + 1) - 5 = 8 * k + 3 by omega,
    show 6 * (k + 1) = 6 * k + 6 by omega,
    pow_add, pow_add, pow_mul, pow_mul]
  have hperiod : (2 : ZMod 473) ^ 8 = 3 ^ 6 := by decide
  have hbase : (2 : ZMod 473) ^ 3 * 494251421 =
      3 ^ 6 * 83499104 := by decide
  rw [hperiod]
  calc
    (3 ^ 6 : ZMod 473) ^ k * 2 ^ 3 * 494251421 =
        (3 ^ 6) ^ k * (2 ^ 3 * 494251421) := by ring
    _ = (3 ^ 6) ^ k * (3 ^ 6 * 83499104) := by rw [hbase]
    _ = (3 ^ 6) ^ k * 3 ^ 6 * 83499104 := by ring

/-- Exact factorization defining the natural branch defect. -/
theorem branchDelta_factor {m : ℕ} (hm : 0 < m) :
    473 * branchDelta m =
      3 ^ (6 * m) * 83499104 - 2 ^ (8 * m - 5) * 494251421 := by
  have hle := (branchDelta_raw_positive hm).le
  have hdvd : 473 ∣
      3 ^ (6 * m) * 83499104 - 2 ^ (8 * m - 5) * 494251421 :=
    (Nat.modEq_iff_dvd' hle).mp (branchDelta_raw_modEq hm)
  exact Nat.mul_div_cancel' hdvd

theorem branchDelta_positive {m : ℕ} (hm : 0 < m) :
    0 < branchDelta m := by
  have hfactor := branchDelta_factor hm
  have hraw := branchDelta_raw_positive hm
  by_contra hzero
  simp only [Nat.not_lt, nonpos_iff_eq_zero] at hzero
  rw [hzero, mul_zero] at hfactor
  omega

theorem Z_odd (q : ℕ) : Odd (Z q) := by
  rw [Nat.odd_iff]
  simp only [Z]
  omega

/-- Cancelling the common factor `17` converts a congruence modulo `17^2`
into the reduced congruence modulo `17`. -/
theorem seventeen_mul_modEq_iff (a b : ℕ) :
    Nat.ModEq (17 ^ 2) (17 * a) (17 * b) ↔ Nat.ModEq 17 a b := by
  rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd]
  constructor
  · intro h
    have h' : (17 : ℤ) * 17 ∣
        (17 : ℤ) * ((b : ℤ) - (a : ℤ)) := by
      convert h using 1 <;> norm_num <;> ring
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h'
  · intro h
    have h' := Int.mul_dvd_mul_left (17 : ℤ) h
    convert h' using 1 <;> norm_num <;> ring

/-- Exact mod-17 root of the reduced `Z` rail. -/
theorem seventeen_dvd_Zbar_iff (r : ℕ) :
    17 ∣ Zbar r ↔ r % 17 = 14 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  simp only [Zbar]
  omega

/-- Exact mod-17 root of the reduced `W` rail. -/
theorem seventeen_dvd_Wbar_iff (r : ℕ) :
    17 ∣ Wbar r ↔ r % 17 = 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  simp only [Wbar]
  omega

/-- The current reduced `Z` factor detects a second collision factor exactly
at the residue `r=14 (mod 17)`. -/
theorem current_core_deep_iff {n r v u : ℕ}
    (hcore : u = 17 * v) (hfactor : Zbar r = 3 ^ (6 * n) * v) :
    17 ^ 2 ∣ u ↔ r % 17 = 14 := by
  have hcancel : 17 ^ 2 ∣ u ↔ 17 ∣ v := by
    rw [hcore, show 17 ^ 2 = 17 * 17 by norm_num]
    exact Nat.mul_dvd_mul_iff_left (by norm_num)
  have hcoprime : Nat.Coprime 17 (3 ^ (6 * n)) :=
    (by norm_num : Nat.Coprime 17 3).pow_right _
  calc
    17 ^ 2 ∣ u ↔ 17 ∣ v := hcancel
    _ ↔ 17 ∣ 3 ^ (6 * n) * v := by
      constructor
      · exact fun hv => dvd_mul_of_dvd_right hv _
      · exact hcoprime.dvd_of_dvd_mul_left
    _ ↔ 17 ∣ Zbar r := by rw [hfactor]
    _ ↔ r % 17 = 14 := seventeen_dvd_Zbar_iff r

/-- The successor reduced `W` factor detects a second collision factor
exactly at the distinct residue `r=1 (mod 17)`. -/
theorem successor_core_deep_iff {m r v u : ℕ}
    (hcore : u = 17 * v) (hfactor : Wbar r = 2 ^ (8 * m - 5) * v) :
    17 ^ 2 ∣ u ↔ r % 17 = 1 := by
  have hcancel : 17 ^ 2 ∣ u ↔ 17 ∣ v := by
    rw [hcore, show 17 ^ 2 = 17 * 17 by norm_num]
    exact Nat.mul_dvd_mul_iff_left (by norm_num)
  have hcoprime : Nat.Coprime 17 (2 ^ (8 * m - 5)) :=
    (by norm_num : Nat.Coprime 17 2).pow_right _
  calc
    17 ^ 2 ∣ u ↔ 17 ∣ v := hcancel
    _ ↔ 17 ∣ 2 ^ (8 * m - 5) * v := by
      constructor
      · exact fun hv => dvd_mul_of_dvd_right hv _
      · exact hcoprime.dvd_of_dvd_mul_left
    _ ↔ 17 ∣ Wbar r := by rw [hfactor]
    _ ↔ r % 17 = 1 := seventeen_dvd_Wbar_iff r

/-- The affine `Z` coordinate detects the invariant unit slice exactly.
Its constant is divisible by `17`, while its slope is coprime to `17`. -/
theorem seventeen_dvd_Z_iff (q : ℕ) : 17 ∣ Z q ↔ 17 ∣ q := by
  have hconstant : 17 ∣ 494251421 := by norm_num
  constructor
  · intro hZ
    have hproduct : 17 ∣ 495976448 * q := by
      change 17 ∣ 494251421 + 495976448 * q at hZ
      exact (Nat.dvd_add_iff_left hconstant).mpr
        (by simpa [Nat.add_comm] using hZ)
    exact (by norm_num : Nat.Coprime 17 495976448).dvd_of_dvd_mul_left hproduct
  · intro hq
    obtain ⟨r, hr⟩ := hq
    refine ⟨29073613 + 495976448 * r, ?_⟩
    rw [hr]
    simp only [Z]
    ring

/-- The return coordinate detects the same unit slice. -/
theorem seventeen_dvd_W_iff (q : ℕ) : 17 ∣ W q ↔ 17 ∣ q := by
  have hconstant : 17 ∣ 83499104 := by norm_num
  constructor
  · intro hW
    have hproduct : 17 ∣ 83790531 * q := by
      change 17 ∣ 83499104 + 83790531 * q at hW
      exact (Nat.dvd_add_iff_left hconstant).mpr
        (by simpa [Nat.add_comm] using hW)
    exact (by norm_num : Nat.Coprime 17 83790531).dvd_of_dvd_mul_left hproduct
  · intro hq
    obtain ⟨r, hr⟩ := hq
    refine ⟨4911712 + 83790531 * r, ?_⟩
    rw [hr]
    simp only [W]
    ring

/-- The two moduli selecting the fixed-target odd core are coprime. -/
theorem coreModulus_coprime_returnModulus :
    coreModulus.Coprime returnModulus := by
  norm_num [coreModulus, returnModulus, Nat.Coprime]

/-- Valuation-free CRT interface for QM145g.  Any two requested core
residues select one canonical representative and every other solution is in
the same class modulo the product. -/
theorem exists_unique_core_crt (a b : ℕ) :
    ∃ h : ℕ, h < coreModulus * returnModulus ∧
      Nat.ModEq coreModulus h a ∧ Nat.ModEq returnModulus h b ∧
      ∀ h' : ℕ, Nat.ModEq coreModulus h' a →
        Nat.ModEq returnModulus h' b →
        Nat.ModEq (coreModulus * returnModulus) h' h := by
  let h : ℕ := ↑(Nat.chineseRemainder
    coreModulus_coprime_returnModulus a b)
  refine ⟨h, Nat.chineseRemainder_lt_mul
    coreModulus_coprime_returnModulus a b (by norm_num [coreModulus])
      (by norm_num [returnModulus]), ?_, ?_, ?_⟩
  · exact (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.1
  · exact (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.2
  · intro h' hhA hhB
    apply (Nat.modEq_and_modEq_iff_modEq_mul
      coreModulus_coprime_returnModulus).mp
    exact ⟨hhA.trans (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.1.symm,
      hhB.trans (Nat.chineseRemainder
        coreModulus_coprime_returnModulus a b).property.2.symm⟩

/-- The source member of a fixed-target CRT family has exactly the dyadic
stride in QM145g. -/
theorem source_stride {m h q : ℕ} (hm : 0 < m)
    (hbase : W q = 2 ^ (8 * m - 5) * h) (t : ℕ) :
    W (q + 2 ^ (8 * m + 15) * t) =
      2 ^ (8 * m - 5) *
        (h + coreModulus * returnModulus * t) := by
  calc
    W (q + 2 ^ (8 * m + 15) * t) =
        W q + 83790531 * 2 ^ (8 * m + 15) * t := by
      simp [W]
      ring
    _ = 2 ^ (8 * m - 5) * h +
        83790531 * 2 ^ (8 * m + 15) * t := by rw [hbase]
    _ = 2 ^ (8 * m - 5) *
        (h + coreModulus * returnModulus * t) := by
      rw [show 8 * m + 15 = (8 * m - 5) + 20 by omega, pow_add]
      norm_num [coreModulus, returnModulus]
      ring

/-- The target member written by the same core lift has exactly the ternary
stride in QM145g. -/
theorem target_stride {m h q' : ℕ}
    (hbase : Z q' = 3 ^ (6 * m) * h) (t : ℕ) :
    Z (q' + 3 ^ (6 * m + 11) * t) =
      3 ^ (6 * m) *
        (h + coreModulus * returnModulus * t) := by
  calc
    Z (q' + 3 ^ (6 * m + 11) * t) =
        Z q' + 495976448 * 3 ^ (6 * m + 11) * t := by
      simp [Z]
      ring
    _ = 3 ^ (6 * m) * h +
        495976448 * 3 ^ (6 * m + 11) * t := by rw [hbase]
    _ = 3 ^ (6 * m) *
        (h + coreModulus * returnModulus * t) := by
      rw [show 6 * m + 11 = 6 * m + 11 by rfl, pow_add]
      norm_num [coreModulus, returnModulus]
      ring

/-- QM145i: the packet color is multiplied by `316` at every positive EC17
step.  The large offset is kept literally to match the executable chart; the
statement is only a congruence modulo `473`. -/
theorem packetColor_transport {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Nat.ModEq 473 (s' + 291427) (316 * (s + 291427)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk] at hs ht ⊢
  have hcoef :
      (3 : ZMod 473) ^ (6 * (k + 1) + 11) =
        2 ^ 20 * 316 * 2 ^ (8 * (k + 1) - 5) := by
    rw [show 6 * (k + 1) + 11 = 17 + 6 * k by omega,
      show 8 * (k + 1) - 5 = 3 + 8 * k by omega,
      pow_add, pow_add, pow_mul, pow_mul]
    have hb : (3 : ZMod 473) ^ 17 = 2 ^ 20 * 316 * 2 ^ 3 := by decide
    have hr : (3 : ZMod 473) ^ 6 = 2 ^ 8 := by decide
    rw [hb, hr]
    ring
  have hconst :
      (17 : ZMod 473) + 2 ^ 20 * 291427 =
        2 ^ 20 * 316 * 291427 := by decide
  have htZ := congrArg (fun x : ℕ => (x : ZMod 473)) ht
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add] at htZ
  have hsZ := congrArg (fun x : ℕ => (x : ZMod 473)) hs
  have hs'Z := congrArg (fun x : ℕ => (x : ZMod 473)) hs'
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hsZ hs'Z
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
  have hunit : IsUnit (2 ^ 20 : ZMod 473) := by
    change IsUnit ((2 ^ 20 : ℕ) : ZMod 473)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  rw [← hunit.mul_left_inj]
  rw [mul_comm _ (2 ^ 20), mul_comm _ (2 ^ 20)]
  rw [mul_add, hs'Z, ← mul_assoc, ← pow_add]
  rw [show 20 + (8 * m - 5) = 8 * m + 15 by omega, htZ]
  rw [hsZ]
  linear_combination (u : ZMod 473) * hcoef + hconst

/-- Packet color zero is an invariant of every positive EC17 step. -/
theorem packetColor_zero_propagates {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hzero : Nat.ModEq 473 (s + 291427) 0) :
    Nat.ModEq 473 (s' + 291427) 0 := by
  have htransport := packetColor_transport hn hm hs hs' ht
  exact htransport.trans (by simpa using hzero.mul_left 316)

/-- Packet color zero cannot be acquired at a later positive EC17 step.
The transport multiplier `316` is a unit modulo `473`, so a zero target
color already forces a zero source color.  This is the missing reverse
direction behind the informal statement that a non-packet bare EC17 ray
can never enter the returning-packet component. -/
theorem packetColor_zero_reflects {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hzero' : Nat.ModEq 473 (s' + 291427) 0) :
    Nat.ModEq 473 (s + 291427) 0 := by
  have htransport := packetColor_transport hn hm hs hs' ht
  have hproduct : Nat.ModEq 473 (316 * (s + 291427)) 0 :=
    htransport.symm.trans hzero'
  rw [← ZMod.natCast_eq_natCast_iff] at hproduct ⊢
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hproduct ⊢
  have hunit : IsUnit (316 : ZMod 473) := by
    change IsUnit ((316 : ℕ) : ZMod 473)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  apply hunit.mul_left_inj.mp
  simpa [mul_comm] using hproduct

/-- Packet validity is exactly invariant, in both time directions, along a
positive EC17 transition. -/
theorem packetColor_zero_iff {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Nat.ModEq 473 (s' + 291427) 0 ↔
      Nat.ModEq 473 (s + 291427) 0 :=
  ⟨packetColor_zero_reflects hn hm hs hs' ht,
    packetColor_zero_propagates hn hm hs hs' ht⟩

/-- Contrapositive form consumed by adversarial searches: once the bare
EC17 color is nonzero, every positive successor still fails the packet
gate. -/
theorem packetColor_nonzero_propagates {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hnonzero : ¬ Nat.ModEq 473 (s + 291427) 0) :
    ¬ Nat.ModEq 473 (s' + 291427) 0 := by
  exact fun hzero' => hnonzero
    (packetColor_zero_reflects hn hm hs hs' ht hzero')

/-- The executable packet color is exactly the centered `Z`-rail congruence.
The factor `32` relating the two coordinates is a unit modulo `473`. -/
theorem packetColor_zero_iff_centered_modEq {n u : ℕ} (hn : 0 < n) :
    Nat.ModEq 473 (2 ^ (8 * n - 5) * u + 291427) 0 ↔
      Nat.ModEq 473 (3 ^ (6 * n) * u) 494251421 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk]
  have hpow : (3 : ZMod 473) ^ (6 * (k + 1)) =
      2 ^ 5 * 2 ^ (8 * (k + 1) - 5) := by
    have hres : (3 : ZMod 473) ^ 6 = 2 ^ 8 := by decide
    rw [pow_mul, hres, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hconstant : (494251421 : ZMod 473) =
      -(2 ^ 5 * 291427) := by decide
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow, hconstant]
  have hunit : IsUnit (2 ^ 5 : ZMod 473) := by
    change IsUnit ((2 ^ 5 : ℕ) : ZMod 473)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  let a : ZMod 473 := 2 ^ (8 * (k + 1) - 5) * u
  let b : ZMod 473 := 291427
  have hab : a + b = 0 ↔ 2 ^ 5 * a = -(2 ^ 5 * b) := by
    constructor
    · intro h
      calc
        2 ^ 5 * a = 2 ^ 5 * (a + b) - 2 ^ 5 * b := by ring
        _ = -(2 ^ 5 * b) := by rw [h]; ring
    · intro h
      apply hunit.mul_right_inj.mp
      calc
        2 ^ 5 * (a + b) = 2 ^ 5 * a + 2 ^ 5 * b := by ring
        _ = 0 := by rw [h]; ring
        _ = 2 ^ 5 * 0 := by ring
  simpa [a, b, mul_assoc] using hab

/-- A hypothetical infinite execution of the deterministic self-writing
coordinate.  `z_factor` records the current ternary branch and `w_factor`
records the next binary branch.  Requiring the next `z_factor` is exactly the
fixed return cylinder; it is not inferred from a finite computation. -/
structure Orbit where
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  core_odd : ∀ t, Odd (core t)
  core_mod_three : ∀ t, core t % 3 = 1
  payload : ℕ → ℕ
  z_factor : ∀ t,
    Z (payload t) = 3 ^ (6 * branch t) * core t
  w_factor : ∀ t,
    W (payload t) = 2 ^ (8 * branch (t + 1) - 5) * core (t + 1)

namespace Orbit

/-! ## Rational centered coordinates -/

def recharge (R : ℚ) : ℚ := (3 ^ 11 * R + 1221) / 2 ^ 15
def ether (R : ℚ) : ℚ := (729 * R + 4) / 256
def boundary (R : ℚ) : ℚ := 2 ^ 18 * R + 2215

/-- QM145a: the recharge map is exactly conjugate to the two-rail
determinant identity in the centered coordinate. -/
theorem recharge_identity (R : ℚ) :
    3 ^ 11 * (473 * R + 4) + 17 =
      2 ^ 15 * (473 * recharge R + 4) := by
  simp [recharge]
  ring

/-- QM145b: one ether cell multiplies the centered `Z` coordinate by
`729`, with denominator `256`. -/
theorem ether_identity (R : ℚ) :
    256 * (473 * ether R + 4) = 729 * (473 * R + 4) := by
  simp [ether]
  ring

/-- Iterated integer-denominator form of the ether conjugacy. -/
theorem ether_iterate_identity (m : ℕ) (R : ℚ) :
    256 ^ m * (473 * ((ether^[m]) R) + 4) =
      729 ^ m * (473 * R + 4) := by
  induction m generalizing R with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, pow_succ, pow_succ]
      calc
        256 ^ m * 256 * (473 * ((ether^[m]) (ether R)) + 4) =
            256 * (256 ^ m *
              (473 * ((ether^[m]) (ether R)) + 4)) := by ring
        _ = 256 * (729 ^ m * (473 * ether R + 4)) := by rw [ih]
        _ = 729 ^ m * (256 * (473 * ether R + 4)) := by ring
        _ = 729 ^ m * (729 * (473 * R + 4)) := by rw [ether_identity]
        _ = 729 ^ m * 729 * (473 * R + 4) := by ring

/-- First half of QM145d: the literal KL boundary conjugates one ether cell
to `(729*C+881)/256`. -/
theorem boundary_ether_conjugacy (R : ℚ) :
    boundary (ether R) = (729 * boundary R + 881) / 256 := by
  simp [boundary, ether]
  ring

/-- Second half of QM145d: the recharge map becomes the stated affine KL
boundary update. -/
theorem boundary_recharge_conjugacy (R : ℚ) :
    boundary (recharge R) =
      (3 ^ 11 * boundary R + 278339) / 2 ^ 15 := by
  simp [boundary, recharge]
  ring

/-- QM145c without a valuation API.  The exact EC17 balance factors the
recharged centered coordinate by `2^(8m)`. -/
theorem recharge_factor_of_transition {R u u' : ℚ} {n m : ℕ}
    (hsource : 473 * R + 4 = 3 ^ (6 * n) * u)
    (htransition : 2 ^ (8 * m + 15) * u' =
      3 ^ (6 * n + 11) * u + 17) :
    473 * recharge R + 4 = 2 ^ (8 * m) * u' := by
  have h := recharge_identity R
  rw [hsource] at h
  have hthree : (3 : ℚ) ^ 11 * (3 ^ (6 * n) * u) =
      3 ^ (6 * n + 11) * u := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hthree, ← htransition] at h
  have htwo : (2 : ℚ) ^ (8 * m + 15) = 2 ^ 15 * 2 ^ (8 * m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [htwo] at h
  have hpos : (0 : ℚ) < 2 ^ 15 := by positivity
  nlinarith

/-- Full centered conjugacy of one accepted EC17 transition. -/
theorem transition_conjugacy {R R' u u' : ℚ} {n m : ℕ}
    (hsource : 473 * R + 4 = 3 ^ (6 * n) * u)
    (htransition : 2 ^ (8 * m + 15) * u' =
      3 ^ (6 * n + 11) * u + 17)
    (htarget : 473 * R' + 4 = 3 ^ (6 * m) * u') :
    R' = (ether^[m]) (recharge R) := by
  have hD := recharge_factor_of_transition hsource htransition
  have hiter := ether_iterate_identity m (recharge R)
  have h256 : (256 : ℚ) ^ m = 2 ^ (8 * m) := by
    rw [show (256 : ℚ) = 2 ^ 8 by norm_num, ← pow_mul]
  have h729 : (729 : ℚ) ^ m = 3 ^ (6 * m) := by
    rw [show (729 : ℚ) = 3 ^ 6 by norm_num, ← pow_mul]
  rw [h256, h729, hD] at hiter
  have hpos : (0 : ℚ) < 2 ^ (8 * m) := by positivity
  have hz : 473 * ((ether^[m]) (recharge R)) + 4 =
      3 ^ (6 * m) * u' := by
    nlinarith
  rw [← htarget] at hz
  nlinarith

/-- SW1 turns every accepted self-writing step into the literal EC17
balance. -/
theorem balance (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
      3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
  have hnext := o.branch_pos (t + 1)
  calc
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
        2 ^ 20 *
          (2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1)) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ = 2 ^ 20 * W (o.payload t) := by rw [o.w_factor]
    _ = 3 ^ 11 * Z (o.payload t) + 17 :=
      (determinant_identity (o.payload t)).symm
    _ = 3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
      rw [o.z_factor, ← mul_assoc, ← pow_add]
      congr 3
      omega

/-- Exact public-payload balance for one accepted target branch.  Unlike the
core recurrence, both exponents are read from the same target branch. -/
theorem payload_rail_balance (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) - 5) * Z (o.payload (t + 1)) =
      3 ^ (6 * o.branch (t + 1)) * W (o.payload t) := by
  rw [o.z_factor (t + 1), o.w_factor t]
  ring

/-- Expanded coefficient form of the complete target cylinder. -/
theorem payload_branch_balance_expanded (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) - 5) * 494251421 +
        473 * 2 ^ (8 * o.branch (t + 1) + 15) * o.payload (t + 1) =
      3 ^ (6 * o.branch (t + 1)) * 83499104 +
        473 * 3 ^ (6 * o.branch (t + 1) + 11) * o.payload t := by
  have hm := o.branch_pos (t + 1)
  have h := o.payload_rail_balance t
  simp only [Z, W] at h
  rw [show 8 * o.branch (t + 1) + 15 =
      (8 * o.branch (t + 1) - 5) + 20 by omega,
    show 6 * o.branch (t + 1) + 11 =
      6 * o.branch (t + 1) + 11 by rfl,
    pow_add, pow_add]
  norm_num
  nlinarith

/-- The public payload itself follows a dyadic affine reset program.  This
is the exact branch-family identity used by the prefix-code worker, now
derived from an arbitrary supplied orbit rather than finite samples. -/
theorem payload_branch_recurrence (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) + 15) * o.payload (t + 1) =
      3 ^ (6 * o.branch (t + 1) + 11) * o.payload t +
        branchDelta (o.branch (t + 1)) := by
  let m := o.branch (t + 1)
  have hm : 0 < m := o.branch_pos (t + 1)
  have hexpanded := o.payload_branch_balance_expanded t
  have hdelta := branchDelta_factor hm
  change
    2 ^ (8 * m + 15) * o.payload (t + 1) =
      3 ^ (6 * m + 11) * o.payload t + branchDelta m
  change
    2 ^ (8 * m - 5) * 494251421 +
        473 * 2 ^ (8 * m + 15) * o.payload (t + 1) =
      3 ^ (6 * m) * 83499104 +
        473 * 3 ^ (6 * m + 11) * o.payload t at hexpanded
  have hraw :
      3 ^ (6 * m) * 83499104 =
        2 ^ (8 * m - 5) * 494251421 + 473 * branchDelta m := by
    have hle := (branchDelta_raw_positive hm).le
    calc
      3 ^ (6 * m) * 83499104 =
          (3 ^ (6 * m) * 83499104 -
            2 ^ (8 * m - 5) * 494251421) +
              2 ^ (8 * m - 5) * 494251421 :=
        (Nat.sub_add_cancel hle).symm
      _ = 2 ^ (8 * m - 5) * 494251421 + 473 * branchDelta m := by
        rw [← hdelta]
        omega
  rw [hraw] at hexpanded
  have hcancel :
      473 * (2 ^ (8 * m + 15) * o.payload (t + 1)) =
        473 * (3 ^ (6 * m + 11) * o.payload t + branchDelta m) := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 473) hcancel

/-- Candidate normalized core decoded from one public payload and its target
branch.  The following lemmas prove this division is exact whenever the
public affine recurrence is satisfied. -/
def payloadStepCore (m q : ℕ) : ℕ :=
  W q / 2 ^ (8 * m - 5)

/-- Converse algebra: the public affine recurrence is equivalent to the
unscaled `Z/W` rail balance. -/
theorem payload_recurrence_rail_balance {m q q' : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m) :
    2 ^ (8 * m - 5) * Z q' = 3 ^ (6 * m) * W q := by
  have hdelta := branchDelta_factor hm
  have hle := (branchDelta_raw_positive hm).le
  have hraw :
      3 ^ (6 * m) * 83499104 =
        2 ^ (8 * m - 5) * 494251421 + 473 * branchDelta m := by
    calc
      3 ^ (6 * m) * 83499104 =
          (3 ^ (6 * m) * 83499104 -
            2 ^ (8 * m - 5) * 494251421) +
              2 ^ (8 * m - 5) * 494251421 :=
        (Nat.sub_add_cancel hle).symm
      _ = 2 ^ (8 * m - 5) * 494251421 + 473 * branchDelta m := by
        rw [← hdelta]
        omega
  calc
    2 ^ (8 * m - 5) * Z q' =
        2 ^ (8 * m - 5) * 494251421 +
          473 * 2 ^ (8 * m + 15) * q' := by
      simp only [Z]
      rw [show 8 * m + 15 = (8 * m - 5) + 20 by omega, pow_add]
      norm_num
      ring
    _ = 2 ^ (8 * m - 5) * 494251421 +
          473 * (2 ^ (8 * m + 15) * q') := by ring
    _ = 2 ^ (8 * m - 5) * 494251421 +
          473 * (3 ^ (6 * m + 11) * q + branchDelta m) := by
      rw [hrecurrence]
    _ = 3 ^ (6 * m) * 83499104 +
          473 * 3 ^ (6 * m + 11) * q := by
      rw [hraw]
      ring
    _ = 3 ^ (6 * m) * W q := by
      simp only [W]
      rw [show 6 * m + 11 = 6 * m + 11 by rfl, pow_add]
      norm_num
      ring

theorem payloadStepCore_factor_W {m q q' : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m) :
    W q = 2 ^ (8 * m - 5) * payloadStepCore m q := by
  have hrail := payload_recurrence_rail_balance hm hrecurrence
  have hdvdProduct : 2 ^ (8 * m - 5) ∣ 3 ^ (6 * m) * W q := by
    rw [← hrail]
    exact dvd_mul_right _ _
  have hcoprime : Nat.Coprime (2 ^ (8 * m - 5)) (3 ^ (6 * m)) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  have hdvd : 2 ^ (8 * m - 5) ∣ W q :=
    hcoprime.dvd_of_dvd_mul_left hdvdProduct
  exact (Nat.mul_div_cancel' hdvd).symm

theorem payloadStepCore_factor_Z {m q q' : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m) :
    Z q' = 3 ^ (6 * m) * payloadStepCore m q := by
  have hrail := payload_recurrence_rail_balance hm hrecurrence
  have hW := payloadStepCore_factor_W hm hrecurrence
  rw [hW] at hrail
  apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ (8 * m - 5))
  calc
    2 ^ (8 * m - 5) * Z q' =
        3 ^ (6 * m) *
          (2 ^ (8 * m - 5) * payloadStepCore m q) := hrail
    _ = 2 ^ (8 * m - 5) *
        (3 ^ (6 * m) * payloadStepCore m q) := by ring

theorem payloadStepCore_odd {m q q' : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m) :
    Odd (payloadStepCore m q) := by
  have hZ := payloadStepCore_factor_Z hm hrecurrence
  have hodd : Odd (3 ^ (6 * m) * payloadStepCore m q) := by
    rw [← hZ]
    exact Z_odd q'
  exact (Nat.odd_mul.mp hodd).2

theorem payloadStepCore_mod_three {m q q' : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m) :
    payloadStepCore m q % 3 = 1 := by
  have hW := payloadStepCore_factor_W hm hrecurrence
  have hcast := congrArg (fun x : ℕ => (x : ZMod 3)) hW
  simp only [W, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hcast
  have hW0 : (83499104 : ZMod 3) = 2 := by decide
  have hWs : (83790531 : ZMod 3) = 0 := by decide
  rw [hW0, hWs, zero_mul, add_zero] at hcast
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk] at hcast ⊢
  have hpow : (2 : ZMod 3) ^ (8 * (k + 1) - 5) = 2 := by
    rw [show 8 * (k + 1) - 5 = 8 * k + 3 by omega,
      pow_add, pow_mul]
    have hperiod : (2 : ZMod 3) ^ 8 = 1 := by decide
    rw [hperiod, one_pow]
    decide
  rw [hpow] at hcast
  have hunit : IsUnit (2 : ZMod 3) := by decide
  have hcoreCast : ((payloadStepCore (k + 1) q : ℕ) : ZMod 3) = 1 := by
    apply hunit.mul_right_inj.mp
    simpa using hcast.symm
  have hmod := (ZMod.natCast_eq_natCast_iff
    (payloadStepCore (k + 1) q) 1 3).mp hcoreCast
  change payloadStepCore (k + 1) q % 3 = 1 % 3 at hmod
  simpa using hmod

/-- QM146b: after dividing consecutive unit-slice cores by `17`, the EC17
recurrence has irreducible defect one. -/
theorem unit_slice_reduced_balance (o : Orbit) (t : ℕ) {v v' : ℕ}
    (hcurrent : o.core t = 17 * v)
    (hnext : o.core (t + 1) = 17 * v') :
    2 ^ (8 * o.branch (t + 1) + 15) * v' =
      3 ^ (6 * o.branch t + 11) * v + 1 := by
  apply Nat.mul_left_cancel (by norm_num : 0 < 17)
  calc
    17 * (2 ^ (8 * o.branch (t + 1) + 15) * v') =
        2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
      rw [hnext]
      ring
    _ = 3 ^ (6 * o.branch t + 11) * o.core t + 17 := o.balance t
    _ = 17 * (3 ^ (6 * o.branch t + 11) * v + 1) := by
      rw [hcurrent]
      ring

/-- QM146c in a reusable one-step form.  The reduced source and target rail
factorizations force the exact affine transport of the payload quotient
modulo `17`. -/
def reducedResidueStep (m : ℕ) (r : ZMod 17) : ZMod 17 :=
  14 + 6 * (-(2 : ZMod 17)) ^ (m - 1) * (r - 1)

/-- The reduced residue dynamics depends on a positive target branch only
modulo eight.  This is the universal algebra behind the worker's finite
three-sample checks of each proposed shallow rail. -/
theorem reducedResidueStep_add_eight_mul (j k : ℕ) (hj : 0 < j)
    (r : ZMod 17) :
    reducedResidueStep (j + 8 * k) r = reducedResidueStep j r := by
  have hexponent : j + 8 * k - 1 = (j - 1) + 8 * k := by omega
  have hperiod : (-(2 : ZMod 17)) ^ 8 = 1 := by decide
  simp only [reducedResidueStep, hexponent, pow_add, pow_mul, hperiod,
    one_pow, mul_one]

theorem reducedResidueStep_one_fixed : reducedResidueStep 1 12 = 12 := by decide
theorem reducedResidueStep_two_fixed : reducedResidueStep 2 2 = 2 := by decide
theorem reducedResidueStep_three_fixed : reducedResidueStep 3 13 = 13 := by decide
theorem reducedResidueStep_four_fixed : reducedResidueStep 4 3 = 3 := by decide
theorem reducedResidueStep_five_fixed : reducedResidueStep 5 15 = 15 := by decide
theorem reducedResidueStep_six_fixed : reducedResidueStep 6 6 = 6 := by decide
theorem reducedResidueStep_seven_fixed : reducedResidueStep 7 9 = 9 := by decide
theorem reducedResidueStep_eight_fixed : reducedResidueStep 8 0 = 0 := by decide

/-- The eight constant-residue rails, valid for all branch heights in the
displayed congruence classes. -/
theorem reducedResidueStep_one_rail (k : ℕ) :
    reducedResidueStep (1 + 8 * k) 12 = 12 := by
  rw [reducedResidueStep_add_eight_mul 1 k (by omega), reducedResidueStep_one_fixed]

theorem reducedResidueStep_two_rail (k : ℕ) :
    reducedResidueStep (2 + 8 * k) 2 = 2 := by
  rw [reducedResidueStep_add_eight_mul 2 k (by omega), reducedResidueStep_two_fixed]

theorem reducedResidueStep_three_rail (k : ℕ) :
    reducedResidueStep (3 + 8 * k) 13 = 13 := by
  rw [reducedResidueStep_add_eight_mul 3 k (by omega), reducedResidueStep_three_fixed]

theorem reducedResidueStep_four_rail (k : ℕ) :
    reducedResidueStep (4 + 8 * k) 3 = 3 := by
  rw [reducedResidueStep_add_eight_mul 4 k (by omega), reducedResidueStep_four_fixed]

theorem reducedResidueStep_five_rail (k : ℕ) :
    reducedResidueStep (5 + 8 * k) 15 = 15 := by
  rw [reducedResidueStep_add_eight_mul 5 k (by omega), reducedResidueStep_five_fixed]

theorem reducedResidueStep_six_rail (k : ℕ) :
    reducedResidueStep (6 + 8 * k) 6 = 6 := by
  rw [reducedResidueStep_add_eight_mul 6 k (by omega), reducedResidueStep_six_fixed]

theorem reducedResidueStep_seven_rail (k : ℕ) :
    reducedResidueStep (7 + 8 * k) 9 = 9 := by
  rw [reducedResidueStep_add_eight_mul 7 k (by omega), reducedResidueStep_seven_fixed]

theorem reducedResidueStep_eight_rail (k : ℕ) :
    reducedResidueStep (8 + 8 * k) 0 = 0 := by
  rw [reducedResidueStep_add_eight_mul 8 k (by omega), reducedResidueStep_eight_fixed]

theorem reduced_payload_transport {m r r' v : ℕ} (hm : 0 < m)
    (hsource : Wbar r = 2 ^ (8 * m - 5) * v)
    (htarget : Zbar r' = 3 ^ (6 * m) * v) :
    ((r' : ℕ) : ZMod 17) - 14 =
      6 * (-(2 : ZMod 17)) ^ (m - 1) * (((r : ℕ) : ZMod 17) - 1) := by
  have hbalance :
      2 ^ (8 * m - 5) * Zbar r' = 3 ^ (6 * m) * Wbar r := by
    rw [htarget, hsource]
    ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk] at hsource htarget hbalance ⊢
  have htwo :
      (2 : ZMod 17) ^ (8 * (k + 1) - 5) = 8 := by
    rw [show 8 * (k + 1) - 5 = 8 * k + 3 by omega,
      pow_add, pow_mul]
    have hperiod : (2 : ZMod 17) ^ 8 = 1 := by decide
    rw [hperiod]
    norm_num
  have hthree :
      (3 : ZMod 17) ^ (6 * (k + 1)) = (-(2 : ZMod 17)) ^ (k + 1) := by
    rw [pow_mul]
    have hbase : (3 : ZMod 17) ^ 6 = -(2 : ZMod 17) := by decide
    rw [hbase]
  have hcast := congrArg (fun x : ℕ => (x : ZMod 17)) hbalance
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [htwo, hthree] at hcast
  simp only [Zbar, Wbar, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
  have hz0 : (29073613 : ZMod 17) = 9 := by decide
  have hz1 : (495976448 : ZMod 17) = 3 := by decide
  have hw0 : (4911712 : ZMod 17) = 4 := by decide
  have hw1 : (83790531 : ZMod 17) = 13 := by decide
  rw [hz0, hz1, hw0, hw1] at hcast
  norm_num at ⊢
  rw [pow_succ] at hcast
  ring_nf at hcast ⊢
  reduce_mod_char at hcast ⊢
  have hmul := congrArg (fun x : ZMod 17 => 5 * x) hcast
  ring_nf at hmul ⊢
  reduce_mod_char at hmul ⊢
  exact hmul

/-- Equivalent state-update form of QM146c, convenient for finite-state
residue graphs and invariant-rail consumers. -/
theorem reduced_payload_step {m r r' v : ℕ} (hm : 0 < m)
    (hsource : Wbar r = 2 ^ (8 * m - 5) * v)
    (htarget : Zbar r' = 3 ^ (6 * m) * v) :
    ((r' : ℕ) : ZMod 17) =
      reducedResidueStep m ((r : ℕ) : ZMod 17) := by
  have h := reduced_payload_transport hm hsource htarget
  exact (sub_eq_iff_eq_add.mp h).trans (by
    simp only [reducedResidueStep]
    ring)

/-- A fixed reduced shallow rail propagates through any exact public-payload
step.  This is the local modulo-`17^2` engine for QM149. -/
theorem payload_mod_seventeen_sq_step {m q q' c : ℕ} (hm : 0 < m)
    (hrecurrence :
      2 ^ (8 * m + 15) * q' =
        3 ^ (6 * m + 11) * q + branchDelta m)
    (hsource : Nat.ModEq (17 ^ 2) q (17 * c))
    (hfixed : reducedResidueStep m (c : ZMod 17) = c) :
    Nat.ModEq (17 ^ 2) q' (17 * c) := by
  have hqdiv : 17 ∣ q :=
    (hsource.dvd_iff (by norm_num : 17 ∣ 17 ^ 2)).mpr
      (dvd_mul_right 17 c)
  have hW := payloadStepCore_factor_W hm hrecurrence
  have hWdiv : 17 ∣ W q := (seventeen_dvd_W_iff q).mpr hqdiv
  obtain ⟨r, hr⟩ := hqdiv
  rw [hW] at hWdiv
  have hcoreDiv : 17 ∣ payloadStepCore m q :=
    ((by norm_num : Nat.Coprime 17 2).pow_right
      (8 * m - 5)).dvd_of_dvd_mul_left hWdiv
  obtain ⟨v, hv⟩ := hcoreDiv
  have hZ := payloadStepCore_factor_Z hm hrecurrence
  have hZdiv : 17 ∣ Z q' := by
    rw [hZ, hv]
    exact dvd_mul_of_dvd_right (dvd_mul_right 17 v) _
  have hq'div : 17 ∣ q' := (seventeen_dvd_Z_iff q').mp hZdiv
  obtain ⟨r', hr'⟩ := hq'div
  have hsourceFactor : Wbar r = 2 ^ (8 * m - 5) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Wbar r = W (17 * r) := (W_seventeen_mul r).symm
      _ = W q := by rw [hr]
      _ = 2 ^ (8 * m - 5) * payloadStepCore m q := hW
      _ = 17 * (2 ^ (8 * m - 5) * v) := by rw [hv]; ring
  have htargetFactor : Zbar r' = 3 ^ (6 * m) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Zbar r' = Z (17 * r') := (Z_seventeen_mul r').symm
      _ = Z q' := by rw [hr']
      _ = 3 ^ (6 * m) * payloadStepCore m q := hZ
      _ = 17 * (3 ^ (6 * m) * v) := by rw [hv]; ring
  have hrc : Nat.ModEq 17 r c := by
    apply (seventeen_mul_modEq_iff r c).mp
    simpa [hr] using hsource
  have hrcZ : ((r : ℕ) : ZMod 17) = c := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact hrc
  have hstep := reduced_payload_step hm hsourceFactor htargetFactor
  have hr'cZ : ((r' : ℕ) : ZMod 17) = c := by
    rw [hstep, hrcZ, hfixed]
  have hr'c : Nat.ModEq 17 r' c := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hr'cZ
  rw [hr']
  exact (seventeen_mul_modEq_iff r' c).mpr hr'c

/-- Integer wrapper used by positive finite reset chains. -/
theorem int_payload_mod_seventeen_sq_step {m c : ℕ} {q q' : ℤ}
    (hm : 0 < m) (hq : 0 < q) (hq' : 0 < q')
    (hrecurrence :
      (2 : ℤ) ^ (8 * m + 15) * q' =
        (3 : ℤ) ^ (6 * m + 11) * q + branchDelta m)
    (hsource : Int.ModEq (17 ^ 2) q (17 * c))
    (hfixed : reducedResidueStep m (c : ZMod 17) = c) :
    Int.ModEq (17 ^ 2) q' (17 * c) := by
  let qNat := q.toNat
  let qNat' := q'.toNat
  have hqcast : (qNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hq'cast : (qNat' : ℤ) = q' := Int.toNat_of_nonneg hq'.le
  have hrecNat :
      2 ^ (8 * m + 15) * qNat' =
        3 ^ (6 * m + 11) * qNat + branchDelta m := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hqcast, hq'cast]
    exact hrecurrence
  have hsourceNat : Nat.ModEq (17 ^ 2) qNat (17 * c) := by
    rw [Nat.modEq_iff_dvd]
    rw [Int.modEq_iff_dvd] at hsource
    simpa [hqcast] using hsource
  have htargetNat :=
    payload_mod_seventeen_sq_step hm hrecNat hsourceNat hfixed
  rw [Int.modEq_iff_dvd]
  rw [Nat.modEq_iff_dvd] at htargetNat
  simpa [hq'cast] using htargetNat

/-! ## The invariant collision factor and its exact local obstruction -/

/-- On the invariant unit slice `17 ∣ payload`, the normalized core contains
the collision factor `17`.  The affine `Z`-rail constant is divisible by
`17`, while substituting `payload = 17*r` supplies the same factor in its
linear term. -/
theorem seventeen_dvd_core_of_payload (o : Orbit) (t : ℕ)
    (hpayload : 17 ∣ o.payload t) : 17 ∣ o.core t := by
  have hZ : 17 ∣ Z (o.payload t) := by
    obtain ⟨r, hr⟩ := hpayload
    rw [hr]
    refine ⟨29073613 + 495976448 * r, ?_⟩
    simp [Z]
    ring
  rw [o.z_factor] at hZ
  have hcoprime : Nat.Coprime 17 (3 ^ (6 * o.branch t)) :=
    (by norm_num : Nat.Coprime 17 3).pow_right _
  exact hcoprime.dvd_of_dvd_mul_left hZ

/-- The defect `17` prevents two consecutive EC17 cores from both carrying
a second factor of `17`.  If `17^2` divided both cores, it would divide both
weighted terms in `balance`, and hence divide their difference `17`.

This elementary theorem is the universal content behind the branch-pressure
worker's finite residue check called `adjacent_deep_core_theorem`. -/
theorem not_both_seventeen_sq_dvd_consecutive (o : Orbit) (t : ℕ) :
    ¬ (17 ^ 2 ∣ o.core t ∧ 17 ^ 2 ∣ o.core (t + 1)) := by
  rintro ⟨hcurrent, hnext⟩
  have hleft : 17 ^ 2 ∣
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) :=
    dvd_mul_of_dvd_right hnext _
  have hright : 17 ^ 2 ∣
      3 ^ (6 * o.branch t + 11) * o.core t :=
    dvd_mul_of_dvd_right hcurrent _
  rw [o.balance t] at hleft
  have hleftMod := Nat.dvd_iff_mod_eq_zero.mp hleft
  have hrightMod := Nat.dvd_iff_mod_eq_zero.mp hright
  have hleftMod289 :
      (3 ^ (6 * o.branch t + 11) * o.core t + 17) % 289 = 0 := by
    norm_num at hleftMod ⊢
    exact hleftMod
  have hrightMod289 :
      (3 ^ (6 * o.branch t + 11) * o.core t) % 289 = 0 := by
    norm_num at hrightMod ⊢
    exact hrightMod
  rw [Nat.add_mod, hrightMod289] at hleftMod289
  norm_num at hleftMod289

/-- Exact local form of the invariant unit slice: both neighboring cores
contain `17`, and at least one of them contains no second factor. -/
theorem consecutive_collision_factor_exact (o : Orbit) (t : ℕ)
    (hcurrent : 17 ∣ o.core t) (hnext : 17 ∣ o.core (t + 1)) :
    17 ∣ o.core t ∧ 17 ∣ o.core (t + 1) ∧
      (¬ 17 ^ 2 ∣ o.core t ∨ ¬ 17 ^ 2 ∣ o.core (t + 1)) := by
  refine ⟨hcurrent, hnext, ?_⟩
  by_cases hdeep : 17 ^ 2 ∣ o.core t
  · exact Or.inr (fun hnextDeep =>
      o.not_both_seventeen_sq_dvd_consecutive t ⟨hdeep, hnextDeep⟩)
  · exact Or.inl hdeep

/-- The unit slice is genuinely invariant, not merely a pattern in the
finite branch rows: divisibility of the public payload by `17` is equivalent
at consecutive times. -/
theorem payload_seventeen_dvd_next_iff (o : Orbit) (t : ℕ) :
    17 ∣ o.payload (t + 1) ↔ 17 ∣ o.payload t := by
  constructor
  · intro hnextPayload
    have hnextCore : 17 ∣ o.core (t + 1) :=
      o.seventeen_dvd_core_of_payload (t + 1) hnextPayload
    have hW : 17 ∣ W (o.payload t) := by
      rw [o.w_factor]
      exact dvd_mul_of_dvd_right hnextCore _
    exact (seventeen_dvd_W_iff (o.payload t)).mp hW
  · intro hPayload
    have hW : 17 ∣ W (o.payload t) :=
      (seventeen_dvd_W_iff (o.payload t)).mpr hPayload
    rw [o.w_factor] at hW
    have hcoprime : Nat.Coprime 17
        (2 ^ (8 * o.branch (t + 1) - 5)) :=
      (by norm_num : Nat.Coprime 17 2).pow_right _
    have hnextCore : 17 ∣ o.core (t + 1) :=
      hcoprime.dvd_of_dvd_mul_left hW
    have hZ : 17 ∣ Z (o.payload (t + 1)) := by
      rw [o.z_factor]
      exact dvd_mul_of_dvd_right hnextCore _
    exact (seventeen_dvd_Z_iff (o.payload (t + 1))).mp hZ

/-- Orbit-level QM146b: every accepted step in the invariant payload slice
admits reduced cores satisfying the exact defect-one recurrence. -/
theorem exists_unit_slice_reduced_balance (o : Orbit) (t : ℕ)
    (hpayload : 17 ∣ o.payload t) :
    ∃ v v', o.core t = 17 * v ∧ o.core (t + 1) = 17 * v' ∧
      2 ^ (8 * o.branch (t + 1) + 15) * v' =
        3 ^ (6 * o.branch t + 11) * v + 1 := by
  obtain ⟨v, hv⟩ := o.seventeen_dvd_core_of_payload t hpayload
  have hnextPayload : 17 ∣ o.payload (t + 1) :=
    (o.payload_seventeen_dvd_next_iff t).mpr hpayload
  obtain ⟨v', hv'⟩ :=
    o.seventeen_dvd_core_of_payload (t + 1) hnextPayload
  exact ⟨v, v', hv, hv', o.unit_slice_reduced_balance t hv hv'⟩

/-- Orbit-level QM146c.  Once consecutive invariant payloads are written as
`17*r` and `17*r'`, the target branch transports their reduced residues by
the stated affine rule in `ZMod 17`. -/
theorem unit_slice_payload_transport (o : Orbit) (t r r' : ℕ)
    (hpayload : o.payload t = 17 * r)
    (hnextPayload : o.payload (t + 1) = 17 * r') :
    ((r' : ℕ) : ZMod 17) =
      reducedResidueStep (o.branch (t + 1)) ((r : ℕ) : ZMod 17) := by
  have hpdiv : 17 ∣ o.payload t := by
    rw [hpayload]
    exact dvd_mul_right 17 r
  have hnextDiv : 17 ∣ o.core (t + 1) := by
    have hW : 17 ∣ W (o.payload t) :=
      (seventeen_dvd_W_iff (o.payload t)).mpr hpdiv
    rw [o.w_factor] at hW
    exact ((by norm_num : Nat.Coprime 17 2).pow_right
      (8 * o.branch (t + 1) - 5)).dvd_of_dvd_mul_left hW
  obtain ⟨v, hv⟩ := hnextDiv
  have hsource : Wbar r =
      2 ^ (8 * o.branch (t + 1) - 5) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Wbar r = W (17 * r) := (W_seventeen_mul r).symm
      _ = W (o.payload t) := by rw [hpayload]
      _ = 2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1) := o.w_factor t
      _ = 17 * (2 ^ (8 * o.branch (t + 1) - 5) * v) := by rw [hv]; ring
  have htarget : Zbar r' = 3 ^ (6 * o.branch (t + 1)) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Zbar r' = Z (17 * r') := (Z_seventeen_mul r').symm
      _ = Z (o.payload (t + 1)) := by rw [hnextPayload]
      _ = 3 ^ (6 * o.branch (t + 1)) * o.core (t + 1) := o.z_factor (t + 1)
      _ = 17 * (3 ^ (6 * o.branch (t + 1)) * v) := by rw [hv]; ring
  exact reduced_payload_step (o.branch_pos (t + 1)) hsource htarget

/-- QM146d, current-state half, stated directly on an orbit in the unit
slice.  A second factor `17` occurs in the current core exactly when the
reduced payload is `14 mod 17`. -/
theorem unit_slice_current_core_deep_iff (o : Orbit) (t r : ℕ)
    (hpayload : o.payload t = 17 * r) :
    17 ^ 2 ∣ o.core t ↔ r % 17 = 14 := by
  have hpdiv : 17 ∣ o.payload t := by
    rw [hpayload]
    exact dvd_mul_right 17 r
  obtain ⟨v, hv⟩ := o.seventeen_dvd_core_of_payload t hpdiv
  have hfactor : Zbar r = 3 ^ (6 * o.branch t) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Zbar r = Z (17 * r) := (Z_seventeen_mul r).symm
      _ = Z (o.payload t) := by rw [hpayload]
      _ = 3 ^ (6 * o.branch t) * o.core t := o.z_factor t
      _ = 17 * (3 ^ (6 * o.branch t) * v) := by rw [hv]; ring
  exact current_core_deep_iff hv hfactor

/-- QM146d, successor half.  Relative to the same source quotient `r`, a
second factor in the successor core occurs exactly at `r=1 mod 17`. -/
theorem unit_slice_successor_core_deep_iff (o : Orbit) (t r : ℕ)
    (hpayload : o.payload t = 17 * r) :
    17 ^ 2 ∣ o.core (t + 1) ↔ r % 17 = 1 := by
  have hpdiv : 17 ∣ o.payload t := by
    rw [hpayload]
    exact dvd_mul_right 17 r
  have hnextDiv : 17 ∣ o.core (t + 1) := by
    have hW : 17 ∣ W (o.payload t) :=
      (seventeen_dvd_W_iff (o.payload t)).mpr hpdiv
    rw [o.w_factor] at hW
    exact ((by norm_num : Nat.Coprime 17 2).pow_right
      (8 * o.branch (t + 1) - 5)).dvd_of_dvd_mul_left hW
  obtain ⟨v, hv⟩ := hnextDiv
  have hfactor : Wbar r =
      2 ^ (8 * o.branch (t + 1) - 5) * v := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 17)
    calc
      17 * Wbar r = W (17 * r) := (W_seventeen_mul r).symm
      _ = W (o.payload t) := by rw [hpayload]
      _ = 2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1) := o.w_factor t
      _ = 17 * (2 ^ (8 * o.branch (t + 1) - 5) * v) := by rw [hv]; ring
  exact successor_core_deep_iff hv hfactor

/-- Universal unit-slice version of the worker's adjacent-depth claim.  If
one payload lies in the invariant slice, both neighboring cores contain one
factor `17`, but the defect recurrence forces at least one of the two to
contain exactly one such factor. -/
theorem unit_slice_consecutive_collision_exact (o : Orbit) (t : ℕ)
    (hpayload : 17 ∣ o.payload t) :
    17 ∣ o.core t ∧ 17 ∣ o.core (t + 1) ∧
      (¬ 17 ^ 2 ∣ o.core t ∨ ¬ 17 ^ 2 ∣ o.core (t + 1)) := by
  apply o.consecutive_collision_factor_exact t
  · exact o.seventeen_dvd_core_of_payload t hpayload
  · exact o.seventeen_dvd_core_of_payload (t + 1)
      ((o.payload_seventeen_dvd_next_iff t).mpr hpayload)

/-- The ternary factor displayed by the self-writing rail is exact, not only
a lower bound. -/
theorem z_exact_factor (o : Orbit) (t : ℕ) :
    3 ^ (6 * o.branch t) ∣ Z (o.payload t) ∧
      ¬ 3 ^ (6 * o.branch t + 1) ∣ Z (o.payload t) := by
  constructor
  · rw [o.z_factor]
    exact dvd_mul_right _ _
  · intro h
    rw [o.z_factor, show 6 * o.branch t + 1 =
      (6 * o.branch t) + 1 by omega, pow_succ'] at h
    have h' : 3 ^ (6 * o.branch t) * 3 ∣
        3 ^ (6 * o.branch t) * o.core t := by
      simpa [mul_comm] using h
    have hthree : 3 ∣ o.core t :=
      (Nat.mul_dvd_mul_iff_left
        (pow_pos (by norm_num : 0 < (3 : ℕ)) _)).mp h'
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hthree
    rw [o.core_mod_three] at hzero
    omega

/-- The binary delay is likewise exact because the normalized successor core
is odd. -/
theorem w_exact_factor (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) - 5) ∣ W (o.payload t) ∧
      ¬ 2 ^ (8 * o.branch (t + 1) - 5 + 1) ∣ W (o.payload t) := by
  constructor
  · rw [o.w_factor]
    exact dvd_mul_right _ _
  · intro h
    rw [o.w_factor, pow_succ'] at h
    have h' : 2 ^ (8 * o.branch (t + 1) - 5) * 2 ∣
        2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1) := by
      simpa [mul_comm] using h
    have htwo : 2 ∣ o.core (t + 1) :=
      (Nat.mul_dvd_mul_iff_left
        (pow_pos (by norm_num : 0 < (2 : ℕ)) _)).mp h'
    exact (Nat.not_even_iff_odd.mpr (o.core_odd (t + 1)))
      (even_iff_two_dvd.mpr htwo)

/-- Forgetting the packet coordinate gives precisely the universal positive
EC17 orbit used by the existing obstruction library. -/
def toEC17 (o : Orbit) : EtherCounterStateNoRepeat.Orbit where
  branch := o.branch
  branch_pos := o.branch_pos
  core := o.core
  core_pos := o.core_pos
  balance := o.balance

/-- In zero-based indexing the same object is the exact ternary-core orbit
of the autonomous ether-counter development. -/
def toTernaryCore (o : Orbit) : EtherCounterAperiodic.TernaryCoreOrbit where
  level t := o.branch t - 1
  core := o.core
  core_pos := o.core_pos
  balance t := by
    have ht := o.branch_pos t
    have ht1 := o.branch_pos (t + 1)
    rw [show 8 * (o.branch (t + 1) - 1) + 23 =
        8 * o.branch (t + 1) + 15 by omega,
      show 6 * (o.branch t - 1) + 17 =
        6 * o.branch t + 11 by omega]
    exact o.balance t

/-- Reinsert the forced factor `3` and the dyadic public register.  This is
the converse normalization needed to reuse the audited periodic-schedule
obstruction. -/
def ternaryCoreToNormalized (o : EtherCounterAperiodic.TernaryCoreOrbit) :
    EtherCounterAperiodic.NormalizedOrbit where
  level := o.level
  value := fun t => 2 ^ (8 * o.level t + 3) * (3 * o.core t)
  oddPart := fun t => 3 * o.core t
  value_pos t := Nat.mul_pos (pow_pos (by omega) _)
    (Nat.mul_pos (by omega) (o.core_pos t))
  factor t := rfl
  transition t := by
    calc
      2 ^ 20 *
          (2 ^ (8 * o.level (t + 1) + 3) * (3 * o.core (t + 1))) =
          3 * (2 ^ (8 * o.level (t + 1) + 23) * o.core (t + 1)) := by
        rw [show 8 * o.level (t + 1) + 23 =
          20 + (8 * o.level (t + 1) + 3) by omega, pow_add]
        ring
      _ = 3 * (3 ^ (6 * o.level t + 17) * o.core t + 17) := by
        rw [o.balance]
      _ = 3 ^ (6 * o.level t + 17) * (3 * o.core t) + 51 := by ring

def toNormalized (o : Orbit) : EtherCounterAperiodic.NormalizedOrbit :=
  ternaryCoreToNormalized o.toTernaryCore

/-! ## Exact promotion from a bare EC17 tail -/

/-- Every core of a bare positive EC17 orbit is odd.  This reuses the exact
finite-prefix parity theorem at a prefix long enough to contain the selected
outgoing transition. -/
theorem bareEC17_core_odd (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    Odd (g.core t) := by
  rw [Nat.odd_iff]
  have h := EtherCounterResidueBound.NaturalPrefix.core_mod_two_eq_one
    (g.toNaturalPrefix (t + 1)) t (by omega)
  simpa [EtherCounterStateNoRepeat.Orbit.toNaturalPrefix] using h

/-- Zero-based ternary-core presentation of an arbitrary bare positive EC17
orbit. -/
def bareEC17ToTernaryCore (g : EtherCounterStateNoRepeat.Orbit) :
    EtherCounterAperiodic.TernaryCoreOrbit where
  level t := g.branch t - 1
  core := g.core
  core_pos := g.core_pos
  balance t := by
    have ht := g.branch_pos t
    have ht1 := g.branch_pos (t + 1)
    rw [show 8 * (g.branch (t + 1) - 1) + 23 =
        8 * g.branch (t + 1) + 15 by omega,
      show 6 * (g.branch t - 1) + 17 =
        6 * g.branch t + 11 by omega]
    exact g.balance t

/-- Every core after the initial one is `1 mod 3`; hence discarding one
state supplies the exact ternary valuation field required by the
self-writing structure. -/
theorem bareEC17_core_next_mod_three
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.core (t + 1) % 3 = 1 := by
  simpa [bareEC17ToTernaryCore] using
    (bareEC17ToTernaryCore g).core_next_mod_three t

/-- The `2^20` part of the centered packet rail is automatic on every
positive bare EC17 transition.  This is QM148a-b in congruence form. -/
theorem bareEC17_centered_dyadic_modEq {n m u u' : ℕ} (hm : 0 < m)
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Nat.ModEq (2 ^ 20) (3 ^ (6 * n) * u) 494251421 := by
  have hleft : Nat.ModEq (2 ^ 20)
      (3 ^ 11 * (3 ^ (6 * n) * u) + 17) 0 := by
    rw [Nat.modEq_zero_iff_dvd]
    have heq : 3 ^ 11 * (3 ^ (6 * n) * u) + 17 =
        2 ^ (8 * m + 15) * u' := by
      calc
        3 ^ 11 * (3 ^ (6 * n) * u) + 17 =
            3 ^ (6 * n + 11) * u + 17 := by
          rw [pow_add]
          ring
        _ = 2 ^ (8 * m + 15) * u' := ht.symm
    rw [heq, show 8 * m + 15 = 20 + (8 * m - 5) by omega, pow_add]
    simpa [mul_assoc] using
      (dvd_mul_right (2 ^ 20) (2 ^ (8 * m - 5) * u'))
  have hright : Nat.ModEq (2 ^ 20)
      (3 ^ 11 * 494251421 + 17) 0 := by
    rw [Nat.modEq_zero_iff_dvd]
    use 83499104
    simpa [Z, W] using determinant_identity 0
  have hadd : Nat.ModEq (2 ^ 20)
      (3 ^ 11 * (3 ^ (6 * n) * u) + 17)
      (3 ^ 11 * 494251421 + 17) := hleft.trans hright.symm
  have hmul : Nat.ModEq (2 ^ 20)
      (3 ^ 11 * (3 ^ (6 * n) * u)) (3 ^ 11 * 494251421) :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl 17) hadd
  exact Nat.ModEq.cancel_left_of_coprime (by norm_num) hmul

/-- Membership of one branch/core state in the affine `Z` payload rail. -/
def OnZRail (n u : ℕ) : Prop :=
  ∃ q, Z q = 3 ^ (6 * n) * u

/-- Divisibility-and-height form of affine rail membership.  This removes
the existential payload from adversarial checks: the centered state must be
at least the rail base and its excess must be divisible by the full stride
`473 * 2^20`, not merely by the packet-color modulus `473`. -/
theorem onZRail_iff (n u : ℕ) :
    OnZRail n u ↔
      494251421 ≤ 3 ^ (6 * n) * u ∧
      495976448 ∣ 3 ^ (6 * n) * u - 494251421 := by
  constructor
  · rintro ⟨q, hq⟩
    constructor
    · rw [← hq]
      simp [Z]
    · use q
      rw [← hq]
      simp [Z]
  · rintro ⟨hle, q, hq⟩
    refine ⟨q, ?_⟩
    simp only [Z]
    omega

theorem zRail_stride_factorization :
    495976448 = 473 * 2 ^ 20 := by norm_num

/-- The two centered congruences force full affine-rail membership.  The
height inequality is not an extra hypothesis: both centered values lie
strictly below one stride if the candidate lies below the rail base, so
congruence would force equality. -/
theorem onZRail_of_centered_modEq {n u : ℕ}
    (h473 : Nat.ModEq 473 (3 ^ (6 * n) * u) 494251421)
    (hdyadic : Nat.ModEq (2 ^ 20) (3 ^ (6 * n) * u) 494251421) :
    OnZRail n u := by
  have hcoprime : Nat.Coprime 473 (2 ^ 20) := by norm_num
  have hfull : Nat.ModEq (473 * 2 ^ 20)
      (3 ^ (6 * n) * u) 494251421 :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp ⟨h473, hdyadic⟩
  have hbase_lt : 494251421 < 473 * 2 ^ 20 := by norm_num
  have hle : 494251421 ≤ 3 ^ (6 * n) * u := by
    by_contra hnot
    have hsmall : 3 ^ (6 * n) * u < 494251421 := by omega
    have hcand_lt : 3 ^ (6 * n) * u < 473 * 2 ^ 20 :=
      lt_trans hsmall hbase_lt
    change (3 ^ (6 * n) * u) % (473 * 2 ^ 20) =
      494251421 % (473 * 2 ^ 20) at hfull
    rw [Nat.mod_eq_of_lt hcand_lt, Nat.mod_eq_of_lt hbase_lt] at hfull
    omega
  rw [onZRail_iff]
  refine ⟨hle, ?_⟩
  rw [zRail_stride_factorization]
  exact (Nat.modEq_iff_dvd' hle).mp hfull.symm

/-- At a state with an outgoing positive bare EC17 step, packet color zero
is already sufficient for the complete affine `Z` rail. -/
theorem onZRail_of_packetColor_zero
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ)
    (hcolor : Nat.ModEq 473
      (2 ^ (8 * g.branch t - 5) * g.core t + 291427) 0) :
    OnZRail (g.branch t) (g.core t) := by
  apply onZRail_of_centered_modEq
  · exact (packetColor_zero_iff_centered_modEq (g.branch_pos t)).mp hcolor
  · exact bareEC17_centered_dyadic_modEq (g.branch_pos (t + 1))
      (g.balance t)

/-- Packet color at every bare EC17 state is equivalent to its color at the
initial state.  This packages both propagation and reflection. -/
theorem packetColor_zero_iff_initial
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    Nat.ModEq 473
        (2 ^ (8 * g.branch t - 5) * g.core t + 291427) 0 ↔
      Nat.ModEq 473
        (2 ^ (8 * g.branch 0 - 5) * g.core 0 + 291427) 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hstep := packetColor_zero_iff
        (g.branch_pos t) (g.branch_pos (t + 1))
        (s := 2 ^ (8 * g.branch t - 5) * g.core t)
        (s' := 2 ^ (8 * g.branch (t + 1) - 5) * g.core (t + 1))
        (u := g.core t) (u' := g.core (t + 1))
        (n := g.branch t) (m := g.branch (t + 1)) rfl rfl (g.balance t)
      exact hstep.trans ih

/-- One packet-color-zero state forces the full affine rail at every state
of the positive bare ray. -/
theorem all_onZRail_of_packetColor_zero
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ)
    (hcolor : Nat.ModEq 473
      (2 ^ (8 * g.branch t - 5) * g.core t + 291427) 0) :
    ∀ j, OnZRail (g.branch j) (g.core j) := by
  have hinitial := (packetColor_zero_iff_initial g t).mp hcolor
  intro j
  apply onZRail_of_packetColor_zero g j
  exact (packetColor_zero_iff_initial g j).mpr hinitial

/-- If every state of a bare EC17 tail lies on the affine `Z` rail, the
entire self-writing orbit is forced.  The `W` factor is not an extra
assumption: it follows from the determinant identity and the bare EC17
balance after cancelling the common factor `2^20`. -/
noncomputable def promoteBareTail
    (g : EtherCounterStateNoRepeat.Orbit)
    (hrail : ∀ t, OnZRail (g.branch (t + 1)) (g.core (t + 1))) :
    SelfWritingKL.Orbit where
  branch t := g.branch (t + 1)
  branch_pos t := g.branch_pos (t + 1)
  core t := g.core (t + 1)
  core_pos t := g.core_pos (t + 1)
  core_odd t := bareEC17_core_odd g (t + 1)
  core_mod_three t := bareEC17_core_next_mod_three g t
  payload t := (hrail t).choose
  z_factor t := (hrail t).choose_spec
  w_factor t := by
    apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ 20)
    calc
      2 ^ 20 * W (hrail t).choose =
          3 ^ 11 * Z (hrail t).choose + 17 :=
        (determinant_identity (hrail t).choose).symm
      _ = 3 ^ (6 * g.branch (t + 1) + 11) *
          g.core (t + 1) + 17 := by
        rw [(hrail t).choose_spec, ← mul_assoc, ← pow_add]
        congr 3
        omega
      _ = 2 ^ (8 * g.branch (t + 2) + 15) * g.core (t + 2) :=
        (g.balance (t + 1)).symm
      _ = 2 ^ 20 *
          (2 ^ (8 * g.branch (t + 2) - 5) * g.core (t + 2)) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        have hpos := g.branch_pos (t + 2)
        omega

/-- QM148d: one color-zero state is sufficient to promote the shifted bare
ray.  Propagation/reflection supplies the color everywhere; the preceding
theorems turn it into full affine-rail membership. -/
noncomputable def promoteBareTailOfPacketColor
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ)
    (hcolor : Nat.ModEq 473
      (2 ^ (8 * g.branch t - 5) * g.core t + 291427) 0) :
    SelfWritingKL.Orbit :=
  promoteBareTail g (fun j =>
    all_onZRail_of_packetColor_zero g t hcolor (j + 1))

/-- Exact promotion criterion.  A bare positive EC17 ray becomes a
self-writing orbit after discarding its first state if and only if every
remaining state belongs to the affine `Z` rail.  Packet color zero is only a
necessary congruence shadow of this stronger all-time rail condition. -/
theorem all_onZRail_iff_exists_selfWriting_tail
    (g : EtherCounterStateNoRepeat.Orbit) :
    (∀ t, OnZRail (g.branch (t + 1)) (g.core (t + 1))) ↔
      ∃ o : SelfWritingKL.Orbit,
        o.branch = (fun t => g.branch (t + 1)) ∧
        o.core = (fun t => g.core (t + 1)) := by
  constructor
  · intro hrail
    exact ⟨promoteBareTail g hrail, rfl, rfl⟩
  · rintro ⟨o, hbranch, hcore⟩
    intro t
    refine ⟨o.payload t, ?_⟩
    simpa [hbranch, hcore] using o.z_factor t

/-- Exact single-color promotion criterion for a supplied positive bare
ray.  Thus the old all-time affine-rail premise is equivalent to checking
the packet color at any one state. -/
theorem packetColor_zero_iff_exists_selfWriting_tail
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    Nat.ModEq 473
        (2 ^ (8 * g.branch t - 5) * g.core t + 291427) 0 ↔
      ∃ o : SelfWritingKL.Orbit,
        o.branch = (fun j => g.branch (j + 1)) ∧
        o.core = (fun j => g.core (j + 1)) := by
  constructor
  · intro hcolor
    exact (all_onZRail_iff_exists_selfWriting_tail g).mp
      (fun j => all_onZRail_of_packetColor_zero g t hcolor (j + 1))
  · intro hexists
    have hrail := (all_onZRail_iff_exists_selfWriting_tail g).mpr hexists 0
    have hrailData := (onZRail_iff (g.branch 1) (g.core 1)).mp hrail
    have h473 : Nat.ModEq 473
        (3 ^ (6 * g.branch 1) * g.core 1) 494251421 := by
      apply ((Nat.modEq_iff_dvd' hrailData.1).mpr ?_).symm
      exact dvd_trans (by norm_num : 473 ∣ 495976448) hrailData.2
    have hcolorOne : Nat.ModEq 473
        (2 ^ (8 * g.branch 1 - 5) * g.core 1 + 291427) 0 :=
      (packetColor_zero_iff_centered_modEq (g.branch_pos 1)).mpr h473
    have hinitial := (packetColor_zero_iff_initial g 1).mp hcolorOne
    exact (packetColor_zero_iff_initial g t).mpr hinitial

/-- Single-state adversarial consumer.  Failure of the full affine rail at
any time prevents the given bare ray from being the tail of a self-writing
orbit, even if its dyadic address stabilizes and its packet color vanishes. -/
theorem no_selfWriting_tail_of_not_onZRail
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ)
    (hfail : ¬ OnZRail (g.branch (t + 1)) (g.core (t + 1))) :
    ¬ ∃ o : SelfWritingKL.Orbit,
      o.branch = (fun j => g.branch (j + 1)) ∧
      o.core = (fun j => g.core (j + 1)) := by
  intro hexists
  have hall := (all_onZRail_iff_exists_selfWriting_tail g).mpr hexists
  exact hfail (hall t)

/-! ## Canonical backward dyadic address -/

/-- One public-payload reset instruction with target branch `m`. -/
def payloadResetStep (m : ℕ) : KLDyadicReset.ResetStep where
  N := 8 * m + 15
  O := 6 * m + 11
  delta := branchDelta m

/-- Finite public-payload program written by a list of target branches. -/
def payloadResetWord (targets : List ℕ) : List KLDyadicReset.ResetStep :=
  targets.map payloadResetStep

/-- A positive finite public-payload chain whose every payload stays in the
same shallow class `17*c (mod 17^2)`. -/
def ObeysPositivePayloadRail (c : ℕ) : List ℕ → ℤ → ℤ → Prop
  | [], qStart, qEnd =>
      qEnd = qStart ∧ 0 < qStart ∧ Int.ModEq (17 ^ 2) qStart (17 * c)
  | m :: targets, qStart, qEnd =>
      0 < qStart ∧ Int.ModEq (17 ^ 2) qStart (17 * c) ∧
        ∃ qNext : ℤ,
          (2 : ℤ) ^ (8 * m + 15) * qNext =
            (3 : ℤ) ^ (6 * m + 11) * qStart + branchDelta m ∧
          ObeysPositivePayloadRail c targets qNext qEnd

theorem obeysPositive_start_pos
    (w : List KLDyadicReset.ResetStep) {qStart qEnd : ℤ}
    (h : KLDyadicReset.ObeysPositive w qStart qEnd) : 0 < qStart := by
  cases w with
  | nil => exact h.2
  | cons e w => exact h.1

/-- Every finite dyadic reset word admits a positive realization whose
initial payload lies in any prescribed class modulo `17^2`.  The dyadic
cylinder width is a unit modulo `17^2`, and a further multiple of `17^2`
preserves the class while making the whole finite chain positive. -/
theorem exists_positive_obeys_initial_mod_seventeen_sq
    (w : List KLDyadicReset.ResetStep) (c : ℕ) :
    ∃ qStart qEnd : ℤ,
      KLDyadicReset.ObeysPositive w qStart qEnd ∧
        Int.ModEq (17 ^ 2) qStart (17 * c) := by
  obtain ⟨qStart, hterminal⟩ := KLDyadicReset.exists_terminalDivisible w
  obtain ⟨qEnd, hobeys⟩ :=
    KLDyadicReset.exists_obeys_of_terminalDivisible w hterminal
  obtain ⟨T, hpositive⟩ :=
    KLDyadicReset.obeysPositive_shift_eventually w hobeys
  have htwo : IsUnit (2 : ZMod (17 ^ 2)) := by
    change IsUnit ((2 : ℕ) : ZMod (17 ^ 2))
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  have hwidth : IsUnit
      ((2 : ZMod (17 ^ 2)) ^ (KLDyadicReset.programData w).S) :=
    htwo.pow _
  obtain ⟨widthUnit, hwidthUnit⟩ := hwidth
  let z : ZMod (17 ^ 2) :=
    (widthUnit⁻¹ : ZMod (17 ^ 2)) *
      ((17 * c : ℕ) - (qStart : ZMod (17 ^ 2)))
  let t0 : ℕ := z.val
  let t : ℕ := t0 + 17 ^ 2 * T
  have htT : T ≤ t := by
    dsimp [t]
    omega
  have hpos := hpositive t htT
  have htz : ((t : ℕ) : ZMod (17 ^ 2)) = z := by
    calc
      ((t : ℕ) : ZMod (17 ^ 2)) =
          z.val + ((17 ^ 2 : ℕ) : ZMod (17 ^ 2)) * T := by
        simp [t, t0]
      _ = z.val := by rw [ZMod.natCast_self]; ring
      _ = z := ZMod.natCast_zmod_val z
  have hwidthz :
      (2 : ZMod (17 ^ 2)) ^ (KLDyadicReset.programData w).S * z =
        (17 : ZMod (17 ^ 2)) * c - (qStart : ZMod (17 ^ 2)) := by
    rw [← hwidthUnit]
    simp [z, Nat.cast_mul]
  refine ⟨qStart + (2 : ℤ) ^ (KLDyadicReset.programData w).S * t,
    qEnd + (3 : ℤ) ^ (KLDyadicReset.programData w).P * t,
    hpos, ?_⟩
  apply (ZMod.intCast_eq_intCast_iff
    (qStart + (2 : ℤ) ^ (KLDyadicReset.programData w).S * t)
    (17 * (c : ℤ)) (17 ^ 2)).mp
  push_cast
  rw [htz, hwidthz]
  ring

/-- A positive realization whose initial payload is on a fixed reduced rail
stays on that rail throughout the finite word. -/
theorem obeysPositivePayloadRail_of_fixed
    (targets : List ℕ) (c : ℕ) {qStart qEnd : ℤ}
    (hpositive : KLDyadicReset.ObeysPositive
      (payloadResetWord targets) qStart qEnd)
    (hfixed : ∀ m ∈ targets,
      0 < m ∧ reducedResidueStep m (c : ZMod 17) = c)
    (hsource : Int.ModEq (17 ^ 2) qStart (17 * c)) :
    ObeysPositivePayloadRail c targets qStart qEnd := by
  induction targets generalizing qStart with
  | nil =>
      exact ⟨hpositive.1, hpositive.2, hsource⟩
  | cons m targets ih =>
      simp only [payloadResetWord, List.map_cons,
        KLDyadicReset.ObeysPositive] at hpositive
      obtain ⟨hqpos, qNext, hstep, htail⟩ := hpositive
      have hmdata := hfixed m (by simp)
      have hqNextPos := obeysPositive_start_pos _ htail
      have hnext : Int.ModEq (17 ^ 2) qNext (17 * c) :=
        int_payload_mod_seventeen_sq_step hmdata.1 hqpos hqNextPos
          (by simpa [payloadResetStep] using hstep) hsource hmdata.2
      refine ⟨hqpos, hsource, qNext,
        by simpa [payloadResetStep] using hstep, ?_⟩
      apply ih htail
      · intro m' hm'
        exact hfixed m' (by simp [hm'])
      · exact hnext

/-- QM149a in its reusable form: every finite target word on a fixed shallow
rail has a strictly positive exact public-payload realization, and every
payload in the realization is `17*c (mod 17^2)`. -/
theorem exists_positive_payload_rail_word
    (targets : List ℕ) (c : ℕ)
    (hfixed : ∀ m ∈ targets,
      0 < m ∧ reducedResidueStep m (c : ZMod 17) = c) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail c targets qStart qEnd := by
  obtain ⟨qStart, qEnd, hpositive, hsource⟩ :=
    exists_positive_obeys_initial_mod_seventeen_sq
      (payloadResetWord targets) c
  exact ⟨qStart, qEnd,
    obeysPositivePayloadRail_of_fixed targets c hpositive hfixed hsource⟩

/-- Convenient residue-class form.  It applies directly to each of the
eight universal fixed rails proved above. -/
theorem exists_positive_payload_rail_word_of_branch_class
    (j c : ℕ) (hj : 0 < j)
    (hrail : ∀ k, reducedResidueStep (j + 8 * k) (c : ZMod 17) = c)
    (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = j + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail c targets qStart qEnd := by
  apply exists_positive_payload_rail_word targets c
  intro m hm
  obtain ⟨k, rfl⟩ := hclass m hm
  exact ⟨by omega, hrail k⟩

theorem exists_positive_one_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 1 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 12 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 1 12 (by omega)
    reducedResidueStep_one_rail targets hclass

theorem exists_positive_two_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 2 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 2 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 2 2 (by omega)
    reducedResidueStep_two_rail targets hclass

theorem exists_positive_three_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 3 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 13 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 3 13 (by omega)
    reducedResidueStep_three_rail targets hclass

theorem exists_positive_four_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 4 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 3 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 4 3 (by omega)
    reducedResidueStep_four_rail targets hclass

theorem exists_positive_five_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 5 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 15 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 5 15 (by omega)
    reducedResidueStep_five_rail targets hclass

theorem exists_positive_six_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 6 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 6 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 6 6 (by omega)
    reducedResidueStep_six_rail targets hclass

theorem exists_positive_seven_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 7 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 9 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 7 9 (by omega)
    reducedResidueStep_seven_rail targets hclass

theorem exists_positive_eight_rail_word (targets : List ℕ)
    (hclass : ∀ m ∈ targets, ∃ k, m = 8 + 8 * k) :
    ∃ qStart qEnd : ℤ,
      ObeysPositivePayloadRail 0 targets qStart qEnd :=
  exists_positive_payload_rail_word_of_branch_class 8 0 (by omega)
    reducedResidueStep_eight_rail targets hclass

/-- Exact public-payload reset program attached to a proposed branch
schedule.  Step `t` reads the target branch `branch (t+1)`, matching the
payload recurrence of an orbit with branch sequence `branch`. -/
def payloadResetProgramOfBranch (branch : ℕ → ℕ) (t : ℕ) :
    KLDyadicReset.ResetStep :=
  payloadResetStep (branch (t + 1))

/-- Every supplied self-writing orbit follows its public-payload reset
program literally. -/
theorem follows_payloadResetProgram (o : Orbit) :
    KLDyadicReset.Follows (payloadResetProgramOfBranch o.branch)
      (fun t => (o.payload t : ℤ)) := by
  intro t
  simp only [payloadResetProgramOfBranch, payloadResetStep]
  exact_mod_cast o.payload_branch_recurrence t

/-- Nonnegativity propagates along the public program because every positive
target branch has a strictly positive affine defect. -/
theorem payload_follows_nonnegative
    (branch : ℕ → ℕ) (hbranch : ∀ t, 0 < branch t)
    (q : ℕ → ℤ)
    (hq : KLDyadicReset.Follows (payloadResetProgramOfBranch branch) q)
    (hzero : 0 ≤ q 0) : ∀ t, 0 ≤ q t := by
  intro t
  induction t with
  | zero => exact hzero
  | succ t ih =>
      have hstep := hq t
      simp only [payloadResetProgramOfBranch, payloadResetStep] at hstep
      have hdelta : 0 < (branchDelta (branch (t + 1)) : ℤ) := by
        exact_mod_cast branchDelta_positive (hbranch (t + 1))
      have hrhs : 0 <
          (3 : ℤ) ^ (6 * branch (t + 1) + 11) * q t +
            branchDelta (branch (t + 1)) := by
        have hproduct : 0 ≤
            (3 : ℤ) ^ (6 * branch (t + 1) + 11) * q t :=
          mul_nonneg (by positivity) ih
        exact add_pos_of_nonneg_of_pos hproduct hdelta
      have hlhs : 0 <
          (2 : ℤ) ^ (8 * branch (t + 1) + 15) * q (t + 1) := by
        rw [hstep]
        exact hrhs
      exact nonneg_of_mul_nonneg_right hlhs.le (by positivity)

/-- Cast a nonnegative integer payload chain back to the literal natural
affine recurrence. -/
theorem payload_toNat_recurrence
    (branch : ℕ → ℕ) (q : ℕ → ℤ)
    (hq : KLDyadicReset.Follows (payloadResetProgramOfBranch branch) q)
    (hqnonneg : ∀ t, 0 ≤ q t) (t : ℕ) :
    2 ^ (8 * branch (t + 1) + 15) * (q (t + 1)).toNat =
      3 ^ (6 * branch (t + 1) + 11) * (q t).toNat +
        branchDelta (branch (t + 1)) := by
  have hstep := hq t
  simp only [payloadResetProgramOfBranch, payloadResetStep] at hstep
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Int.toNat_of_nonneg (hqnonneg t),
    Int.toNat_of_nonneg (hqnonneg (t + 1))]
  exact hstep

/-- Eventual-zero public carry is sufficient to construct a complete
self-writing orbit after discarding the chain's first payload.  The shift is
essential: the first affine step writes the first certified ternary branch. -/
noncomputable def promotePayloadChain
    (branch : ℕ → ℕ) (hbranch : ∀ t, 0 < branch t)
    (q : ℕ → ℤ)
    (hq : KLDyadicReset.Follows (payloadResetProgramOfBranch branch) q)
    (hzero : 0 ≤ q 0) : Orbit := by
  have hqnonneg := payload_follows_nonnegative branch hbranch q hq hzero
  let qNat : ℕ → ℕ := fun t => (q t).toNat
  have hrec : ∀ t,
      2 ^ (8 * branch (t + 1) + 15) * qNat (t + 1) =
        3 ^ (6 * branch (t + 1) + 11) * qNat t +
          branchDelta (branch (t + 1)) := by
    intro t
    exact payload_toNat_recurrence branch q hq hqnonneg t
  exact
    { branch := fun t => branch (t + 1)
      branch_pos := fun t => hbranch (t + 1)
      payload := fun t => qNat (t + 1)
      core := fun t => payloadStepCore (branch (t + 1)) (qNat t)
      core_pos := fun t => Nat.pos_of_ne_zero (fun hcore => by
        have hodd := payloadStepCore_odd (hbranch (t + 1)) (hrec t)
        rw [hcore] at hodd
        norm_num at hodd)
      core_odd := fun t => payloadStepCore_odd (hbranch (t + 1)) (hrec t)
      core_mod_three := fun t =>
        payloadStepCore_mod_three (hbranch (t + 1)) (hrec t)
      z_factor := fun t => payloadStepCore_factor_Z
        (hbranch (t + 1)) (hrec t)
      w_factor := fun t => payloadStepCore_factor_W
        (hbranch (t + 2)) (hrec (t + 1)) }

/-- Complete sufficient address criterion for a shifted self-writing tail. -/
theorem exists_selfWriting_tail_of_eventuallyZeroPayloadCarry
    (branch : ℕ → ℕ) (hbranch : ∀ t, 0 < branch t)
    (hcarry : KLDyadicReset.EventuallyZeroCarry
      (payloadResetProgramOfBranch branch)) :
    ∃ o : Orbit, o.branch = (fun t => branch (t + 1)) := by
  rw [KLDyadicReset.eventuallyZeroCarry_iff_exists_nonnegative_follows] at hcarry
  obtain ⟨q, hq, hzero⟩ := hcarry
  exact ⟨promotePayloadChain branch hbranch q hq hzero, rfl⟩

/-- Necessary public-address condition for every self-writing orbit. -/
theorem payloadCarry_eventually_zero (o : Orbit) :
    KLDyadicReset.EventuallyZeroCarry
      (payloadResetProgramOfBranch o.branch) := by
  apply KLDyadicReset.eventuallyZeroCarry_of_follows
    (payloadResetProgramOfBranch o.branch) (fun t => (o.payload t : ℤ))
      o.follows_payloadResetProgram
  positivity

/-- Branch-only adversarial consumer for the exact public program. -/
theorem no_orbit_with_branch_of_nonzero_payload_carries
    (branch : ℕ → ℕ)
    (hbad : KLDyadicReset.NonzeroCarriesArbitrarilyLate
      (payloadResetProgramOfBranch branch)) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  obtain ⟨J, hzero⟩ := o.payloadCarry_eventually_zero
  obtain ⟨K, hJK, hne⟩ := hbad J
  exact hne (hzero K hJK)

/-- The exact reset program read from an arbitrary proposed branch
schedule.  It is defined before assuming that the schedule has an orbit, so
its canonical carries can be audited independently. -/
def resetProgramOfBranch (branch : ℕ → ℕ) (t : ℕ) :
    KLDyadicReset.ResetStep where
  N := 8 * branch (t + 1) + 15
  O := 6 * branch t + 11
  delta := 17

/-- Any nonnegative integer chain following the branch reset program is in
fact strictly positive at every time.  Positivity after time zero follows
from the positive defect.  At time zero, equality with defect `17` rules out
zero because the left side is divisible by two. -/
theorem follows_positive_of_nonnegative
    (branch : ℕ → ℕ) (m : ℕ → ℤ)
    (hm : KLDyadicReset.Follows (resetProgramOfBranch branch) m)
    (h0 : 0 ≤ m 0) : ∀ t, 0 < m t := by
  have hzero_ne : m 0 ≠ 0 := by
    intro hzero
    have hstep := hm 0
    simp only [resetProgramOfBranch] at hstep
    rw [hzero, mul_zero, zero_add] at hstep
    have hpow : (2 : ℤ) ∣ (2 : ℤ) ^ (8 * branch 1 + 15) :=
      dvd_pow_self 2 (by omega)
    have hleft : (2 : ℤ) ∣
        (2 : ℤ) ^ (8 * branch 1 + 15) * m 1 :=
      dvd_mul_of_dvd_left hpow _
    rw [hstep] at hleft
    norm_num at hleft
  have hbase : 0 < m 0 := by omega
  intro t
  induction t with
  | zero => exact hbase
  | succ t ih =>
      have hstep := hm t
      simp only [resetProgramOfBranch] at hstep
      have hrhs : 0 <
          (3 : ℤ) ^ (6 * branch t + 11) * m t + 17 := by
        have hproduct : 0 <
            (3 : ℤ) ^ (6 * branch t + 11) * m t :=
          mul_pos (by positivity) ih
        omega
      have hlhs : 0 <
          (2 : ℤ) ^ (8 * branch (t + 1) + 15) * m (t + 1) := by
        rw [hstep]
        exact hrhs
      have hreordered : 0 <
          m (t + 1) * (2 : ℤ) ^ (8 * branch (t + 1) + 15) := by
        simpa [mul_comm] using hlhs
      exact pos_of_mul_pos_left hreordered (by positivity)

/-- Complete ordinary-address characterization for the bare positive EC17
core recurrence on a prescribed positive branch schedule.  Eventual zero
carry is neither merely necessary nor heuristic: it is equivalent to the
existence of a positive natural EC17 core ray.  Packet color and the affine
`Z/W` self-writing rail remain additional, separate constraints. -/
theorem eventuallyZeroCarry_iff_exists_bareEC17
    (branch : ℕ → ℕ) (hbranch : ∀ t, 0 < branch t) :
    KLDyadicReset.EventuallyZeroCarry (resetProgramOfBranch branch) ↔
      ∃ o : EtherCounterStateNoRepeat.Orbit, o.branch = branch := by
  rw [KLDyadicReset.eventuallyZeroCarry_iff_exists_nonnegative_follows]
  constructor
  · rintro ⟨m, hm, h0⟩
    have hmpos := follows_positive_of_nonnegative branch m hm h0
    let o : EtherCounterStateNoRepeat.Orbit :=
      { branch := branch
        branch_pos := hbranch
        core := fun t => (m t).toNat
        core_pos := fun t => by
          have hcast := Int.toNat_of_nonneg (hmpos t).le
          apply Nat.pos_of_ne_zero
          intro hzero
          have hmzero : m t = 0 := by
            calc
              m t = ((m t).toNat : ℤ) := hcast.symm
              _ = 0 := by simp [hzero]
          exact (ne_of_gt (hmpos t)) hmzero
        balance := fun t => by
          have hstep := hm t
          simp only [resetProgramOfBranch] at hstep
          rw [← Int.toNat_of_nonneg (hmpos t).le,
            ← Int.toNat_of_nonneg (hmpos (t + 1)).le] at hstep
          exact_mod_cast hstep }
    exact ⟨o, rfl⟩
  · rintro ⟨o, rfl⟩
    let m : ℕ → ℤ := fun t => o.core t
    refine ⟨m, ?_, by simp [m]⟩
    intro t
    simp only [resetProgramOfBranch, m]
    exact_mod_cast o.balance t

def resetProgram (o : Orbit) : ℕ → KLDyadicReset.ResetStep :=
  resetProgramOfBranch o.branch

/-- The normalized EC17 cores follow that reset program literally. -/
theorem follows_resetProgram (o : Orbit) :
    KLDyadicReset.Follows o.resetProgram (fun t => (o.core t : ℤ)) := by
  intro t
  simp only [resetProgram, resetProgramOfBranch]
  exact_mod_cast o.balance t

/-- Every self-writing step contributes positive dyadic precision, so the
accumulated reset precision dominates the number of steps. -/
theorem resetPrecision_ge (o : Orbit) (J : ℕ) :
    J ≤ (KLDyadicReset.cumulative o.resetProgram J).S := by
  induction J with
  | zero => simp [KLDyadicReset.cumulative, KLDyadicReset.initialData]
  | succ J ih =>
      rw [KLDyadicReset.cumulative_succ_S]
      have hN : 0 < (o.resetProgram J).N := by
        simp [resetProgram, resetProgramOfBranch]
      omega

/-- The accumulated binary precision of the self-writing reset program is
unbounded. -/
theorem resetPrecision_unbounded (o : Orbit) :
    ∀ L, ∃ J, L ≤ (KLDyadicReset.cumulative o.resetProgram J).S := by
  intro L
  exact ⟨L, o.resetPrecision_ge L⟩

/-- Necessary inverse-limit condition for an ordinary self-writing orbit:
the canonical initial EC17-core residues must eventually become literally
constant at the one natural initial core. -/
theorem initialResidue_eventually_constant (o : Orbit) :
    ∃ J, ∀ K, J ≤ K →
      KLDyadicReset.initialResidue o.resetProgram K = o.core 0 := by
  simpa using KLDyadicReset.initialResidue_eventually_constant_of_follows
    o.resetProgram (fun t => (o.core t : ℤ)) o.follows_resetProgram
      (by positivity) o.resetPrecision_unbounded

/-- Operational version of the same obstruction: all sufficiently late
canonical address carries must vanish. -/
theorem carryDigit_eventually_zero (o : Orbit) :
    ∃ J, ∀ K, J ≤ K →
      KLDyadicReset.carryDigit o.resetProgram K = 0 := by
  exact KLDyadicReset.carryDigit_eventually_zero_of_follows
    o.resetProgram (fun t => (o.core t : ℤ)) o.follows_resetProgram
      (by positivity) o.resetPrecision_unbounded

/-- Ready-made adversarial consumer: infinitely recurring nonzero canonical
carries are incompatible with an ordinary self-writing orbit. -/
theorem false_of_cofinally_nonzero_carries (o : Orbit)
    (hbad : ∀ J, ∃ K, J ≤ K ∧
      KLDyadicReset.carryDigit o.resetProgram K ≠ 0) : False := by
  obtain ⟨J, hzero⟩ := o.carryDigit_eventually_zero
  obtain ⟨K, hJK, hne⟩ := hbad J
  exact hne (hzero K hJK)

/-- Branch-only exclusion interface.  A checker may compute the canonical
carries from a proposed schedule without first constructing any payloads; if
nonzero carries recur cofinally, no self-writing orbit can realize that
schedule. -/
theorem no_orbit_with_branch_of_cofinally_nonzero_carries
    (branch : ℕ → ℕ)
    (hbad : ∀ J, ∃ K, J ≤ K ∧
      KLDyadicReset.carryDigit (resetProgramOfBranch branch) K ≠ 0) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply o.false_of_cofinally_nonzero_carries
  simpa [resetProgram] using hbad

/-- Height-form branch exclusion, useful when a symbolic or morphic analysis
shows the canonical residues themselves escape every ordinary bound. -/
theorem no_orbit_with_branch_of_unbounded_residues
    (branch : ℕ → ℕ)
    (hbad : KLDyadicReset.ResiduesUnbounded
      (resetProgramOfBranch branch)) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply KLDyadicReset.no_nonnegative_follows_of_unbounded_residues
    o.resetProgram (by simpa [resetProgram] using hbad)
  exact ⟨fun t => (o.core t : ℤ), o.follows_resetProgram, by positivity⟩

/-- Change-form branch exclusion: perpetual acquisition of new canonical
high bits also rules out an ordinary orbit. -/
theorem no_orbit_with_branch_of_changes
    (branch : ℕ → ℕ)
    (hbad : KLDyadicReset.ChangesArbitrarilyLate
      (resetProgramOfBranch branch)) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply KLDyadicReset.no_nonnegative_follows_of_changes
    o.resetProgram o.resetPrecision_unbounded
      (by simpa [resetProgram] using hbad)
  exact ⟨fun t => (o.core t : ℤ), o.follows_resetProgram, by positivity⟩

/-- One branch schedule can select at most one ordinary initial normalized
core. -/
theorem initial_core_unique_of_same_branch (o o' : Orbit)
    (hbranch : o.branch = o'.branch) : o.core 0 = o'.core 0 := by
  have hfollows' : KLDyadicReset.Follows o.resetProgram
      (fun t => (o'.core t : ℤ)) := by
    simpa [resetProgram, hbranch] using o'.follows_resetProgram
  have hint := KLDyadicReset.initial_eq_of_unbounded_cumulative_precision
    o.resetProgram (fun t => (o.core t : ℤ)) (fun t => (o'.core t : ℤ))
      o.follows_resetProgram hfollows' o.resetPrecision_unbounded
  exact_mod_cast hint

/-- Consequently a branch schedule selects at most one initial public
payload in the self-writing coordinate. -/
theorem initial_payload_unique_of_same_branch (o o' : Orbit)
    (hbranch : o.branch = o'.branch) : o.payload 0 = o'.payload 0 := by
  have hcore := initial_core_unique_of_same_branch o o' hbranch
  have hz : Z (o.payload 0) = Z (o'.payload 0) := by
    rw [o.z_factor, o'.z_factor, hcore, hbranch]
  simp [Z] at hz
  omega

/-- Every accepted step is outward in the public self-writing coordinate.
This is a theorem about a supplied exact orbit, not evidence that one exists. -/
theorem payload_strictMono (o : Orbit) : StrictMono o.payload := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hfirst :
      3 ^ 11 * Z (o.payload t) <
        2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
    calc
      3 ^ 11 * Z (o.payload t) =
          3 ^ (6 * o.branch t + 11) * o.core t := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
      _ < 2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
        rw [o.balance]
        omega
  have hsecond :
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
        3 ^ 11 * Z (o.payload (t + 1)) := by
    calc
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
          3 ^ (6 * o.branch (t + 1) + 11) * o.core (t + 1) :=
        Nat.mul_lt_mul_of_pos_right
          (EtherCounterStateNoRepeat.Orbit.binary_lt_ternary_at_branch
            (o.branch (t + 1))) (o.core_pos (t + 1))
      _ = 3 ^ 11 * Z (o.payload (t + 1)) := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
  have hz : Z (o.payload t) < Z (o.payload (t + 1)) := by
    apply (Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ 11)).mp
    exact hfirst.trans hsecond
  simp [Z] at hz
  omega

/-- The self-writing map does not rescue a finite or ultimately periodic
branch dispatcher.  Any infinite accepted execution must use a genuinely
aperiodic schedule. -/
theorem branch_not_eventually_periodic (o : Orbit) (K p : ℕ) (hp : 0 < p) :
    ¬ EtherCounterAperiodic.EventuallyPeriodicFrom o.branch K p := by
  intro hperiodic
  apply o.toNormalized.branch_not_eventually_periodic K p hp
  intro k
  simpa [toNormalized, ternaryCoreToNormalized, toTernaryCore] using
    congrArg (fun n => n - 1) (hperiodic k)

end Orbit
end SelfWritingKL
end KontoroC
