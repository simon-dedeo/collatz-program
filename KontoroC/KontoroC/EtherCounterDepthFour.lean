/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterNineCycle

/-! # Depth-four carry cells

The modular and budget arithmetic for the two QM120 cells which survive every
mod-27 phase.  The all-cycle nondivisibility of their canonical carries is
not asserted here.
-/

namespace KontoroC
namespace EtherCounterDepthFour

def cellAMass (q : ℕ) := 1296 * q + 23895
def cellATernaryMass (q : ℕ) := 972 * q + 17577
def cellASurvivingDefect (q : ℕ) := 17 * 2 ^ (1280 * q + 23384)
def cellABudget (q : ℕ) := (q * (462 * q + 2501) + 101) / 102

def cellBMass (q : ℕ) := 1296 * q + 23031
def cellBTernaryMass (q : ℕ) := 972 * q + 16929
def cellBSurvivingDefect (q : ℕ) := 17 * 2 ^ (1280 * q + 22536)
def cellBBudget (q : ℕ) := (q * (462 * q + 1885) + 101) / 102

theorem cellA_mass_cast_eq_neg_one (q : ℕ) :
    ((2 ^ cellAMass q : ℕ) : ZMod 81) = -1 := by
  have hM : cellAMass q = 54 * (24 * q + 442) + 27 := by
    dsimp only [cellAMass]
    ring
  have hz : (2 : ZMod 81) ^ cellAMass q = -1 := by
    rw [hM, pow_add, pow_mul,
      show (2 : ZMod 81) ^ 54 = 1 by decide, one_pow]
    decide
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem cellB_mass_cast_eq_neg_one (q : ℕ) :
    ((2 ^ cellBMass q : ℕ) : ZMod 81) = -1 := by
  have hM : cellBMass q = 54 * (24 * q + 426) + 27 := by
    dsimp only [cellBMass]
    ring
  have hz : (2 : ZMod 81) ^ cellBMass q = -1 := by
    rw [hM, pow_add, pow_mul,
      show (2 : ZMod 81) ^ 54 = 1 by decide, one_pow]
    decide
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem cellA_defect_cast_eq_neg_one (q : ℕ) (hq : q % 27 = 14) :
    (cellASurvivingDefect q : ZMod 81) = -1 := by
  let k := q / 27
  have hdecomp := Nat.mod_add_div q 27
  have hk : q = 27 * k + 14 := by dsimp only [k]; omega
  rw [hk]
  have he : 1280 * (27 * k + 14) + 23384 = 54 * (640 * k + 764) + 48 := by
    ring
  simp only [cellASurvivingDefect, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [he, pow_add, pow_mul,
    show (2 : ZMod 81) ^ 54 = 1 by decide, one_pow]
  decide

theorem cellB_defect_cast_eq_seventyOne (q : ℕ) (hq : q % 27 = 0) :
    (cellBSurvivingDefect q : ZMod 81) = 71 := by
  obtain ⟨k, rfl⟩ := (Nat.dvd_iff_mod_eq_zero).2 hq
  have he : 1280 * (27 * k) + 22536 = 54 * (640 * k + 417) + 18 := by
    ring
  simp only [cellBSurvivingDefect, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [he, pow_add, pow_mul,
    show (2 : ZMod 81) ^ 54 = 1 by decide, one_pow]
  decide

theorem cellA_mass_lt_budget (q : ℕ) (hq : 311 ≤ q) :
    cellAMass q < cellABudget q := by
  rw [cellABudget]
  apply (Nat.lt_div_iff_mul_lt (by norm_num : 0 < 102)).2
  have hpoly : cellAMass q * 102 < q * (462 * q + 2501) := by
    dsimp only [cellAMass]
    nlinarith
  calc
    cellAMass q * 102 < q * (462 * q + 2501) := hpoly
    _ = q * (462 * q + 2501) + 101 - (102 - 1) := by omega

theorem cellB_mass_lt_budget (q : ℕ) (hq : 324 ≤ q) :
    cellBMass q < cellBBudget q := by
  rw [cellBBudget]
  apply (Nat.lt_div_iff_mul_lt (by norm_num : 0 < 102)).2
  have hpoly : cellBMass q * 102 < q * (462 * q + 1885) := by
    dsimp only [cellBMass]
    nlinarith
  calc
    cellBMass q * 102 < q * (462 * q + 1885) := hpoly
    _ = q * (462 * q + 1885) + 101 - (102 - 1) := by omega

theorem cellA_carry_equivalence (p : ℕ) (r y C : ℤ)
    (hy : (y : ZMod 81) = 1)
    (hcarry : r - y = (2 : ℤ) ^ p * C) :
    (r : ZMod 81) = 1 ↔ (C : ZMod 81) = 0 :=
  EtherCounterNineCycle.residue_eq_required_iff_carry_eq_zero
    81 1 p r y C ((ZMod.isUnit_iff_coprime 2 81).2 (by norm_num)) hy hcarry

theorem cellB_carry_equivalence (p : ℕ) (r y C : ℤ)
    (hy : (y : ZMod 81) = 10)
    (hcarry : r - y = (2 : ℤ) ^ p * C) :
    (r : ZMod 81) = 10 ↔ (C : ZMod 81) = 0 :=
  EtherCounterNineCycle.residue_eq_required_iff_carry_eq_zero
    81 10 p r y C ((ZMod.isUnit_iff_coprime 2 81).2 (by norm_num)) hy hcarry

end EtherCounterDepthFour
end KontoroC
