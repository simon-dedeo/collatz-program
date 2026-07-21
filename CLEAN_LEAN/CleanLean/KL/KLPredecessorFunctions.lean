/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.PredecessorTransfer
import CleanLean.KL.ResidueSystem
import Mathlib.FieldTheory.Finite.Basic

/-!
# The literal KL predecessor function family

This file fixes the floor, residue-coordinate, nonperiodicity, and infimum
conventions for the functions to which the repaired elimination theorem will
be applied.  The three base difference inequalities are intentionally left as
a separate combinatorial theorem.
-/

namespace CleanLean.KL

open CleanLean.Collatz
open scoped BigOperators

/-- Positive nonperiodic targets in one concrete KL residue state.  The state
coordinate `s` represents the original residue `2+3s (mod 3^k)`. -/
def KLTarget (k : ℕ) (state : ResidueSystem.State k) :=
  {a : ℕ // 0 < a ∧
    a ≡ 2 + 3 * state.val [MOD 3 ^ k] ∧
    ¬ IsSyracusePeriodic a}

/-- The integer cutoff represented by the real logarithmic scale `y`. -/
noncomputable def klCutoff (a : ℕ) (y : ℝ) : ℕ :=
  ⌊(2 : ℝ) ^ y * a⌋₊

/-- Literal targetwise value `pi*_a(2^y a)`. -/
noncomputable def klTargetCount (a : ℕ) (y : ℝ) : ℕ :=
  boundedPredecessorCount a (klCutoff a y)

/-- Natural-valued infimum over all positive nonperiodic targets in the
specified residue class.  Downstream theorems carry nonemptiness explicitly,
so the empty-set convention of `sInf` is never used. -/
noncomputable def klPhiNat (k : ℕ) (state : ResidueSystem.State k)
    (y : ℝ) : ℕ :=
  sInf (Set.range fun a : KLTarget k state => klTargetCount a.val y)

/-- Real-valued form consumed by `SatisfiesBaseSystem`. -/
noncomputable def klPhi (k : ℕ) (state : ResidueSystem.State k)
    (y : ℝ) : ℝ :=
  klPhiNat k state y

/-- Explicit nonemptiness obligation for every residue-class infimum. -/
def KLTargetsNonempty (k : ℕ) : Prop :=
  ∀ state : ResidueSystem.State k, Nonempty (KLTarget k state)

/-- Euler multiplication preserves any residue class coprime to `3^k`, and a
sufficiently large such multiple cannot remain on the finite cycle of the
starting representative.  Thus every concrete KL target pool is nonempty.

This deliberately avoids the much stronger (and unnecessary) assertion that
two is a primitive root modulo every power of three. -/
theorem klTargetsNonempty (k : ℕ) : KLTargetsNonempty k := by
  intro state
  let modulus : ℕ := 3 ^ k
  let m : ℕ := 2 + 3 * state.val
  have hmpos : 0 < m := by simp [m]
  by_cases hmnon : ¬ IsSyracusePeriodic m
  · exact ⟨⟨m, hmpos, Nat.ModEq.refl m, hmnon⟩⟩
  · have hmperiodic : IsSyracusePeriodic m := by
      by_contra h
      exact hmnon h
    obtain ⟨p, hp, hperiod⟩ := hmperiodic
    let orbitSum : ℕ :=
      ∑ i ∈ Finset.range p, syracuseStep^[i] m
    let exponent : ℕ := Nat.totient modulus * (orbitSum + 1)
    let b : ℕ := 2 ^ exponent * m
    have hmodulus : 0 < modulus := by positivity
    have htotient : 0 < Nat.totient modulus :=
      Nat.totient_pos.mpr hmodulus
    have horbit_lt_exponent : orbitSum < exponent := by
      dsimp [exponent]
      have hmul : orbitSum + 1 ≤
          Nat.totient modulus * (orbitSum + 1) := by
        exact Nat.le_mul_of_pos_left _ htotient
      omega
    have hexponent_lt_pow : exponent < 2 ^ exponent :=
      exponent.lt_two_pow_self
    have horbit_lt_b : orbitSum < b := by
      have hmone : 1 ≤ m := hmpos
      exact horbit_lt_exponent.trans
        (hexponent_lt_pow.trans_le
          (Nat.le_mul_of_pos_right (2 ^ exponent) hmone))
    have hcoprime : Nat.Coprime 2 modulus := by
      exact (by norm_num : Nat.Coprime 2 3).pow_right k
    have hpowmod : 2 ^ exponent ≡ 1 [MOD modulus] := by
      have heuler : 2 ^ Nat.totient modulus ≡ 1 [MOD modulus] :=
        Nat.ModEq.pow_totient hcoprime
      have h := heuler.pow (orbitSum + 1)
      simpa [exponent, pow_mul] using h
    have hbmod : b ≡ m [MOD modulus] := by
      simpa [b] using hpowmod.mul (Nat.ModEq.refl m)
    have hbnon : ¬ IsSyracusePeriodic b := by
      intro hbperiodic
      have hreach : syracuseStep^[exponent] b = m := by
        simpa [b] using iterate_syracuse_two_pow_mul m exponent
      obtain ⟨q, hq⟩ :=
        periodic_predecessor_is_target_iterate hreach hbperiodic
      have hqle : syracuseStep^[q] m ≤ orbitSum := by
        exact periodic_iterate_le_orbitSum hp hperiod
      rw [hq] at hqle
      omega
    exact ⟨⟨b, by positivity, hbmod, hbnon⟩⟩

theorem klPhiNat_attained
    {k : ℕ} {state : ResidueSystem.State k} {y : ℝ}
    (hne : Nonempty (KLTarget k state)) :
    ∃ a : KLTarget k state, klTargetCount a.val y = klPhiNat k state y := by
  have hrange : (Set.range fun a : KLTarget k state =>
      klTargetCount a.val y).Nonempty := Set.range_nonempty _
  obtain ⟨a, ha⟩ := Nat.sInf_mem hrange
  exact ⟨a, by simpa only [klPhiNat] using ha⟩

theorem klPhiNat_le_target
    {k : ℕ} {state : ResidueSystem.State k} (y : ℝ)
    (a : KLTarget k state) :
    klPhiNat k state y ≤ klTargetCount a.val y := by
  exact Nat.sInf_le ⟨a, rfl⟩

theorem le_klPhiNat
    {k : ℕ} {state : ResidueSystem.State k} {y : ℝ}
    (hne : Nonempty (KLTarget k state)) {bound : ℕ}
    (hbound : ∀ a : KLTarget k state, bound ≤ klTargetCount a.val y) :
    bound ≤ klPhiNat k state y := by
  obtain ⟨a, ha⟩ := klPhiNat_attained (y := y) hne
  rw [← ha]
  exact hbound a

theorem klCutoff_self_le {a : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    a ≤ klCutoff a y := by
  apply Nat.le_floor
  have hrpow : (1 : ℝ) ≤ (2 : ℝ) ^ y :=
    Real.one_le_rpow (by norm_num) hy
  have ha : (0 : ℝ) ≤ a := by positivity
  nlinarith

theorem one_le_klTargetCount {a : ℕ} (ha : 0 < a)
    {y : ℝ} (hy : 0 ≤ y) :
    1 ≤ klTargetCount a y := by
  rw [klTargetCount, boundedPredecessorCount]
  apply Finset.card_pos.mpr
  exact ⟨a, self_mem_boundedPredecessors ha
    (klCutoff_self_le hy)⟩

/-- Property (P1): every nonempty residue infimum is at least one for
nonnegative logarithmic scale. -/
theorem one_le_klPhi
    {k : ℕ} (hne : KLTargetsNonempty k)
    (state : ResidueSystem.State k) {y : ℝ} (hy : 0 ≤ y) :
    1 ≤ klPhi k state y := by
  have hnat : (1 : ℕ) ≤ klPhiNat k state y :=
    le_klPhiNat (hne state)
      (fun a => one_le_klTargetCount a.property.1 hy)
  change (1 : ℝ) ≤ (klPhiNat k state y : ℝ)
  exact_mod_cast hnat

/-- Unconditional form of (P1), after discharging target-pool nonemptiness. -/
theorem one_le_klPhi_unconditional
    {k : ℕ} (state : ResidueSystem.State k) {y : ℝ} (hy : 0 ≤ y) :
    1 ≤ klPhi k state y :=
  one_le_klPhi (klTargetsNonempty k) state hy

theorem klCutoff_mono {a : ℕ} : Monotone (klCutoff a) := by
  intro x y hxy
  apply Nat.floor_mono
  have hrpow : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
    Real.monotone_rpow_of_base_ge_one (by norm_num) hxy
  exact mul_le_mul_of_nonneg_right hrpow (by positivity)

theorem klTargetCount_mono (a : ℕ) : Monotone (klTargetCount a) := by
  intro x y hxy
  exact boundedPredecessorCount_mono (klCutoff_mono hxy)

/-- Property (P2): the residue infimum is nondecreasing in logarithmic scale.
-/
theorem klPhi_mono
    {k : ℕ} (hne : KLTargetsNonempty k)
    (state : ResidueSystem.State k) :
    Monotone (klPhi k state) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := klPhiNat_attained (y := y) (hne state)
  have hnat : klPhiNat k state x ≤ klPhiNat k state y :=
    (klPhiNat_le_target x a).trans
      (((klTargetCount_mono a.val) hxy).trans_eq ha)
  change (klPhiNat k state x : ℝ) ≤ (klPhiNat k state y : ℝ)
  exact_mod_cast hnat

/-- Unconditional form of (P2), after discharging target-pool nonemptiness. -/
theorem klPhi_mono_unconditional
    {k : ℕ} (state : ResidueSystem.State k) :
    Monotone (klPhi k state) :=
  klPhi_mono (klTargetsNonempty k) state

end CleanLean.KL
