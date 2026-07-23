/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLControllerReset
import Mathlib.Data.ZMod.Units

/-!
# The dyadic affine cylinder of a reset program

A reset step has the exact form

`2^N * mNext = 3^O * m + delta`.

This file accumulates a finite list of such steps into one affine identity,
then extracts the unique initial dyadic residue class and the separation
bound for two payload chains following the same program.  It is the exact
dyadic dual of `KLControllerReset.ControllerData`.
-/

namespace KontoroC
namespace KLDyadicReset

/-- One normalized controller-reset instruction. -/
structure ResetStep where
  N : ℕ
  O : ℕ
  delta : ℤ
  deriving DecidableEq, Repr

/-- Accumulated exponents and affine defect. -/
structure ResetData where
  S : ℕ
  P : ℕ
  D : ℤ
  deriving DecidableEq, Repr

/-- QM138a. -/
def ResetData.step (d : ResetData) (e : ResetStep) : ResetData :=
  ⟨d.S + e.N, d.P + e.O,
    (3 : ℤ) ^ e.O * d.D + (2 : ℤ) ^ d.S * e.delta⟩

def initialData : ResetData := ⟨0, 0, 0⟩

def accumulate : List ResetStep → ResetData → ResetData
  | [], d => d
  | e :: w, d => accumulate w (d.step e)

def programData (w : List ResetStep) : ResetData :=
  accumulate w initialData

theorem accumulate_append (u v : List ResetStep) (d : ResetData) :
    accumulate (u ++ v) d = accumulate v (accumulate u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, accumulate]
      exact ih (d.step e)

theorem programData_append_singleton (w : List ResetStep) (e : ResetStep) :
    programData (w ++ [e]) = (programData w).step e := by
  simp [programData, accumulate_append, accumulate]

/-- A finite payload chain obeys the reset instructions exactly. -/
def Obeys : List ResetStep → ℤ → ℤ → Prop
  | [], mStart, mEnd => mEnd = mStart
  | e :: w, mStart, mEnd =>
      ∃ mMiddle : ℤ,
        (2 : ℤ) ^ e.N * mMiddle =
          (3 : ℤ) ^ e.O * mStart + e.delta ∧
        Obeys w mMiddle mEnd

theorem obeys_append (u v : List ResetStep) (mStart mEnd : ℤ) :
    Obeys (u ++ v) mStart mEnd ↔
      ∃ mMiddle : ℤ,
        Obeys u mStart mMiddle ∧ Obeys v mMiddle mEnd := by
  induction u generalizing mStart with
  | nil =>
      simp only [Obeys]
      constructor
      · intro h
        exact ⟨mStart, rfl, h⟩
      · rintro ⟨middle, hmiddle, htail⟩
        subst middle
        exact htail
  | cons e u ih =>
      simp only [List.cons_append, Obeys]
      constructor
      · rintro ⟨next, hstep, hrest⟩
        obtain ⟨middle, hu, hv⟩ := (ih next).mp hrest
        exact ⟨middle, ⟨next, hstep, hu⟩, hv⟩
      · rintro ⟨middle, ⟨next, hstep, hu⟩, hv⟩
        exact ⟨next, hstep, (ih next).mpr ⟨middle, hu, hv⟩⟩

/-- One reset step preserves the accumulated affine invariant. -/
theorem ResetData.step_invariant (d : ResetData) (e : ResetStep)
    {origin current next : ℤ}
    (hinv : (2 : ℤ) ^ d.S * current =
      (3 : ℤ) ^ d.P * origin + d.D)
    (hstep : (2 : ℤ) ^ e.N * next =
      (3 : ℤ) ^ e.O * current + e.delta) :
    (2 : ℤ) ^ (d.step e).S * next =
      (3 : ℤ) ^ (d.step e).P * origin + (d.step e).D := by
  simp only [ResetData.step]
  rw [pow_add, pow_add]
  calc
    (2 : ℤ) ^ d.S * 2 ^ e.N * next =
        (2 : ℤ) ^ d.S * ((2 : ℤ) ^ e.N * next) := by ring
    _ = (2 : ℤ) ^ d.S *
        ((3 : ℤ) ^ e.O * current + e.delta) := by rw [hstep]
    _ = (3 : ℤ) ^ e.O * ((2 : ℤ) ^ d.S * current) +
        (2 : ℤ) ^ d.S * e.delta := by ring
    _ = (3 : ℤ) ^ e.O *
        ((3 : ℤ) ^ d.P * origin + d.D) +
          (2 : ℤ) ^ d.S * e.delta := by rw [hinv]
    _ = (3 : ℤ) ^ d.P * 3 ^ e.O * origin +
        ((3 : ℤ) ^ e.O * d.D + (2 : ℤ) ^ d.S * e.delta) := by ring

/-- The invariant survives an arbitrary finite reset block. -/
theorem accumulate_invariant (w : List ResetStep) (d : ResetData)
    {origin current finish : ℤ}
    (hinv : (2 : ℤ) ^ d.S * current =
      (3 : ℤ) ^ d.P * origin + d.D)
    (hw : Obeys w current finish) :
    let out := accumulate w d
    (2 : ℤ) ^ out.S * finish =
      (3 : ℤ) ^ out.P * origin + out.D := by
  induction w generalizing d current with
  | nil =>
      simp only [Obeys] at hw
      subst finish
      simpa [accumulate]
  | cons e w ih =>
      rcases hw with ⟨middle, hstep, hw⟩
      simpa only [accumulate] using
        ih (d.step e) (d.step_invariant e hinv hstep) hw

/-- QM138b. -/
theorem program_exact (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : Obeys w mStart mEnd) :
    (2 : ℤ) ^ (programData w).S * mEnd =
      (3 : ℤ) ^ (programData w).P * mStart +
        (programData w).D := by
  simpa [programData, initialData] using
    accumulate_invariant w initialData
      (origin := mStart) (current := mStart) (finish := mEnd)
      (by simp [initialData]) hw

/-- QM138c: every realized block puts its initial payload in the selected
dyadic cylinder. -/
theorem initial_modEq_neg_defect
    (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : Obeys w mStart mEnd) :
    (3 : ℤ) ^ (programData w).P * mStart ≡
      -(programData w).D [ZMOD (2 : ℤ) ^ (programData w).S] := by
  rw [Int.modEq_iff_dvd]
  use -mEnd
  have hexact := program_exact w hw
  calc
    -(programData w).D -
        (3 : ℤ) ^ (programData w).P * mStart =
      -((3 : ℤ) ^ (programData w).P * mStart +
        (programData w).D) := by ring
    _ = -((2 : ℤ) ^ (programData w).S * mEnd) := by rw [← hexact]
    _ = (2 : ℤ) ^ (programData w).S * -mEnd := by ring

/-- Terminal dyadic cylinder in divisibility form. -/
def TerminalDivisible (w : List ResetStep) (mStart : ℤ) : Prop :=
  (2 : ℤ) ^ (programData w).S ∣
    (3 : ℤ) ^ (programData w).P * mStart + (programData w).D

theorem terminalDivisible_of_obeys
    (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : Obeys w mStart mEnd) :
    TerminalDivisible w mStart := by
  use mEnd
  exact (program_exact w hw).symm

/-- QM138e: the one accumulated dyadic cylinder reconstructs every
intermediate integral quotient of the finite reset block. -/
theorem exists_obeys_of_terminalDivisible
    (w : List ResetStep) {mStart : ℤ}
    (hterm : TerminalDivisible w mStart) :
    ∃ mEnd : ℤ, Obeys w mStart mEnd := by
  induction w using List.reverseRecOn generalizing mStart with
  | nil =>
      exact ⟨mStart, rfl⟩
  | append_singleton u e ih =>
      let d := programData u
      let prefixNumerator :=
        (3 : ℤ) ^ d.P * mStart + d.D
      have hfull := hterm
      rw [TerminalDivisible, programData_append_singleton] at hfull
      simp only [ResetData.step] at hfull
      have hfull' : (2 : ℤ) ^ (d.S + e.N) ∣
          (3 : ℤ) ^ e.O * prefixNumerator +
            (2 : ℤ) ^ d.S * e.delta := by
        convert hfull using 1 <;> dsimp [prefixNumerator, d] <;>
          rw [pow_add] <;> ring
      have hsmallDivisor : (2 : ℤ) ^ d.S ∣
          (2 : ℤ) ^ (d.S + e.N) := by
        exact_mod_cast pow_dvd_pow 2 (Nat.le_add_right d.S e.N)
      have hsmallFull : (2 : ℤ) ^ d.S ∣
          (3 : ℤ) ^ e.O * prefixNumerator +
            (2 : ℤ) ^ d.S * e.delta :=
        hsmallDivisor.trans hfull'
      have hdelta : (2 : ℤ) ^ d.S ∣ (2 : ℤ) ^ d.S * e.delta :=
        dvd_mul_right _ _
      have hoddProduct : (2 : ℤ) ^ d.S ∣
          (3 : ℤ) ^ e.O * prefixNumerator := by
        have hsub := Int.dvd_sub hsmallFull hdelta
        convert hsub using 1 <;> ring
      have hcopNat : (3 ^ e.O).Coprime (2 ^ d.S) := by
        exact (by norm_num : Nat.Coprime 3 2).pow _ _
      have hprefix : (2 : ℤ) ^ d.S ∣ prefixNumerator :=
        hcopNat.isCoprime.symm.dvd_of_dvd_mul_left hoddProduct
      have hprefixTerm : TerminalDivisible u mStart := by
        simpa [TerminalDivisible, prefixNumerator, d] using hprefix
      obtain ⟨middle, hu⟩ := ih hprefixTerm
      have hexact := program_exact u hu
      change (2 : ℤ) ^ d.S * middle = prefixNumerator at hexact
      have hfullFactored :
          (2 : ℤ) ^ d.S * (2 : ℤ) ^ e.N ∣
            (2 : ℤ) ^ d.S *
              ((3 : ℤ) ^ e.O * middle + e.delta) := by
        rw [← pow_add]
        convert hfull' using 1 <;> rw [← hexact] <;> ring
      have hnextDiv : (2 : ℤ) ^ e.N ∣
          (3 : ℤ) ^ e.O * middle + e.delta :=
        Int.dvd_of_mul_dvd_mul_left
          (pow_ne_zero d.S (by norm_num : (2 : ℤ) ≠ 0)) hfullFactored
      obtain ⟨mEnd, hmEnd⟩ := hnextDiv
      refine ⟨mEnd, (obeys_append u [e] mStart mEnd).mpr ?_⟩
      refine ⟨middle, hu, ?_⟩
      exact ⟨mEnd, hmEnd.symm, rfl⟩

theorem terminalDivisible_iff_exists_obeys
    (w : List ResetStep) (mStart : ℤ) :
    TerminalDivisible w mStart ↔ ∃ mEnd : ℤ, Obeys w mStart mEnd :=
  ⟨exists_obeys_of_terminalDivisible w,
    fun ⟨mEnd, hw⟩ => terminalDivisible_of_obeys w hw⟩

/-! ## Positive finite realizations -/

/-- A reset chain all of whose payloads, including both endpoints, are
strictly positive. -/
def ObeysPositive : List ResetStep → ℤ → ℤ → Prop
  | [], mStart, mEnd => mEnd = mStart ∧ 0 < mStart
  | e :: w, mStart, mEnd =>
      0 < mStart ∧ ∃ mMiddle : ℤ,
        (2 : ℤ) ^ e.N * mMiddle =
          (3 : ℤ) ^ e.O * mStart + e.delta ∧
        ObeysPositive w mMiddle mEnd

theorem obeysPositive_obeys
    (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : ObeysPositive w mStart mEnd) :
    Obeys w mStart mEnd := by
  induction w generalizing mStart with
  | nil => exact hw.1
  | cons e w ih =>
      exact ⟨hw.2.choose, hw.2.choose_spec.1,
        ih hw.2.choose_spec.2⟩

/-- The accumulated written and odd exponents split additively across an
arbitrary initial accumulator. -/
theorem accumulate_S (w : List ResetStep) (d : ResetData) :
    (accumulate w d).S = d.S + (w.map ResetStep.N).sum := by
  induction w generalizing d with
  | nil => simp [accumulate]
  | cons e w ih =>
      simp only [accumulate, ih, ResetData.step, List.map_cons,
        List.sum_cons]
      omega

theorem accumulate_P (w : List ResetStep) (d : ResetData) :
    (accumulate w d).P = d.P + (w.map ResetStep.O).sum := by
  induction w generalizing d with
  | nil => simp [accumulate]
  | cons e w ih =>
      simp only [accumulate, ih, ResetData.step, List.map_cons,
        List.sum_cons]
      omega

theorem programData_cons_S (e : ResetStep) (w : List ResetStep) :
    (programData (e :: w)).S = e.N + (programData w).S := by
  simp [programData, initialData, accumulate, accumulate_S,
    ResetData.step]

theorem programData_cons_P (e : ResetStep) (w : List ResetStep) :
    (programData (e :: w)).P = e.O + (programData w).P := by
  simp [programData, initialData, accumulate, accumulate_P,
    ResetData.step]

/-- The exact affine symmetry of a finite reset chain.  Its initial payload
may be shifted by the full dyadic cylinder width; every later payload shifts
by the corresponding positive prefix coefficient. -/
theorem obeys_shift
    (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : Obeys w mStart mEnd) (t : ℤ) :
    Obeys w
      (mStart + (2 : ℤ) ^ (programData w).S * t)
      (mEnd + (3 : ℤ) ^ (programData w).P * t) := by
  induction w generalizing mStart t with
  | nil =>
      simpa [Obeys, programData, initialData, accumulate] using hw
  | cons e w ih =>
      obtain ⟨middle, hstep, htail⟩ := hw
      rw [programData_cons_S, programData_cons_P]
      refine ⟨middle + (2 : ℤ) ^ (programData w).S *
          ((3 : ℤ) ^ e.O * t), ?_, ?_⟩
      · rw [pow_add]
        calc
          (2 : ℤ) ^ e.N *
              (middle + (2 : ℤ) ^ (programData w).S *
                ((3 : ℤ) ^ e.O * t)) =
              (2 : ℤ) ^ e.N * middle +
                (3 : ℤ) ^ e.O *
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S * t) := by ring
          _ = (3 : ℤ) ^ e.O * mStart + e.delta +
                (3 : ℤ) ^ e.O *
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S * t) := by rw [hstep]
          _ = (3 : ℤ) ^ e.O *
                (mStart +
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S) * t) +
                e.delta := by ring
      · convert ih htail ((3 : ℤ) ^ e.O * t) using 1 <;>
          rw [pow_add] <;> ring

/-- A quantitative form of finite positivity: after a large enough
nonnegative cylinder shift, the entire realized chain is positive. -/
theorem obeysPositive_shift_eventually
    (w : List ResetStep) {mStart mEnd : ℤ}
    (hw : Obeys w mStart mEnd) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      ObeysPositive w
        (mStart + (2 : ℤ) ^ (programData w).S * t)
        (mEnd + (3 : ℤ) ^ (programData w).P * t) := by
  induction w generalizing mStart with
  | nil =>
      simp only [Obeys] at hw
      subst mEnd
      refine ⟨mStart.natAbs + 1, fun t ht => ?_⟩
      simp only [programData, accumulate, initialData, pow_zero, one_mul,
        ObeysPositive]
      refine ⟨True.intro, ?_⟩
      have habs : mStart ≤ (mStart.natAbs : ℤ) := Int.le_natAbs
      have ht' : (mStart.natAbs : ℤ) + 1 ≤ (t : ℤ) := by exact_mod_cast ht
      omega
  | cons e w ih =>
      obtain ⟨middle, hstep, htail⟩ := hw
      obtain ⟨Ttail, hTtail⟩ := ih htail
      refine ⟨max (mStart.natAbs + 1) Ttail, fun t ht => ?_⟩
      have hstartBound : mStart.natAbs + 1 ≤ t :=
        le_trans (Nat.le_max_left _ _) ht
      have htailBound : Ttail ≤ t :=
        le_trans (Nat.le_max_right _ _) ht
      have htailScale : Ttail ≤ 3 ^ e.O * t := by
        exact le_trans htailBound (Nat.le_mul_of_pos_left t (by positivity))
      have htailPositive := hTtail (3 ^ e.O * t) htailScale
      rw [programData_cons_S, programData_cons_P]
      refine ⟨?_, middle + (2 : ℤ) ^ (programData w).S *
          ((3 : ℤ) ^ e.O * t), ?_, ?_⟩
      · have habs : mStart ≤ (mStart.natAbs : ℤ) := Int.le_natAbs
        have ht' : (mStart.natAbs : ℤ) + 1 ≤ (t : ℤ) := by
          exact_mod_cast hstartBound
        have hp : (1 : ℤ) ≤ (2 : ℤ) ^ (e.N + (programData w).S) := by
          exact one_le_pow₀ (by norm_num)
        have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
        have hprod : (t : ℤ) ≤
            (2 : ℤ) ^ (e.N + (programData w).S) * (t : ℤ) := by
          nlinarith
        omega
      · rw [pow_add]
        calc
          (2 : ℤ) ^ e.N *
              (middle + (2 : ℤ) ^ (programData w).S *
                ((3 : ℤ) ^ e.O * (t : ℤ))) =
              (2 : ℤ) ^ e.N * middle +
                (3 : ℤ) ^ e.O *
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S * (t : ℤ)) := by ring
          _ = (3 : ℤ) ^ e.O * mStart + e.delta +
                (3 : ℤ) ^ e.O *
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S * (t : ℤ)) := by rw [hstep]
          _ = (3 : ℤ) ^ e.O *
                (mStart +
                  ((2 : ℤ) ^ e.N *
                    (2 : ℤ) ^ (programData w).S) * (t : ℤ)) +
                e.delta := by ring
      · convert htailPositive using 1 <;> norm_cast <;> ring

/-- The odd slope in the initial cylinder is coprime to its dyadic modulus. -/
theorem three_pow_coprime_two_pow (P S : ℕ) :
    (3 ^ P).Coprime (2 ^ S) := by
  exact Nat.coprime_pow_primes P S Nat.prime_three Nat.prime_two (by norm_num)

/-- The selected initial dyadic cylinder exists even when the accumulated
defect is negative. -/
theorem exists_initial_payload_class (w : List ResetStep) :
    ∃ m : ℕ,
      (3 : ℤ) ^ (programData w).P * m ≡
        -(programData w).D [ZMOD (2 : ℤ) ^ (programData w).S] := by
  let modulus := 2 ^ (programData w).S
  letI : NeZero modulus := ⟨by positivity⟩
  let z : ZMod modulus :=
    ((3 ^ (programData w).P : ℕ) : ZMod modulus)⁻¹ *
      (-(programData w).D : ZMod modulus)
  refine ⟨z.val, ?_⟩
  change (((3 ^ (programData w).P : ℕ) : ℤ) * (z.val : ℤ)) ≡
    -(programData w).D [ZMOD (modulus : ℕ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hcast : (3 : ZMod modulus) ^ (programData w).P =
      ((3 ^ (programData w).P : ℕ) : ZMod modulus) := by
    norm_cast
  rw [hcast]
  rw [ZMod.natCast_zmod_val]
  dsimp only [z]
  calc
    ((3 ^ (programData w).P : ℕ) : ZMod modulus) *
          (((3 ^ (programData w).P : ℕ) : ZMod modulus)⁻¹ *
            (-(programData w).D : ZMod modulus)) =
        (((3 ^ (programData w).P : ℕ) : ZMod modulus) *
          ((3 ^ (programData w).P : ℕ) : ZMod modulus)⁻¹) *
            (-(programData w).D : ZMod modulus) := by ring
    _ = -(programData w).D := by
      rw [ZMod.coe_mul_inv_eq_one _
        (three_pow_coprime_two_pow
          (programData w).P (programData w).S), one_mul]

theorem exists_terminalDivisible (w : List ResetStep) :
    ∃ mStart : ℤ, TerminalDivisible w mStart := by
  obtain ⟨m, hm⟩ := exists_initial_payload_class w
  refine ⟨m, ?_⟩
  rw [Int.modEq_iff_dvd] at hm
  rw [TerminalDivisible]
  have hneg := dvd_neg.mpr hm
  simpa [sub_eq_add_neg] using hneg

/-- QM138f: every finite reset instruction word, without any sign condition
on its affine defects, is realized by a chain of strictly positive integer
payloads.  Thus positivity creates no finite-cylinder obstruction. -/
theorem exists_positive_obeys (w : List ResetStep) :
    ∃ mStart mEnd : ℤ, ObeysPositive w mStart mEnd := by
  obtain ⟨mStart, hterm⟩ := exists_terminalDivisible w
  obtain ⟨mEnd, hw⟩ := exists_obeys_of_terminalDivisible w hterm
  obtain ⟨T, hT⟩ := obeysPositive_shift_eventually w hw
  exact ⟨mStart + (2 : ℤ) ^ (programData w).S * T,
    mEnd + (3 : ℤ) ^ (programData w).P * T,
    hT T le_rfl⟩

/-- The selected initial dyadic class is unique. -/
theorem initial_payload_class_unique
    (w : List ResetStep) {m m' : ℤ}
    (hm : (3 : ℤ) ^ (programData w).P * m ≡
      -(programData w).D [ZMOD (2 : ℤ) ^ (programData w).S])
    (hm' : (3 : ℤ) ^ (programData w).P * m' ≡
      -(programData w).D [ZMOD (2 : ℤ) ^ (programData w).S]) :
    m ≡ m' [ZMOD (2 : ℤ) ^ (programData w).S] := by
  have hmul := hm.trans hm'.symm
  rw [Int.modEq_iff_dvd] at hmul ⊢
  have hfact : (2 : ℤ) ^ (programData w).S ∣
      (3 : ℤ) ^ (programData w).P * (m' - m) := by
    convert hmul using 1 <;> ring
  have hcopNat := three_pow_coprime_two_pow
    (programData w).P (programData w).S
  exact hcopNat.isCoprime.symm.dvd_of_dvd_mul_left hfact

/-- QM138d, exact difference identity for two chains following one block. -/
theorem two_chains_difference
    (w : List ResetStep) {mStart mEnd mStart' mEnd' : ℤ}
    (hw : Obeys w mStart mEnd) (hw' : Obeys w mStart' mEnd') :
    (2 : ℤ) ^ (programData w).S * (mEnd - mEnd') =
      (3 : ℤ) ^ (programData w).P * (mStart - mStart') := by
  have h := program_exact w hw
  have h' := program_exact w hw'
  linear_combination h - h'

/-- Therefore cumulative written precision divides the initial separation. -/
theorem two_pow_dvd_initial_difference
    (w : List ResetStep) {mStart mEnd mStart' mEnd' : ℤ}
    (hw : Obeys w mStart mEnd) (hw' : Obeys w mStart' mEnd') :
    (2 : ℤ) ^ (programData w).S ∣ mStart - mStart' := by
  have hdiff := two_chains_difference w hw hw'
  have hdiv : (2 : ℤ) ^ (programData w).S ∣
      (3 : ℤ) ^ (programData w).P * (mStart - mStart') := by
    use mEnd - mEnd'
    exact hdiff.symm
  have hcopNat := three_pow_coprime_two_pow
    (programData w).P (programData w).S
  exact hcopNat.isCoprime.symm.dvd_of_dvd_mul_left hdiv

/-! ## Infinite programs -/

/-- An infinite payload path following one reset program. -/
def Follows (e : ℕ → ResetStep) (m : ℕ → ℤ) : Prop :=
  ∀ j, (2 : ℤ) ^ (e j).N * m (j + 1) =
    (3 : ℤ) ^ (e j).O * m j + (e j).delta

/-- Accumulator after the first `J` reset instructions. -/
def cumulative (e : ℕ → ResetStep) : ℕ → ResetData
  | 0 => initialData
  | J + 1 => (cumulative e J).step (e J)

theorem cumulative_exact (e : ℕ → ResetStep) (m : ℕ → ℤ)
    (hm : Follows e m) (J : ℕ) :
    (2 : ℤ) ^ (cumulative e J).S * m J =
      (3 : ℤ) ^ (cumulative e J).P * m 0 +
        (cumulative e J).D := by
  induction J with
  | zero => simp [cumulative, initialData]
  | succ J ih =>
      exact (cumulative e J).step_invariant (e J) ih (hm J)

theorem cumulative_two_chains_difference
    (e : ℕ → ResetStep) (m m' : ℕ → ℤ)
    (hm : Follows e m) (hm' : Follows e m') (J : ℕ) :
    (2 : ℤ) ^ (cumulative e J).S * (m J - m' J) =
      (3 : ℤ) ^ (cumulative e J).P * (m 0 - m' 0) := by
  have h := cumulative_exact e m hm J
  have h' := cumulative_exact e m' hm' J
  linear_combination h - h'

theorem cumulative_two_pow_dvd_initial_difference
    (e : ℕ → ResetStep) (m m' : ℕ → ℤ)
    (hm : Follows e m) (hm' : Follows e m') (J : ℕ) :
    (2 : ℤ) ^ (cumulative e J).S ∣ m 0 - m' 0 := by
  have hdiff := cumulative_two_chains_difference e m m' hm hm' J
  have hdiv : (2 : ℤ) ^ (cumulative e J).S ∣
      (3 : ℤ) ^ (cumulative e J).P * (m 0 - m' 0) := by
    use m J - m' J
    exact hdiff.symm
  have hcopNat := three_pow_coprime_two_pow
    (cumulative e J).P (cumulative e J).S
  exact hcopNat.isCoprime.symm.dvd_of_dvd_mul_left hdiv

/-! ## Canonical inverse-limit residues -/

/-- The finite cylinder condition at cumulative depth `J`. -/
def CumulativeTerminal (e : ℕ → ResetStep) (J : ℕ) (mStart : ℤ) : Prop :=
  (2 : ℤ) ^ (cumulative e J).S ∣
    (3 : ℤ) ^ (cumulative e J).P * mStart +
      (cumulative e J).D

theorem cumulativeTerminal_of_follows
    (e : ℕ → ResetStep) (m : ℕ → ℤ)
    (hm : Follows e m) (J : ℕ) :
    CumulativeTerminal e J (m 0) := by
  use m J
  exact (cumulative_exact e m hm J).symm

/-- A terminal cylinder at depth `J+1` necessarily lies in the terminal
cylinder of its prefix at depth `J`. -/
theorem cumulativeTerminal_of_succ
    (e : ℕ → ResetStep) (J : ℕ) {mStart : ℤ}
    (h : CumulativeTerminal e (J + 1) mStart) :
    CumulativeTerminal e J mStart := by
  let d := cumulative e J
  let prefixNumerator :=
    (3 : ℤ) ^ d.P * mStart + d.D
  have hfull := h
  rw [CumulativeTerminal, cumulative] at hfull
  simp only [ResetData.step] at hfull
  have hfull' : (2 : ℤ) ^ (d.S + (e J).N) ∣
      (3 : ℤ) ^ (e J).O * prefixNumerator +
        (2 : ℤ) ^ d.S * (e J).delta := by
    convert hfull using 1 <;> dsimp [prefixNumerator, d] <;>
      rw [pow_add] <;> ring
  have hsmallDivisor : (2 : ℤ) ^ d.S ∣
      (2 : ℤ) ^ (d.S + (e J).N) := by
    rw [pow_add]
    exact dvd_mul_right _ _
  have hsmallFull : (2 : ℤ) ^ d.S ∣
      (3 : ℤ) ^ (e J).O * prefixNumerator +
        (2 : ℤ) ^ d.S * (e J).delta :=
    hsmallDivisor.trans hfull'
  have hdelta : (2 : ℤ) ^ d.S ∣
      (2 : ℤ) ^ d.S * (e J).delta := dvd_mul_right _ _
  have hoddProduct : (2 : ℤ) ^ d.S ∣
      (3 : ℤ) ^ (e J).O * prefixNumerator := by
    have hsub := Int.dvd_sub hsmallFull hdelta
    convert hsub using 1 <;> ring
  have hcop : (3 ^ (e J).O).Coprime (2 ^ d.S) :=
    (by norm_num : Nat.Coprime 3 2).pow _ _
  have hprefix : (2 : ℤ) ^ d.S ∣ prefixNumerator :=
    hcop.isCoprime.symm.dvd_of_dvd_mul_left hoddProduct
  simpa [CumulativeTerminal, prefixNumerator, d] using hprefix

theorem cumulativeTerminal_prefix
    (e : ℕ → ResetStep) {J K : ℕ} {mStart : ℤ}
    (hJK : J ≤ K) (hK : CumulativeTerminal e K mStart) :
    CumulativeTerminal e J mStart := by
  induction K with
  | zero =>
      have : J = 0 := Nat.eq_zero_of_le_zero hJK
      simpa [this] using hK
  | succ K ih =>
      rcases Nat.eq_or_lt_of_le hJK with hEq | hLt
      · simpa [hEq] using hK
      · exact ih (Nat.le_of_lt_succ hLt)
          (cumulativeTerminal_of_succ e K hK)

/-- Canonical representative in `[0,2^S)` of the unique initial cylinder at
depth `J`. -/
noncomputable def initialResidue (e : ℕ → ResetStep) (J : ℕ) : ℕ := by
  let d := cumulative e J
  let modulus := 2 ^ d.S
  letI : NeZero modulus := ⟨by positivity⟩
  exact (((3 ^ d.P : ℕ) : ZMod modulus)⁻¹ *
    (-d.D : ZMod modulus)).val

theorem initialResidue_lt (e : ℕ → ResetStep) (J : ℕ) :
    initialResidue e J < 2 ^ (cumulative e J).S := by
  unfold initialResidue
  exact ZMod.val_lt _

theorem initialResidue_terminal (e : ℕ → ResetStep) (J : ℕ) :
    CumulativeTerminal e J (initialResidue e J) := by
  let d := cumulative e J
  let modulus := 2 ^ d.S
  letI : NeZero modulus := ⟨by positivity⟩
  let z : ZMod modulus :=
    ((3 ^ d.P : ℕ) : ZMod modulus)⁻¹ * (-d.D : ZMod modulus)
  have hz : (initialResidue e J : ZMod modulus) = z := by
    rw [show initialResidue e J = z.val by rfl]
    exact ZMod.natCast_zmod_val z
  have hunit : ((3 ^ d.P : ℕ) : ZMod modulus) * z = -d.D := by
    dsimp [z]
    calc
      ((3 ^ d.P : ℕ) : ZMod modulus) *
          (((3 ^ d.P : ℕ) : ZMod modulus)⁻¹ * (-d.D : ZMod modulus)) =
          (((3 ^ d.P : ℕ) : ZMod modulus) *
            ((3 ^ d.P : ℕ) : ZMod modulus)⁻¹) *
              (-d.D : ZMod modulus) := by ring
      _ = -d.D := by
        rw [ZMod.coe_mul_inv_eq_one _
          (three_pow_coprime_two_pow d.P d.S), one_mul]
  have hm : ((3 ^ d.P : ℕ) : ℤ) * (initialResidue e J : ℤ) ≡
      -d.D [ZMOD (modulus : ℕ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [hz]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hunit
  rw [CumulativeTerminal]
  rw [Int.modEq_iff_dvd] at hm
  have hneg := dvd_neg.mpr hm
  simpa [d, modulus, sub_eq_add_neg] using hneg

/-- Exact endpoint quotient of the canonical finite cylinder. -/
noncomputable def canonicalEndpoint (e : ℕ → ResetStep) (J : ℕ) : ℤ :=
  (initialResidue_terminal e J).choose

theorem canonicalEndpoint_exact (e : ℕ → ResetStep) (J : ℕ) :
    (2 : ℤ) ^ (cumulative e J).S * canonicalEndpoint e J =
      (3 : ℤ) ^ (cumulative e J).P * initialResidue e J +
        (cumulative e J).D := by
  exact (initialResidue_terminal e J).choose_spec.symm

/-- Two initial integers satisfying the same cumulative terminal cylinder
are congruent modulo all written binary precision. -/
theorem cumulativeTerminal_unique_modEq
    (e : ℕ → ResetStep) (J : ℕ) {a b : ℤ}
    (ha : CumulativeTerminal e J a)
    (hb : CumulativeTerminal e J b) :
    a ≡ b [ZMOD (2 : ℤ) ^ (cumulative e J).S] := by
  rw [Int.modEq_iff_dvd]
  have hsub := Int.dvd_sub hb ha
  have hmul : (2 : ℤ) ^ (cumulative e J).S ∣
      (3 : ℤ) ^ (cumulative e J).P * (b - a) := by
    convert hsub using 1 <;> ring
  have hcop := three_pow_coprime_two_pow
    (cumulative e J).P (cumulative e J).S
  exact hcop.isCoprime.symm.dvd_of_dvd_mul_left hmul

/-- QM139a, compatibility of canonical representatives. -/
theorem initialResidue_modEq
    (e : ℕ → ResetStep) {J K : ℕ} (hJK : J ≤ K) :
    initialResidue e J ≡ initialResidue e K
      [MOD 2 ^ (cumulative e J).S] := by
  rw [← Int.natCast_modEq_iff]
  exact cumulativeTerminal_unique_modEq e J
    (initialResidue_terminal e J)
    (cumulativeTerminal_prefix e hJK (initialResidue_terminal e K))

/-- Later compatible canonical representatives can only move upward. -/
theorem initialResidue_mono (e : ℕ → ResetStep) :
    Monotone (initialResidue e) := by
  intro J K hJK
  let modulus := 2 ^ (cumulative e J).S
  have hmodEq := initialResidue_modEq e hJK
  have hsmall : initialResidue e J < modulus := initialResidue_lt e J
  have heqmod : initialResidue e J = initialResidue e K % modulus := by
    calc
      initialResidue e J = initialResidue e J % modulus :=
        (Nat.mod_eq_of_lt hsmall).symm
      _ = initialResidue e K % modulus := hmodEq
  rw [heqmod]
  exact Nat.mod_le _ _

theorem cumulative_succ_S (e : ℕ → ResetStep) (J : ℕ) :
    (cumulative e (J + 1)).S =
      (cumulative e J).S + (e J).N := by
  simp [cumulative, ResetData.step]

theorem cumulative_succ_P (e : ℕ → ResetStep) (J : ℕ) :
    (cumulative e (J + 1)).P =
      (cumulative e J).P + (e J).O := by
  simp [cumulative, ResetData.step]

/-- The bounded new binary block written into the canonical initial
representative by reset `J`. -/
noncomputable def carryDigit (e : ℕ → ResetStep) (J : ℕ) : ℕ :=
  (initialResidue e (J + 1) - initialResidue e J) /
    2 ^ (cumulative e J).S

/-- QM140a, exact base-`2^N` digit decomposition. -/
theorem initialResidue_succ_eq_add_carry
    (e : ℕ → ResetStep) (J : ℕ) :
    initialResidue e (J + 1) = initialResidue e J +
      2 ^ (cumulative e J).S * carryDigit e J := by
  have hmono : initialResidue e J ≤ initialResidue e (J + 1) :=
    initialResidue_mono e (Nat.le_succ J)
  have hdiv : 2 ^ (cumulative e J).S ∣
      initialResidue e (J + 1) - initialResidue e J :=
    (Nat.modEq_iff_dvd' hmono).mp
      (initialResidue_modEq e (Nat.le_succ J))
  have hmul := Nat.mul_div_cancel' hdiv
  rw [carryDigit]
  calc
    initialResidue e (J + 1) =
        (initialResidue e (J + 1) - initialResidue e J) +
          initialResidue e J := (Nat.sub_add_cancel hmono).symm
    _ = 2 ^ (cumulative e J).S *
          ((initialResidue e (J + 1) - initialResidue e J) /
            2 ^ (cumulative e J).S) + initialResidue e J := by rw [hmul]
    _ = initialResidue e J +
          2 ^ (cumulative e J).S *
            ((initialResidue e (J + 1) - initialResidue e J) /
              2 ^ (cumulative e J).S) := by omega

theorem carryDigit_lt (e : ℕ → ResetStep) (J : ℕ) :
    carryDigit e J < 2 ^ (e J).N := by
  let width := 2 ^ (cumulative e J).S
  have hdecomp := initialResidue_succ_eq_add_carry e J
  have hnext := initialResidue_lt e (J + 1)
  rw [cumulative_succ_S, pow_add] at hnext
  have hprod : width * carryDigit e J < width * 2 ^ (e J).N := by
    calc
      width * carryDigit e J ≤
          initialResidue e J + width * carryDigit e J :=
            Nat.le_add_left _ _
      _ = initialResidue e (J + 1) := hdecomp.symm
      _ < width * 2 ^ (e J).N := hnext
  exact Nat.lt_of_mul_lt_mul_left hprod

/-- QM140b, the exact one-reset carry congruence. -/
theorem carryDigit_law (e : ℕ → ResetStep) (J : ℕ) :
    (2 : ℤ) ^ (e J).N ∣
      (3 : ℤ) ^ (e J).O * canonicalEndpoint e J +
        (3 : ℤ) ^ ((cumulative e J).P + (e J).O) * carryDigit e J +
          (e J).delta := by
  let d := cumulative e J
  let r := initialResidue e J
  let q := carryDigit e J
  let z := canonicalEndpoint e J
  let zNext := canonicalEndpoint e (J + 1)
  have hcurr := canonicalEndpoint_exact e J
  have hnext := canonicalEndpoint_exact e (J + 1)
  have hres := initialResidue_succ_eq_add_carry e J
  change (2 : ℤ) ^ (e J).N ∣
    (3 : ℤ) ^ (e J).O * z +
      (3 : ℤ) ^ (d.P + (e J).O) * q + (e J).delta
  refine ⟨zNext, ?_⟩
  change (3 : ℤ) ^ (e J).O * z +
      (3 : ℤ) ^ (d.P + (e J).O) * (q : ℤ) + (e J).delta =
    (2 : ℤ) ^ (e J).N * zNext
  have hcurr' : (2 : ℤ) ^ d.S * z =
      (3 : ℤ) ^ d.P * r + d.D := hcurr
  have hres' : (initialResidue e (J + 1) : ℤ) =
      r + (2 : ℤ) ^ d.S * q := by exact_mod_cast hres
  have hnext' : (2 : ℤ) ^ (d.S + (e J).N) * zNext =
      (3 : ℤ) ^ (d.P + (e J).O) *
          (r + (2 : ℤ) ^ d.S * q) +
        ((3 : ℤ) ^ (e J).O * d.D +
          (2 : ℤ) ^ d.S * (e J).delta) := by
    rw [show d.S + (e J).N = (cumulative e (J + 1)).S by
      exact (cumulative_succ_S e J).symm]
    rw [show d.P + (e J).O = (cumulative e (J + 1)).P by
      exact (cumulative_succ_P e J).symm]
    rw [← hres']
    simpa only [cumulative, ResetData.step] using hnext
  have hscaled : (2 : ℤ) ^ d.S *
        ((3 : ℤ) ^ (e J).O * z +
          (3 : ℤ) ^ (d.P + (e J).O) * (q : ℤ) + (e J).delta) =
      (2 : ℤ) ^ d.S * ((2 : ℤ) ^ (e J).N * zNext) := by
    calc
      (2 : ℤ) ^ d.S *
          ((3 : ℤ) ^ (e J).O * z +
            (3 : ℤ) ^ (d.P + (e J).O) * (q : ℤ) +
              (e J).delta) =
          (3 : ℤ) ^ (e J).O * ((2 : ℤ) ^ d.S * z) +
            (2 : ℤ) ^ d.S *
              ((3 : ℤ) ^ (d.P + (e J).O) * (q : ℤ)) +
            (2 : ℤ) ^ d.S * (e J).delta := by ring
      _ = (3 : ℤ) ^ (e J).O *
            ((3 : ℤ) ^ d.P * r + d.D) +
          (2 : ℤ) ^ d.S *
            ((3 : ℤ) ^ (d.P + (e J).O) * (q : ℤ)) +
          (2 : ℤ) ^ d.S * (e J).delta := by rw [hcurr']
      _ = (2 : ℤ) ^ (d.S + (e J).N) * zNext := by
        rw [hnext']
        rw [pow_add]
        ring
      _ = (2 : ℤ) ^ d.S *
          ((2 : ℤ) ^ (e J).N * zNext) := by rw [pow_add]; ring
  exact (mul_left_cancel₀
    (pow_ne_zero d.S (by norm_num : (2 : ℤ) ≠ 0)) hscaled)

/-- The carry digit is uniquely determined within its canonical range. -/
theorem carryDigit_unique
    (e : ℕ → ResetStep) (J q : ℕ) (hq : q < 2 ^ (e J).N)
    (hdecomp : initialResidue e (J + 1) = initialResidue e J +
      2 ^ (cumulative e J).S * q) :
    q = carryDigit e J := by
  have hcanonical := initialResidue_succ_eq_add_carry e J
  have hmul : 2 ^ (cumulative e J).S * q =
      2 ^ (cumulative e J).S * carryDigit e J := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-- QM140c: zero carry is exactly immediate integrality of the next reset
on the current canonical endpoint. -/
theorem carryDigit_eq_zero_iff
    (e : ℕ → ResetStep) (J : ℕ) :
    carryDigit e J = 0 ↔
      (2 : ℤ) ^ (e J).N ∣
        (3 : ℤ) ^ (e J).O * canonicalEndpoint e J +
          (e J).delta := by
  constructor
  · intro hq
    simpa [hq] using carryDigit_law e J
  · intro hbase
    have hlaw := carryDigit_law e J
    have hsub := Int.dvd_sub hlaw hbase
    have hqmul : (2 : ℤ) ^ (e J).N ∣
        (3 : ℤ) ^ ((cumulative e J).P + (e J).O) *
          carryDigit e J := by
      convert hsub using 1 <;> ring
    have hcop := three_pow_coprime_two_pow
      ((cumulative e J).P + (e J).O) (e J).N
    have hqdiv : (2 : ℤ) ^ (e J).N ∣ (carryDigit e J : ℤ) :=
      hcop.isCoprime.symm.dvd_of_dvd_mul_left hqmul
    have hqdivNat : 2 ^ (e J).N ∣ carryDigit e J := by
      exact_mod_cast hqdiv
    exact Nat.eq_zero_of_dvd_of_lt hqdivNat (carryDigit_lt e J)

theorem cumulative_S_mono (e : ℕ → ResetStep) :
    Monotone (fun J => (cumulative e J).S) := by
  intro J K hJK
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJK
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ]
      have hstep : (cumulative e (J + d)).S ≤
          (cumulative e (J + d + 1)).S := by
        change (cumulative e (J + d)).S ≤
          ((cumulative e (J + d)).step (e (J + d))).S
        simp [ResetData.step]
      exact (ih (Nat.le_add_right J d)).trans hstep

/-- Once an ordinary nonnegative initial payload lies below the current
modulus, it is exactly the canonical representative. -/
theorem initialResidue_eq_of_follows_of_lt
    (e : ℕ → ResetStep) (m : ℕ → ℤ) (hm : Follows e m)
    (h0 : 0 ≤ m 0) (J : ℕ)
    (hlt : (m 0).toNat < 2 ^ (cumulative e J).S) :
    initialResidue e J = (m 0).toNat := by
  have hmodInt := cumulativeTerminal_unique_modEq e J
    (initialResidue_terminal e J) (cumulativeTerminal_of_follows e m hm J)
  have hcast : ((m 0).toNat : ℤ) = m 0 := Int.toNat_of_nonneg h0
  rw [← hcast] at hmodInt
  have hmodNat := Int.natCast_modEq_iff.mp hmodInt
  exact hmodNat.eq_of_lt_of_lt (initialResidue_lt e J) hlt

/-- QM139b: an ordinary nonnegative infinite payload forces eventual exact
stabilization of the canonical residue sequence. -/
theorem initialResidue_eventually_constant_of_follows
    (e : ℕ → ResetStep) (m : ℕ → ℤ) (hm : Follows e m)
    (h0 : 0 ≤ m 0)
    (hunbounded : ∀ L, ∃ J, L ≤ (cumulative e J).S) :
    ∃ J, ∀ K, J ≤ K → initialResidue e K = (m 0).toNat := by
  let M := (m 0).toNat
  obtain ⟨J, hJ⟩ := hunbounded (M + 1)
  refine ⟨J, fun K hJK => ?_⟩
  apply initialResidue_eq_of_follows_of_lt e m hm h0 K
  have hSK : M + 1 ≤ (cumulative e K).S :=
    hJ.trans (cumulative_S_mono e hJK)
  have hpow : 2 ^ (M + 1) ≤ 2 ^ (cumulative e K).S :=
    Nat.pow_le_pow_right (by norm_num) hSK
  exact M.lt_two_pow_self.trans
    ((Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self M)).trans_le hpow)

/-- Operational form of QM139b/QM140: an ordinary nonnegative payload makes
all sufficiently late exact carry digits vanish. -/
theorem carryDigit_eventually_zero_of_follows
    (e : ℕ → ResetStep) (m : ℕ → ℤ) (hm : Follows e m)
    (h0 : 0 ≤ m 0)
    (hunbounded : ∀ L, ∃ J, L ≤ (cumulative e J).S) :
    ∃ J, ∀ K, J ≤ K → carryDigit e K = 0 := by
  obtain ⟨J, hstable⟩ :=
    initialResidue_eventually_constant_of_follows e m hm h0 hunbounded
  refine ⟨J, fun K hJK => ?_⟩
  rw [carryDigit, hstable K hJK,
    hstable (K + 1) (hJK.trans (Nat.le_succ K))]
  simp

def NonzeroCarriesArbitrarilyLate (e : ℕ → ResetStep) : Prop :=
  ∀ J, ∃ K, J ≤ K ∧ carryDigit e K ≠ 0

/-- The carry-digit version of the inverse-limit no-go criterion. -/
theorem no_nonnegative_follows_of_nonzero_carries
    (e : ℕ → ResetStep)
    (hunbounded : ∀ L, ∃ J, L ≤ (cumulative e J).S)
    (hcarry : NonzeroCarriesArbitrarilyLate e) :
    ¬ ∃ m : ℕ → ℤ, Follows e m ∧ 0 ≤ m 0 := by
  rintro ⟨m, hm, h0⟩
  obtain ⟨J, hzero⟩ :=
    carryDigit_eventually_zero_of_follows e m hm h0 hunbounded
  obtain ⟨K, hJK, hne⟩ := hcarry J
  exact hne (hzero K hJK)

/-- Canonical residues keep acquiring genuinely new high bits arbitrarily
late. -/
def ChangesArbitrarilyLate (e : ℕ → ResetStep) : Prop :=
  ∀ J, ∃ K, J ≤ K ∧ initialResidue e K ≠ initialResidue e J

/-- QM139's adversarial consumer: perpetual canonical-residue change rules
out every infinite reset chain beginning at a nonnegative ordinary integer. -/
theorem no_nonnegative_follows_of_changes
    (e : ℕ → ResetStep)
    (hunbounded : ∀ L, ∃ J, L ≤ (cumulative e J).S)
    (hchange : ChangesArbitrarilyLate e) :
    ¬ ∃ m : ℕ → ℤ, Follows e m ∧ 0 ≤ m 0 := by
  rintro ⟨m, hm, h0⟩
  obtain ⟨J, hstable⟩ :=
    initialResidue_eventually_constant_of_follows e m hm h0 hunbounded
  obtain ⟨K, hJK, hne⟩ := hchange J
  exact hne ((hstable K hJK).trans (hstable J le_rfl).symm)

/-- If cumulative written binary precision is unbounded, one infinite reset
program has at most one ordinary integer initial payload. -/
theorem initial_eq_of_unbounded_cumulative_precision
    (e : ℕ → ResetStep) (m m' : ℕ → ℤ)
    (hm : Follows e m) (hm' : Follows e m')
    (hunbounded : ∀ K, ∃ J, K ≤ (cumulative e J).S) :
    m 0 = m' 0 := by
  by_contra hne
  let distance := (m 0 - m' 0).natAbs
  obtain ⟨J, hJ⟩ := hunbounded (distance + 1)
  have hdiv := cumulative_two_pow_dvd_initial_difference e m m' hm hm' J
  have hdiffne : m 0 - m' 0 ≠ 0 := sub_ne_zero.mpr hne
  have hsize : 2 ^ (cumulative e J).S ≤ distance := by
    have h := Int.natAbs_le_of_dvd_ne_zero hdiv hdiffne
    simpa [distance, Int.natAbs_pow] using h
  have hpowle : 2 ^ (distance + 1) ≤ 2 ^ (cumulative e J).S :=
    Nat.pow_le_pow_right (by norm_num) hJ
  have hlt : distance < 2 ^ (distance + 1) := by
    exact distance.lt_two_pow_self.trans
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self distance))
  exact (not_lt_of_ge (hpowle.trans hsize)) hlt

end KLDyadicReset
end KontoroC
