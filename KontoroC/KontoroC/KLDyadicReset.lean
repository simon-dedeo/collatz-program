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

/-- A finite payload chain obeys the reset instructions exactly. -/
def Obeys : List ResetStep → ℤ → ℤ → Prop
  | [], mStart, mEnd => mEnd = mStart
  | e :: w, mStart, mEnd =>
      ∃ mMiddle : ℤ,
        (2 : ℤ) ^ e.N * mMiddle =
          (3 : ℤ) ^ e.O * mStart + e.delta ∧
        Obeys w mMiddle mEnd

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
