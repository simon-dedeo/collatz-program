/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PacketTiming
import Mathlib.Data.Nat.ModEq

/-!
# Generic congruence seams for a finite carry turnaround

These lemmas formalize two arithmetic interfaces used by the proposed
strike--scrub--turnaround cell: parity-compatible CRT, and writing an
arbitrary dyadic residue with an odd coefficient.  They assert existence of
one finite alignment, not an infinite rail.
-/

namespace KontoroC

/-- Multiplication by an odd natural permutes every power-of-two residue
ring.  The witness is chosen canonically below the modulus. -/
theorem exists_oddCoefficient_solution_mod_twoPow
    (C v E : ℕ) (hC : Odd C) :
    ∃ w : ℕ, w < 2 ^ E ∧ C * w ≡ v [MOD 2 ^ E] := by
  let M := 2 ^ E
  have hM : 0 < M := by simp [M]
  letI : NeZero M := ⟨hM.ne'⟩
  have hcop : C.Coprime M := by
    dsimp [M]
    exact hC.coprime_two_right.pow_right E
  have hunit : IsUnit (C : ZMod M) :=
    (ZMod.isUnit_iff_coprime C M).2 hcop
  let wz : ZMod M := (C : ZMod M)⁻¹ * (v : ZMod M)
  let w := wz.val
  have hwcast : (w : ZMod M) = wz := ZMod.natCast_zmod_val wz
  refine ⟨w, ZMod.val_lt wz, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, hwcast, wz]
  calc
    (C : ZMod M) * ((C : ZMod M)⁻¹ * (v : ZMod M)) =
        ((C : ZMod M) * (C : ZMod M)⁻¹) * (v : ZMod M) := by ring
    _ = v := by rw [ZMod.mul_inv_of_unit _ hunit, one_mul]

/-- If two desired exponent classes are even, their halves can be combined
by ordinary CRT.  Doubling the result simultaneously restores the classes
modulo `2*3^k` and `2^(n+1)`. -/
theorem exists_parityCompatible_threePow_twoPow_crt
    (k n ellThree ellTwo : ℕ)
    (hThree : Even ellThree) (hTwo : Even ellTwo) :
    ∃ ell : ℕ, Even ell ∧
      ell ≡ ellThree [MOD 2 * 3 ^ k] ∧
      ell ≡ ellTwo [MOD 2 ^ (n + 1)] := by
  obtain ⟨a, ha⟩ := hThree
  obtain ⟨b, hb⟩ := hTwo
  have hcop : (3 ^ k).Coprime (2 ^ n) :=
    (by norm_num : Nat.Coprime 3 2).pow k n
  let c : ℕ := ↑(Nat.chineseRemainder hcop a b)
  refine ⟨2 * c, even_two_mul c, ?_, ?_⟩
  · have hc := (Nat.chineseRemainder hcop a b).property.1.mul_left' 2
    simpa [c, ha, two_mul] using hc
  · have hc := (Nat.chineseRemainder hcop a b).property.2.mul_left' 2
    simpa [c, hb, pow_succ, two_mul, mul_two, mul_comm] using hc

/-- An odd coefficient writes every prescribed half-residue.  This is the
form directly used after a turnaround expression has exposed one factor
`2`: the ambient congruence gains one binary digit. -/
theorem exists_oddCoefficient_dyadicWriter
    (C R v E : ℕ) (hC : Odd C) :
    ∃ w : ℕ, w < 2 ^ E ∧
      R + 2 * C * w ≡ R + 2 * v [MOD 2 ^ (E + 1)] := by
  obtain ⟨w, hwlt, hw⟩ :=
    exists_oddCoefficient_solution_mod_twoPow C v E hC
  refine ⟨w, hwlt, ?_⟩
  have hmul := hw.mul_left' 2
  have hadd := hmul.add_left R
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hadd

end KontoroC
