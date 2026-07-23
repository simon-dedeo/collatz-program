/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLControllerSwitch
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Units

/-!
# Exact affine data for a KL controller word

A positive-center word has an exact integer numerator.  This file records
the numerator coefficients `(A,B)` and the number `r` of divided letters.
For every legal word taking `h` to `h'`, they satisfy

`3^r * h' = A*h + B`.

Consequently a target congruence for `h'` is equivalent to one explicit
congruence for the accumulated integer numerator.  This is QM134a--c.
-/

namespace KontoroC
namespace KLControllerReset

open KLRechargeLedger KLControllerSwitch

/-- Integer numerator data accumulated by a positive-center word. -/
structure ControllerData where
  A : ℕ
  B : ℕ
  r : ℕ
  deriving DecidableEq, Repr

/-- QM134a: update the affine numerator data by one controller letter. -/
def ControllerData.step (d : ControllerData) : CenterMove → ControllerData
  | .transport => ⟨4 * d.A, 4 * d.B, d.r⟩
  | .retarded => ⟨4 * d.A, 4 * d.B + 2 * 3 ^ d.r, d.r + 1⟩
  | .advanced => ⟨2 * d.A, 2 * d.B + 3 ^ d.r, d.r + 1⟩

def initialData : ControllerData := ⟨1, 0, 0⟩

/-- Read a word from left to right, in the same order as `runCenter`. -/
def accumulate : List CenterMove → ControllerData → ControllerData
  | [], d => d
  | m :: w, d => accumulate w (d.step m)

def wordData (w : List CenterMove) : ControllerData :=
  accumulate w initialData

/-- Binary scaling exponent in the homogeneous numerator coefficient. -/
def scaleBits : List CenterMove → ℕ
  | [] => 0
  | .transport :: w => 2 + scaleBits w
  | .retarded :: w => 2 + scaleBits w
  | .advanced :: w => 1 + scaleBits w

/-- Number of divided letters, hence the ternary denominator exponent. -/
def dividedCount : List CenterMove → ℕ
  | [] => 0
  | .transport :: w => dividedCount w
  | .retarded :: w => 1 + dividedCount w
  | .advanced :: w => 1 + dividedCount w

theorem accumulate_A (w : List CenterMove) (d : ControllerData) :
    (accumulate w d).A = d.A * 2 ^ scaleBits w := by
  induction w generalizing d with
  | nil => simp [accumulate, scaleBits]
  | cons m w ih =>
      rw [accumulate, ih]
      cases m <;> simp [ControllerData.step, scaleBits, pow_add] <;> ring

theorem accumulate_r (w : List CenterMove) (d : ControllerData) :
    (accumulate w d).r = d.r + dividedCount w := by
  induction w generalizing d with
  | nil => simp [accumulate, dividedCount]
  | cons m w ih =>
      rw [accumulate, ih]
      cases m <;> simp [ControllerData.step, dividedCount] <;> omega

/-- The numerator slope is always a pure power of two. -/
theorem wordData_A (w : List CenterMove) :
    (wordData w).A = 2 ^ scaleBits w := by
  simpa [wordData, initialData] using accumulate_A w initialData

/-- The denominator exponent is exactly the number of divided letters. -/
theorem wordData_r (w : List CenterMove) :
    (wordData w).r = dividedCount w := by
  simpa [wordData, initialData] using accumulate_r w initialData

/-- In particular the numerator slope is invertible at every ternary
precision. -/
theorem wordData_A_coprime_three_pow (w : List CenterMove) (k : ℕ) :
    (wordData w).A.Coprime (3 ^ k) := by
  rw [wordData_A]
  exact Nat.coprime_pow_primes (scaleBits w) k
    Nat.prime_two Nat.prime_three (by norm_num)

/-- Cancellation of an invertible natural multiplier from a congruence. -/
theorem modEq_of_mul_modEq_mul_of_coprime
    {A M x y : ℕ} (hcop : A.Coprime M)
    (hmul : A * x ≡ A * y [MOD M]) :
    x ≡ y [MOD M] := by
  rw [Nat.modEq_iff_dvd] at hmul ⊢
  have hmul' : (M : ℤ) ∣ (A : ℤ) * ((y : ℤ) - (x : ℤ)) := by
    convert hmul using 1 <;> push_cast <;> ring
  exact hcop.isCoprime.symm.dvd_of_dvd_mul_left hmul'

/-- A linear congruence with invertible slope always has a solution. -/
theorem exists_affine_modEq_of_coprime
    (A B target modulus : ℕ) (hmodulus : 0 < modulus)
    (hcop : A.Coprime modulus) :
    ∃ h : ℕ, A * h + B ≡ target [MOD modulus] := by
  letI : NeZero modulus := ⟨Nat.ne_of_gt hmodulus⟩
  let z : ZMod modulus :=
    (A : ZMod modulus)⁻¹ *
      ((target : ZMod modulus) - (B : ZMod modulus))
  refine ⟨z.val, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp only [z]
  calc
    (A : ZMod modulus) *
          ((A : ZMod modulus)⁻¹ *
            ((target : ZMod modulus) - (B : ZMod modulus))) + B =
        ((A : ZMod modulus) * (A : ZMod modulus)⁻¹) *
            ((target : ZMod modulus) - (B : ZMod modulus)) + B := by ring
    _ = (target : ZMod modulus) - (B : ZMod modulus) + B := by
      rw [ZMod.coe_mul_inv_eq_one A hcop, one_mul]
    _ = target := by ring

/-- A fixed controller word has at most one initial ternary residue class
producing any prescribed numerator residue.  This is the ternary analogue
of the exact dyadic cylinder theorem for shortcut parity words. -/
theorem numerator_modEq_injective
    (w : List CenterMove) {k h₁ h₂ : ℕ}
    (hnum : (wordData w).A * h₁ + (wordData w).B ≡
      (wordData w).A * h₂ + (wordData w).B [MOD 3 ^ k]) :
    h₁ ≡ h₂ [MOD 3 ^ k] := by
  have hmul : (wordData w).A * h₁ ≡
      (wordData w).A * h₂ [MOD 3 ^ k] :=
    Nat.ModEq.add_right_cancel' (wordData w).B hnum
  exact modEq_of_mul_modEq_mul_of_coprime
    (wordData_A_coprime_three_pow w k) hmul

/-- QM136a: the numerator congruence of a fixed word and target has exactly
one solution class.  This theorem makes no claim that a representative in
that class makes the word legal. -/
theorem exists_unique_numerator_input_class
    (w : List CenterMove) (g k : ℕ) :
    ∃ h : ℕ,
      ((wordData w).A * h + (wordData w).B ≡
        3 ^ (wordData w).r * g
          [MOD 3 ^ (k + (wordData w).r)]) ∧
      ∀ h' : ℕ,
        (wordData w).A * h' + (wordData w).B ≡
          3 ^ (wordData w).r * g
            [MOD 3 ^ (k + (wordData w).r)] →
        h' ≡ h [MOD 3 ^ (k + (wordData w).r)] := by
  obtain ⟨h, hh⟩ := exists_affine_modEq_of_coprime
    (wordData w).A (wordData w).B (3 ^ (wordData w).r * g)
    (3 ^ (k + (wordData w).r))
    (by positivity)
    (wordData_A_coprime_three_pow w (k + (wordData w).r))
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  exact numerator_modEq_injective w (hh'.trans hh.symm)

/-- Optional CRT consumer of QM132d and QM136a: any prescribed dyadic
shortcut cylinder and the unique ternary numerator cylinder have a common
natural representative.  This proves local congruence compatibility only;
it supplies neither positivity of later quotients nor controller legality. -/
theorem exists_dyadic_and_numerator_input
    (w : List CenterMove) (dyadicClass N g k : ℕ) :
    ∃ z : ℕ,
      z ≡ dyadicClass [MOD 2 ^ N] ∧
      (wordData w).A * z + (wordData w).B ≡
        3 ^ (wordData w).r * g
          [MOD 3 ^ (k + (wordData w).r)] := by
  obtain ⟨h, hh, _hunique⟩ :=
    exists_unique_numerator_input_class w g k
  have hcop : (2 ^ N).Coprime (3 ^ (k + (wordData w).r)) :=
    Nat.coprime_pow_primes N (k + (wordData w).r)
      Nat.prime_two Nat.prime_three (by norm_num)
  let z := Nat.chineseRemainder hcop dyadicClass h
  refine ⟨z, z.property.1, ?_⟩
  have hztern : (z : ℕ) ≡ h [MOD 3 ^ (k + (wordData w).r)] :=
    z.property.2
  exact ((hztern.mul_left (wordData w).A).add_right
    (wordData w).B).trans hh

/-- One legal controller step preserves the affine numerator invariant. -/
theorem ControllerData.step_invariant (d : ControllerData)
    {origin h : ℕ} (hinv : 3 ^ d.r * h = d.A * origin + d.B)
    (m : CenterMove) (hm : m.Legal h) :
    3 ^ (d.step m).r * m.apply h =
      (d.step m).A * origin + (d.step m).B := by
  cases m with
  | transport =>
      simp only [ControllerData.step, CenterMove.apply, transportCenter]
      calc
        3 ^ d.r * (4 * h) = 4 * (3 ^ d.r * h) := by ring
        _ = 4 * (d.A * origin + d.B) := by rw [hinv]
        _ = 4 * d.A * origin + 4 * d.B := by ring
  | retarded =>
      have hh9 : h % 9 = 7 := hm
      have hh3 : h % 3 = 1 := by omega
      have hcenter := three_mul_retardedCenter hh3
      simp only [ControllerData.step, CenterMove.apply]
      rw [pow_succ, mul_assoc, hcenter]
      calc
        3 ^ d.r * (4 * h + 2) =
            4 * (3 ^ d.r * h) + 2 * 3 ^ d.r := by ring
        _ = 4 * (d.A * origin + d.B) + 2 * 3 ^ d.r := by rw [hinv]
        _ = 4 * d.A * origin + (4 * d.B + 2 * 3 ^ d.r) := by ring
  | advanced =>
      have hh9 : h % 9 = 1 := hm
      have hh3 : h % 3 = 1 := by omega
      have hcenter := three_mul_advancedCenter hh3
      simp only [ControllerData.step, CenterMove.apply]
      rw [pow_succ, mul_assoc, hcenter]
      calc
        3 ^ d.r * (2 * h + 1) =
            2 * (3 ^ d.r * h) + 3 ^ d.r := by ring
        _ = 2 * (d.A * origin + d.B) + 3 ^ d.r := by rw [hinv]
        _ = 2 * d.A * origin + (2 * d.B + 3 ^ d.r) := by ring

/-- The affine invariant survives an arbitrary legal word, even when begun
from already accumulated data. -/
theorem accumulate_invariant (w : List CenterMove) (d : ControllerData)
    {origin h : ℕ} (hinv : 3 ^ d.r * h = d.A * origin + d.B)
    (hw : LegalWord w h) :
    let out := accumulate w d
    3 ^ out.r * runCenter w h = out.A * origin + out.B := by
  induction w generalizing d h with
  | nil => simpa [accumulate, runCenter]
  | cons m w ih =>
      rcases hw with ⟨hm, hw⟩
      simpa only [accumulate, runCenter] using
        ih (d.step m) (d.step_invariant hinv m hm) hw

/-- QM134b: exact affine/radix form of a legal positive-center word. -/
theorem wordData_exact (w : List CenterMove) {h : ℕ}
    (hw : LegalWord w h) :
    3 ^ (wordData w).r * runCenter w h =
      (wordData w).A * h + (wordData w).B := by
  simpa [wordData, initialData] using
    accumulate_invariant w initialData (origin := h) (h := h) (by rfl) hw

/-- Multiplying both values and the modulus by `3^r` is reversible. -/
theorem three_pow_mul_modEq_iff (h' g k r : ℕ) :
    h' ≡ g [MOD 3 ^ k] ↔
      3 ^ r * h' ≡ 3 ^ r * g [MOD 3 ^ (k + r)] := by
  have hcancel := Nat.ModEq.mul_left_cancel_iff'
    (a := h') (b := g) (m := 3 ^ k)
    (by positivity : 3 ^ r ≠ 0)
  rw [show 3 ^ (k + r) = 3 ^ r * 3 ^ k by
    rw [Nat.add_comm, pow_add]]
  exact hcancel.symm

/-- QM134c: exact ternary connector test for a legal controller word. -/
theorem endpoint_modEq_iff_numerator_modEq
    (w : List CenterMove) {h g k : ℕ} (hw : LegalWord w h) :
    runCenter w h ≡ g [MOD 3 ^ k] ↔
      (wordData w).A * h + (wordData w).B ≡
        3 ^ (wordData w).r * g [MOD 3 ^ (k + (wordData w).r)] := by
  rw [← wordData_exact w hw]
  exact three_pow_mul_modEq_iff
    (runCenter w h) g k (wordData w).r

/-- A fixed legal connector aimed at one target cylinder selects at most one
initial cylinder, at the stronger precision `k+r`. -/
theorem endpoint_target_initial_modEq
    (w : List CenterMove) {h₁ h₂ g k : ℕ}
    (hw₁ : LegalWord w h₁) (hw₂ : LegalWord w h₂)
    (htarget₁ : runCenter w h₁ ≡ g [MOD 3 ^ k])
    (htarget₂ : runCenter w h₂ ≡ g [MOD 3 ^ k]) :
    h₁ ≡ h₂ [MOD 3 ^ (k + (wordData w).r)] := by
  have hnum₁ :=
    (endpoint_modEq_iff_numerator_modEq w hw₁).mp htarget₁
  have hnum₂ :=
    (endpoint_modEq_iff_numerator_modEq w hw₂).mp htarget₂
  exact numerator_modEq_injective w (hnum₁.trans hnum₂.symm)

/-! ## Abstract reset recurrence -/

/-- Cancelling a normalized depth-`N` initial displacement from the exact
Syracuse difference cocycle leaves the odd multiplier at the endpoint. -/
theorem endpoint_difference_of_normalized_start
    {x c endpoint cEnd m : ℤ} {N O : ℕ}
    (hstart : x - c = (2 : ℤ) ^ N * m)
    (hcocycle : (2 : ℤ) ^ N * (endpoint - cEnd) =
      (3 : ℤ) ^ O * (x - c)) :
    endpoint - cEnd = (3 : ℤ) ^ O * m := by
  apply mul_left_cancel₀ (pow_ne_zero N (by norm_num : (2 : ℤ) ≠ 0))
  calc
    (2 : ℤ) ^ N * (endpoint - cEnd) =
        (3 : ℤ) ^ O * (x - c) := hcocycle
    _ = (3 : ℤ) ^ O * ((2 : ℤ) ^ N * m) := by rw [hstart]
    _ = (2 : ℤ) ^ N * ((3 : ℤ) ^ O * m) := by ring

/-- QM134d: exact affine recurrence between two normalized controller
resets.  No positivity, integrality, or branch legality is silently added;
those are the genuine conditions a counterexample construction must supply.
-/
theorem exact_reset_recurrence
    {x c endpoint cEnd cNext m mNext : ℤ} {N O NNext : ℕ}
    (hstart : x - c = (2 : ℤ) ^ N * m)
    (hcocycle : (2 : ℤ) ^ N * (endpoint - cEnd) =
      (3 : ℤ) ^ O * (x - c))
    (hnext : endpoint - cNext = (2 : ℤ) ^ NNext * mNext) :
    (2 : ℤ) ^ NNext * mNext =
      (3 : ℤ) ^ O * m + (cEnd - cNext) := by
  have hend := endpoint_difference_of_normalized_start hstart hcocycle
  calc
    (2 : ℤ) ^ NNext * mNext = endpoint - cNext := hnext.symm
    _ = (endpoint - cEnd) + (cEnd - cNext) := by ring
    _ = (3 : ℤ) ^ O * m + (cEnd - cNext) := by rw [hend]

end KLControllerReset
end KontoroC
