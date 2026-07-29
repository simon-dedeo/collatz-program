/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongDoublingQuineResidual

/-!
# Return length is an exact Hensel instruction

The six-high-cell return crossed the Archimedean precision wall by inserting
extra `g -> g` cells.  This file compares two *consecutive* return lengths
from the same source payload.  The comparison eliminates the source and all
large forcing constants.

If the length-`k` and length-`k+1` returns have outputs `X` and `Y`, then

`3^Q X = 2^(P-77) + 2^P Y`.

Equivalently, the shorter output has the forced factor

`X = 2^(P-77) z`

with `z` odd, and the longer output is obtained by the stationary 77-bit
negative Hensel instruction

`3^Q z = 1 + 2^77 Y`.

Thus adaptive return length is genuine state, but not free branching: every
extra high cell first demands exactly `23(g-1)` zero bits and then applies one
fixed-width Hensel division.  This is a construction interface, not an orbit.
-/

namespace KontoroC
namespace LongReturnLengthHensel

open LongDoublingQuineThreshold

/-- The exact long-return balance, with the return length exposed as data. -/
def ReturnBalance (k g F Fnext : ℕ) : Prop :=
  3 ^ R k g * F = defect k g + 2 ^ S k g * Fnext

theorem P_sub_seventy_seven_eq (g : ℕ) : P g - 77 = 23 * (g - 1) := by
  simp only [P]
  omega

theorem seventy_seven_le_P {g : ℕ} (hg : 0 < g) : 77 ≤ P g := by
  simp only [P]
  omega

/-- The Hensel cell has ample real gain even after paying one additional
binary bit beyond the complete forced block. -/
theorem double_two_pow_P_lt_three_pow_Q (g : ℕ) :
    2 ^ (P g + 1) < 3 ^ Q g := by
  have hconstant : 2 ^ 55 < 3 ^ 40 := by norm_num
  have hpowers : (2 ^ 23) ^ g ≤ (3 ^ 17) ^ g :=
    Nat.pow_le_pow_left three_pow_17_gt_two_pow_23.le g
  calc
    2 ^ (P g + 1) = 2 ^ 55 * (2 ^ 23) ^ g := by
      rw [show P g + 1 = 55 + 23 * g by simp [P]; omega,
        pow_add, pow_mul]
    _ < 3 ^ 40 * (2 ^ 23) ^ g :=
      Nat.mul_lt_mul_of_pos_right hconstant (by positivity)
    _ ≤ 3 ^ 40 * (3 ^ 17) ^ g := Nat.mul_le_mul_left _ hpowers
    _ = 3 ^ Q g := by
      rw [show Q g = 40 + 17 * g by simp [Q]; omega,
        pow_add, pow_mul]

theorem R_succ_eq (k g : ℕ) : R (k + 1) g = R k g + Q g := by
  simp only [R]
  ring

theorem S_succ_eq (k g : ℕ) : S (k + 1) g = S k g + P g := by
  simp only [S]
  ring

theorem appended_defect_exponent_eq (k g : ℕ) (hg : 0 < g) :
    77 + (k + 1) * P g = S k g + (P g - 77) := by
  have hP := seventy_seven_le_P hg
  let e := P g - 77
  have hPe : 77 + e = P g := by dsimp [e]; omega
  calc
    77 + (k + 1) * P g = 77 + (k + 1) * (77 + e) := by rw [hPe]
    _ = 154 + k * (77 + e) + e := by ring
    _ = 154 + k * P g + e := by rw [hPe]
    _ = S k g + (P g - 77) := by rfl

/-- Once the length-`k` output is fixed, the length-`k+1` return exists
exactly when the two candidate outputs obey one small affine equation. -/
theorem returnBalance_succ_iff
    {k g F X Y : ℕ} (hg : 0 < g) (hbase : ReturnBalance k g F X) :
    ReturnBalance (k + 1) g F Y ↔
      3 ^ Q g * X = 2 ^ (P g - 77) + 2 ^ P g * Y := by
  have hR := R_succ_eq k g
  have hS := S_succ_eq k g
  have hE := appended_defect_exponent_eq k g hg
  have hscaled :
      3 ^ R (k + 1) g * F =
        3 ^ Q g * defect k g + 2 ^ S k g * (3 ^ Q g * X) := by
    calc
      3 ^ R (k + 1) g * F =
          3 ^ Q g * (3 ^ R k g * F) := by
            rw [hR, pow_add]
            ring
      _ = 3 ^ Q g * (defect k g + 2 ^ S k g * X) := by
            rw [hbase]
      _ = 3 ^ Q g * defect k g +
          2 ^ S k g * (3 ^ Q g * X) := by ring
  constructor
  · intro hnext
    have hnext' :
        3 ^ R (k + 1) g * F =
          3 ^ Q g * defect k g +
            2 ^ S k g * (2 ^ (P g - 77) + 2 ^ P g * Y) := by
      calc
        3 ^ R (k + 1) g * F =
            defect (k + 1) g + 2 ^ S (k + 1) g * Y := hnext
        _ = 3 ^ Q g * defect k g +
            2 ^ S k g * (2 ^ (P g - 77) + 2 ^ P g * Y) := by
              rw [defect_succ, hS, hE, pow_add, pow_add]
              ring
    have hadd :
        3 ^ Q g * defect k g + 2 ^ S k g * (3 ^ Q g * X) =
          3 ^ Q g * defect k g +
            2 ^ S k g * (2 ^ (P g - 77) + 2 ^ P g * Y) :=
      hscaled.symm.trans hnext'
    have hmul := Nat.add_left_cancel hadd
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ S k g) hmul
  · intro hxy
    calc
      3 ^ R (k + 1) g * F =
          3 ^ Q g * defect k g + 2 ^ S k g * (3 ^ Q g * X) := hscaled
      _ = 3 ^ Q g * defect k g +
          2 ^ S k g * (2 ^ (P g - 77) + 2 ^ P g * Y) := by rw [hxy]
      _ = defect (k + 1) g + 2 ^ S (k + 1) g * Y := by
        rw [defect_succ, hS, hE, pow_add, pow_add]
        ring

/-- The small affine equation is exactly a forced zero block followed by a
stationary 77-bit Hensel step. -/
theorem output_equation_iff_hensel {g X Y : ℕ} (hg : 0 < g) :
    3 ^ Q g * X = 2 ^ (P g - 77) + 2 ^ P g * Y ↔
      ∃ z : ℕ, Odd z ∧ X = 2 ^ (P g - 77) * z ∧
        3 ^ Q g * z = 1 + 2 ^ 77 * Y := by
  let e := P g - 77
  have hP := seventy_seven_le_P hg
  have hsplit : P g = e + 77 := by
    dsimp [e]
    omega
  constructor
  · intro hxy
    change 3 ^ Q g * X = 2 ^ e + 2 ^ P g * Y at hxy
    have hdvdProd : 2 ^ e ∣ 3 ^ Q g * X := by
      refine ⟨1 + 2 ^ 77 * Y, ?_⟩
      calc
        3 ^ Q g * X = 2 ^ e + 2 ^ P g * Y := hxy
        _ = 2 ^ e * (1 + 2 ^ 77 * Y) := by
          rw [hsplit, pow_add]
          ring
    have hcop : Nat.Coprime (2 ^ e) (3 ^ Q g) :=
      Nat.Coprime.pow e (Q g) (by norm_num)
    have hdvd : 2 ^ e ∣ X := hcop.dvd_of_dvd_mul_left hdvdProd
    obtain ⟨z, hz⟩ := hdvd
    have hsmall : 3 ^ Q g * z = 1 + 2 ^ 77 * Y := by
      have hfactored :
          2 ^ e * (3 ^ Q g * z) = 2 ^ e * (1 + 2 ^ 77 * Y) := by
        calc
          2 ^ e * (3 ^ Q g * z) = 3 ^ Q g * X := by rw [hz]; ring
          _ = 2 ^ e + 2 ^ P g * Y := hxy
          _ = 2 ^ e * (1 + 2 ^ 77 * Y) := by
            rw [hsplit, pow_add]
            ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ e) hfactored
    have hrhsOdd : Odd (1 + 2 ^ 77 * Y) := by
      rw [Nat.odd_iff]
      norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    have hprodOdd : Odd (3 ^ Q g * z) := by simpa [hsmall] using hrhsOdd
    exact ⟨z, (Nat.odd_mul.mp hprodOdd).2, hz, hsmall⟩
  · rintro ⟨z, _hzOdd, hX, hsmall⟩
    rw [hX]
    change 3 ^ Q g * (2 ^ e * z) = 2 ^ e + 2 ^ P g * Y
    rw [hsplit, pow_add]
    calc
      3 ^ Q g * (2 ^ e * z) = 2 ^ e * (3 ^ Q g * z) := by ring
      _ = 2 ^ e * (1 + 2 ^ 77 * Y) := by rw [hsmall]
      _ = 2 ^ e + 2 ^ e * 2 ^ 77 * Y := by ring

/-- The fixed-width instruction exposed after the forced zero block. -/
def HenselStep (g z y : ℕ) : Prop :=
  3 ^ Q g * z = 1 + 2 ^ 77 * y

theorem henselStep_odd {g z y : ℕ} (h : HenselStep g z y) : Odd z := by
  have hrhsOdd : Odd (1 + 2 ^ 77 * y) := by
    rw [Nat.odd_iff]
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have hprodEq : 3 ^ Q g * z = 1 + 2 ^ 77 * y := h
  have hprodOdd : Odd (3 ^ Q g * z) := by
    rw [hprodEq]
    exact hrhsOdd
  exact (Nat.odd_mul.mp hprodOdd).2

theorem henselStep_target_unique {g z y₁ y₂ : ℕ}
    (h₁ : HenselStep g z y₁) (h₂ : HenselStep g z y₂) : y₁ = y₂ := by
  simp only [HenselStep] at h₁ h₂
  omega

/-- Once one low-77-bit Hensel cell exists, it transports an arbitrary
ordinary tail.  The input tail is written in base two and the output tail is
multiplied by the odd ternary gain. -/
theorem henselStep_lift {g z y : ℕ} (h : HenselStep g z y) (t : ℕ) :
    HenselStep g (z + 2 ^ 77 * t) (y + 3 ^ Q g * t) := by
  simp only [HenselStep] at h ⊢
  calc
    3 ^ Q g * (z + 2 ^ 77 * t) =
        3 ^ Q g * z + 2 ^ 77 * (3 ^ Q g * t) := by ring
    _ = 1 + 2 ^ 77 * y + 2 ^ 77 * (3 ^ Q g * t) := by rw [h]
    _ = 1 + 2 ^ 77 * (y + 3 ^ Q g * t) := by ring

/-- The lifted output is forced: there is no hidden state in a fixed Hensel
cylinder. -/
theorem henselStep_lift_target {g z y t Y : ℕ}
    (h : HenselStep g z y)
    (hY : HenselStep g (z + 2 ^ 77 * t) Y) :
    Y = y + 3 ^ Q g * t := by
  exact henselStep_target_unique hY (henselStep_lift h t)

/-- Crucially, the decoded longer-return output is larger than the shorter
candidate even after the latter has paid its entire `23(g-1)`-bit zero block.
This is the exact self-supply inequality behind the adaptive-length attack. -/
theorem henselStep_grows_forced_output
    {g z y X : ℕ} (hg : 0 < g) (hstep : HenselStep g z y)
    (hX : X = 2 ^ (P g - 77) * z) : X < y := by
  have hzOdd := henselStep_odd hstep
  have hzPos : 0 < z := hzOdd.pos
  have hP := seventy_seven_le_P hg
  have hsplit : P g = (P g - 77) + 77 := by omega
  have hgain := double_two_pow_P_lt_three_pow_Q g
  by_contra hnot
  have hyx : y ≤ X := by omega
  have hscaled : 2 ^ 77 * y ≤ 2 ^ P g * z := by
    calc
      2 ^ 77 * y ≤ 2 ^ 77 * X := Nat.mul_le_mul_left _ hyx
      _ = 2 ^ ((P g - 77) + 77) * z := by
        rw [hX, pow_add]
        ring
      _ = 2 ^ P g * z := by rw [← hsplit]
  have hupper : 3 ^ Q g * z ≤ 1 + 2 ^ P g * z := by
    rw [hstep]
    omega
  have hlower : 2 ^ (P g + 1) * z < 3 ^ Q g * z :=
    Nat.mul_lt_mul_of_pos_right hgain hzPos
  have hmiddle : 1 + 2 ^ P g * z < 2 ^ (P g + 1) * z := by
    have hone : 1 < 2 ^ P g * z := by
      have hpow : 1 < 2 ^ P g := one_lt_pow₀ (by omega) (by omega)
      exact hpow.trans_le (Nat.le_mul_of_pos_right _ hzPos)
    calc
      1 + 2 ^ P g * z < 2 * (2 ^ P g * z) := by omega
      _ = 2 ^ (P g + 1) * z := by rw [pow_succ]; ring
  omega

/-- A conditional two-level diagonal splice.  Once one finite base alignment
places the current Hensel output in the next forced-zero cylinder, *every*
higher tail passes through both Hensel cells, with no further address choice.
The surviving tail is multiplied by the product of the two odd ternary gains. -/
theorem diagonal_hensel_splice
    {g z y r znext ynext : ℕ}
    (hcurrent : HenselStep g z y)
    (halign : y + 3 ^ Q g * r = 2 ^ (P (2 * g) - 77) * znext)
    (hnext : HenselStep (2 * g) znext ynext)
    (t : ℕ) :
    HenselStep g
        (z + 2 ^ 77 * (r + 2 ^ (P (2 * g) - 77 + 77) * t))
        (2 ^ (P (2 * g) - 77) *
          (znext + 2 ^ 77 * (3 ^ Q g * t))) ∧
      HenselStep (2 * g)
        (znext + 2 ^ 77 * (3 ^ Q g * t))
        (ynext + 3 ^ Q (2 * g) * (3 ^ Q g * t)) := by
  constructor
  · have hlift := henselStep_lift hcurrent
        (r + 2 ^ (P (2 * g) - 77 + 77) * t)
    have htarget :
        y + 3 ^ Q g * (r + 2 ^ (P (2 * g) - 77 + 77) * t) =
          2 ^ (P (2 * g) - 77) *
            (znext + 2 ^ 77 * (3 ^ Q g * t)) := by
      calc
        y + 3 ^ Q g * (r + 2 ^ (P (2 * g) - 77 + 77) * t) =
            (y + 3 ^ Q g * r) +
              3 ^ Q g * (2 ^ (P (2 * g) - 77 + 77) * t) := by ring
        _ = 2 ^ (P (2 * g) - 77) * znext +
              3 ^ Q g * (2 ^ (P (2 * g) - 77 + 77) * t) := by rw [halign]
        _ = 2 ^ (P (2 * g) - 77) *
            (znext + 2 ^ 77 * (3 ^ Q g * t)) := by
              rw [pow_add]
              ring
    rw [htarget] at hlift
    exact hlift
  · exact henselStep_lift hnext (3 ^ Q g * t)

/-- Complete return-length holonomy: appending one high cell is equivalent
to exposing the forced zero block and executing the 77-bit Hensel decoder. -/
theorem returnBalance_succ_iff_hensel
    {k g F X Y : ℕ} (hg : 0 < g) (hbase : ReturnBalance k g F X) :
    ReturnBalance (k + 1) g F Y ↔
      ∃ z : ℕ, Odd z ∧ X = 2 ^ (P g - 77) * z ∧
        HenselStep g z Y := by
  simp only [HenselStep]
  rw [returnBalance_succ_iff hg hbase, output_equation_iff_hensel hg]

end LongReturnLengthHensel
end KontoroC
