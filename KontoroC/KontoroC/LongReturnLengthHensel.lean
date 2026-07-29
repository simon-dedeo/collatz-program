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

/-- Multiplication by a unit permutes a finite residue ring.  The witness is
the literal inverse unit in `ZMod M`, not a search oracle. -/
theorem solve_coprime_linear_congruence
    (a b target M : ℕ) (hM : 0 < M) (hcop : Nat.Coprime a M) :
    ∃ r : ℕ, r < M ∧ (b + a * r) % M = target % M := by
  letI : NeZero M := ⟨hM.ne'⟩
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime a hcop
  let targetZ : ZMod M := target - b
  let rZ : ZMod M := (u⁻¹ : (ZMod M)ˣ) * targetZ
  let r := rZ.val
  have hrCast : (r : ZMod M) = rZ := ZMod.natCast_zmod_val rZ
  have heqZ : ((b + a * r : ℕ) : ZMod M) = (target : ZMod M) := by
    push_cast
    rw [hrCast]
    dsimp [rZ, targetZ]
    have hu : (u : ZMod M) = (a : ZMod M) :=
      ZMod.coe_unitOfCoprime a hcop
    rw [← hu, ← mul_assoc, Units.mul_inv]
    simp
  refine ⟨r, ?_, ?_⟩
  · dsimp [r]
    exact ZMod.val_lt rZ
  · calc
      (b + a * r) % M =
          (((b + a * r : ℕ) : ZMod M).val) := by
            rw [ZMod.val_natCast]
      _ = ((target : ZMod M).val) := congrArg ZMod.val heqZ
      _ = target % M := by rw [ZMod.val_natCast]

/-- Multiplication by an odd natural permutes every dyadic residue ring. -/
theorem solve_odd_linear_congruence (a b target w : ℕ) (ha : Odd a) :
    ∃ r : ℕ, r < 2 ^ w ∧ (b + a * r) % 2 ^ w = target % 2 ^ w := by
  apply solve_coprime_linear_congruence
  · positivity
  · exact Nat.Coprime.pow_right w (Nat.coprime_two_right.mpr ha)

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

/-- The finite base alignment assumed by `diagonal_hensel_splice` always
exists.  It is the unique solution of one odd linear congruence modulo the
next complete block `2^P(2g)`; no search or unproved CRT oracle is used. -/
theorem exists_diagonal_hensel_alignment
    {g y : ℕ} (hg : 0 < g) :
    ∃ r znext ynext : ℕ,
      r < 2 ^ P (2 * g) ∧
      y + 3 ^ Q g * r = 2 ^ (P (2 * g) - 77) * znext ∧
      HenselStep (2 * g) znext ynext := by
  let e := P (2 * g) - 77
  let w := e + 77
  let a := 3 ^ Q g
  let c := 3 ^ Q (2 * g)
  have htwoG : 0 < 2 * g := by omega
  have hPnext := seventy_seven_le_P htwoG
  have hsplit : P (2 * g) = e + 77 := by dsimp [e]; omega
  have htargetLt : 2 ^ e < 2 ^ w := by
    dsimp [w]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hcaOdd : Odd (c * a) := by
    have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
    dsimp [c, a]
    exact (Odd.pow (n := Q (2 * g)) hthree).mul
      (Odd.pow (n := Q g) hthree)
  obtain ⟨r, hrLt, hrmod⟩ :=
    solve_odd_linear_congruence (c * a) (c * y) (2 ^ e) w hcaOdd
  rw [Nat.mod_eq_of_lt htargetLt] at hrmod
  have hinside : c * y + (c * a) * r = c * (y + a * r) := by ring
  rw [hinside] at hrmod
  let ynext := (c * (y + a * r)) / 2 ^ w
  have hN : c * (y + a * r) = 2 ^ e + 2 ^ w * ynext := by
    calc
      c * (y + a * r) =
          (c * (y + a * r)) % 2 ^ w +
            2 ^ w * ((c * (y + a * r)) / 2 ^ w) :=
        (Nat.mod_add_div _ _).symm
      _ = 2 ^ e + 2 ^ w * ynext := by rw [hrmod]
  have hdvdProd : 2 ^ e ∣ c * (y + a * r) := by
    refine ⟨1 + 2 ^ 77 * ynext, ?_⟩
    rw [hN]
    dsimp [w]
    rw [pow_add]
    ring
  have hcop : Nat.Coprime (2 ^ e) c := by
    dsimp [c]
    exact Nat.Coprime.pow e (Q (2 * g)) (by norm_num)
  have hdvd : 2 ^ e ∣ y + a * r := hcop.dvd_of_dvd_mul_left hdvdProd
  obtain ⟨znext, hznext⟩ := hdvd
  have hstep : HenselStep (2 * g) znext ynext := by
    simp only [HenselStep]
    change c * znext = 1 + 2 ^ 77 * ynext
    have hfactor :
        2 ^ e * (c * znext) = 2 ^ e * (1 + 2 ^ 77 * ynext) := by
      calc
        2 ^ e * (c * znext) = c * (y + a * r) := by rw [hznext]; ring
        _ = 2 ^ e + 2 ^ w * ynext := hN
        _ = 2 ^ e * (1 + 2 ^ 77 * ynext) := by
          dsimp [w]
          rw [pow_add]
          ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ e) hfactor
  refine ⟨r, znext, ynext, ?_, ?_, hstep⟩
  · simpa [hsplit] using hrLt
  · simpa [e, a] using hznext

/-- Unconditional Hensel-level diagonal splice.  Every current cell admits a
finite next alignment, and that one alignment transports all higher tails
through both opcode levels. -/
theorem exists_diagonal_hensel_splice
    {g z y : ℕ} (hg : 0 < g) (hcurrent : HenselStep g z y) :
    ∃ r znext ynext : ℕ,
      r < 2 ^ P (2 * g) ∧
      y + 3 ^ Q g * r = 2 ^ (P (2 * g) - 77) * znext ∧
      HenselStep (2 * g) znext ynext ∧
      ∀ t : ℕ,
        HenselStep g
            (z + 2 ^ 77 * (r + 2 ^ (P (2 * g) - 77 + 77) * t))
            (2 ^ (P (2 * g) - 77) *
              (znext + 2 ^ 77 * (3 ^ Q g * t))) ∧
          HenselStep (2 * g)
            (znext + 2 ^ 77 * (3 ^ Q g * t))
            (ynext + 3 ^ Q (2 * g) * (3 ^ Q g * t)) := by
  obtain ⟨r, znext, ynext, hr, halign, hnext⟩ :=
    exists_diagonal_hensel_alignment (y := y) hg
  exact ⟨r, znext, ynext, hr, halign, hnext,
    fun t ↦ diagonal_hensel_splice hcurrent halign hnext t⟩

/-- Complete return-length holonomy: appending one high cell is equivalent
to exposing the forced zero block and executing the 77-bit Hensel decoder. -/
theorem returnBalance_succ_iff_hensel
    {k g F X Y : ℕ} (hg : 0 < g) (hbase : ReturnBalance k g F X) :
    ReturnBalance (k + 1) g F Y ↔
      ∃ z : ℕ, Odd z ∧ X = 2 ^ (P g - 77) * z ∧
        HenselStep g z Y := by
  simp only [HenselStep]
  rw [returnBalance_succ_iff hg hbase, output_equation_iff_hensel hg]

/-- Every Hensel cell is realized by an actual pair of adjacent algebraic
long-return balances.  A single ternary congruence chooses the transported
tail; the resulting source payload `F` is an ordinary positive natural. -/
theorem exists_adjacent_return_realization
    {g z y : ℕ} (hg : 0 < g) (hcell : HenselStep g z y) (k : ℕ) :
    ∃ t F X Y : ℕ,
      t < 3 ^ R k g ∧ 0 < F ∧
      X = 2 ^ (P g - 77) * (z + 2 ^ 77 * t) ∧
      Y = y + 3 ^ Q g * t ∧
      ReturnBalance k g F X ∧ ReturnBalance (k + 1) g F Y := by
  let e := P g - 77
  let M := 3 ^ R k g
  let base := defect k g + 2 ^ S k g * (2 ^ e * z)
  let coeff := 2 ^ (S k g + P g)
  have hP := seventy_seven_le_P hg
  have hsplit : P g = e + 77 := by dsimp [e]; omega
  have hcop : Nat.Coprime coeff M := by
    dsimp [coeff, M]
    exact Nat.Coprime.pow (S k g + P g) (R k g) (by norm_num)
  obtain ⟨t, ht, htmod⟩ :=
    solve_coprime_linear_congruence coeff base 0 M (by positivity) hcop
  simp only [Nat.zero_mod] at htmod
  let X := 2 ^ e * (z + 2 ^ 77 * t)
  let Y := y + 3 ^ Q g * t
  have hnumerator :
      defect k g + 2 ^ S k g * X = base + coeff * t := by
    dsimp [X, base, coeff]
    rw [hsplit, pow_add, pow_add]
    ring
  have hnumMod : (defect k g + 2 ^ S k g * X) % M = 0 := by
    rw [hnumerator]
    exact htmod
  have hdiv : M ∣ defect k g + 2 ^ S k g * X :=
    Nat.dvd_iff_mod_eq_zero.mpr hnumMod
  let F := (defect k g + 2 ^ S k g * X) / M
  have hFmul : M * F = defect k g + 2 ^ S k g * X := by
    dsimp [F]
    exact Nat.mul_div_cancel' hdiv
  have hdefectPos : 0 < defect k g := by
    apply Nat.add_pos_left
    exact Nat.mul_pos (by positivity) (by dsimp [b0]; positivity)
  have hFpos : 0 < F := by
    by_contra hnot
    have hFzero : F = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hFzero, mul_zero] at hFmul
    omega
  have hbase : ReturnBalance k g F X := by
    change 3 ^ R k g * F = defect k g + 2 ^ S k g * X
    simpa [M] using hFmul
  have hlift : HenselStep g (z + 2 ^ 77 * t) Y := by
    simpa [Y] using henselStep_lift hcell t
  have hnext : ReturnBalance (k + 1) g F Y := by
    apply (returnBalance_succ_iff_hensel hg hbase).2
    exact ⟨z + 2 ^ 77 * t, henselStep_odd hlift, rfl, hlift⟩
  exact ⟨t, F, X, Y, by simpa [M] using ht, hFpos, rfl, rfl, hbase, hnext⟩

/-- A realized adjacent-return pair carries a full ordinary tail.  Shifting
the Hensel tail by one ternary return modulus changes the common source and
both sibling outputs by the displayed exact affine laws. -/
theorem adjacent_return_realization_lift
    {k g F X Y : ℕ}
    (hbase : ReturnBalance k g F X)
    (hnext : ReturnBalance (k + 1) g F Y)
    (t : ℕ) :
    ReturnBalance k g
        (F + 2 ^ (S k g + P g) * t)
        (X + 2 ^ P g * (3 ^ R k g * t)) ∧
      ReturnBalance (k + 1) g
        (F + 2 ^ (S k g + P g) * t)
        (Y + 3 ^ Q g * (3 ^ R k g * t)) := by
  have hR := R_succ_eq k g
  have hS := S_succ_eq k g
  constructor
  · simp only [ReturnBalance] at hbase ⊢
    rw [mul_add, hbase, pow_add]
    ring
  · simp only [ReturnBalance] at hnext ⊢
    rw [mul_add, hnext, hR, hS, pow_add, pow_add]
    ring

/-- Every positive odd affine progression contains a source of an adjacent
long-return pair at any positive opcode and any chosen return length.  One
dyadic unit congruence simultaneously enforces the shorter return balance and
the 77-bit Hensel condition for the longer sibling. -/
theorem exists_adjacent_return_on_odd_progression
    {opcode sourceBase stride : ℕ}
    (hopcode : 0 < opcode) (hstride : Odd stride) (k : ℕ) :
    ∃ t source X Y : ℕ,
      0 < source ∧ source = sourceBase + stride * t ∧
      ReturnBalance k opcode source X ∧
      ReturnBalance (k + 1) opcode source Y := by
  let e := P opcode - 77
  let E := S k opcode + e
  let modulus := 2 ^ (E + 77)
  let ternary := 3 ^ Q opcode
  let slope := 3 ^ R k opcode
  let forcing := defect k opcode
  let b := ternary * slope * sourceBase
  let coeff := ternary * slope * stride
  let target := ternary * forcing + 2 ^ E
  have hcoeffOdd : Odd coeff := by
    have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
    dsimp [coeff, ternary, slope]
    exact ((Odd.pow (n := Q opcode) hthree).mul
      (Odd.pow (n := R k opcode) hthree)).mul hstride
  obtain ⟨t0, ht0, ht0mod⟩ :=
    solve_odd_linear_congruence coeff b target (E + 77) hcoeffOdd
  let extra := forcing + 1
  let t := t0 + modulus * extra
  have htmod : (b + coeff * t) % modulus = target % modulus := by
    have hexpand :
        b + coeff * t = b + coeff * t0 + (coeff * extra) * modulus := by
      dsimp [t]
      ring
    rw [hexpand]
    simpa using ht0mod
  let source := sourceBase + stride * t
  have hleft : b + coeff * t = ternary * slope * source := by
    dsimp [b, coeff, source]
    ring
  rw [hleft] at htmod
  have hforcingPos : 0 < forcing := by
    dsimp [forcing]
    apply Nat.add_pos_left
    exact Nat.mul_pos (by positivity) (by dsimp [b0]; positivity)
  have hmodulusPos : 0 < modulus := by positivity
  have hextraLe : extra ≤ modulus * extra :=
    Nat.le_mul_of_pos_left extra hmodulusPos
  have hforcingLtT : forcing < t := by
    have hforcingLtExtra : forcing < extra := by
      dsimp [extra]
      omega
    have hproductLeT : modulus * extra ≤ t := by
      dsimp [t]
      omega
    exact hforcingLtExtra.trans_le (hextraLe.trans hproductLeT)
  have hstridePos : 0 < stride := hstride.pos
  have htPos : 0 < t := hforcingPos.trans hforcingLtT
  have hsourcePos : 0 < source := by
    dsimp [source]
    exact Nat.add_pos_right _ (Nat.mul_pos hstridePos htPos)
  have hslopePos : 0 < slope := by positivity
  have hforcingLtProduct : forcing < slope * source := by
    have ht_le_stride : t ≤ stride * t :=
      Nat.le_mul_of_pos_left t hstridePos
    have hstride_le_source : stride * t ≤ source := by
      dsimp [source]
      omega
    have hsource_le_slope : source ≤ slope * source :=
      Nat.le_mul_of_pos_left source hslopePos
    exact hforcingLtT.trans_le
      (ht_le_stride.trans (hstride_le_source.trans hsource_le_slope))
  let N := slope * source - forcing
  have hdecomp : slope * source = forcing + N := by
    dsimp [N]
    omega
  have hmodEq :
      ternary * slope * source ≡ target [MOD modulus] := htmod
  have htarget : target = ternary * forcing + 2 ^ E := rfl
  rw [htarget] at hmodEq
  have hleftDecomp :
      ternary * slope * source = ternary * forcing + ternary * N := by
    calc
      ternary * slope * source = ternary * (slope * source) := by ring
      _ = ternary * (forcing + N) := by rw [hdecomp]
      _ = ternary * forcing + ternary * N := by ring
  rw [hleftDecomp] at hmodEq
  have hNModEq : ternary * N ≡ 2 ^ E [MOD modulus] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl (ternary * forcing)) hmodEq
  have htargetLt : 2 ^ E < modulus := by
    dsimp [modulus]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hNmod : (ternary * N) % modulus = 2 ^ E := by
    rw [Nat.ModEq] at hNModEq
    simpa [Nat.mod_eq_of_lt htargetLt] using hNModEq
  let Y := (ternary * N) / modulus
  have hTN : ternary * N = 2 ^ E + modulus * Y := by
    calc
      ternary * N = (ternary * N) % modulus +
          modulus * ((ternary * N) / modulus) :=
        (Nat.mod_add_div _ _).symm
      _ = 2 ^ E + modulus * Y := by rw [hNmod]
  have hdvdProd : 2 ^ E ∣ ternary * N := by
    refine ⟨1 + 2 ^ 77 * Y, ?_⟩
    rw [hTN]
    dsimp [modulus]
    rw [pow_add]
    ring
  have hcop : Nat.Coprime (2 ^ E) ternary := by
    dsimp [ternary]
    exact Nat.Coprime.pow E (Q opcode) (by norm_num)
  have hdvd : 2 ^ E ∣ N := hcop.dvd_of_dvd_mul_left hdvdProd
  obtain ⟨znext, hznext⟩ := hdvd
  have hcell : HenselStep opcode znext Y := by
    simp only [HenselStep]
    change ternary * znext = 1 + 2 ^ 77 * Y
    have hfactor :
        2 ^ E * (ternary * znext) = 2 ^ E * (1 + 2 ^ 77 * Y) := by
      calc
        2 ^ E * (ternary * znext) = ternary * N := by rw [hznext]; ring
        _ = 2 ^ E + modulus * Y := hTN
        _ = 2 ^ E * (1 + 2 ^ 77 * Y) := by
          dsimp [modulus]
          rw [pow_add]
          ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ E) hfactor
  let X := 2 ^ e * znext
  have hN_as_output : N = 2 ^ S k opcode * X := by
    dsimp [X, E] at hznext ⊢
    rw [hznext, pow_add]
    ring
  have hbase : ReturnBalance k opcode source X := by
    simp only [ReturnBalance]
    change slope * source = forcing + 2 ^ S k opcode * X
    rw [hdecomp, hN_as_output]
  have hnext : ReturnBalance (k + 1) opcode source Y := by
    apply (returnBalance_succ_iff_hensel hopcode hbase).2
    refine ⟨znext, henselStep_odd hcell, ?_, hcell⟩
    rfl
  exact ⟨t, source, X, Y, hsourcePos, rfl, hbase, hnext⟩

/-- A realized adjacent pair can be extended to a realized adjacent pair at
the doubled opcode while preserving the literal common endpoint: first lift
the current pair along its full tail, then select the next source inside that
odd affine progression. -/
theorem extend_adjacent_return_pair
    {k g F X Y : ℕ} (hg : 0 < g)
    (hbase : ReturnBalance k g F X)
    (hnext : ReturnBalance (k + 1) g F Y)
    (knext : ℕ) :
    ∃ t F' X' common Xnext Ynext : ℕ,
      F' = F + 2 ^ (S k g + P g) * t ∧
      X' = X + 2 ^ P g * (3 ^ R k g * t) ∧
      common = Y + 3 ^ Q g * (3 ^ R k g * t) ∧
      ReturnBalance k g F' X' ∧
      ReturnBalance (k + 1) g F' common ∧
      ReturnBalance knext (2 * g) common Xnext ∧
      ReturnBalance (knext + 1) (2 * g) common Ynext := by
  let stride := 3 ^ Q g * 3 ^ R k g
  have hstrideOdd : Odd stride := by
    have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
    exact (Odd.pow (n := Q g) hthree).mul (Odd.pow (n := R k g) hthree)
  obtain ⟨t, common, Xnext, Ynext, _hcommonPos, hcommon,
      hnextBase, hnextLong⟩ :=
    exists_adjacent_return_on_odd_progression
      (opcode := 2 * g) (sourceBase := Y) (stride := stride)
      (by omega) hstrideOdd knext
  let F' := F + 2 ^ (S k g + P g) * t
  let X' := X + 2 ^ P g * (3 ^ R k g * t)
  have hlift := adjacent_return_realization_lift hbase hnext t
  refine ⟨t, F', X', common, Xnext, Ynext, rfl, rfl, ?_, hlift.1,
    ?_, hnextBase, hnextLong⟩
  · simpa [stride, mul_assoc] using hcommon
  · have hcommon' : common = Y + 3 ^ Q g * (3 ^ R k g * t) := by
      simpa [stride, mul_assoc] using hcommon
    rw [hcommon']
    exact hlift.2

end LongReturnLengthHensel
end KontoroC
