/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.MarkerBankLink

/-!
# Quarantined invariant-register obstruction for a hypothetical marker bank

**Retraction notice.**  The concrete synthesized-marker route which motivated
this file was subsequently found not to compose under the public unit-state
semantics: its third raw division uses an exponent belonging to a different
source label.  Nothing in this file validates that retracted route.

The theorems below remain valid conditional number theory.  They describe
what would follow *if* a legal path had the two displayed invariant-register
presentations.  They are retained as a reusable boundary lemma, not as a
theorem about an existing Collatz dispatcher.

Because the public register offset is a unit modulo its stride, those two
congruences force the difference of the visible binary exponents to be a
period of `2` modulo the register stride.  Already modulo `3^5 = 243`, where
`2` has order `162`, this forces every returning opcode to satisfy

`j = 123 (mod 162)`.

Using only the slightly deeper factor `3^7 = 2187` strengthens this to

`j = 447 (mod 1458)`.

For that hypothetical architecture, no opcode below `447` could return to
the fixed one-cell source class.  The retracted concrete audit did not supply
the hypotheses of this statement.
-/

namespace KontoroC

namespace MarkerBankInvariantReturn

/-- If the same value carries two visible binary exponents in one invariant
register class, their powers of two agree modulo the register stride. -/
theorem pow_modEq_of_two_invariant_presentations
    {M R E A y : ℕ}
    (hR : Nat.Coprime R M)
    (hA : 2 ^ A * y ≡ R [MOD M])
    (hE : 2 ^ E * y ≡ R [MOD M]) :
    2 ^ A ≡ 2 ^ E [MOD M] := by
  have hprod : Nat.Coprime (2 ^ A * y) M := by
    rw [Nat.coprime_iff_gcd_eq_one, hA.gcd_eq]
    exact hR.gcd_eq_one
  have hy : Nat.Coprime y M :=
    hprod.coprime_dvd_left (dvd_mul_left y (2 ^ A))
  apply Nat.ModEq.cancel_right_of_coprime hy.symm.gcd_eq_one
  exact hA.trans hE.symm

/-- After cancelling the smaller visible power, the exponent difference is
a period of two modulo the register stride. -/
theorem exponent_difference_modEq_one
    {M R E A y : ℕ}
    (hR : Nat.Coprime R M)
    (hM2 : Nat.Coprime M 2)
    (hEA : E ≤ A)
    (hA : 2 ^ A * y ≡ R [MOD M])
    (hE : 2 ^ E * y ≡ R [MOD M]) :
    2 ^ (A - E) ≡ 1 [MOD M] := by
  have hpowers := pow_modEq_of_two_invariant_presentations hR hA hE
  have hfactor :
      2 ^ (A - E) * 2 ^ E ≡ 1 * 2 ^ E [MOD M] := by
    simpa [← pow_add, Nat.sub_add_cancel hEA] using hpowers
  apply Nat.ModEq.cancel_right_of_coprime _ hfactor
  simpa using (hM2.pow 1 E).gcd_eq_one

def registerModulus : ℕ := 671265207750760396088265

def registerOffset : ℕ := 631264625086677058414369

def gapD : ℕ := 2 * 3 ^ 56

def turnaroundP (j : ℕ) : ℕ := gapD + 2 + 23 * j

theorem registerOffset_coprime_registerModulus :
    Nat.Coprime registerOffset registerModulus := by
  norm_num [registerOffset, registerModulus]

theorem registerModulus_coprime_two :
    Nat.Coprime registerModulus 2 := by
  norm_num [registerModulus]

set_option maxRecDepth 10000 in
theorem two_order_mod_243 : orderOf (2 : ZMod 243) = 162 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro p hp hd
  have hsplit : p ∣ 2 ∨ p ∣ 3 ^ 4 := by
    apply hp.dvd_mul.mp
    norm_num at hd ⊢
    exact hd
  rcases hsplit with h2 | h3
  · have peq : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one
    subst p
    decide
  · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have peq : p = 3 :=
      (Nat.dvd_prime (by norm_num)).mp hp3 |>.resolve_left hp.ne_one
    subst p
    decide

set_option maxRecDepth 10000 in
theorem two_order_mod_2187 : orderOf (2 : ZMod 2187) = 1458 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro p hp hd
  have hsplit : p ∣ 2 ∨ p ∣ 3 ^ 6 := by
    apply hp.dvd_mul.mp
    norm_num at hd ⊢
    exact hd
  rcases hsplit with h2 | h3
  · have peq : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one
    subst p
    decide
  · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have peq : p = 3 :=
      (Nat.dvd_prime (by norm_num)).mp hp3 |>.resolve_left hp.ne_one
    subst p
    decide

/-- Concrete return restriction.  `hOut` is the invariant presentation left
by turnaround opcode `j`; `hNext` is the fixed one-cell presentation required
to use the resulting odd core as the next marker-bank source. -/
theorem opcode_mod_162_of_return {j y : ℕ}
    (hOut :
      2 ^ (turnaroundP j - 51) * y ≡
        registerOffset [MOD registerModulus])
    (hNext :
      2 ^ 26 * y ≡ registerOffset [MOD registerModulus]) :
    j % 162 = 123 := by
  have hle : 26 ≤ turnaroundP j - 51 := by
    dsimp [turnaroundP, gapD]
    omega
  have hperiod := exponent_difference_modEq_one
    registerOffset_coprime_registerModulus
    registerModulus_coprime_two hle hOut hNext
  have h243 :
      2 ^ ((turnaroundP j - 51) - 26) ≡ 1 [MOD 243] :=
    hperiod.of_dvd (by norm_num [registerModulus])
  have hz :
      (2 : ZMod 243) ^ ((turnaroundP j - 51) - 26) = 1 := by
    have hzcast :
        ((2 ^ ((turnaroundP j - 51) - 26) : ℕ) : ZMod 243) =
          ((1 : ℕ) : ZMod 243) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h243
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hzcast
  have hdvd : 162 ∣ (turnaroundP j - 51) - 26 := by
    rw [← two_order_mod_243]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz
  have hform :
      (turnaroundP j - 51) - 26 = 2 * 3 ^ 56 - 75 + 23 * j := by
    dsimp [turnaroundP, gapD]
    omega
  rw [hform] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [show 2 * 3 ^ 56 = 162 * 3 ^ 52 by ring] at hk
  omega

/-- A stronger concrete restriction using the `3^7` factor of the public
register modulus. -/
theorem opcode_mod_1458_of_return {j y : ℕ}
    (hOut :
      2 ^ (turnaroundP j - 51) * y ≡
        registerOffset [MOD registerModulus])
    (hNext :
      2 ^ 26 * y ≡ registerOffset [MOD registerModulus]) :
    j % 1458 = 447 := by
  have hle : 26 ≤ turnaroundP j - 51 := by
    dsimp [turnaroundP, gapD]
    omega
  have hperiod := exponent_difference_modEq_one
    registerOffset_coprime_registerModulus
    registerModulus_coprime_two hle hOut hNext
  have h2187 :
      2 ^ ((turnaroundP j - 51) - 26) ≡ 1 [MOD 2187] :=
    hperiod.of_dvd (by norm_num [registerModulus])
  have hz :
      (2 : ZMod 2187) ^ ((turnaroundP j - 51) - 26) = 1 := by
    have hzcast :
        ((2 ^ ((turnaroundP j - 51) - 26) : ℕ) : ZMod 2187) =
          ((1 : ℕ) : ZMod 2187) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h2187
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hzcast
  have hdvd : 1458 ∣ (turnaroundP j - 51) - 26 := by
    rw [← two_order_mod_2187]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz
  have hform :
      (turnaroundP j - 51) - 26 = 2 * 3 ^ 56 - 75 + 23 * j := by
    dsimp [turnaroundP, gapD]
    omega
  rw [hform] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [show 2 * 3 ^ 56 = 1458 * 3 ^ 50 by ring] at hk
  omega

/-- Every returning opcode is at least `447`. -/
theorem opcode_ge_447_of_return {j y : ℕ}
    (hOut :
      2 ^ (turnaroundP j - 51) * y ≡
        registerOffset [MOD registerModulus])
    (hNext :
      2 ^ 26 * y ≡ registerOffset [MOD registerModulus]) :
    447 ≤ j := by
  have hj := opcode_mod_1458_of_return hOut hNext
  have hmod_le : j % 1458 ≤ j := Nat.mod_le _ _
  omega

theorem no_opcode_below_447_return {j y : ℕ} (hj : j < 447) :
    ¬ (
      2 ^ (turnaroundP j - 51) * y ≡
        registerOffset [MOD registerModulus] ∧
      2 ^ 26 * y ≡ registerOffset [MOD registerModulus]) := by
  rintro ⟨hOut, hNext⟩
  exact (not_le_of_gt hj) (opcode_ge_447_of_return hOut hNext)

/-- Conditional legacy endpoint: none of `0,...,15` can satisfy both
invariant presentations.  The retracted MB audit did not establish those
presentations along a legal linked unit path. -/
theorem no_audited_opcode_return {j y : ℕ} (hj : j ≤ 15) :
    ¬ (
      2 ^ (turnaroundP j - 51) * y ≡
        registerOffset [MOD registerModulus] ∧
      2 ^ 26 * y ≡ registerOffset [MOD registerModulus]) := by
  exact no_opcode_below_447_return (by omega)

end MarkerBankInvariantReturn

end KontoroC
