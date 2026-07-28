/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SignedUnitShuttle

/-!
# The signed power-difference debris contains a canonical ruler clock

The opposite-sign unit composition does not create a second affine rail, but
its odd debris is not inert.  On the even public levels, subtracting one from

`3^(17*n+40) - 2^(8*n+15)`

exposes exactly the two-adic valuation of `3^(17*n+40)-1`.  Binary LTE turns
this into `2 + v2(17*n+40)`.  Thus the failed sign shuttle's residual contains
an unbounded, canonically decoded ruler clock; no externally supplied address
is used in this statement.

This is a decoder interface, not yet a return macro or a counterexample.  A
constructive continuation must route the odd cofactor back to a public source
state while preserving the ordinary boundary packet.
-/

namespace KontoroC
namespace SignedDebrisRuler

open SignedUnitShuttle

/-- Binary LTE for powers of three with a positive even exponent. -/
theorem padicValNat_three_pow_sub_one {Q : ℕ} (hQ : Q ≠ 0) (hQeven : Even Q) :
    padicValNat 2 (3 ^ Q - 1) = 2 + padicValNat 2 Q := by
  have h := padicValNat.pow_two_sub_one
    (x := 3) (n := Q) (by norm_num) (by norm_num) hQ hQeven
  have hfour : padicValNat 2 (3 + 1) = 2 := by
    norm_num only
    simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using
      (padicValNat_base_pow (p := 2) (by norm_num) 2)
  have htwo : padicValNat 2 (3 - 1) = 1 := by
    norm_num only
    exact padicValNat_base (by norm_num)
  rw [hfour, htwo] at h
  omega

/-- Subtracting a strictly higher power of two preserves the exact binary
valuation.  The order assumption also rules out truncated subtraction. -/
theorem padicValNat_sub_two_pow_of_val_lt
    {a P : ℕ} (ha : a ≠ 0) (hpow : 2 ^ P ≤ a)
    (hval : padicValNat 2 a < P) :
    padicValNat 2 (a - 2 ^ P) = padicValNat 2 a := by
  let v := padicValNat 2 a
  have hvdvd : 2 ^ v ∣ a := pow_padicValNat_dvd
  have hvP : 2 ^ v ∣ 2 ^ P := pow_dvd_pow 2 (Nat.le_of_lt hval)
  have hdiffdvd : 2 ^ v ∣ a - 2 ^ P := Nat.dvd_sub hvdvd hvP
  have hne : a - 2 ^ P ≠ 0 := by
    intro hz
    have hae : a = 2 ^ P := Nat.sub_eq_zero_iff_le.mp hz |>.antisymm hpow
    have hvpow : padicValNat 2 a = P := by
      rw [hae, padicValNat.prime_pow]
    omega
  have hlower : v ≤ padicValNat 2 (a - 2 ^ P) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hne).mp hdiffdvd
  have hnot : ¬2 ^ (v + 1) ∣ a := by
    intro hdvd
    have := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha).mp hdvd
    omega
  have hnotdiff : ¬2 ^ (v + 1) ∣ a - 2 ^ P := by
    intro hdvd
    have hnextP : v + 1 ≤ P := hval
    have hpvd : 2 ^ (v + 1) ∣ 2 ^ P := pow_dvd_pow 2 hnextP
    apply hnot
    have hadd : 2 ^ (v + 1) ∣ (a - 2 ^ P) + 2 ^ P := dvd_add hdvd hpvd
    rwa [Nat.sub_add_cancel hpow] at hadd
  have hupper : ¬v + 1 ≤ padicValNat 2 (a - 2 ^ P) := by
    intro hle
    exact hnotdiff ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hne).mpr hle)
  dsimp only [v] at hlower hupper ⊢
  omega

/-- The affine ternary exponent on even public levels grows more slowly than
the elementary exponential bound needed to place its binary valuation below
the unit-cell binary exponent. -/
theorem even_minusTernary_lt_pow (k : ℕ) :
    minusTernary (2 * k) < 2 ^ (k + 6) := by
  induction k with
  | zero => norm_num [minusTernary]
  | succ k ih =>
      rw [show k + 1 + 6 = (k + 6) + 1 by omega, pow_succ]
      simp only [minusTernary] at ih ⊢
      have hbase : 34 < 2 ^ (k + 6) := by
        calc
          34 < 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (k + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- The LTE valuation lies strictly below the positive-cell binary scale, so
the large subtracted power cannot disturb it. -/
theorem even_debris_val_lt_plusBinary (k : ℕ) :
    2 + padicValNat 2 (minusTernary (2 * k)) < plusBinary (2 * k) := by
  let Q := minusTernary (2 * k)
  let v := padicValNat 2 Q
  have hQpos : 0 < Q := by simp [Q, minusTernary]
  have hvdvd : 2 ^ v ∣ Q := pow_padicValNat_dvd
  have hvpow : 2 ^ v ≤ Q := Nat.le_of_dvd hQpos hvdvd
  have hvlt : v < k + 6 := by
    by_contra h
    have hexp : k + 6 ≤ v := by omega
    have hmono : 2 ^ (k + 6) ≤ 2 ^ v :=
      Nat.pow_le_pow_right (by norm_num) hexp
    have hQbound := even_minusTernary_lt_pow k
    dsimp only [Q] at hvpow hQbound
    omega
  dsimp only [v, Q] at hvlt ⊢
  simp only [plusBinary]
  omega

/-- Quotient witnessing `2^(8j)=1 (mod 17)`. -/
def geometric17 (j : ℕ) : ℕ := (2 ^ (8 * j) - 1) / 17

theorem geometric17_spec (j : ℕ) :
    17 * geometric17 j = 2 ^ (8 * j) - 1 := by
  have hbase : 17 ∣ 2 ^ 8 - 1 := by norm_num
  have hpower : 2 ^ 8 - 1 ∣ (2 ^ 8) ^ j - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ 8) 1 j
  have hdiv : 17 ∣ 2 ^ (8 * j) - 1 := by
    simpa only [pow_mul] using hbase.trans hpower
  exact Nat.mul_div_cancel' hdiv

/-- Explicit public levels on which the affine ternary exponent has an
arbitrarily long binary ruler tick. -/
def rulerLevel (j : ℕ) : ℕ := 3 * geometric17 (j + 1) - 1

theorem minusTernary_rulerLevel (j : ℕ) :
    minusTernary (2 * rulerLevel j) = 3 * 2 ^ (8 * (j + 1) + 1) := by
  have hgeom := geometric17_spec (j + 1)
  have hgeompos : 0 < geometric17 (j + 1) := by
    have hpow : 17 < 2 ^ (8 * (j + 1)) := by
      calc
        17 < 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (8 * (j + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  simp only [minusTernary, rulerLevel]
  rw [pow_add, pow_one]
  omega

theorem rulerLevel_padicValNat (j : ℕ) :
    padicValNat 2 (minusTernary (2 * rulerLevel j)) = 8 * (j + 1) + 1 := by
  rw [minusTernary_rulerLevel, mul_comm]
  rw [padicValNat_base_pow_mul (p := 2) (n := 3)
    (by norm_num) (by norm_num)]
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num), zero_add]

/-- The decoded collision gaps are genuinely unbounded; this is not merely a
level-dependent closed formula. -/
theorem debris_clock_unbounded (d : ℕ) :
    ∃ k : ℕ, d ≤ 2 + padicValNat 2 (minusTernary (2 * k)) := by
  refine ⟨rulerLevel d, ?_⟩
  rw [rulerLevel_padicValNat]
  omega

/-- Positive result of the second collision after the debris exposes its
exact dyadic ruler gap. -/
def rulerCofactor (k : ℕ) : ℕ :=
  (plusMinusDebris (2 * k) - 1).divMaxPow 2

/-- Main decoder identity: on every even public level, the odd signed debris
has a `-1` collision whose exact gap is `2+v2(17*(2k)+40)`. -/
theorem plusMinusDebris_sub_one_padicValNat (k : ℕ) :
    padicValNat 2 (plusMinusDebris (2 * k) - 1) =
      2 + padicValNat 2 (minusTernary (2 * k)) := by
  let Q := minusTernary (2 * k)
  let P := plusBinary (2 * k)
  have hQP : 2 ^ P < 3 ^ Q :=
    two_pow_plusBinary_lt_three_pow_minusTernary (2 * k)
  have hrewrite : plusMinusDebris (2 * k) - 1 =
      (3 ^ Q - 1) - 2 ^ P := by
    simp only [plusMinusDebris, Q, P]
    omega
  have hQ0 : Q ≠ 0 := by simp [Q, minusTernary]
  have hQeven : Even Q := by
    refine ⟨17 * k + 20, ?_⟩
    simp only [Q, minusTernary]
    ring
  have hLTE := padicValNat_three_pow_sub_one hQ0 hQeven
  have hQpos : 0 < Q := by simp [Q, minusTernary]
  have ha0 : 3 ^ Q - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hQpos.ne' (by norm_num))
  have hpow : 2 ^ P ≤ 3 ^ Q - 1 := by omega
  have hval : padicValNat 2 (3 ^ Q - 1) < P := by
    rw [hLTE]
    exact even_debris_val_lt_plusBinary k
  rw [hrewrite, padicValNat_sub_two_pow_of_val_lt ha0 hpow hval, hLTE]

/-- The ruler collision leaves an exact positive odd cofactor, ready to be
tested as the next public work register. -/
theorem rulerCofactor_spec (k : ℕ) :
    plusMinusDebris (2 * k) - 1 =
        2 ^ (2 + padicValNat 2 (minusTernary (2 * k))) * rulerCofactor k ∧
      0 < rulerCofactor k ∧ Odd (rulerCofactor k) := by
  let N := plusMinusDebris (2 * k) - 1
  have hN0 : N ≠ 0 := by
    have hpos := plusMinusDebris_pos (2 * k)
    have hneone : plusMinusDebris (2 * k) ≠ 1 := by
      intro heq
      have hval := plusMinusDebris_sub_one_padicValNat k
      rw [heq] at hval
      norm_num at hval
      omega
    dsimp only [N]
    omega
  have hfactor := Nat.pow_padicValNat_mul_divMaxPow 2 N
  have hval := plusMinusDebris_sub_one_padicValNat k
  have hnot : ¬2 ∣ N.divMaxPow 2 :=
    Nat.not_dvd_divMaxPow (by omega) hN0
  have hodd : Odd (N.divMaxPow 2) := by
    rw [Nat.odd_iff]
    have hlt := Nat.mod_lt (N.divMaxPow 2) (by omega : 0 < 2)
    have hne : N.divMaxPow 2 % 2 ≠ 0 := by
      intro hz
      exact hnot (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  constructor
  · change N =
      2 ^ (2 + padicValNat 2 (minusTernary (2 * k))) * N.divMaxPow 2
    rw [← hval]
    exact hfactor.symm
  · constructor
    · change 0 < N.divMaxPow 2
      exact hodd.pos
    · change Odd (N.divMaxPow 2)
      exact hodd

end SignedDebrisRuler
end KontoroC
