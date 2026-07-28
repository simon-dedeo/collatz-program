/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SignedDebrisRuler

/-!
# The raw debris ruler is not the next public unit collision

`SignedDebrisRuler` proves that the residual

`R_m = 3^(17m+40) - 2^(8m+15)`

contains an unbounded valuation in `R_m-1` on even levels.  A literal next
unit cell, however, does not test `R_m ± 1`.  If the reached public label is
`ell`, it tests `3^(17ell+40) R_m ± 1`.

This module performs that semantic substitution exactly.  Any order-based
materialization has even total binary exponent and therefore odd target
label `ell`.  When `m` is even, the combined ternary exponent is odd.  The
actual next minus and plus numerators then have exact valuations one and two,
respectively, far below every public unit exponent.  Thus the even-level raw
ruler cannot be promoted by simply appending another unit cell.

The odd-`m` scaled-minus branch is not closed here: its combined ternary
exponent is even and binary LTE can again produce a large valuation.  That is
the correctly typed successor target.
-/

namespace KontoroC
namespace SignedDebrisSemanticNoGo

open SignedUnitShuttle SignedDebrisRuler

/-- An odd power of three is `3 mod 8`. -/
theorem three_pow_odd_zmod_eight {E : ℕ} (hE : Odd E) :
    (3 : ZMod 8) ^ E = 3 := by
  obtain ⟨j, rfl⟩ := hE
  rw [pow_add, pow_mul]
  rw [show (3 : ZMod 8) ^ 2 = 1 by decide, one_pow, one_mul]
  simp

/-- If the leading odd power is `3 mod 8` and the removed term starts at bit
three or above, subtracting one leaves exact valuation one. -/
theorem padicValNat_odd_three_pow_sub_high_sub_one
    {E high : ℕ} (hE : Odd E) (hhigh : high < 3 ^ E)
    (hhigh8 : 8 ∣ high) :
    padicValNat 2 (3 ^ E - high - 1) = 1 := by
  have hle : high ≤ 3 ^ E := Nat.le_of_lt hhigh
  have hone : 1 ≤ 3 ^ E - high := Nat.sub_pos_of_lt hhigh
  have hcast2 : ((3 ^ E - high - 1 : ℕ) : ZMod 2) = 0 := by
    push_cast [hle, hone]
    have hhigh2 : ((high : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff high 2).2 (dvd_trans (by norm_num) hhigh8)
    rw [hhigh2, show (3 : ZMod 2) = 1 by decide, one_pow]
    simp
  have hdvd2 : 2 ∣ 3 ^ E - high - 1 :=
    (ZMod.natCast_eq_zero_iff (3 ^ E - high - 1) 2).1 hcast2
  have hcast4 : ((3 ^ E - high - 1 : ℕ) : ZMod 4) = 2 := by
    push_cast [hle, hone]
    have hpow4 : (3 : ZMod 4) ^ E = 3 := by
      obtain ⟨j, rfl⟩ := hE
      rw [pow_add, pow_mul]
      rw [show (3 : ZMod 4) ^ 2 = 1 by decide, one_pow, one_mul]
      simp
    have hhigh4 : ((high : ℕ) : ZMod 4) = 0 :=
      (ZMod.natCast_eq_zero_iff high 4).2 (dvd_trans (by norm_num) hhigh8)
    rw [hpow4, hhigh4]
    decide
  have hnot4 : ¬4 ∣ 3 ^ E - high - 1 := by
    intro hdvd
    have hz := (ZMod.natCast_eq_zero_iff (3 ^ E - high - 1) 4).2 hdvd
    rw [hcast4] at hz
    exact (by decide : (2 : ZMod 4) ≠ 0) hz
  have hN0 : 3 ^ E - high - 1 ≠ 0 := by
    intro hz
    apply hnot4
    rw [hz]
    exact dvd_zero 4
  have hdvdPow : 2 ^ 1 ∣ 3 ^ E - high - 1 := by
    rw [pow_one]
    exact hdvd2
  have hlower : 1 ≤ padicValNat 2 (3 ^ E - high - 1) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hN0).1 hdvdPow
  have hupper : ¬2 ≤ padicValNat 2 (3 ^ E - high - 1) := by
    intro h
    apply hnot4
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hN0).2 h
  omega

/-- Under the same hypotheses, adding one instead gives exact valuation two. -/
theorem padicValNat_odd_three_pow_sub_high_add_one
    {E high : ℕ} (hE : Odd E) (hhigh : high < 3 ^ E)
    (hhigh8 : 8 ∣ high) :
    padicValNat 2 (3 ^ E - high + 1) = 2 := by
  have hle : high ≤ 3 ^ E := Nat.le_of_lt hhigh
  have hcast4 : ((3 ^ E - high + 1 : ℕ) : ZMod 4) = 0 := by
    push_cast [hle]
    have hpow4 : (3 : ZMod 4) ^ E = 3 := by
      obtain ⟨j, rfl⟩ := hE
      rw [pow_add, pow_mul]
      rw [show (3 : ZMod 4) ^ 2 = 1 by decide, one_pow, one_mul]
      simp
    have hhigh4 : ((high : ℕ) : ZMod 4) = 0 :=
      (ZMod.natCast_eq_zero_iff high 4).2 (dvd_trans (by norm_num) hhigh8)
    rw [hpow4, hhigh4]
    decide
  have hdvd4 : 4 ∣ 3 ^ E - high + 1 :=
    (ZMod.natCast_eq_zero_iff (3 ^ E - high + 1) 4).1 hcast4
  have hcast8 : ((3 ^ E - high + 1 : ℕ) : ZMod 8) = 4 := by
    push_cast [hle]
    have hhighCast : ((high : ℕ) : ZMod 8) = 0 :=
      (ZMod.natCast_eq_zero_iff high 8).2 hhigh8
    rw [three_pow_odd_zmod_eight hE, hhighCast]
    norm_num
  have hnot8 : ¬8 ∣ 3 ^ E - high + 1 := by
    intro hdvd
    have hz := (ZMod.natCast_eq_zero_iff (3 ^ E - high + 1) 8).2 hdvd
    rw [hcast8] at hz
    exact (by decide : (4 : ZMod 8) ≠ 0) hz
  have hN0 : 3 ^ E - high + 1 ≠ 0 := by positivity
  have hlower : 2 ≤ padicValNat 2 (3 ^ E - high + 1) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hN0).1 (by simpa using hdvd4)
  have hupper : ¬3 ≤ padicValNat 2 (3 ^ E - high + 1) := by
    intro h
    apply hnot8
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hN0).2 h
  omega

/-- Subtracting any multiple of a strictly higher power of two preserves the
exact valuation.  This is the scaled counterpart of the raw-power lemma in
`SignedDebrisRuler`. -/
theorem padicValNat_sub_of_high_power
    {x y P : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hle : y ≤ x)
    (hyP : 2 ^ P ∣ y) (hval : padicValNat 2 x < P) :
    padicValNat 2 (x - y) = padicValNat 2 x := by
  let v := padicValNat 2 x
  have hvdvdx : 2 ^ v ∣ x := pow_padicValNat_dvd
  have hvP : 2 ^ v ∣ 2 ^ P := pow_dvd_pow 2 (Nat.le_of_lt hval)
  have hvdvdy : 2 ^ v ∣ y := hvP.trans hyP
  have hvdiff : 2 ^ v ∣ x - y := Nat.dvd_sub hvdvdx hvdvdy
  have hne : x - y ≠ 0 := by
    intro hz
    have hxy : x = y := (Nat.sub_eq_zero_iff_le.mp hz).antisymm hle
    have hPley : P ≤ padicValNat 2 y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy).1 hyP
    rw [← hxy] at hPley
    omega
  have hlower : v ≤ padicValNat 2 (x - y) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hne).1 hvdiff
  have hnotx : ¬2 ^ (v + 1) ∣ x := by
    intro hdvd
    have := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx).1 hdvd
    omega
  have hvoneP : v + 1 ≤ P := hval
  have hvoney : 2 ^ (v + 1) ∣ y :=
    (pow_dvd_pow 2 hvoneP).trans hyP
  have hnotdiff : ¬2 ^ (v + 1) ∣ x - y := by
    intro hdvd
    apply hnotx
    have hadd : 2 ^ (v + 1) ∣ (x - y) + y := dvd_add hdvd hvoney
    rwa [Nat.sub_add_cancel hle] at hadd
  have hupper : ¬v + 1 ≤ padicValNat 2 (x - y) := by
    intro h
    exact hnotdiff ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hne).2 h)
  dsimp only [v] at hlower hupper ⊢
  omega

/-- Total binary exponent of a positive-level cell followed by a
negative-level cell. -/
def binaryTotal (m ell : ℕ) : ℕ := plusBinary m + minusBinary ell

/-- Its target is odd whenever the total binary exponent is even. -/
theorem target_odd_of_binaryTotal_even {m ell : ℕ}
    (hB : Even (binaryTotal m ell)) : Odd ell := by
  rw [← Nat.not_even_iff_odd]
  intro hell
  obtain ⟨u, hu⟩ := hB
  obtain ⟨v, hv⟩ := hell
  simp only [binaryTotal, plusBinary, minusBinary] at hu
  omega

/-- Divisibility by three of `2^B-1` already forces `B` even. -/
theorem exponent_even_of_three_dvd_two_pow_sub_one {B : ℕ}
    (hdiv : 3 ∣ 2 ^ B - 1) : Even B := by
  rw [← Nat.not_odd_iff_even]
  intro hB
  have hcast : ((2 ^ B - 1 : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 ^ B - 1) 3).2 hdiv
  have hpow : (2 : ZMod 3) ^ B = 2 := by
    obtain ⟨j, rfl⟩ := hB
    rw [pow_add, pow_mul]
    rw [show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow, one_mul]
    simp
  have hone : 1 ≤ 2 ^ B := by
    have : 0 < 2 ^ B := by positivity
    omega
  push_cast [hone] at hcast
  rw [hpow] at hcast
  exact (by decide : (2 : ZMod 3) - 1 ≠ 0) hcast

/-- Any order-based materialization divisibility at positive ternary
precision therefore has odd target label. -/
theorem target_odd_of_materialization
    {m ell T : ℕ} (hT : 0 < T)
    (hdiv : 3 ^ T ∣ 2 ^ binaryTotal m ell - 1) : Odd ell := by
  have hthree : 3 ∣ 3 ^ T := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
    rw [pow_succ]
    exact dvd_mul_left 3 (3 ^ t)
  exact target_odd_of_binaryTotal_even
    (exponent_even_of_three_dvd_two_pow_sub_one (hthree.trans hdiv))

/-- Literal numerator tested by a following sign-negative level-two cell. -/
def scaledMinusNumerator (ell m : ℕ) : ℕ :=
  3 ^ minusTernary ell * plusMinusDebris m - 1

/-- Literal numerator tested by a following sign-positive level-one cell. -/
def scaledPlusNumerator (ell m : ℕ) : ℕ :=
  3 ^ minusTernary ell * plusMinusDebris m + 1

/-- Semantic no-go, minus rail: an even-level residual at an odd public
target has actual next valuation one, not the raw ruler valuation. -/
theorem scaledMinusNumerator_even_level_padicValNat
    (ell k : ℕ) (hell : Odd ell) :
    padicValNat 2 (scaledMinusNumerator ell (2 * k)) = 1 := by
  let a := minusTernary ell
  let Q := minusTernary (2 * k)
  let P := plusBinary (2 * k)
  let E := a + Q
  let high := 2 ^ P * 3 ^ a
  have hE : Odd E := by
    dsimp only [E, a, Q]
    obtain ⟨j, rfl⟩ := hell
    refine ⟨17 * j + 17 * k + 48, ?_⟩
    simp only [minusTernary]
    ring
  have hscale := two_pow_plusBinary_lt_three_pow_minusTernary (2 * k)
  have hhigh : high < 3 ^ E := by
    dsimp only [high, P, a, E, Q]
    rw [pow_add]
    have hm := (Nat.mul_lt_mul_left
      (by positivity : 0 < 3 ^ minusTernary ell)).2 hscale
    simpa [mul_comm] using hm
  have hhigh8 : 8 ∣ high := by
    dsimp only [high, P]
    have hP : 3 ≤ plusBinary (2 * k) := by simp [plusBinary]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hP) _
  have hrewrite : scaledMinusNumerator ell (2 * k) = 3 ^ E - high - 1 := by
    dsimp only [scaledMinusNumerator, E, high, a, Q, P]
    rw [plusMinusDebris, Nat.mul_sub_left_distrib, pow_add]
    ring
  rw [hrewrite]
  exact padicValNat_odd_three_pow_sub_high_sub_one hE hhigh hhigh8

/-- Semantic no-go, plus rail: the alternative sign has exact valuation two. -/
theorem scaledPlusNumerator_even_level_padicValNat
    (ell k : ℕ) (hell : Odd ell) :
    padicValNat 2 (scaledPlusNumerator ell (2 * k)) = 2 := by
  let a := minusTernary ell
  let Q := minusTernary (2 * k)
  let P := plusBinary (2 * k)
  let E := a + Q
  let high := 2 ^ P * 3 ^ a
  have hE : Odd E := by
    dsimp only [E, a, Q]
    obtain ⟨j, rfl⟩ := hell
    refine ⟨17 * j + 17 * k + 48, ?_⟩
    simp only [minusTernary]
    ring
  have hscale := two_pow_plusBinary_lt_three_pow_minusTernary (2 * k)
  have hhigh : high < 3 ^ E := by
    dsimp only [high, P, a, E, Q]
    rw [pow_add]
    have hm := (Nat.mul_lt_mul_left
      (by positivity : 0 < 3 ^ minusTernary ell)).2 hscale
    simpa [mul_comm] using hm
  have hhigh8 : 8 ∣ high := by
    dsimp only [high, P]
    have hP : 3 ≤ plusBinary (2 * k) := by simp [plusBinary]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hP) _
  have hrewrite : scaledPlusNumerator ell (2 * k) = 3 ^ E - high + 1 := by
    dsimp only [scaledPlusNumerator, E, high, a, Q, P]
    rw [plusMinusDebris, Nat.mul_sub_left_distrib, pow_add]
    ring
  rw [hrewrite]
  exact padicValNat_odd_three_pow_sub_high_add_one hE hhigh hhigh8

/-- Correctly typed live branch.  When both the reached label and residual
level are odd, the actual sign-negative collision reads the binary ruler of
the *sum* of their ternary exponents, provided that valuation lies below the
residual's high binary scale. -/
theorem scaledMinusNumerator_odd_level_padicValNat
    (ell k : ℕ) (hell : Odd ell)
    (hroom :
      2 + padicValNat 2
          (minusTernary ell + minusTernary (2 * k + 1)) <
        plusBinary (2 * k + 1)) :
    padicValNat 2 (scaledMinusNumerator ell (2 * k + 1)) =
      2 + padicValNat 2
        (minusTernary ell + minusTernary (2 * k + 1)) := by
  let a := minusTernary ell
  let Q := minusTernary (2 * k + 1)
  let P := plusBinary (2 * k + 1)
  let E := a + Q
  let high := 2 ^ P * 3 ^ a
  have hEeven : Even E := by
    dsimp only [E, a, Q]
    obtain ⟨j, rfl⟩ := hell
    refine ⟨17 * j + 17 * k + 57, ?_⟩
    simp only [minusTernary]
    ring
  have hE0 : E ≠ 0 := by simp [E, a, Q, minusTernary]
  have hscale := two_pow_plusBinary_lt_three_pow_minusTernary (2 * k + 1)
  have hhigh : high < 3 ^ E := by
    dsimp only [high, P, a, E, Q]
    rw [pow_add]
    have hm := (Nat.mul_lt_mul_left
      (by positivity : 0 < 3 ^ minusTernary ell)).2 hscale
    simpa [mul_comm] using hm
  have hx0 : 3 ^ E - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hE0 (by norm_num))
  have hy0 : high ≠ 0 := by positivity
  have hle : high ≤ 3 ^ E - 1 := by omega
  have hyP : 2 ^ P ∣ high := by
    exact dvd_mul_right (2 ^ P) (3 ^ a)
  have hLTE := padicValNat_three_pow_sub_one hE0 hEeven
  have hval : padicValNat 2 (3 ^ E - 1) < P := by
    rw [hLTE]
    simpa [E, P, a, Q] using hroom
  have hpres := padicValNat_sub_of_high_power hx0 hy0 hle hyP hval
  have hrewrite : scaledMinusNumerator ell (2 * k + 1) =
      (3 ^ E - 1) - high := by
    dsimp only [scaledMinusNumerator, E, high, a, Q, P]
    rw [plusMinusDebris, Nat.mul_sub_left_distrib, pow_add]
    simp only [Nat.sub_sub, mul_comm, add_comm]
  rw [hrewrite, hpres, hLTE]

/-! ## An explicit correctly typed odd-level router -/

/-- Odd multiplier used to solve
`17*(ell+m)+80 = 2^d*u` without a modular search.  The middle exponent makes
`2^(d+7d+8)=2^(8(d+1))=1 (mod 17)`, and the last term gives size room. -/
def routerOddMultiplier (d m : ℕ) : ℕ :=
  17 + 80 * 2 ^ (7 * d + 8) + 34 * m

/-- Quotient before subtracting the current residual level. -/
def routerBase (d m : ℕ) : ℕ :=
  2 ^ d + 80 * geometric17 (d + 1) + 2 * m * 2 ^ d

/-- Public reached label whose scaled ternary exponent sum has exact binary
valuation `d`. -/
def routerLabel (d m : ℕ) : ℕ := routerBase d m - m

theorem routerOddMultiplier_odd (d m : ℕ) : Odd (routerOddMultiplier d m) := by
  refine ⟨8 * 5 * 2 ^ (7 * d + 8) + 17 * m + 8, ?_⟩
  simp only [routerOddMultiplier]
  ring

theorem routerBase_ge_level (d m : ℕ) : m ≤ routerBase d m := by
  have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
  simp only [routerBase]
  nlinarith

/-- Exact integral identity behind the router label. -/
theorem routerBase_identity (d m : ℕ) :
    17 * routerBase d m + 80 = 2 ^ d * routerOddMultiplier d m := by
  have hgeom := geometric17_spec (d + 1)
  have hgeomAdd : 17 * geometric17 (d + 1) + 1 = 2 ^ (8 * (d + 1)) := by
    have hpow : 0 < 2 ^ (8 * (d + 1)) := by positivity
    omega
  simp only [routerBase, routerOddMultiplier]
  calc
    17 * (2 ^ d + 80 * geometric17 (d + 1) + 2 * m * 2 ^ d) + 80 =
        17 * 2 ^ d + 80 * 2 ^ (8 * (d + 1)) + 34 * m * 2 ^ d := by
      nlinarith [hgeomAdd]
    _ = 2 ^ d * (17 + 80 * 2 ^ (7 * d + 8) + 34 * m) := by
      rw [show 8 * (d + 1) = d + (7 * d + 8) by omega, pow_add]
      ring

theorem routerLabel_add_level (d m : ℕ) :
    routerLabel d m + m = routerBase d m := by
  exact Nat.sub_add_cancel (routerBase_ge_level d m)

/-- The public exponent sum is literally a power of two times the odd
multiplier. -/
theorem router_combined_ternary (d m : ℕ) :
    minusTernary (routerLabel d m) + minusTernary m =
      2 ^ d * routerOddMultiplier d m := by
  rw [show minusTernary (routerLabel d m) + minusTernary m =
      17 * (routerLabel d m + m) + 80 by
    simp only [minusTernary]
    ring,
    routerLabel_add_level, routerBase_identity]

theorem router_combined_padicValNat (d m : ℕ) :
    padicValNat 2
        (minusTernary (routerLabel d m) + minusTernary m) = d := by
  rw [router_combined_ternary]
  rw [padicValNat_base_pow_mul (by norm_num)
    (routerOddMultiplier_odd d m).pos.ne']
  have hnot : ¬2 ∣ routerOddMultiplier d m := by
    simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using
      routerOddMultiplier_odd d m
  rw [padicValNat.eq_zero_of_not_dvd hnot, zero_add]

/-- If the current residual level is odd and `d>0`, the constructed reached
label is also odd, as required by the scaled-minus branch. -/
theorem routerLabel_odd {d m : ℕ} (hd : 0 < d) (hm : Odd m) :
    Odd (routerLabel d m) := by
  rw [← Nat.not_even_iff_odd]
  intro hell
  obtain ⟨a, ha⟩ := hell
  obtain ⟨b, hb⟩ := hm
  have hdvdPow : 2 ∣ 2 ^ d := by
    exact pow_dvd_pow 2 hd
  have hdvdRight : 2 ∣ 2 ^ d * routerOddMultiplier d m :=
    dvd_mul_of_dvd_left hdvdPow _
  obtain ⟨c, hc⟩ := hdvdRight
  rw [← router_combined_ternary] at hc
  simp only [minusTernary] at hc
  omega

/-- Requested ruler exponent for a legal sign-negative target. -/
def routerPrecision (target : ℕ) : ℕ := minusBinary target - 2

theorem routerPrecision_add_two (target : ℕ) :
    2 + routerPrecision target = minusBinary target := by
  simp [routerPrecision, minusBinary]
  omega

theorem routerPrecision_pos (target : ℕ) : 0 < routerPrecision target := by
  simp [routerPrecision, minusBinary]

/-- The explicit witness used by the router has the requested valuation.
This named form is the interface needed by later boundary-rail constructions. -/
theorem typedRouter_padicValNat
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    padicValNat 2
        (scaledMinusNumerator
          (routerLabel (routerPrecision target) m) m) =
      minusBinary target := by
  let d := routerPrecision target
  let ell := routerLabel d m
  have hd : 0 < d := routerPrecision_pos target
  have hell : Odd ell := routerLabel_odd hd hm
  obtain ⟨k, hk⟩ := hm
  have hmform : m = 2 * k + 1 := by omega
  subst m
  have hval := scaledMinusNumerator_odd_level_padicValNat ell k hell
    (by
      rw [router_combined_padicValNat]
      simpa only [d, routerPrecision_add_two] using hroom)
  rw [hval, router_combined_padicValNat]
  exact routerPrecision_add_two target

/-- All-parameter valuation router.  Every odd residual level with enough
binary room has an explicit odd reached label whose actual scaled-minus
collision lands in any requested public sign-negative target exponent. -/
theorem exists_typed_scaledMinus_router
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    ∃ ell : ℕ, Odd ell ∧
      padicValNat 2 (scaledMinusNumerator ell m) = minusBinary target := by
  let d := routerPrecision target
  let ell := routerLabel d m
  have hd : 0 < d := routerPrecision_pos target
  have hell : Odd ell := routerLabel_odd hd hm
  exact ⟨ell, hell, typedRouter_padicValNat m target hm hroom⟩

/-- The router leaves an exact positive odd public cofactor, not only a
matching divisibility exponent.  Reproducing this cofactor is the remaining
closure equation. -/
theorem exists_typed_scaledMinus_router_cofactor
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    ∃ ell w : ℕ, Odd ell ∧ 0 < w ∧ Odd w ∧
      scaledMinusNumerator ell m = 2 ^ minusBinary target * w := by
  obtain ⟨ell, hell, hval⟩ :=
    exists_typed_scaledMinus_router m target hm hroom
  let N := scaledMinusNumerator ell m
  let w := N.divMaxPow 2
  have hR := plusMinusDebris_pos m
  have hthree : 1 < 3 ^ minusTernary ell :=
    Nat.one_lt_pow (by simp [minusTernary]) (by norm_num)
  have hprod : 1 < 3 ^ minusTernary ell * plusMinusDebris m := by
    calc
      1 < 3 ^ minusTernary ell := hthree
      _ = 3 ^ minusTernary ell * 1 := by ring
      _ ≤ 3 ^ minusTernary ell * plusMinusDebris m :=
        Nat.mul_le_mul_left _ hR
  have hNpos : 0 < N := by
    dsimp only [N, scaledMinusNumerator]
    omega
  have hfactor := Nat.pow_padicValNat_mul_divMaxPow 2 N
  have hnot : ¬2 ∣ w := by
    dsimp only [w]
    exact Nat.not_dvd_divMaxPow (by omega) hNpos.ne'
  have hwodd : Odd w := by
    simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using hnot
  refine ⟨ell, w, hell, hwodd.pos, hwodd, ?_⟩
  change N = 2 ^ minusBinary target * N.divMaxPow 2
  rw [← hval]
  exact hfactor.symm

/-- No sign-negative public target exponent can match the actual valuation. -/
theorem scaledMinus_not_public_binary
    (ell k target : ℕ) (hell : Odd ell) :
    padicValNat 2 (scaledMinusNumerator ell (2 * k)) ≠ minusBinary target := by
  rw [scaledMinusNumerator_even_level_padicValNat ell k hell]
  simp [minusBinary]

/-- Nor can a sign-positive target exponent match the alternative valuation. -/
theorem scaledPlus_not_public_binary
    (ell k target : ℕ) (hell : Odd ell) :
    padicValNat 2 (scaledPlusNumerator ell (2 * k)) ≠ plusBinary target := by
  rw [scaledPlusNumerator_even_level_padicValNat ell k hell]
  simp [plusBinary]

end SignedDebrisSemanticNoGo
end KontoroC
