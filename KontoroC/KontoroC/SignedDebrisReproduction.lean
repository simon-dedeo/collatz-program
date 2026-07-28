/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SignedDebrisSemanticNoGo
import KontoroC.GliderKLTailSynchronization

/-!
# Arithmetic forced by exact signed-debris reproduction

The typed odd-level router in `SignedDebrisSemanticNoGo` emits an exact odd
cofactor.  The first natural closure ansatz is that this cofactor is another
member of the same positive debris family.  This file records the rigid
three-adic clock forced by that ansatz.

This is symbolic obstruction work, not a bounded search.  In particular, an
exact reproduction makes the total binary exponent equal to one modulo both
the reached source scale and the reproduced debris scale.  The order of four
modulo a power of three then makes that total exponent exponentially large in
the smaller of the two ternary scales.
-/

namespace KontoroC
namespace SignedDebrisReproduction

open SignedUnitShuttle SignedDebrisSemanticNoGo

/-- The emitted cofactor is exactly the next positive signed debris. -/
def Reproduces (ell m target next : ℕ) : Prop :=
  scaledMinusNumerator ell m =
    2 ^ minusBinary target * plusMinusDebris next

/-- Precision simultaneously visible in the reached source scale and in the
putative reproduced debris. -/
def commonTernaryPrecision (ell next : ℕ) : ℕ :=
  min (minusTernary ell) (minusTernary next)

/-- Exact reproduction forces a large power-of-three divisor of the total
binary return exponent minus one. -/
theorem commonTernaryPrecision_dvd_binaryReturn_sub_one
    {ell m target next : ℕ} (hrep : Reproduces ell m target next) :
    3 ^ commonTernaryPrecision ell next ∣
      2 ^ (minusBinary target + plusBinary next) - 1 := by
  let K := commonTernaryPrecision ell next
  let M := 3 ^ K
  have hKell : K ≤ minusTernary ell := by
    exact Nat.min_le_left _ _
  have hKnext : K ≤ minusTernary next := by
    exact Nat.min_le_right _ _
  have hMell : M ∣ 3 ^ minusTernary ell := by
    exact pow_dvd_pow 3 hKell
  have hMnext : M ∣ 3 ^ minusTernary next := by
    exact pow_dvd_pow 3 hKnext
  have hellCast : ((3 ^ minusTernary ell : ℕ) : ZMod M) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hMell
  have hnextCast : ((3 ^ minusTernary next : ℕ) : ZMod M) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hMnext
  have hellPow : (3 : ZMod M) ^ minusTernary ell = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hellCast
  have hnextPow : (3 : ZMod M) ^ minusTernary next = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnextCast
  have hdebrisLe : 2 ^ plusBinary next ≤ 3 ^ minusTernary next :=
    Nat.le_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary next)
  have hsourcePos : 1 ≤
      3 ^ minusTernary ell * plusMinusDebris m := by
    exact Nat.succ_le_iff.mpr
      (Nat.mul_pos (by positivity) (plusMinusDebris_pos m))
  have hsourcePos' : 1 ≤
      3 ^ minusTernary ell *
        (3 ^ minusTernary m - 2 ^ plusBinary m) := by
    simpa only [plusMinusDebris] using hsourcePos
  have hcast := congrArg (fun n : ℕ => (n : ZMod M)) hrep
  simp only [scaledMinusNumerator, plusMinusDebris] at hcast
  rw [Nat.cast_sub hsourcePos'] at hcast
  push_cast [hdebrisLe] at hcast
  rw [hellPow, hnextPow] at hcast
  have hpowe :
      (2 : ZMod M) ^ (minusBinary target + plusBinary next) = 1 := by
    rw [pow_add]
    simp only [zero_mul, zero_sub, mul_neg] at hcast
    exact (neg_inj.mp hcast).symm
  have hsubCast :
      ((2 ^ (minusBinary target + plusBinary next) - 1 : ℕ) : ZMod M) = 0 := by
    have hone : 1 ≤ 2 ^ (minusBinary target + plusBinary next) :=
      Nat.one_le_pow _ 2 (by omega)
    push_cast [hone]
    rw [hpowe]
    simp
  exact (ZMod.natCast_eq_zero_iff _ _).1 hsubCast

/-- Reproduction already forces the public target label odd: the total
binary return exponent must be even modulo three. -/
theorem target_odd_of_reproduces
    {ell m target next : ℕ} (hrep : Reproduces ell m target next) :
    Odd target := by
  have hdiv := commonTernaryPrecision_dvd_binaryReturn_sub_one hrep
  have hKpos : 0 < commonTernaryPrecision ell next := by
    simp [commonTernaryPrecision, minusTernary]
  have hthree : 3 ∣ 3 ^ commonTernaryPrecision ell next :=
    dvd_pow_self 3 hKpos.ne'
  have hEven := exponent_even_of_three_dvd_two_pow_sub_one
    (hthree.trans hdiv)
  rw [← Nat.not_even_iff_odd]
  intro htEven
  obtain ⟨a, ha⟩ := hEven
  obtain ⟨b, hb⟩ := htEven
  simp only [minusBinary, plusBinary] at ha
  omega

/-- The multiplicative order of four turns the reproduction congruence into
an exponential divisibility condition on half the binary return exponent. -/
theorem reproduction_clock_divides_half_binaryReturn
    {ell m target next : ℕ} (hrep : Reproduces ell m target next) :
    3 ^ (commonTernaryPrecision ell next - 1) ∣
      (minusBinary target + plusBinary next) / 2 := by
  let K := commonTernaryPrecision ell next
  let S := minusBinary target + plusBinary next
  have hKpos : 0 < K := by simp [K, commonTernaryPrecision, minusTernary]
  have hdiv := commonTernaryPrecision_dvd_binaryReturn_sub_one hrep
  have hSeven : Even S :=
    exponent_even_of_three_dvd_two_pow_sub_one
      ((dvd_pow_self 3 hKpos.ne').trans hdiv)
  have htwo : 2 * (S / 2) = S := Nat.two_mul_div_two_of_even hSeven
  have hpoweTwo :
      (2 : ZMod (3 ^ K)) ^ S = 1 := by
    have hcast : ((2 ^ S - 1 : ℕ) : ZMod (3 ^ K)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdiv
    have hone : 1 ≤ 2 ^ S := Nat.one_le_pow S 2 (by omega)
    push_cast [hone] at hcast
    linear_combination hcast
  have hpoweFour :
      (4 : ZMod (3 ^ K)) ^ (S / 2) = 1 := by
    rw [show (4 : ZMod (3 ^ K)) = 2 ^ 2 by norm_num, ← pow_mul, htwo]
    exact hpoweTwo
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hKpos.ne'
  rw [hd] at hpoweFour
  change 3 ^ (K - 1) ∣ S / 2
  rw [hd, Nat.succ_sub_one]
  rw [← GliderKLTailSynchronization.orderOf_four_threePow d]
  exact orderOf_dvd_of_pow_eq_one hpoweFour

/-- Consequently the binary return length is at least twice the full common
three-adic clock. -/
theorem two_mul_common_clock_le_binaryReturn
    {ell m target next : ℕ} (hrep : Reproduces ell m target next) :
    2 * 3 ^ (commonTernaryPrecision ell next - 1) ≤
      minusBinary target + plusBinary next := by
  have hdiv := reproduction_clock_divides_half_binaryReturn hrep
  have hpos : 0 < (minusBinary target + plusBinary next) / 2 := by
    have : 2 ≤ minusBinary target + plusBinary next := by
      simp only [minusBinary, plusBinary]
      omega
    omega
  have hle : 3 ^ (commonTernaryPrecision ell next - 1) ≤
      (minusBinary target + plusBinary next) / 2 :=
    Nat.le_of_dvd hpos hdiv
  have hEven : Even (minusBinary target + plusBinary next) := by
    obtain ⟨j, hj⟩ := target_odd_of_reproduces hrep
    refine ⟨?_, ?_⟩
    · exact 23 * j + 4 * next + 46
    · simp only [minusBinary, plusBinary]
      omega
  have htwo : 2 * ((minusBinary target + plusBinary next) / 2) =
      minusBinary target + plusBinary next :=
    Nat.two_mul_div_two_of_even hEven
  calc
    2 * 3 ^ (commonTernaryPrecision ell next - 1) ≤
        2 * ((minusBinary target + plusBinary next) / 2) :=
      Nat.mul_le_mul_left 2 hle
    _ = minusBinary target + plusBinary next := htwo

/-! ## Size localization and the explicit-router no-go -/

/-- The binary term is already below one third of its matching ternary
power.  The public exponents have far more separation than mere positivity
of the debris requires. -/
theorem two_pow_plusBinary_lt_three_pow_minusTernary_pred (m : ℕ) :
    2 ^ plusBinary m < 3 ^ (minusTernary m - 1) := by
  have hPpos : 0 < plusBinary m := by simp [plusBinary]
  have hExp : plusBinary m ≤ minusTernary m - 1 := by
    simp only [plusBinary, minusTernary]
    omega
  calc
    2 ^ plusBinary m < 3 ^ plusBinary m :=
      Nat.pow_lt_pow_left (by norm_num) hPpos.ne'
    _ ≤ 3 ^ (minusTernary m - 1) :=
      Nat.pow_le_pow_right (by norm_num) hExp

/-- Hence every positive debris exceeds two thirds of its leading power of
three. -/
theorem two_mul_three_pow_pred_lt_plusMinusDebris (m : ℕ) :
    2 * 3 ^ (minusTernary m - 1) < plusMinusDebris m := by
  have hQpos : 0 < minusTernary m := by simp [minusTernary]
  have hsmall := two_pow_plusBinary_lt_three_pow_minusTernary_pred m
  have hpow : 3 ^ minusTernary m = 3 * 3 ^ (minusTernary m - 1) := by
    calc
      3 ^ minusTernary m = 3 ^ ((minusTernary m - 1) + 1) := by
        congr 1
      _ = 3 ^ (minusTernary m - 1) * 3 := by rw [pow_succ]
      _ = 3 * 3 ^ (minusTernary m - 1) := by rw [mul_comm]
  simp only [plusMinusDebris]
  omega

/-- The scaled-minus numerator lies above the preceding combined ternary
power.  This lower bound is what localizes any reproduced level. -/
theorem three_pow_combined_pred_lt_scaledMinusNumerator (ell m : ℕ) :
    3 ^ (minusTernary ell + minusTernary m - 1) <
      scaledMinusNumerator ell m := by
  have hR := two_mul_three_pow_pred_lt_plusMinusDebris m
  have hmul :
      3 ^ minusTernary ell * (2 * 3 ^ (minusTernary m - 1)) <
        3 ^ minusTernary ell * plusMinusDebris m := by
    exact (Nat.mul_lt_mul_left (by positivity)).2 hR
  have hpow :
      3 ^ minusTernary ell * 3 ^ (minusTernary m - 1) =
        3 ^ (minusTernary ell + minusTernary m - 1) := by
    rw [← pow_add]
    congr 1
  have hfactor :
      3 ^ minusTernary ell * (2 * 3 ^ (minusTernary m - 1)) =
        2 * 3 ^ (minusTernary ell + minusTernary m - 1) := by
    calc
      3 ^ minusTernary ell * (2 * 3 ^ (minusTernary m - 1)) =
          2 * (3 ^ minusTernary ell *
            3 ^ (minusTernary m - 1)) := by ring
      _ = 2 * 3 ^ (minusTernary ell + minusTernary m - 1) := by
        rw [hpow]
  rw [hfactor] at hmul
  have hxpos : 0 < 3 ^ (minusTernary ell + minusTernary m - 1) := by
    positivity
  have hadd :
      3 ^ (minusTernary ell + minusTernary m - 1) + 1 ≤
        2 * 3 ^ (minusTernary ell + minusTernary m - 1) := by
    omega
  dsimp only [scaledMinusNumerator]
  rw [Nat.lt_sub_iff_add_lt]
  exact hadd.trans_lt hmul

/-- The same numerator remains strictly below its full combined leading
power. -/
theorem scaledMinusNumerator_lt_three_pow_combined (ell m : ℕ) :
    scaledMinusNumerator ell m <
      3 ^ (minusTernary ell + minusTernary m) := by
  have hRlt : plusMinusDebris m < 3 ^ minusTernary m := by
    simp only [plusMinusDebris]
    have hpos : 0 < 2 ^ plusBinary m := by positivity
    have hle := Nat.le_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary m)
    omega
  have hmul := (Nat.mul_lt_mul_left
    (by positivity : 0 < 3 ^ minusTernary ell)).2 hRlt
  have hone : 1 ≤ 3 ^ minusTernary ell * plusMinusDebris m := by
    exact Nat.succ_le_iff.mpr
      (Nat.mul_pos (by positivity) (plusMinusDebris_pos m))
  dsimp only [scaledMinusNumerator]
  rw [pow_add]
  omega

/-- Under the router's binary-room inequality, exact reproduction cannot
move to a level below the reached label. -/
theorem reached_le_next_of_reproduces_of_room
    {ell m target next : ℕ} (hrep : Reproduces ell m target next)
    (hroom : minusBinary target < plusBinary m) :
    ell ≤ next := by
  have hlower := three_pow_combined_pred_lt_scaledMinusNumerator ell m
  have hRlt : plusMinusDebris next < 3 ^ minusTernary next := by
    simp only [plusMinusDebris]
    have hpos : 0 < 2 ^ plusBinary next := by positivity
    have hle := Nat.le_of_lt (two_pow_plusBinary_lt_three_pow_minusTernary next)
    omega
  have hbase : 2 ^ minusBinary target ≤ 3 ^ minusBinary target :=
    Nat.pow_le_pow_left (by norm_num) _
  have hupperMul :
      2 ^ minusBinary target * plusMinusDebris next <
        3 ^ minusBinary target * 3 ^ minusTernary next := by
    calc
      2 ^ minusBinary target * plusMinusDebris next ≤
          3 ^ minusBinary target * plusMinusDebris next :=
        Nat.mul_le_mul_right _ hbase
      _ < 3 ^ minusBinary target * 3 ^ minusTernary next :=
        (Nat.mul_lt_mul_left (by positivity)).2 hRlt
  have hupper :
      2 ^ minusBinary target * plusMinusDebris next <
        3 ^ (minusBinary target + minusTernary next) := by
    simpa [pow_add] using hupperMul
  have hrep' : scaledMinusNumerator ell m =
      2 ^ minusBinary target * plusMinusDebris next := hrep
  rw [hrep'] at hlower
  have hExp :
      minusTernary ell + minusTernary m - 1 <
        minusBinary target + minusTernary next :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hlower.trans hupper)
  simp only [minusTernary, minusBinary, plusBinary] at hExp hroom
  omega

/-- Exact reproduction also cannot jump more than two public levels beyond
the sum of the reached and residual labels. -/
theorem next_le_reached_add_level_add_two_of_reproduces
    {ell m target next : ℕ} (hrep : Reproduces ell m target next) :
    next ≤ ell + m + 2 := by
  have hlowerR := two_mul_three_pow_pred_lt_plusMinusDebris next
  have hRlower : 3 ^ (minusTernary next - 1) < plusMinusDebris next := by
    omega
  have hfactor : plusMinusDebris next ≤
      2 ^ minusBinary target * plusMinusDebris next := by
    have hone : 1 ≤ 2 ^ minusBinary target :=
      Nat.one_le_pow _ 2 (by omega)
    calc
      plusMinusDebris next = 1 * plusMinusDebris next := by simp
      _ ≤ 2 ^ minusBinary target * plusMinusDebris next :=
        Nat.mul_le_mul_right _ hone
  have hupper := scaledMinusNumerator_lt_three_pow_combined ell m
  have hrep' : scaledMinusNumerator ell m =
      2 ^ minusBinary target * plusMinusDebris next := hrep
  rw [hrep'] at hupper
  have hchain : 3 ^ (minusTernary next - 1) <
      3 ^ (minusTernary ell + minusTernary m) := by
    calc
      3 ^ (minusTernary next - 1) < plusMinusDebris next := hRlower
      _ ≤ 2 ^ minusBinary target * plusMinusDebris next := hfactor
      _ < 3 ^ (minusTernary ell + minusTernary m) := hupper
  have hExp : minusTernary next - 1 <
      minusTernary ell + minusTernary m :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 hchain
  simp only [minusTernary] at hExp
  omega

/-- The explicit router label is at least the current residual level. -/
theorem level_le_routerLabel (d m : ℕ) :
    m ≤ routerLabel d m := by
  have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
  have htwom : 2 * m ≤ 2 * m * 2 ^ d := by nlinarith
  have hbase : 2 * m ≤ routerBase d m := by
    simp only [routerBase]
    omega
  rw [routerLabel]
  omega

/-- The room condition makes the requested target smaller than the current
residual level. -/
theorem target_le_level_of_room {m target : ℕ}
    (hroom : minusBinary target < plusBinary m) : target ≤ m := by
  simp only [minusBinary, plusBinary] at hroom
  omega

/-- Main architectural no-go: the explicit odd-level router's cofactor can
never be a single later member of the same positive-debris family.  The
order clock is exponential in the reached label, while reproduction size
localizes the next label to a linear window. -/
theorem no_explicit_router_reproduces_single_debris
    (m target next : ℕ)
    (hroom : minusBinary target < plusBinary m) :
    ¬ Reproduces (routerLabel (routerPrecision target) m) m target next := by
  intro hrep
  let d := routerPrecision target
  let ell := routerLabel d m
  have hmell : m ≤ ell := level_le_routerLabel d m
  have htargm : target ≤ m := target_le_level_of_room hroom
  have htargell : target ≤ ell := htargm.trans hmell
  have hellnext : ell ≤ next :=
    reached_le_next_of_reproduces_of_room hrep hroom
  have hnext : next ≤ ell + m + 2 :=
    next_le_reached_add_level_add_two_of_reproduces hrep
  have hcommon : commonTernaryPrecision ell next = minusTernary ell := by
    rw [commonTernaryPrecision, Nat.min_eq_left]
    simp only [minusTernary]
    omega
  have hclock := two_mul_common_clock_le_binaryReturn hrep
  rw [hcommon] at hclock
  have hclock' :
      2 * 3 ^ (17 * ell + 39) ≤ 23 * target + 8 * next + 69 := by
    simp only [minusTernary, minusBinary, plusBinary] at hclock
    have hexp : 17 * ell + 40 - 1 = 17 * ell + 39 := by omega
    rw [hexp] at hclock
    omega
  have hlinear : 23 * target + 8 * next + 69 ≤ 39 * ell + 85 := by
    omega
  let k := 8 * ell + 19
  have hquad : 39 * ell + 85 < 2 * k ^ 2 + 1 := by
    dsimp only [k]
    nlinarith
  have hpowLower : 2 * k ^ 2 + 1 ≤ 3 ^ (17 * ell + 39) := by
    calc
      2 * k ^ 2 + 1 ≤ 2 ^ (2 * k) :=
        Nat.two_mul_sq_add_one_le_two_pow_two_mul k
      _ ≤ 3 ^ (2 * k) := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 3 ^ (17 * ell + 39) := by
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp only [k]
        omega
  have : 23 * target + 8 * next + 69 <
      2 * 3 ^ (17 * ell + 39) := by
    calc
      23 * target + 8 * next + 69 ≤ 39 * ell + 85 := hlinear
      _ < 2 * k ^ 2 + 1 := hquad
      _ ≤ 3 ^ (17 * ell + 39) := hpowLower
      _ < 2 * 3 ^ (17 * ell + 39) := by
        have hx : 0 < 3 ^ (17 * ell + 39) := by positivity
        omega
  omega

end SignedDebrisReproduction
end KontoroC
