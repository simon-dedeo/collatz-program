/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CycleCertificate

/-!
# Positive accelerated periods dividing three are trivial

The fully accelerated odd Collatz map has no positive odd point of period
dividing three other than `1`.  The proof first retains the exact literal
valuation replay as a legal three-letter word.  Its affine cycle equation is
then coercive enough to bound all three valuations, after which a 36-case
kernel computation closes the finite box.

This theorem concerns positive integer periodic points only.  It says nothing
about aperiodic escape or unrelated period-three auxiliary constructions.
-/

namespace KontoroC
namespace AcceleratedPeriodThreeNoGo

/-- The exact affine equation for a legal three-instruction cycle. -/
theorem three_step_cycle_equation
    {n a b c : ℕ} (hlegal : WordLegal n [a, b, c])
    (hclose : runWord n [a, b, c] = n) :
    (2 ^ (a + b + c) - 27) * n =
      9 + 3 * 2 ^ a + 2 ^ (a + b) := by
  have hn : 0 < n := hlegal.1.1
  have heq := cycle_denominator_mul_seed hn hlegal hclose
  have htotal : totalValuation [a, b, c] = a + b + c := by
    simp [totalValuation]
    omega
  have hoffset : affineOffset [a, b, c] =
      9 + 3 * 2 ^ a + 2 ^ (a + b) := by
    simp [affineOffset, Nat.pow_add]
    ring
  rw [htotal, hoffset] at heq
  exact heq

/-- For a nontrivial positive seed, the three-step cycle equation forces the
coercive inequality used to bound the valuation triple. -/
theorem three_step_cycle_coercive
    {n a b c : ℕ} (hnTwo : 2 ≤ n)
    (heq : (2 ^ (a + b + c) - 27) * n =
      9 + 3 * 2 ^ a + 2 ^ (a + b)) :
    2 ^ (a + b) * (2 ^ (c + 1) - 1) ≤ 63 + 3 * 2 ^ a := by
  have hdenomPos : 27 < 2 ^ (a + b + c) := by
    by_contra hnot
    have hzero : 2 ^ (a + b + c) - 27 = 0 := by omega
    rw [hzero, zero_mul] at heq
    have hrhs : 0 < 9 + 3 * 2 ^ a + 2 ^ (a + b) := by positivity
    omega
  have htwice :
      2 * (2 ^ (a + b + c) - 27) ≤
        9 + 3 * 2 ^ a + 2 ^ (a + b) := by
    calc
      2 * (2 ^ (a + b + c) - 27) =
          (2 ^ (a + b + c) - 27) * 2 := by ring
      _ ≤ (2 ^ (a + b + c) - 27) * n :=
        Nat.mul_le_mul_left _ hnTwo
      _ = 9 + 3 * 2 ^ a + 2 ^ (a + b) := heq
  have hsub :
      2 * (2 ^ (a + b + c) - 27) =
        2 * 2 ^ (a + b + c) - 54 := by
    omega
  have hpowProduct :
      2 ^ (a + b) * 2 ^ (c + 1) =
        2 * 2 ^ (a + b + c) := by
    rw [← Nat.pow_add]
    ring_nf
  calc
    2 ^ (a + b) * (2 ^ (c + 1) - 1) =
        2 ^ (a + b) * 2 ^ (c + 1) - 2 ^ (a + b) := by
          rw [Nat.mul_sub_left_distrib]
          simp
    _ = 2 * 2 ^ (a + b + c) - 2 ^ (a + b) := by
          rw [hpowProduct]
    _ ≤ 63 + 3 * 2 ^ a := by omega

/-- The coercive inequality bounds the first valuation. -/
theorem first_valuation_le_four
    {a b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hcoercive :
      2 ^ (a + b) * (2 ^ (c + 1) - 1) ≤ 63 + 3 * 2 ^ a) :
    a ≤ 4 := by
  have hQ : 2 ^ (a + 1) ≤ 2 ^ (a + b) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hfactor : 3 ≤ 2 ^ (c + 1) - 1 := by
    have hp : 2 ^ 2 ≤ 2 ^ (c + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hp ⊢
    omega
  have hlower := Nat.mul_le_mul hQ hfactor
  have hsix : 6 * 2 ^ a ≤
      2 ^ (a + b) * (2 ^ (c + 1) - 1) := by
    rw [Nat.pow_succ] at hlower
    nlinarith
  have hpowBound : 2 ^ a ≤ 21 := by omega
  by_contra hnot
  have haFive : 5 ≤ a := by omega
  have hpFive : 2 ^ 5 ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by omega) haFive
  norm_num at hpFive
  omega

/-- Once the first valuation is bounded, the second valuation is at most
three. -/
theorem second_valuation_le_three
    {a b c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hcoercive :
      2 ^ (a + b) * (2 ^ (c + 1) - 1) ≤ 63 + 3 * 2 ^ a) :
    b ≤ 3 := by
  have hfactor : 3 ≤ 2 ^ (c + 1) - 1 := by
    have hp : 2 ^ 2 ≤ 2 ^ (c + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hp ⊢
    omega
  by_contra hnot
  have hbFour : 4 ≤ b := by omega
  have hpB : 16 ≤ 2 ^ b := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hbFour
    norm_num at this ⊢
    exact this
  have hpowSplit : 2 ^ (a + b) = 2 ^ a * 2 ^ b := by
    rw [Nat.pow_add]
  have hlower : 48 * 2 ^ a ≤
      2 ^ (a + b) * (2 ^ (c + 1) - 1) := by
    have hQlower : 2 ^ a * 16 ≤ 2 ^ (a + b) := by
      rw [hpowSplit]
      exact Nat.mul_le_mul_left (2 ^ a) hpB
    calc
      48 * 2 ^ a = (2 ^ a * 16) * 3 := by ring
      _ ≤ 2 ^ (a + b) * (2 ^ (c + 1) - 1) :=
        Nat.mul_le_mul hQlower hfactor
  have hpA : 2 ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) ha
    norm_num at this ⊢
    exact this
  omega

/-- With the first two positive, the third valuation is also at most three. -/
theorem third_valuation_le_three
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haFour : a ≤ 4)
    (hcoercive :
      2 ^ (a + b) * (2 ^ (c + 1) - 1) ≤ 63 + 3 * 2 ^ a) :
    c ≤ 3 := by
  have hQ : 4 ≤ 2 ^ (a + b) := by
    have hp : 2 ^ 2 ≤ 2 ^ (a + b) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hp ⊢
    exact hp
  have hpA : 2 ^ a ≤ 16 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) haFour
    norm_num at this ⊢
    exact this
  by_contra hnot
  have hcFour : 4 ≤ c := by omega
  have hpC : 32 ≤ 2 ^ (c + 1) := by
    have hp : 2 ^ 5 ≤ 2 ^ (c + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hp ⊢
    exact hp
  have hlower : 124 ≤
      2 ^ (a + b) * (2 ^ (c + 1) - 1) := by
    have hfactor : 31 ≤ 2 ^ (c + 1) - 1 := by omega
    calc
      124 = 4 * 31 := by norm_num
      _ ≤ 2 ^ (a + b) * (2 ^ (c + 1) - 1) :=
        Nat.mul_le_mul hQ hfactor
  omega

/-- A legal positive accelerated cycle of three instructions has seed one. -/
theorem legal_three_cycle_eq_one
    {n a b c : ℕ} (hlegal : WordLegal n [a, b, c])
    (hclose : runWord n [a, b, c] = n) :
    n = 1 := by
  have hn : 0 < n := hlegal.1.1
  have hpositive := wordLegal_positive_entries hlegal
  have ha : 0 < a := hpositive a (by simp)
  have hb : 0 < b := hpositive b (by simp)
  have hc : 0 < c := hpositive c (by simp)
  by_contra hnOne
  have hnTwo : 2 ≤ n := by omega
  have heq := three_step_cycle_equation hlegal hclose
  have hcoercive := three_step_cycle_coercive hnTwo heq
  have haFour := first_valuation_le_four hb hc hcoercive
  have hbThree := second_valuation_le_three ha hc hcoercive
  have hcThree := third_valuation_le_three ha hb haFour hcoercive
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num at heq <;> omega

/-- Requested literal theorem.  The hypotheses are the positive odd state
and an actual third iterate of `oddStep`, not merely the affine cycle
equation.  The proof constructs and replays the three exact valuations before
using the bounded arithmetic argument. -/
theorem no_nontrivial_positive_accelerated_period_three
    {n : ℕ} (hn : 0 < n) (hnodd : n % 2 = 1)
    (hperiod : (oddStep^[3]) n = n) :
    n = 1 := by
  let a := oddValuation n
  let n₁ := oddStep n
  let b := oddValuation n₁
  let n₂ := oddStep n₁
  let c := oddValuation n₂
  have hlegal : WordLegal n [a, b, c] := by
    refine ⟨⟨hn, hnodd, rfl⟩, ⟨?_, ?_, rfl⟩, ⟨?_, ?_, rfl⟩, trivial⟩
    · exact oddStep_pos n
    · exact oddStep_mod_two n
    · exact oddStep_pos n₁
    · exact oddStep_mod_two n₁
  have hclose : runWord n [a, b, c] = n := by
    simpa [a, b, c, n₁, n₂, runWord,
      Function.iterate_succ_apply'] using hperiod
  exact legal_three_cycle_eq_one hlegal hclose

/-- Calibration: the unique surviving point really has valuation word
`[2,2,2]` and is fixed by three accelerated steps. -/
theorem one_period_three_calibration :
    WordLegal 1 [2, 2, 2] ∧ runWord 1 [2, 2, 2] = 1 := by
  have hstep := legalInstruction_of_step_equation
    (n := 1) (k := 2) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hlegal, hone⟩ := hstep
  constructor
  · simp only [WordLegal]
    refine ⟨hlegal, ?_⟩
    rw [hone]
    exact ⟨hlegal, by rw [hone]; exact ⟨hlegal, trivial⟩⟩
  · simp [runWord, hone]

end AcceleratedPeriodThreeNoGo
end KontoroC
