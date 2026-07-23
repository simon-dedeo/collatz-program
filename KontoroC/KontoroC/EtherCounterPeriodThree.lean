/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterStateNoRepeat
import KontoroC.EtherCounterGeometricMahler
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Basic

/-!
# Literal period-three EC17 composition

This file derives the three phase defect in one cycle directly from the
natural EC17 balance.  No theta-value theorem or function-field surrogate is
used.  The result is the exact arithmetic identity QM65.
-/

namespace KontoroC
namespace EtherCounterPeriodThree

open EtherCounterStateNoRepeat

/-- A positive EC17 orbit whose branch schedule has three affine phases and
positive cycle gain. -/
structure Ray extends EtherCounterStateNoRepeat.Orbit where
  cycleGain : ℕ
  cycleGain_pos : 0 < cycleGain
  branch_zero : ∀ q, branch (3 * q) = branch 0 + cycleGain * q
  branch_one : ∀ q, branch (3 * q + 1) = branch 1 + cycleGain * q
  branch_two : ∀ q, branch (3 * q + 2) = branch 2 + cycleGain * q

namespace Ray

/-- Reindex the positive one-based EC17 branch as the zero-based level used
by the universal cumulative-scale theorems. -/
def toTernaryCoreOrbit (g : Ray) : EtherCounterAperiodic.TernaryCoreOrbit where
  level t := g.branch t - 1
  core := g.core
  core_pos := g.core_pos
  balance t := by
    have ht : 1 ≤ g.branch t := g.branch_pos t
    have hnext : 1 ≤ g.branch (t + 1) := g.branch_pos (t + 1)
    simpa [Nat.sub_add_cancel ht, Nat.sub_add_cancel hnext,
      show 8 * (g.branch (t + 1) - 1) + 23 =
        8 * g.branch (t + 1) + 15 by omega,
      show 6 * (g.branch t - 1) + 17 =
        6 * g.branch t + 11 by omega] using g.balance t

theorem toTernaryCoreOrbit_oneBasedLevel (g : Ray) (t : ℕ) :
    g.toTernaryCoreOrbit.oneBasedLevel t = g.branch t := by
  simp only [toTernaryCoreOrbit,
    EtherCounterAperiodic.TernaryCoreOrbit.oneBasedLevel]
  exact Nat.sub_add_cancel (g.branch_pos t)

theorem toTernaryCoreOrbit_core (g : Ray) (t : ℕ) :
    g.toTernaryCoreOrbit.core t = g.core t := rfl

/-- Exact terminal branch at a cycle boundary. -/
theorem branch_three_mul (g : Ray) (q : ℕ) :
    g.branch (3 * q) = g.branch 0 + g.cycleGain * q :=
  g.branch_zero q

/-- Exact prefix sum over `q` complete three-phase cycles. -/
theorem oneBasedLevelSum_three_mul (g : Ray) (q : ℕ) :
    g.toTernaryCoreOrbit.oneBasedLevelSum (3 * q) =
      q * (g.branch 0 + g.branch 1 + g.branch 2) +
        3 * g.cycleGain * q.choose 2 := by
  induction q with
  | zero =>
      simp [EtherCounterAperiodic.TernaryCoreOrbit.oneBasedLevelSum]
  | succ q ih =>
      rw [show 3 * (q + 1) = ((3 * q + 2) + 1) by omega,
        g.toTernaryCoreOrbit.oneBasedLevelSum_succ,
        show 3 * q + 2 = (3 * q + 1) + 1 by omega,
        g.toTernaryCoreOrbit.oneBasedLevelSum_succ,
        show 3 * q + 1 = 3 * q + 1 by rfl,
        g.toTernaryCoreOrbit.oneBasedLevelSum_succ, ih,
        g.toTernaryCoreOrbit_oneBasedLevel,
        g.toTernaryCoreOrbit_oneBasedLevel,
        g.toTernaryCoreOrbit_oneBasedLevel,
        g.branch_zero q, g.branch_one q, g.branch_two q]
      rw [show (q + 1).choose 2 = q.choose 2 + q by
        rw [show q + 1 = q.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      ring

theorem two_mul_choose_two (q : ℕ) :
    2 * q.choose 2 = q * (q - 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show (q + 1).choose 2 = q.choose 2 + q by
        rw [show q + 1 = q.succ by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]]
      cases q with
      | zero => simp
      | succ q =>
          simp only [Nat.add_sub_cancel]
          have ih' := ih
          simp only [Nat.add_sub_cancel] at ih'
          nlinarith

/-- QM93: a positive period-three EC17 survivor must carry quadratic core
bit growth even though its branch grows only linearly. -/
theorem quadratic_core_growth (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    2 ^ (q * (435 + g.cycleGain * (84 * q - 412))) <
      g.core (3 * q) ^ 41 := by
  let o := g.toTernaryCoreOrbit
  let S := o.oneBasedLevelSum (3 * q)
  let n₀ := o.oneBasedLevel 0
  let nN := o.oneBasedLevel (3 * q)
  let K := g.cycleGain
  let B := g.branch 0 + g.branch 1 + g.branch 2
  have hS : S = q * B + 3 * K * q.choose 2 := by
    simpa [o, S, B, K] using g.oneBasedLevelSum_three_mul q
  have hn₀ : n₀ = g.branch 0 := by
    simpa [o, n₀] using g.toTernaryCoreOrbit_oneBasedLevel 0
  have hnN : nN = g.branch 0 + K * q := by
    simpa [o, nN, K] using
      (g.toTernaryCoreOrbit_oneBasedLevel (3 * q)).trans (g.branch_zero q)
  have hB : 3 ≤ B := by
    dsimp only [B]
    have h0 := g.branch_pos 0
    have h1 := g.branch_pos 1
    have h2 := g.branch_pos 2
    omega
  have hchoose := two_mul_choose_two q
  have hchooseK : 168 * K * q.choose 2 =
      84 * K * q * (q - 1) := by
    calc
      168 * K * q.choose 2 = 84 * K * (2 * q.choose 2) := by ring
      _ = 84 * K * (q * (q - 1)) := by rw [hchoose]
      _ = 84 * K * q * (q - 1) := by ring
  have hKidentity :
      328 * K * q + q * K * (84 * q - 412) =
        168 * K * q.choose 2 := by
    calc
      328 * K * q + q * K * (84 * q - 412) =
          q * K * (328 + (84 * q - 412)) := by ring
      _ = q * K * (84 * q - 84) := by
        rw [show 328 + (84 * q - 412) = 84 * q - 84 by omega]
      _ = 84 * K * q * (q - 1) := by
        rw [show 84 * q - 84 = 84 * (q - 1) by omega]
        ring
      _ = 168 * K * q.choose 2 := hchooseK.symm
  have hBmul : 168 * q ≤ 56 * q * B := by
    nlinarith [Nat.mul_le_mul_left (56 * q) hB]
  have hstrong :
      328 * nN + q * (435 + K * (84 * q - 412)) ≤
        56 * S + 328 * n₀ + 89 * (3 * q) := by
    rw [hS, hn₀, hnN]
    calc
      328 * (g.branch 0 + K * q) +
            q * (435 + K * (84 * q - 412)) =
          328 * g.branch 0 + 435 * q +
            (328 * K * q + q * K * (84 * q - 412)) := by ring
      _ = 328 * g.branch 0 + 435 * q + 168 * K * q.choose 2 := by
        rw [hKidentity]
      _ ≤ 328 * g.branch 0 + (267 * q + 56 * q * B) +
            168 * K * q.choose 2 := by omega
      _ = 56 * (q * B + 3 * K * q.choose 2) +
            328 * g.branch 0 + 89 * (3 * q) := by ring
  have hterminal :
      328 * nN ≤ 56 * S + 328 * n₀ + 89 * (3 * q) :=
    le_trans (Nat.le_add_right _ _) hstrong
  have hgeneral := o.terminalExponent_core_power_lower (3 * q) (by omega)
    (by simpa [S, n₀, nN] using hterminal)
  have hexponent :
      q * (435 + K * (84 * q - 412)) ≤
        56 * S + 328 * n₀ + 89 * (3 * q) - 328 * nN := by
    omega
  have hpow :
      2 ^ (q * (435 + K * (84 * q - 412))) ≤
        2 ^ (56 * S + 328 * n₀ + 89 * (3 * q) - 328 * nN) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hgeneral' :
      2 ^ (56 * S + 328 * n₀ + 89 * (3 * q) - 328 * nN) <
        g.core (3 * q) ^ 41 := by
    simpa [S, n₀, nN, o, toTernaryCoreOrbit] using hgeneral
  exact lt_of_le_of_lt hpow hgeneral'

/-- Search-facing bit-length form of `quadratic_core_growth`.  A checker need
only inspect the ordinary core's binary digit count; it never expands either
large power in QM93. -/
theorem quadratic_binaryDigits_growth (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    (q * (435 + g.cycleGain * (84 * q - 412))) / 41 <
      (Nat.log 2 (g.core (3 * q))).succ :=
  EtherCounterAperiodic.TernaryCoreOrbit.exponent_div_41_lt_binaryDigits_of_two_pow_lt_pow_41
    _ _ (g.quadratic_core_growth q hq)

/-- QM96: near-optimal lower quadratic core growth at a period-three cycle
boundary. -/
theorem sharp_quadratic_core_growth_lower (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    2 ^ (q * (7869 + g.cycleGain * (1506 * q - 6826))) <
      g.core (3 * q) ^ 665 := by
  let o := g.toTernaryCoreOrbit
  let S := o.oneBasedLevelSum (3 * q)
  let n₀ := o.oneBasedLevel 0
  let nN := o.oneBasedLevel (3 * q)
  let K := g.cycleGain
  let B := g.branch 0 + g.branch 1 + g.branch 2
  have hS : S = q * B + 3 * K * q.choose 2 := by
    simpa [o, S, B, K] using g.oneBasedLevelSum_three_mul q
  have hn₀ : n₀ = g.branch 0 := by
    simpa [o, n₀] using g.toTernaryCoreOrbit_oneBasedLevel 0
  have hnN : nN = g.branch 0 + K * q := by
    simpa [o, nN, K] using
      (g.toTernaryCoreOrbit_oneBasedLevel (3 * q)).trans (g.branch_zero q)
  have hB : 3 ≤ B := by
    dsimp only [B]
    have h0 := g.branch_pos 0
    have h1 := g.branch_pos 1
    have h2 := g.branch_pos 2
    omega
  have hchoose := two_mul_choose_two q
  have hchooseK : 3012 * K * q.choose 2 =
      1506 * K * q * (q - 1) := by
    calc
      3012 * K * q.choose 2 = 1506 * K * (2 * q.choose 2) := by ring
      _ = 1506 * K * (q * (q - 1)) := by rw [hchoose]
      _ = 1506 * K * q * (q - 1) := by ring
  have hKidentity :
      5320 * K * q + q * K * (1506 * q - 6826) =
        3012 * K * q.choose 2 := by
    calc
      5320 * K * q + q * K * (1506 * q - 6826) =
          q * K * (5320 + (1506 * q - 6826)) := by ring
      _ = q * K * (1506 * q - 1506) := by
        rw [show 5320 + (1506 * q - 6826) = 1506 * q - 1506 by omega]
      _ = 1506 * K * q * (q - 1) := by
        rw [show 1506 * q - 1506 = 1506 * (q - 1) by omega]
        ring
      _ = 3012 * K * q.choose 2 := hchooseK.symm
  have hBmul : 3012 * q ≤ 1004 * q * B := by
    nlinarith [Nat.mul_le_mul_left (1004 * q) hB]
  have hstrong :
      5320 * nN + q * (7869 + K * (1506 * q - 6826)) ≤
        1004 * S + 5320 * n₀ + 1619 * (3 * q) := by
    rw [hS, hn₀, hnN]
    calc
      5320 * (g.branch 0 + K * q) +
            q * (7869 + K * (1506 * q - 6826)) =
          5320 * g.branch 0 + 7869 * q +
            (5320 * K * q + q * K * (1506 * q - 6826)) := by ring
      _ = 5320 * g.branch 0 + 7869 * q + 3012 * K * q.choose 2 := by
        rw [hKidentity]
      _ ≤ 5320 * g.branch 0 + (4857 * q + 1004 * q * B) +
            3012 * K * q.choose 2 := by omega
      _ = 1004 * (q * B + 3 * K * q.choose 2) +
            5320 * g.branch 0 + 1619 * (3 * q) := by ring
  have hterminal :
      5320 * nN ≤ 1004 * S + 5320 * n₀ + 1619 * (3 * q) :=
    le_trans (Nat.le_add_right _ _) hstrong
  have hgeneral := o.terminalExponent_core_power_lower_665 (3 * q)
    (by omega) (by simpa [S, n₀, nN] using hterminal)
  have hexponent :
      q * (7869 + K * (1506 * q - 6826)) ≤
        1004 * S + 5320 * n₀ + 1619 * (3 * q) - 5320 * nN := by
    omega
  have hpow :
      2 ^ (q * (7869 + K * (1506 * q - 6826))) ≤
        2 ^ (1004 * S + 5320 * n₀ + 1619 * (3 * q) - 5320 * nN) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hgeneral' :
      2 ^ (1004 * S + 5320 * n₀ + 1619 * (3 * q) - 5320 * nN) <
        g.core (3 * q) ^ 665 := by
    simpa [S, n₀, nN, o, toTernaryCoreOrbit] using hgeneral
  exact lt_of_le_of_lt hpow hgeneral'

/-- QM98: matching upper quadratic core growth at a period-three boundary. -/
theorem sharp_quadratic_core_growth_upper (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    g.core (3 * q) ^ 306 <
      2 ^ (306 * (Nat.log 2 (g.core 0)).succ +
        q * (462 * (g.branch 0 + g.branch 1 + g.branch 2) + 2235 +
          g.cycleGain * (693 * q - 3141))) := by
  let o := g.toTernaryCoreOrbit
  let S := o.oneBasedLevelSum (3 * q)
  let T := o.nextOneBasedLevelSum (3 * q)
  let n₀ := o.oneBasedLevel 0
  let nN := o.oneBasedLevel (3 * q)
  let K := g.cycleGain
  let B := g.branch 0 + g.branch 1 + g.branch 2
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let U := 306 * L₀ + q * (462 * B + 2235 + K * (693 * q - 3141))
  have hS : S = q * B + 3 * K * q.choose 2 := by
    simpa [o, S, B, K] using g.oneBasedLevelSum_three_mul q
  have hn₀ : n₀ = g.branch 0 := by
    simpa [o, n₀] using g.toTernaryCoreOrbit_oneBasedLevel 0
  have hnN : nN = g.branch 0 + K * q := by
    simpa [o, nN, K] using
      (g.toTernaryCoreOrbit_oneBasedLevel (3 * q)).trans (g.branch_zero q)
  have hshift : T + n₀ = S + nN := by
    simpa [S, T, n₀, nN] using
      o.nextSum_add_initial_eq_sum_add_terminal (3 * q)
  have hT : T = q * B + 3 * K * q.choose 2 + K * q := by
    rw [hS, hn₀, hnN] at hshift
    omega
  have hchoose := two_mul_choose_two q
  have hchooseK : 1386 * K * q.choose 2 =
      693 * K * q * (q - 1) := by
    calc
      1386 * K * q.choose 2 = 693 * K * (2 * q.choose 2) := by ring
      _ = 693 * K * (q * (q - 1)) := by rw [hchoose]
      _ = 693 * K * q * (q - 1) := by ring
  have hKidentity :
      2448 * K * q + q * K * (693 * q - 3141) =
        1386 * K * q.choose 2 := by
    calc
      2448 * K * q + q * K * (693 * q - 3141) =
          q * K * (2448 + (693 * q - 3141)) := by ring
      _ = q * K * (693 * q - 693) := by
        rw [show 2448 + (693 * q - 3141) = 693 * q - 693 by omega]
      _ = 693 * K * q * (q - 1) := by
        rw [show 693 * q - 693 = 693 * (q - 1) by omega]
        ring
      _ = 1386 * K * q.choose 2 := hchooseK.symm
  have hexponents :
      306 * L₀ + 2910 * S + 5335 * (3 * q) =
        2448 * T + 4590 * (3 * q) + U := by
    rw [hS, hT]
    dsimp only [U]
    calc
      306 * L₀ + 2910 * (q * B + 3 * K * q.choose 2) +
            5335 * (3 * q) =
          306 * L₀ + 2910 * q * B + 8730 * K * q.choose 2 +
            16005 * q := by ring
      _ = 306 * L₀ + 2910 * q * B +
            7344 * K * q.choose 2 + 1386 * K * q.choose 2 +
            16005 * q := by ring
      _ = 306 * L₀ + 2910 * q * B +
            7344 * K * q.choose 2 +
              (2448 * K * q + q * K * (693 * q - 3141)) +
            16005 * q := by rw [hKidentity]
      _ = 2448 * (q * B + 3 * K * q.choose 2 + K * q) +
            4590 * (3 * q) +
            (306 * L₀ +
              q * (462 * B + 2235 + K * (693 * q - 3141))) := by
        ring
  have hupper := o.core_power_upper_306 (3 * q) (by omega)
  change 2 ^ (2448 * T + 4590 * (3 * q)) * g.core (3 * q) ^ 306 <
    2 ^ (306 * L₀ + 2910 * S + 5335 * (3 * q)) at hupper
  have hrhs :
      2 ^ (306 * L₀ + 2910 * S + 5335 * (3 * q)) =
        2 ^ (2448 * T + 4590 * (3 * q)) * 2 ^ U := by
    rw [hexponents, pow_add]
  rw [hrhs] at hupper
  have hcancel : g.core (3 * q) ^ 306 < 2 ^ U := by
    exact (Nat.mul_lt_mul_left
      (by positivity : 0 < 2 ^ (2448 * T + 4590 * (3 * q)))).mp hupper
  simpa [U, L₀, B, K] using hcancel

/-- QM99 lower bit-length consumer. -/
theorem sharp_quadratic_binaryDigits_lower (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    (q * (7869 + g.cycleGain * (1506 * q - 6826))) / 665 <
      (Nat.log 2 (g.core (3 * q))).succ :=
  EtherCounterAperiodic.TernaryCoreOrbit.exponent_div_lt_binaryDigits_of_two_pow_lt_pow
    665 _ _ (by norm_num) (g.sharp_quadratic_core_growth_lower q hq)

/-- QM99 upper bit-length consumer.  The additive `306` accounts exactly
for passing from the binary logarithm to the positive integer digit count. -/
theorem sharp_quadratic_binaryDigits_upper (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    306 * (Nat.log 2 (g.core (3 * q))).succ <
      306 * (Nat.log 2 (g.core 0)).succ +
        q * (462 * (g.branch 0 + g.branch 1 + g.branch 2) + 2235 +
          g.cycleGain * (693 * q - 3141)) + 306 := by
  have hlog :=
    EtherCounterAperiodic.TernaryCoreOrbit.power_mul_binaryLog_lt_exponent_of_pow_lt_two_pow
      306 _ _ (g.core_pos (3 * q)).ne'
      (g.sharp_quadratic_core_growth_upper q hq)
  omega

/-! ## Exact residual width of the near-optimal band -/

-- Large cleared-denominator numerals make elaboration recurse more deeply
-- than the default while checking the three residual-band declarations.
set_option maxRecDepth 50000

def phaseSum (g : Ray) : ℕ :=
  g.branch 0 + g.branch 1 + g.branch 2

def sharpLowerExponent (g : Ray) (q : ℕ) : ℕ :=
  q * (7869 + g.cycleGain * (1506 * q - 6826))

def sharpGrowthExponent (g : Ray) (q : ℕ) : ℕ :=
  q * (462 * phaseSum g + 2235 + g.cycleGain * (693 * q - 3141))

def sharpUpperExponent (g : Ray) (q : ℕ) : ℕ :=
  306 * (Nat.log 2 (g.core 0)).succ + sharpGrowthExponent g q

/-- Growth numerator supplied by the sharper upper separator
`3^971 < 2^1539`. -/
def tight971GrowthExponent (g : Ray) (q : ℕ) : ℕ :=
  q * (1466 * phaseSum g + 7092 +
    g.cycleGain * (2199 * q - 9967))

/-- Determinant-one gap between the old `/306` budget and the sharper
`/971` upper estimate. -/
def tight971Gap (g : Ray) (q : ℕ) : ℕ :=
  q * (6 * phaseSum g + 33 + 9 * g.cycleGain * (q - 1))

/-- Exact cleared identity behind QM112. -/
theorem tight971_gap_identity (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    971 * sharpGrowthExponent g q =
      306 * tight971GrowthExponent g q + tight971Gap g q := by
  let r := q - 5
  let B := phaseSum g
  have hqrep : q = r + 5 := by dsimp only [r]; omega
  simp only [sharpGrowthExponent, tight971GrowthExponent, tight971Gap]
  rw [hqrep]
  rw [show 693 * (r + 5) - 3141 = 693 * r + 324 by omega,
    show 2199 * (r + 5) - 9967 = 2199 * r + 1028 by omega,
    show r + 5 - 1 = r + 4 by omega]
  ring

/-- QM111: the sharper 971st-power estimate at a period-three cycle
boundary. -/
theorem sharp_quadratic_core_growth_upper_971
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    g.core (3 * q) ^ 971 <
      2 ^ (971 * (Nat.log 2 (g.core 0)).succ +
        tight971GrowthExponent g q) := by
  let o := g.toTernaryCoreOrbit
  let S := o.oneBasedLevelSum (3 * q)
  let T := o.nextOneBasedLevelSum (3 * q)
  let n₀ := o.oneBasedLevel 0
  let nN := o.oneBasedLevel (3 * q)
  let K := g.cycleGain
  let B := phaseSum g
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let U := 971 * L₀ + tight971GrowthExponent g q
  have hS : S = q * B + 3 * K * q.choose 2 := by
    simpa [o, S, B, K, phaseSum] using g.oneBasedLevelSum_three_mul q
  have hn₀ : n₀ = g.branch 0 := by
    simpa [o, n₀] using g.toTernaryCoreOrbit_oneBasedLevel 0
  have hnN : nN = g.branch 0 + K * q := by
    simpa [o, nN, K] using
      (g.toTernaryCoreOrbit_oneBasedLevel (3 * q)).trans (g.branch_zero q)
  have hshift : T + n₀ = S + nN := by
    simpa [S, T, n₀, nN] using
      o.nextSum_add_initial_eq_sum_add_terminal (3 * q)
  have hT : T = q * B + 3 * K * q.choose 2 + K * q := by
    rw [hS, hn₀, hnN] at hshift
    omega
  have hchoose := two_mul_choose_two q
  have hchooseK : 4398 * K * q.choose 2 =
      2199 * K * q * (q - 1) := by
    calc
      4398 * K * q.choose 2 = 2199 * K * (2 * q.choose 2) := by ring
      _ = 2199 * K * (q * (q - 1)) := by rw [hchoose]
      _ = 2199 * K * q * (q - 1) := by ring
  have hKidentity :
      7768 * K * q + q * K * (2199 * q - 9967) =
        4398 * K * q.choose 2 := by
    calc
      7768 * K * q + q * K * (2199 * q - 9967) =
          q * K * (7768 + (2199 * q - 9967)) := by ring
      _ = q * K * (2199 * q - 2199) := by
        rw [show 7768 + (2199 * q - 9967) = 2199 * q - 2199 by omega]
      _ = 2199 * K * q * (q - 1) := by
        rw [show 2199 * q - 2199 = 2199 * (q - 1) by omega]
        ring
      _ = 4398 * K * q.choose 2 := hchooseK.symm
  have hexponents :
      971 * L₀ + 9234 * S + 16929 * (3 * q) =
        7768 * T + 14565 * (3 * q) + U := by
    rw [hS, hT]
    dsimp only [U, tight971GrowthExponent]
    change
      971 * L₀ + 9234 * (q * B + 3 * K * q.choose 2) +
          16929 * (3 * q) =
        7768 * (q * B + 3 * K * q.choose 2 + K * q) +
          14565 * (3 * q) +
            (971 * L₀ +
              q * (1466 * B + 7092 + K * (2199 * q - 9967)))
    calc
      971 * L₀ + 9234 * (q * B + 3 * K * q.choose 2) +
            16929 * (3 * q) =
          971 * L₀ + 9234 * q * B + 27702 * K * q.choose 2 +
            50787 * q := by ring
      _ = 971 * L₀ + 9234 * q * B +
            23304 * K * q.choose 2 + 4398 * K * q.choose 2 +
            50787 * q := by ring
      _ = 971 * L₀ + 9234 * q * B +
            23304 * K * q.choose 2 +
              (7768 * K * q + q * K * (2199 * q - 9967)) +
            50787 * q := by rw [hKidentity]
      _ = 7768 * (q * B + 3 * K * q.choose 2 + K * q) +
            14565 * (3 * q) +
              (971 * L₀ +
                q * (1466 * B + 7092 + K * (2199 * q - 9967))) := by
        ring
  have hupper := o.core_power_upper_971 (3 * q) (by omega)
  change
    2 ^ (7768 * T + 14565 * (3 * q)) * g.core (3 * q) ^ 971 <
      2 ^ (971 * L₀ + 9234 * S + 16929 * (3 * q)) at hupper
  have hrhs :
      2 ^ (971 * L₀ + 9234 * S + 16929 * (3 * q)) =
        2 ^ (7768 * T + 14565 * (3 * q)) * 2 ^ U := by
    rw [hexponents, pow_add]
  rw [hrhs] at hupper
  have hcancel : g.core (3 * q) ^ 971 < 2 ^ U := by
    exact (Nat.mul_lt_mul_left
      (by positivity : 0 < 2 ^ (7768 * T + 14565 * (3 * q)))).mp hupper
  simpa [U, L₀] using hcancel

/-- Exact cleared-denominator width after the adjacent convergents cancel.
The quadratic coefficient is only `9*K`, because
`665*693 - 306*1506 = 9`. -/
def sharpBandWidth (g : Ray) (q : ℕ) : ℕ :=
  203490 * ((Nat.log 2 (g.core 0)).succ + 1) +
    q * (307230 * (phaseSum g - 3) + 51) +
      9 * g.cycleGain * q * (q - 1)

/-- The exact arithmetic cancellation hidden by the two decimal leading
coefficients. -/
theorem sharp_exponent_gap_identity (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    665 * (sharpUpperExponent g q + 306) =
      306 * sharpLowerExponent g q + sharpBandWidth g q := by
  let r := q - 5
  let b := phaseSum g - 3
  have hphase : 3 ≤ phaseSum g := by
    dsimp only [phaseSum]
    have h0 := g.branch_pos 0
    have h1 := g.branch_pos 1
    have h2 := g.branch_pos 2
    omega
  have hqrep : q = r + 5 := by dsimp only [r]; omega
  have hbrep : phaseSum g = b + 3 := by dsimp only [b]; omega
  simp only [sharpUpperExponent, sharpGrowthExponent, sharpLowerExponent,
    sharpBandWidth]
  rw [hqrep, hbrep]
  rw [show 693 * (r + 5) - 3141 = 693 * r + 324 by omega,
    show 1506 * (r + 5) - 6826 = 1506 * r + 704 by omega,
    show b + 3 - 3 = b by omega,
    show r + 5 - 1 = r + 4 by omega]
  ring

/-- Cleared-denominator QM99 sandwich. -/
theorem sharp_binaryDigits_scaled_sandwich
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    306 * sharpLowerExponent g q <
        203490 * (Nat.log 2 (g.core (3 * q))).succ ∧
      203490 * (Nat.log 2 (g.core (3 * q))).succ <
        665 * (sharpUpperExponent g q + 306) := by
  let L := (Nat.log 2 (g.core (3 * q))).succ
  have hlower : sharpLowerExponent g q / 665 < L := by
    simpa [sharpLowerExponent, L] using g.sharp_quadratic_binaryDigits_lower q hq
  have hlower' : sharpLowerExponent g q < L * 665 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 665)).1 hlower
  have hlowerScaled :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 306)).2 hlower'
  have hupper : 306 * L < sharpUpperExponent g q + 306 := by
    simpa [sharpUpperExponent, sharpGrowthExponent, phaseSum, L] using
      g.sharp_quadratic_binaryDigits_upper q hq
  have hupperScaled :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 665)).2 hupper
  constructor
  · change 306 * sharpLowerExponent g q < 203490 * L
    calc
      306 * sharpLowerExponent g q < 306 * (L * 665) := hlowerScaled
      _ = 203490 * L := by ring
  · change 203490 * L < 665 * (sharpUpperExponent g q + 306)
    calc
      203490 * L = 665 * (306 * L) := by ring
      _ < 665 * (sharpUpperExponent g q + 306) := hupperScaled

/-- Search-normalized form: after subtracting the forced lower exponent, the
remaining scaled digit coordinate lies in one explicit interval. -/
theorem sharp_binaryDigits_residual_window
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    306 * sharpLowerExponent g q <
        203490 * (Nat.log 2 (g.core (3 * q))).succ ∧
      203490 * (Nat.log 2 (g.core (3 * q))).succ <
        306 * sharpLowerExponent g q + sharpBandWidth g q := by
  have hband := g.sharp_binaryDigits_scaled_sandwich q hq
  refine ⟨hband.1, ?_⟩
  rw [← g.sharp_exponent_gap_identity q hq]
  exact hband.2

/-! ## Normalized residue margins -/

/-- Ceiling of the new-growth exponent after division by the upper power
`306`. -/
def sharpUpperBudget (g : Ray) (q : ℕ) : ℕ :=
  (sharpGrowthExponent g q + 305) / 306

/-- Rounded binary growth budget from the sharper 971st-power estimate. -/
def tight971Budget (g : Ray) (q : ℕ) : ℕ :=
  (tight971GrowthExponent g q + 970) / 971

/-- Elementary ceiling-division inequality, kept explicit so certificate
consumers need no rational arithmetic. -/
theorem le_mul_ceilDiv (A d : ℕ) (hd : 0 < d) :
    A ≤ d * ((A + (d - 1)) / d) := by
  have hdecomp := Nat.div_add_mod (A + (d - 1)) d
  have hmod := Nat.mod_lt (A + (d - 1)) hd
  omega

/-- QM116a: direct binary-digit form of the sharper 971st-power estimate. -/
theorem core_binaryDigits_le_initial_add_tight971Budget
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    (Nat.log 2 (g.core (3 * q))).succ ≤
      (Nat.log 2 (g.core 0)).succ + tight971Budget g q := by
  let L := (Nat.log 2 (g.core (3 * q))).succ
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let C := tight971GrowthExponent g q
  let V := tight971Budget g q
  have hpower := g.sharp_quadratic_core_growth_upper_971 q hq
  have hlog :=
    EtherCounterAperiodic.TernaryCoreOrbit.power_mul_binaryLog_lt_exponent_of_pow_lt_two_pow
      971 (971 * L₀ + C) (g.core (3 * q))
        (g.core_pos (3 * q)).ne' (by simpa [L₀, C] using hpower)
  have hceil : C ≤ 971 * V := by
    simpa [C, V, tight971Budget] using
      le_mul_ceilDiv C 971 (by norm_num)
  change L ≤ L₀ + V
  change 971 * (L - 1) < 971 * L₀ + C at hlog
  omega

/-- QM112a--b: once the determinant-one gap pays for the fixed initial
bit-length allowance, the genuine cycle-boundary core lies below the old
coarse binary budget itself. -/
theorem core_lt_two_pow_upperBudget_of_tight971Gap
    (g : Ray) (q : ℕ) (hq : 5 ≤ q)
    (hthreshold :
      297126 * ((Nat.log 2 (g.core 0)).succ + 1) ≤ tight971Gap g q) :
    g.core (3 * q) < 2 ^ sharpUpperBudget g q := by
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let A := sharpGrowthExponent g q
  let C := tight971GrowthExponent g q
  let D := tight971Gap g q
  let U := sharpUpperBudget g q
  have hidentity : 971 * A = 306 * C + D := by
    simpa [A, C, D] using g.tight971_gap_identity q hq
  have hceil : A ≤ 306 * U := by
    simpa [A, U, sharpUpperBudget] using
      le_mul_ceilDiv A 306 (by norm_num)
  have hthreshold' : 297126 * (L₀ + 1) ≤ D := by
    simpa [L₀, D] using hthreshold
  have hleft : 306 * C + 297126 * (L₀ + 1) ≤ 971 * A := by
    rw [hidentity]
    exact Nat.add_le_add_left hthreshold' (306 * C)
  have hright : 971 * A ≤ 971 * (306 * U) :=
    Nat.mul_le_mul_left 971 hceil
  have hexponent : 971 * L₀ + C < 971 * U := by
    omega
  have htight := g.sharp_quadratic_core_growth_upper_971 q hq
  change g.core (3 * q) ^ 971 < 2 ^ (971 * L₀ + C) at htight
  have hpowStrict : g.core (3 * q) ^ 971 < 2 ^ (971 * U) :=
    htight.trans (Nat.pow_lt_pow_right (by norm_num) hexponent)
  by_contra hnot
  push Not at hnot
  have hraised := Nat.pow_le_pow_left hnot 971
  have hreverse : 2 ^ (971 * U) ≤ g.core (3 * q) ^ 971 := by
    rw [show 971 * U = U * 971 by omega, pow_mul]
    exact hraised
  exact (not_lt_of_ge hreverse) hpowStrict

/-- The determinant-one gap is eventually large enough for QM112a, hence
the genuine core eventually lies below the old coarse budget.  The explicit
witness uses only a linear lower bound on the positive quadratic gap. -/
theorem eventually_core_lt_two_pow_upperBudget (g : Ray) :
    ∃ Q, ∀ q, Q ≤ q →
      g.core (3 * q) < 2 ^ sharpUpperBudget g q := by
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let H := 297126 * (L₀ + 1)
  let Q := max 5 H
  refine ⟨Q, ?_⟩
  intro q hq
  have hq5 : 5 ≤ q := (le_max_left 5 H).trans hq
  have hHq : H ≤ q := (le_max_right 5 H).trans hq
  apply g.core_lt_two_pow_upperBudget_of_tight971Gap q hq5
  change H ≤ tight971Gap g q
  have hfactor : 0 <
      6 * phaseSum g + 33 + 9 * g.cycleGain * (q - 1) := by omega
  exact hHq.trans (by
    simpa [tight971Gap] using Nat.le_mul_of_pos_right q hfactor)

/-- QM100: the core at cycle `q` has at most the initial bit length plus the
rounded sharp-growth budget. -/
theorem core_binaryDigits_le_initial_add_upperBudget
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    (Nat.log 2 (g.core (3 * q))).succ ≤
      (Nat.log 2 (g.core 0)).succ + sharpUpperBudget g q := by
  let L := (Nat.log 2 (g.core (3 * q))).succ
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let A := sharpGrowthExponent g q
  let U := sharpUpperBudget g q
  have hupper := g.sharp_quadratic_binaryDigits_upper q hq
  have hupper' : 306 * L < 306 * L₀ + A + 306 := by
    change 306 * L < sharpUpperExponent g q + 306
    simpa [sharpUpperExponent, sharpGrowthExponent, phaseSum, L, L₀, A] using hupper
  have hceil : A ≤ 306 * U := by
    simpa [U, sharpUpperBudget] using
      le_mul_ceilDiv A 306 (by norm_num)
  change L ≤ L₀ + U
  omega

/-- QM105: power-level form of QM100.  The actual cycle-boundary core lies
strictly below the theorem-forced binary budget times the fixed initial-core
bit budget. -/
theorem core_lt_two_pow_upperBudget_add_initialDigits
    (g : Ray) (q : ℕ) (hq : 5 ≤ q) :
    g.core (3 * q) <
      2 ^ (sharpUpperBudget g q + (Nat.log 2 (g.core 0)).succ) := by
  have hself : g.core (3 * q) <
      2 ^ (Nat.log 2 (g.core (3 * q))).succ :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hdigits := g.core_binaryDigits_le_initial_add_upperBudget q hq
  have hexponents : (Nat.log 2 (g.core (3 * q))).succ ≤
      sharpUpperBudget g q + (Nat.log 2 (g.core 0)).succ := by
    omega
  exact hself.trans_le (Nat.pow_le_pow_right (by norm_num) hexponents)

/-- Shift the prescribed branch schedule to the boundary after `q` complete
three-step cycles. -/
def shiftedBranch (g : Ray) (q t : ℕ) : ℕ :=
  g.branch (3 * q + t)

/-- The literal natural EC17 prefix beginning exactly at cycle boundary
`3*q`; the shifted future starts at `g.branch (3*q)`, not its predecessor. -/
def shiftedNaturalPrefix (g : Ray) (q length : ℕ) :
    EtherCounterResidueBound.NaturalPrefix (shiftedBranch g q) length where
  branch_pos t _ := g.branch_pos (3 * q + t)
  core t := g.core (3 * q + t)
  core_pos t _ := g.core_pos (3 * q + t)
  balance t _ := by
    simpa [shiftedBranch, EtherCounterResidueBound.binaryExponent,
      EtherCounterResidueBound.ternaryExponent, Nat.add_assoc] using
        g.balance (3 * q + t)

theorem shiftedCore_admitsNaturalPrefix
    (g : Ray) (q length : ℕ) :
    EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g q) length (g.core (3 * q)) := by
  exact ⟨shiftedNaturalPrefix g q length, rfl⟩

def normalizedPrecision (g : Ray) (q R : ℕ) : ℕ :=
  sharpUpperBudget g q + R

def shiftedInitialResidue (g : Ray) (q R length : ℕ) :
    ZMod (2 ^ normalizedPrecision g q R) :=
  EtherCounterResidueBound.initialResidue (shiftedBranch g q)
    (normalizedPrecision g q R) length

/-- QM101: every positive forced residue at precision `U(q)+R` obeys the
same bit budget as the actual cycle-boundary core.  The proof bootstraps the
unknown comparison between the initial bit length and `R`: an oversized
residue first forces enough precision for QM62, which identifies it with the
actual core and yields the contradiction. -/
theorem shiftedInitialResidue_binaryDigits_le
    (g : Ray) (q R length : ℕ) (hq : 5 ≤ q)
    (hprecision : normalizedPrecision g q R ≤
      EtherCounterResidueBound.binaryMass (shiftedBranch g q) 0 length)
    (hresidue_pos : 0 < (shiftedInitialResidue g q R length).val) :
    (Nat.log 2 (shiftedInitialResidue g q R length).val).succ ≤
      sharpUpperBudget g q + (Nat.log 2 (g.core 0)).succ := by
  let P := normalizedPrecision g q R
  let r := (shiftedInitialResidue g q R length).val
  let U := sharpUpperBudget g q
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let pref := shiftedNaturalPrefix g q length
  have hcoreDigits := g.core_binaryDigits_le_initial_add_upperBudget q hq
  by_contra hbad
  push Not at hbad
  have hbadR : U + L₀ < (Nat.log 2 r).succ := by
    simpa [U, L₀, r] using hbad
  have hrlt : r < 2 ^ P := by
    simpa [r, P, shiftedInitialResidue, normalizedPrecision] using
      ZMod.val_lt (shiftedInitialResidue g q R length)
  have hrdigits : (Nat.log 2 r).succ ≤ P := by
    have hlog : Nat.log 2 r < P :=
      Nat.log_lt_of_lt_pow (by simpa [r] using hresidue_pos.ne') hrlt
    omega
  have hbudget_lt_P : L₀ + U < P := by
    omega
  have hcoreLog : Nat.log 2 (g.core (3 * q)) < P := by
    change (Nat.log 2 (g.core (3 * q))).succ ≤ L₀ + U at hcoreDigits
    omega
  have hcoreSmall : g.core (3 * q) < 2 ^ P :=
    (Nat.log_lt_iff_lt_pow Nat.one_lt_two (g.core_pos (3 * q)).ne').1
      hcoreLog
  have heq0 := EtherCounterResidueBound.initialResidue_val_eq_initial_core
    pref P (by simpa [P, pref, shiftedNaturalPrefix] using hprecision)
      (by simpa [pref, shiftedNaturalPrefix] using hcoreSmall)
  have heq : r = g.core (3 * q) := by
    simpa [r, P, pref, shiftedInitialResidue, shiftedNaturalPrefix] using heq0
  have hdigitsEq : (Nat.log 2 r).succ =
      (Nat.log 2 (g.core (3 * q))).succ :=
    congrArg (fun z : ℕ => (Nat.log 2 z).succ) heq
  have hbadCore : L₀ + U < (Nat.log 2 (g.core (3 * q))).succ := by
    rw [← hdigitsEq]
    omega
  change (Nat.log 2 (g.core (3 * q))).succ ≤ L₀ + U at hcoreDigits
  exact (not_lt_of_ge hcoreDigits) hbadCore

/-- QM102: the normalized finite-row margin lower-bounds the one fixed
initial core bit length. -/
theorem shiftedInitialResidue_normalizedMargin_le_initialDigits
    (g : Ray) (q R length : ℕ) (hq : 5 ≤ q)
    (hprecision : normalizedPrecision g q R ≤
      EtherCounterResidueBound.binaryMass (shiftedBranch g q) 0 length)
    (hresidue_pos : 0 < (shiftedInitialResidue g q R length).val) :
    (Nat.log 2 (shiftedInitialResidue g q R length).val).succ -
        sharpUpperBudget g q ≤
      (Nat.log 2 (g.core 0)).succ := by
  have h := g.shiftedInitialResidue_binaryDigits_le q R length hq
    hprecision hresidue_pos
  omega

def normalizedResidueMargin (g : Ray) (q R length : ℕ) : ℕ :=
  (Nat.log 2 (shiftedInitialResidue g q R length).val).succ -
    sharpUpperBudget g q

/-- QM103: a supplied cofinal family of exact rows with unbounded normalized
margins excludes the entire proposed period-three ray.  No finite trend or
unboundedness assertion is hidden in this consumer. -/
theorem false_of_unbounded_normalizedResidueMargins
    (g : Ray) (q R length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hprecision : ∀ j, normalizedPrecision g (q j) (R j) ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g (q j)) 0 (length j))
    (hresidue_pos : ∀ j,
      0 < (shiftedInitialResidue g (q j) (R j) (length j)).val)
    (hunbounded : ∀ M, ∃ j, M <
      normalizedResidueMargin g (q j) (R j) (length j)) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbound := g.shiftedInitialResidue_normalizedMargin_le_initialDigits
    (q j) (R j) (length j) (hq j) (hprecision j) (hresidue_pos j)
  change normalizedResidueMargin g (q j) (R j) (length j) ≤
    (Nat.log 2 (g.core 0)).succ at hbound
  omega

/-- QM104: if the canonical least residue at padding `R` fails to replay as
the initial core of *every* natural prefix on the shifted schedule, then `R`
is strictly smaller than the one fixed initial-core bit length.

This is stronger than the positive-residue margin bound and needs no
positivity premise.  The failure theorem forces the actual cycle-boundary
core above `2^(U+R)`, while QM100 keeps it below `2^(L₀+U)`. -/
theorem replayFailure_padding_lt_initialDigits
    (g : Ray) (q R length : ℕ) (hq : 5 ≤ q)
    (hprecision : normalizedPrecision g q R ≤
      EtherCounterResidueBound.binaryMass (shiftedBranch g q) 0 length)
    (hfail : ∀ pref : EtherCounterResidueBound.NaturalPrefix
      (shiftedBranch g q) length,
      pref.core 0 ≠
        (EtherCounterResidueBound.initialResidue (shiftedBranch g q)
          (normalizedPrecision g q R) length).val) :
    R < (Nat.log 2 (g.core 0)).succ := by
  let P := normalizedPrecision g q R
  let U := sharpUpperBudget g q
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let pref := shiftedNaturalPrefix g q length
  have hlower : 2 ^ P ≤ g.core (3 * q) := by
    simpa [P, pref, shiftedNaturalPrefix] using
      EtherCounterResidueBound.initial_core_ge_modulus_of_least_residue_fails
        (branch := shiftedBranch g q) (length := length) (P := P)
        (by simpa [P] using hprecision)
        (by simpa [P] using hfail) pref
  have hcoreDigits := g.core_binaryDigits_le_initial_add_upperBudget q hq
  have hcoreSmall : g.core (3 * q) < 2 ^ (L₀ + U) := by
    have hself : g.core (3 * q) <
        2 ^ (Nat.log 2 (g.core (3 * q))).succ :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hpower : 2 ^ (Nat.log 2 (g.core (3 * q))).succ ≤
        2 ^ (L₀ + U) := by
      apply Nat.pow_le_pow_right (by norm_num)
      simpa [L₀, U] using hcoreDigits
    exact hself.trans_le hpower
  by_contra hnot
  push Not at hnot
  have hexponents : L₀ + U ≤ P := by
    dsimp [P, normalizedPrecision, L₀, U]
    omega
  have hpower : 2 ^ (L₀ + U) ≤ 2 ^ P :=
    Nat.pow_le_pow_right (by norm_num) hexponents
  exact (Nat.not_lt_of_ge hlower) (hcoreSmall.trans_le hpower)

/-- QM116b: the sharper 971-budget turns a failed exact future replay at
precision `P` into the improved lower bound `P-V<L₀`. -/
theorem replayFailure_tight971Margin_lt_initialDigits
    (g : Ray) (q R length : ℕ) (hq : 5 ≤ q)
    (hbudget : tight971Budget g q ≤ normalizedPrecision g q R)
    (hprecision : normalizedPrecision g q R ≤
      EtherCounterResidueBound.binaryMass (shiftedBranch g q) 0 length)
    (hfail : ∀ pref : EtherCounterResidueBound.NaturalPrefix
      (shiftedBranch g q) length,
      pref.core 0 ≠
        (EtherCounterResidueBound.initialResidue (shiftedBranch g q)
          (normalizedPrecision g q R) length).val) :
    normalizedPrecision g q R - tight971Budget g q <
      (Nat.log 2 (g.core 0)).succ := by
  let P := normalizedPrecision g q R
  let V := tight971Budget g q
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let pref := shiftedNaturalPrefix g q length
  have hlower : 2 ^ P ≤ g.core (3 * q) := by
    simpa [P, pref, shiftedNaturalPrefix] using
      EtherCounterResidueBound.initial_core_ge_modulus_of_least_residue_fails
        (branch := shiftedBranch g q) (length := length) (P := P)
        (by simpa [P] using hprecision)
        (by simpa [P] using hfail) pref
  have hcoreDigits := g.core_binaryDigits_le_initial_add_tight971Budget q hq
  have hcoreSmall : g.core (3 * q) < 2 ^ (L₀ + V) := by
    have hself : g.core (3 * q) <
        2 ^ (Nat.log 2 (g.core (3 * q))).succ :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    exact hself.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by simpa [L₀, V] using hcoreDigits))
  by_contra hnot
  push Not at hnot
  have hVP : V ≤ P := by simpa [V, P] using hbudget
  have hexponents : L₀ + V ≤ P := by omega
  have hpower : 2 ^ (L₀ + V) ≤ 2 ^ P :=
    Nat.pow_le_pow_right (by norm_num) hexponents
  exact (Nat.not_lt_of_ge hlower) (hcoreSmall.trans_le hpower)

/-- Replay-free QM116b.  It is enough for the raw forced future residue to
miss the immediately preceding EC17 congruence modulo the corresponding
power of three.  The congruence is stated with its invertible power of two
left in place, so no modular-inverse convention enters the Lean interface. -/
theorem predecessorCongruenceFailure_tight971Margin_lt_initialDigits
    (g : Ray) (q R length : ℕ) (hq : 5 ≤ q)
    (hbudget : tight971Budget g q ≤ normalizedPrecision g q R)
    (hprecision : normalizedPrecision g q R ≤
      EtherCounterResidueBound.binaryMass (shiftedBranch g q) 0 length)
    (hfail : ¬
      2 ^ (8 * g.branch (3 * q) + 15) *
          (shiftedInitialResidue g q R length).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)]) :
    normalizedPrecision g q R - tight971Budget g q <
      (Nat.log 2 (g.core 0)).succ := by
  let P := normalizedPrecision g q R
  let V := tight971Budget g q
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let pref := shiftedNaturalPrefix g q length
  have hcoreDigits := g.core_binaryDigits_le_initial_add_tight971Budget q hq
  by_contra hnot
  push Not at hnot
  have hVP : V ≤ P := by simpa [V, P] using hbudget
  have hexponents : L₀ + V ≤ P := by omega
  have hcoreSmall : g.core (3 * q) < 2 ^ P := by
    have hself : g.core (3 * q) <
        2 ^ (Nat.log 2 (g.core (3 * q))).succ :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hbitsBudget :
        (Nat.log 2 (g.core (3 * q))).succ ≤ L₀ + V := by
      simpa [L₀, V] using hcoreDigits
    have hbitsP : (Nat.log 2 (g.core (3 * q))).succ ≤ P :=
      hbitsBudget.trans hexponents
    exact hself.trans_le (Nat.pow_le_pow_right (by norm_num) hbitsP)
  have heq0 := EtherCounterResidueBound.initialResidue_val_eq_initial_core
    pref P (by simpa [P, pref, shiftedNaturalPrefix] using hprecision)
      (by simpa [pref, shiftedNaturalPrefix] using hcoreSmall)
  have heq : (shiftedInitialResidue g q R length).val = g.core (3 * q) := by
    simpa [shiftedInitialResidue, P, pref, shiftedNaturalPrefix,
      normalizedPrecision] using heq0
  have hindex : 3 * q - 1 + 1 = 3 * q := by omega
  have hcoreMod := EtherCounterResidueBound.ec17_successor_mul_modEq
    (g.branch (3 * q - 1)) (g.branch (3 * q))
      (g.core (3 * q - 1)) (g.core (3 * q))
      (by simpa [hindex] using g.balance (3 * q - 1))
  apply hfail
  simpa [heq] using hcoreMod

/-- Cofinal exact replay failures exclude a period-three ray.  This theorem
asserts no computational failure and no unboundedness result: it only turns a
supplied unbounded family of formally stated finite failures into `False`. -/
theorem false_of_unbounded_replayFailures
    (g : Ray) (q R length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hprecision : ∀ j, normalizedPrecision g (q j) (R j) ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g (q j)) 0 (length j))
    (hfail : ∀ j
      (pref : EtherCounterResidueBound.NaturalPrefix
        (shiftedBranch g (q j)) (length j)),
      pref.core 0 ≠
        (EtherCounterResidueBound.initialResidue (shiftedBranch g (q j))
          (normalizedPrecision g (q j) (R j)) (length j)).val)
    (hunbounded : ∀ M, ∃ j, M < R j) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbound := g.replayFailure_padding_lt_initialDigits
    (q j) (R j) (length j) (hq j) (hprecision j) (hfail j)
  omega

/-- Cofinal QM116 replay consumer: unbounded tightened margins `P-V` among
exact failed rows exclude the ray. -/
theorem false_of_unbounded_tight971ReplayFailureMargins
    (g : Ray) (q R length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbudget : ∀ j, tight971Budget g (q j) ≤
      normalizedPrecision g (q j) (R j))
    (hprecision : ∀ j, normalizedPrecision g (q j) (R j) ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g (q j)) 0 (length j))
    (hfail : ∀ j
      (pref : EtherCounterResidueBound.NaturalPrefix
        (shiftedBranch g (q j)) (length j)),
      pref.core 0 ≠
        (EtherCounterResidueBound.initialResidue (shiftedBranch g (q j))
          (normalizedPrecision g (q j) (R j)) (length j)).val)
    (hunbounded : ∀ M, ∃ j, M <
      normalizedPrecision g (q j) (R j) - tight971Budget g (q j)) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbound := g.replayFailure_tight971Margin_lt_initialDigits
    (q j) (R j) (length j) (hq j) (hbudget j) (hprecision j) (hfail j)
  omega

/-- Cofinal replay-free QM116 consumer using only failure of the immediate
predecessor congruence for the raw future residue. -/
theorem false_of_unbounded_tight971PredecessorFailureMargins
    (g : Ray) (q R length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbudget : ∀ j, tight971Budget g (q j) ≤
      normalizedPrecision g (q j) (R j))
    (hprecision : ∀ j, normalizedPrecision g (q j) (R j) ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g (q j)) 0 (length j))
    (hfail : ∀ j, ¬
      2 ^ (8 * g.branch (3 * q j) + 15) *
          (shiftedInitialResidue g (q j) (R j) (length j)).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hunbounded : ∀ M, ∃ j, M <
      normalizedPrecision g (q j) (R j) - tight971Budget g (q j)) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbound :=
    g.predecessorCongruenceFailure_tight971Margin_lt_initialDigits
      (q j) (R j) (length j) (hq j) (hbudget j) (hprecision j) (hfail j)
  omega

/-! ## Normalized predecessor/future CRT failures -/

/-- QM106: a failed canonical CRT representative at the theorem-forced
binary precision bounds the immediately preceding ternary exponent by the
one fixed initial-core bit length.

The predicate `Required` deliberately remains abstract.  A checker may
instantiate it with exact EC17 replay, but Lean only promotes a row after it
receives both residue congruences, the canonical product bound, success of
the genuine core, and failure of the candidate. -/
theorem normalizedCRTFailure_predecessorExponent_lt_initialDigits
    (g : Ray) (q candidate : ℕ) (Required : ℕ → Prop) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hrequired : Required (g.core (3 * q)))
    (hfail : ¬ Required candidate) :
    6 * g.branch (3 * q - 1) + 11 <
      (Nat.log 2 (g.core 0)).succ := by
  let U := sharpUpperBudget g q
  let E := 6 * g.branch (3 * q - 1) + 11
  let L₀ := (Nat.log 2 (g.core 0)).succ
  have hcoprime : (2 ^ U).Coprime (3 ^ E) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  have hlower : 2 ^ U * 3 ^ E ≤ g.core (3 * q) := by
    apply EtherCounterResidueBound.coprime_residue_failure_forces_product_lower_bound
      (m := 2 ^ U) (n := 3 ^ E) (candidate := candidate)
      (x := g.core (3 * q)) (Required := Required) hcoprime
    · simpa [U] using hbinary
    · simpa [E] using hternary
    · simpa [U, E] using hcandidate
    · exact hrequired
    · exact hfail
  have hupper : g.core (3 * q) < 2 ^ (U + L₀) := by
    simpa [U, L₀] using
      g.core_lt_two_pow_upperBudget_add_initialDigits q hq
  have hproduct : 2 ^ U * 3 ^ E < 2 ^ U * 2 ^ L₀ := by
    calc
      2 ^ U * 3 ^ E ≤ g.core (3 * q) := hlower
      _ < 2 ^ (U + L₀) := hupper
      _ = 2 ^ U * 2 ^ L₀ := by rw [pow_add]
  have hthree_lt_two : 3 ^ E < 2 ^ L₀ :=
    (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ U)).mp hproduct
  change E < L₀
  by_contra hnot
  push Not at hnot
  have htwo_mono : 2 ^ L₀ ≤ 2 ^ E :=
    Nat.pow_le_pow_right (by norm_num) hnot
  have htwo_lt_three : 2 ^ E < 3 ^ E :=
    Nat.pow_lt_pow_left (by norm_num) (by dsimp [E]; omega)
  omega

/-- Replay-specialized QM106.  Here `Required` is no longer an arbitrary
predicate: it is exactly existence of a positive natural EC17 prefix on the
shifted future schedule. -/
theorem normalizedCRTFailure_predecessorExponent_lt_initialDigits_of_noPrefix
    (g : Ray) (q candidate length : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hfail : ¬ EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g q) length candidate) :
    6 * g.branch (3 * q - 1) + 11 <
      (Nat.log 2 (g.core 0)).succ := by
  apply g.normalizedCRTFailure_predecessorExponent_lt_initialDigits
    q candidate
      (EtherCounterResidueBound.AdmitsNaturalPrefix
        (shiftedBranch g q) length) hq hbinary hternary hcandidate
  · exact g.shiftedCore_admitsNaturalPrefix q length
  · exact hfail

/-- Direct compact-certificate specialization of QM106 for an
under-divisibility replay failure.  This is the kernel endpoint for a worker
row: no expanded list of intermediate cores, and no separately supplied
`AdmitsNaturalPrefix` negation, is required. -/
theorem normalizedCRTFailure_predecessorExponent_lt_initialDigits_of_compactNondivisible
    (g : Ray) (q candidate length : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (certificate :
      EtherCounterResidueBound.CompactNondivisibleReplayFailure
        (shiftedBranch g q) candidate)
    (hstep : certificate.step < length) :
    6 * g.branch (3 * q - 1) + 11 <
      (Nat.log 2 (g.core 0)).succ := by
  apply g.normalizedCRTFailure_predecessorExponent_lt_initialDigits_of_noPrefix
    q candidate length hq hbinary hternary hcandidate
  exact certificate.not_admitsNaturalPrefix hstep

/-- Direct compact-certificate specialization of QM106 for an even terminal
quotient.  The explicit `step+1<length` premise preserves the necessary
off-by-one distinction from under-divisibility. -/
theorem normalizedCRTFailure_predecessorExponent_lt_initialDigits_of_compactEven
    (g : Ray) (q candidate length : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (certificate :
      EtherCounterResidueBound.CompactEvenQuotientReplayFailure
        (shiftedBranch g q) candidate)
    (hnext : certificate.step + 1 < length) :
    6 * g.branch (3 * q - 1) + 11 <
      (Nat.log 2 (g.core 0)).succ := by
  apply g.normalizedCRTFailure_predecessorExponent_lt_initialDigits_of_noPrefix
    q candidate length hq hbinary hternary hcandidate
  exact certificate.not_admitsNaturalPrefix hnext

/-! ## Replay-free normalized CRT margins -/

/-- Bit-length form behind QM108.  A positive canonical CRT representative
cannot use more bits than the theorem-forced growth budget plus the one fixed
initial-core bit length, independently of whether it replays. -/
theorem normalizedCRT_candidate_binaryDigits_le
    (g : Ray) (q candidate : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcandidate_pos : 0 < candidate) :
    (Nat.log 2 candidate).succ ≤
      sharpUpperBudget g q + (Nat.log 2 (g.core 0)).succ := by
  let U := sharpUpperBudget g q
  let E := 6 * g.branch (3 * q - 1) + 11
  let L₀ := (Nat.log 2 (g.core 0)).succ
  have hcoreUpper : g.core (3 * q) < 2 ^ (U + L₀) := by
    simpa [U, L₀] using
      g.core_lt_two_pow_upperBudget_add_initialDigits q hq
  by_contra hbad
  push Not at hbad
  have hexponents : U + L₀ ≤ Nat.log 2 candidate := by
    omega
  have hbudgetPow : 2 ^ (U + L₀) ≤ 2 ^ Nat.log 2 candidate :=
    Nat.pow_le_pow_right (by norm_num) hexponents
  have hlogPow : 2 ^ Nat.log 2 candidate ≤ candidate :=
    Nat.pow_log_le_self 2 hcandidate_pos.ne'
  have hcore_lt_candidate : g.core (3 * q) < candidate :=
    hcoreUpper.trans_le (hbudgetPow.trans hlogPow)
  have hcoprime : (2 ^ U).Coprime (3 ^ E) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  have hproductMod : g.core (3 * q) ≡ candidate
      [MOD (2 ^ U) * (3 ^ E)] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).1
      ⟨by simpa [U] using hbinary, by simpa [E] using hternary⟩
  have heq : g.core (3 * q) = candidate :=
    hproductMod.eq_of_lt_of_lt
      (hcore_lt_candidate.trans (by simpa [U, E] using hcandidate))
      (by simpa [U, E] using hcandidate)
  exact (ne_of_lt hcore_lt_candidate) heq

def normalizedCRTMargin (g : Ray) (q candidate : ℕ) : ℕ :=
  (Nat.log 2 candidate).succ - sharpUpperBudget g q

/-- The coefficient of the binary CRT modulus in a canonical representative.
Writing the candidate as `r₂ + 2^U * lift`, this quotient is either `lift`
or `lift` plus the harmless quotient of `r₂`; for the canonical binary
residue `r₂<2^U` it is exactly `lift`. -/
def normalizedCRTLift (g : Ray) (q candidate : ℕ) : ℕ :=
  candidate / 2 ^ sharpUpperBudget g q

/-- Exact search simplification: for a canonical CRT representative at
binary precision `U`, lift zero is equivalent to the raw forced future
residue itself satisfying the immediate predecessor congruence.  Thus the
eventual-zero hinge can be tested without constructing the product-modulus
CRT candidate. -/
theorem normalizedCRTLift_eq_zero_iff_shiftedResidue_predecessorCongruence
    (g : Ray) (q length candidate : ℕ)
    (hbinary : (shiftedInitialResidue g q 0 length).val ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary :
      2 ^ (8 * g.branch (3 * q) + 15) * candidate ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11)) :
    normalizedCRTLift g q candidate = 0 ↔
      2 ^ (8 * g.branch (3 * q) + 15) *
          (shiftedInitialResidue g q 0 length).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)] := by
  let U := sharpUpperBudget g q
  let E := 6 * g.branch (3 * q - 1) + 11
  let A := 8 * g.branch (3 * q) + 15
  let residue := (shiftedInitialResidue g q 0 length).val
  have hresidue : residue < 2 ^ U := by
    simpa [residue, U, shiftedInitialResidue, normalizedPrecision] using
      ZMod.val_lt (shiftedInitialResidue g q 0 length)
  have hmoduli : (2 ^ U).Coprime (3 ^ E) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  constructor
  · intro hlift
    have hcandSmall : candidate < 2 ^ U := by
      have hor : 2 ^ U = 0 ∨ candidate < 2 ^ U :=
        Nat.div_eq_zero_iff.mp (by
          simpa [normalizedCRTLift, U] using hlift)
      exact hor.resolve_left (by positivity)
    have hbinary' : residue ≡ candidate [MOD 2 ^ U] := by
      simpa [U, residue] using hbinary
    have heq : residue = candidate :=
      hbinary'.eq_of_lt_of_lt hresidue hcandSmall
    simpa [A, E, residue, heq] using hternary
  · intro hresidueTernary
    have hcandidateTernary : 2 ^ A * candidate ≡ 17 [MOD 3 ^ E] := by
      simpa [A, E] using hternary
    have hresidueTernary' : 17 ≡ 2 ^ A * residue [MOD 3 ^ E] := by
      simpa [A, E, residue] using hresidueTernary.symm
    have hmul : 2 ^ A * candidate ≡ 2 ^ A * residue [MOD 3 ^ E] :=
      hcandidateTernary.trans hresidueTernary'
    have hcancelCoprime : Nat.gcd (3 ^ E) (2 ^ A) = 1 :=
      ((by norm_num : Nat.Coprime 3 2).pow _ _).gcd_eq_one
    have hternaryPair : candidate ≡ residue [MOD 3 ^ E] :=
      Nat.ModEq.cancel_left_of_coprime hcancelCoprime hmul
    have hproductMod : candidate ≡ residue [MOD (2 ^ U) * (3 ^ E)] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hmoduli).1
        ⟨by simpa [U, residue] using hbinary.symm, hternaryPair⟩
    have hresidueProduct : residue < 2 ^ U * 3 ^ E := by
      exact hresidue.trans_le (Nat.le_mul_of_pos_right _ (by positivity))
    have heq : candidate = residue :=
      hproductMod.eq_of_lt_of_lt
        (by simpa [U, E] using hcandidate) hresidueProduct
    rw [normalizedCRTLift, heq]
    exact Nat.div_eq_of_lt (by simpa [U] using hresidue)

/-- A hypothetical period-three ray eventually forces the raw finite-future
residue to satisfy the predecessor congruence, provided the finite prefix
contains enough binary mass to determine that residue.  This removes the CRT
candidate entirely from the asymptotic arithmetic hinge. -/
theorem shiftedInitialResidue_eventually_predecessorCongruence
    (g : Ray) (length : ℕ → ℕ)
    (hprecision : ∀ q, normalizedPrecision g q 0 ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g q) 0 (length q)) :
    ∃ Q, ∀ q, Q ≤ q →
      2 ^ (8 * g.branch (3 * q) + 15) *
          (shiftedInitialResidue g q 0 (length q)).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)] := by
  obtain ⟨Qcore, hcore⟩ := g.eventually_core_lt_two_pow_upperBudget
  refine ⟨max 1 Qcore, ?_⟩
  intro q hq
  have hq_pos : 1 ≤ q := (le_max_left 1 Qcore).trans hq
  have hQcore : Qcore ≤ q := (le_max_right 1 Qcore).trans hq
  have hsmall : g.core (3 * q) < 2 ^ normalizedPrecision g q 0 := by
    simpa [normalizedPrecision] using hcore q hQcore
  have heq : (shiftedInitialResidue g q 0 (length q)).val =
      g.core (3 * q) := by
    simpa [shiftedInitialResidue, shiftedNaturalPrefix] using
      EtherCounterResidueBound.initialResidue_val_eq_initial_core
        (shiftedNaturalPrefix g q (length q)) (normalizedPrecision g q 0)
          (by simpa [shiftedNaturalPrefix] using hprecision q)
          (by simpa [shiftedNaturalPrefix] using hsmall)
  have hindex : 3 * q - 1 + 1 = 3 * q := by omega
  have hbalance :
      2 ^ (8 * g.branch (3 * q) + 15) * g.core (3 * q) =
        3 ^ (6 * g.branch (3 * q - 1) + 11) * g.core (3 * q - 1) + 17 := by
    simpa [hindex] using g.balance (3 * q - 1)
  rw [heq, hbalance]
  exact (Nat.modEq_modulus_mul_add_iff.mpr (Nat.ModEq.refl 17)).symm

/-- The cheapest visible consequence of the predecessor congruence: because
its power-of-two exponent is odd, the shifted residue must be `1 mod 3`.
This is the exact theorem interface for the worker's one-trit diagnostic. -/
theorem shiftedInitialResidue_mod_three_eq_one_of_predecessorCongruence
    (g : Ray) (q R length : ℕ)
    (hcongruence :
      2 ^ (8 * g.branch (3 * q) + 15) *
          (shiftedInitialResidue g q R length).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)]) :
    (shiftedInitialResidue g q R length).val % 3 = 1 := by
  let residue := (shiftedInitialResidue g q R length).val
  let A := 8 * g.branch (3 * q) + 15
  let E := 6 * g.branch (3 * q - 1) + 11
  have hthreeDvd : 3 ∣ 3 ^ E :=
    dvd_pow (dvd_refl 3) (by dsimp [E]; omega)
  have hmod3 : 2 ^ A * residue ≡ 17 [MOD 3] :=
    Nat.ModEq.of_dvd hthreeDvd (by simpa [A, E, residue] using hcongruence)
  have htwo8 : 2 ^ 8 ≡ 1 [MOD 3] := by norm_num
  have htwo15 : 2 ^ 15 ≡ 2 [MOD 3] := by norm_num
  have htwoA : 2 ^ A ≡ 2 [MOD 3] := by
    have hpow : (2 ^ 8) ^ g.branch (3 * q) * 2 ^ 15 ≡
        1 ^ g.branch (3 * q) * 2 [MOD 3] :=
      (htwo8.pow _).mul htwo15
    simpa [A, pow_mul, pow_add] using hpow
  have hscaled : 2 * residue ≡ 2 * 1 [MOD 3] :=
    ((htwoA.mul_right residue).symm.trans hmod3).trans (by norm_num)
  have hcancel : residue ≡ 1 [MOD 3] :=
    Nat.ModEq.cancel_left_of_coprime (by norm_num) hscaled
  simpa [Nat.ModEq] using hcancel

/-- Direct no-ray consumer for the candidate-free formulation: arbitrarily
late failures of the raw predecessor congruence contradict the eventual
congruence forced by every period-three ray. -/
theorem false_of_cofinally_failed_shiftedResidue_predecessorCongruence
    (g : Ray) (length : ℕ → ℕ)
    (hprecision : ∀ q, normalizedPrecision g q 0 ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g q) 0 (length q))
    (hfail : ∀ Q, ∃ q, Q ≤ q ∧ ¬
      2 ^ (8 * g.branch (3 * q) + 15) *
          (shiftedInitialResidue g q 0 (length q)).val ≡ 17
        [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)]) :
    False := by
  obtain ⟨Q, heventual⟩ :=
    g.shiftedInitialResidue_eventually_predecessorCongruence length hprecision
  obtain ⟨q, hQq, hne⟩ := hfail Q
  exact hne (heventual q hQq)

/-- Even the first ternary digit is enough: if the canonical shifted residue
is not `1 mod 3` at arbitrarily late cycle boundaries, no period-three ray
can realize the schedule. -/
theorem false_of_cofinally_shiftedInitialResidue_mod_three_ne_one
    (g : Ray) (length : ℕ → ℕ)
    (hprecision : ∀ q, normalizedPrecision g q 0 ≤
      EtherCounterResidueBound.binaryMass
        (shiftedBranch g q) 0 (length q))
    (hfail : ∀ Q, ∃ q, Q ≤ q ∧
      (shiftedInitialResidue g q 0 (length q)).val % 3 ≠ 1) :
    False := by
  apply g.false_of_cofinally_failed_shiftedResidue_predecessorCongruence
    length hprecision
  intro Q
  obtain ⟨q, hQq, hmod3⟩ := hfail Q
  refine ⟨q, hQq, ?_⟩
  intro hcongruence
  exact hmod3
    (g.shiftedInitialResidue_mod_three_eq_one_of_predecessorCongruence
      q 0 (length q) hcongruence)

/-- QM108: the replay-free normalized candidate margin lower-bounds the
same fixed initial-core bit length. -/
theorem normalizedCRT_candidateMargin_le_initialDigits
    (g : Ray) (q candidate : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcandidate_pos : 0 < candidate) :
    normalizedCRTMargin g q candidate ≤
      (Nat.log 2 (g.core 0)).succ := by
  have hbits := g.normalizedCRT_candidate_binaryDigits_le q candidate hq
    hbinary hternary hcandidate hcandidate_pos
  change (Nat.log 2 candidate).succ - sharpUpperBudget g q ≤
    (Nat.log 2 (g.core 0)).succ
  omega

/-- Under a hypothetical ray, every normalized CRT lift lies in one fixed
finite set whose size depends only on the initial core.  This is the exact
pigeonhole form of the missing arithmetic obstruction: unbounded computed
margins are equivalent to escaping every such finite lift alphabet. -/
theorem normalizedCRTLift_lt_two_pow_initialDigits
    (g : Ray) (q candidate : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcandidate_pos : 0 < candidate) :
    normalizedCRTLift g q candidate <
      2 ^ (Nat.log 2 (g.core 0)).succ := by
  let U := sharpUpperBudget g q
  let L₀ := (Nat.log 2 (g.core 0)).succ
  have hbits := g.normalizedCRT_candidate_binaryDigits_le q candidate hq
    hbinary hternary hcandidate hcandidate_pos
  have hcandBits : candidate < 2 ^ (Nat.log 2 candidate).succ :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two candidate
  have hpowers : 2 ^ (Nat.log 2 candidate).succ ≤ 2 ^ (U + L₀) :=
    Nat.pow_le_pow_right (by norm_num) (by simpa [U, L₀] using hbits)
  have hcandProduct : candidate < 2 ^ L₀ * 2 ^ U := by
    calc
      candidate < 2 ^ (Nat.log 2 candidate).succ := hcandBits
      _ ≤ 2 ^ (U + L₀) := hpowers
      _ = 2 ^ L₀ * 2 ^ U := by rw [pow_add]; ac_rfl
  exact (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ U)).2
    (by simpa [normalizedCRTLift, U, L₀] using hcandProduct)

/-- If a period-three ray existed, the normalized CRT lift would take one
fixed value at arbitrarily late cycle indices.  Therefore the replay-free
search can be attacked one fixed lift at a time; proving that every fixed
lift occurs only finitely often is enough to exclude the ray. -/
theorem exists_cofinally_constant_normalizedCRTLift
    (g : Ray) (candidate : ℕ → ℕ)
    (hbinary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : ∀ q, candidate q <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcandidate_pos : ∀ q, 0 < candidate q) :
    ∃ lift < 2 ^ (Nat.log 2 (g.core 0)).succ,
      ∀ N, ∃ n, N < n ∧
        normalizedCRTLift g (n + 5) (candidate (n + 5)) = lift := by
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let lifts : ℕ → Fin (2 ^ L₀) := fun n =>
    ⟨normalizedCRTLift g (n + 5) (candidate (n + 5)),
      g.normalizedCRTLift_lt_two_pow_initialDigits
        (n + 5) (candidate (n + 5)) (by omega)
        (hbinary (n + 5)) (hternary (n + 5))
        (hcandidate (n + 5)) (hcandidate_pos (n + 5))⟩
  obtain ⟨lift, hinfinite⟩ := Finite.exists_infinite_fiber lifts
  refine ⟨lift, by simpa [L₀] using lift.isLt, ?_⟩
  have hset : ({n : ℕ | lifts n = lift} : Set ℕ).Infinite := by
    rw [show {n : ℕ | lifts n = lift} = lifts ⁻¹' ({lift} : Set (Fin (2 ^ L₀))) by
      ext n
      simp]
    exact Set.infinite_coe_iff.mp hinfinite
  intro N
  obtain ⟨n, hnmem, hn⟩ := hset.exists_gt N
  refine ⟨n, hn, ?_⟩
  simpa [lifts] using congrArg Fin.val hnmem

/-- Fixed-lift exclusion principle.  It is enough to prove, separately for
each natural lift, that the canonical CRT construction eventually avoids
that lift.  No uniform avoidance bound in the lift is required.  This is
strictly weaker in shape than a full multi-value linear-independence theorem
and isolates a possible fixed-linear-form route beyond the 1989 threshold. -/
theorem false_of_eventually_avoids_each_normalizedCRTLift
    (g : Ray) (candidate : ℕ → ℕ)
    (hbinary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : ∀ q, candidate q <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcandidate_pos : ∀ q, 0 < candidate q)
    (havoid : ∀ lift, ∃ N, ∀ n, N < n →
      normalizedCRTLift g (n + 5) (candidate (n + 5)) ≠ lift) :
    False := by
  obtain ⟨lift, _hlift, hcofinal⟩ :=
    g.exists_cofinally_constant_normalizedCRTLift candidate
      hbinary hternary hcandidate hcandidate_pos
  obtain ⟨N, hN⟩ := havoid lift
  obtain ⟨n, hn, heq⟩ := hcofinal N
  exact hN n hn heq

/-- QM109: unbounded replay-free normalized CRT margins exclude a
period-three ray.  No replay predicate or failure certificate is assumed. -/
theorem false_of_unbounded_normalizedCRTMargins
    (g : Ray) (q candidate : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbinary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 2 ^ sharpUpperBudget g (q j)])
    (hternary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hcandidate : ∀ j, candidate j <
      2 ^ sharpUpperBudget g (q j) *
        3 ^ (6 * g.branch (3 * q j - 1) + 11))
    (hcandidate_pos : ∀ j, 0 < candidate j)
    (hunbounded : ∀ M, ∃ j, M <
      normalizedCRTMargin g (q j) (candidate j)) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbound := g.normalizedCRT_candidateMargin_le_initialDigits
    (q j) (candidate j) (hq j) (hbinary j) (hternary j)
      (hcandidate j) (hcandidate_pos j)
  omega

/-- Converse/completeness form of the normalized CRT test.  Once the growing
predecessor exponent reaches the fixed initial-core bit length, the canonical
representative is not merely compatible with a hypothetical ray: it is the
actual cycle-boundary core. -/
theorem normalizedCRT_candidate_eq_core_of_initialDigits_le_predecessorExponent
    (g : Ray) (q candidate : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hthreshold : (Nat.log 2 (g.core 0)).succ ≤
      6 * g.branch (3 * q - 1) + 11) :
    g.core (3 * q) = candidate := by
  let U := sharpUpperBudget g q
  let E := 6 * g.branch (3 * q - 1) + 11
  let L₀ := (Nat.log 2 (g.core 0)).succ
  have hcoreUpper : g.core (3 * q) < 2 ^ (U + L₀) := by
    simpa [U, L₀] using
      g.core_lt_two_pow_upperBudget_add_initialDigits q hq
  have htwoPowers : 2 ^ (U + L₀) ≤ 2 ^ U * 2 ^ E := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    simpa [E, L₀] using Nat.add_le_add_left hthreshold U
  have hbasePowers : 2 ^ E < 3 ^ E :=
    Nat.pow_lt_pow_left (by norm_num) (by dsimp [E]; omega)
  have hproductPowers : 2 ^ U * 2 ^ E < 2 ^ U * 3 ^ E :=
    (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ U)).2 hbasePowers
  have hcoreProduct : g.core (3 * q) < 2 ^ U * 3 ^ E :=
    hcoreUpper.trans_le htwoPowers |>.trans hproductPowers
  have hcoprime : (2 ^ U).Coprime (3 ^ E) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  have hproductMod : g.core (3 * q) ≡ candidate
      [MOD (2 ^ U) * (3 ^ E)] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).1
      ⟨by simpa [U] using hbinary, by simpa [E] using hternary⟩
  apply hproductMod.eq_of_lt_of_lt hcoreProduct
  simpa [U, E] using hcandidate

/-- Under the same threshold, the canonical representative admits every
finite shifted natural prefix, since it is the genuine core.  Thus a reported
failure at this point contradicts the hypothetical ray outright. -/
theorem normalizedCRT_candidate_admitsPrefix_of_threshold
    (g : Ray) (q candidate length : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hthreshold : (Nat.log 2 (g.core 0)).succ ≤
      6 * g.branch (3 * q - 1) + 11) :
    EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g q) length candidate := by
  have heq :=
    g.normalizedCRT_candidate_eq_core_of_initialDigits_le_predecessorExponent
      q candidate hq hbinary hternary hcandidate hthreshold
  rw [← heq]
  exact g.shiftedCore_admitsNaturalPrefix q length

/-- The predecessor branch at cycle boundary `q` is already at least `q`.
This is the elementary bridge making unbounded cycle indices sufficient for
the cofinal CRT consumer. -/
theorem cycleIndex_le_predecessorBranch
    (g : Ray) (q : ℕ) (hq : 1 ≤ q) :
    q ≤ g.branch (3 * q - 1) := by
  have hindex : 3 * q - 1 = 3 * (q - 1) + 2 := by omega
  rw [hindex, g.branch_two]
  have hgain : q - 1 ≤ g.cycleGain * (q - 1) :=
    Nat.le_mul_of_pos_left _ g.cycleGain_pos
  have hbase := g.branch_pos 2
  omega

/-- QM112c: for every correctly formed canonical CRT row family, a
hypothetical period-three ray forces the normalized lift to be eventually
exactly zero.  The remaining obstruction is therefore the single arithmetic
claim that lift zero cannot recur forever. -/
theorem normalizedCRT_eventually_zeroLift
    (g : Ray) (candidate : ℕ → ℕ)
    (hbinary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : ∀ q, candidate q <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11)) :
    ∃ Q, ∀ q, Q ≤ q → normalizedCRTLift g q (candidate q) = 0 := by
  obtain ⟨Qcore, hcore⟩ := g.eventually_core_lt_two_pow_upperBudget
  let L₀ := (Nat.log 2 (g.core 0)).succ
  let Q := max 5 (max Qcore L₀)
  refine ⟨Q, ?_⟩
  intro q hq
  have hq5 : 5 ≤ q := (le_max_left 5 (max Qcore L₀)).trans hq
  have hQcore : Qcore ≤ q :=
    (le_max_left Qcore L₀).trans
      ((le_max_right 5 (max Qcore L₀)).trans hq)
  have hL₀q : L₀ ≤ q :=
    (le_max_right Qcore L₀).trans
      ((le_max_right 5 (max Qcore L₀)).trans hq)
  have hbranch : q ≤ g.branch (3 * q - 1) :=
    g.cycleIndex_le_predecessorBranch q (by omega)
  have hthreshold : (Nat.log 2 (g.core 0)).succ ≤
      6 * g.branch (3 * q - 1) + 11 := by
    change L₀ ≤ 6 * g.branch (3 * q - 1) + 11
    omega
  have heq :=
    g.normalizedCRT_candidate_eq_core_of_initialDigits_le_predecessorExponent
      q (candidate q) hq5 (hbinary q) (hternary q) (hcandidate q) hthreshold
  change candidate q / 2 ^ sharpUpperBudget g q = 0
  rw [← heq]
  exact Nat.div_eq_of_lt (hcore q hQcore)

/-- Direct falsifier paired with QM112c: it is enough to produce nonzero
normalized lifts at arbitrarily late cycles.  Eventual nonzeroness is not
required. -/
theorem false_of_cofinally_nonzero_normalizedCRTLift
    (g : Ray) (candidate : ℕ → ℕ)
    (hbinary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : ∀ q, candidate q <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hnonzero : ∀ Q, ∃ q, Q ≤ q ∧
      normalizedCRTLift g q (candidate q) ≠ 0) :
    False := by
  obtain ⟨Q, hzero⟩ :=
    g.normalizedCRT_eventually_zeroLift candidate hbinary hternary hcandidate
  obtain ⟨q, hQq, hne⟩ := hnonzero Q
  exact hne (hzero q hQq)

/-- Search interpretation: after the cycle index itself reaches the fixed
initial bit length, every correctly formed canonical CRT row must replay.
Consequently a hypothetical ray has an eventual all-success tail; observing
arbitrarily late failures is exactly the missing contradiction, not a trend
that follows from finitely many rows. -/
theorem normalizedCRT_candidate_admitsPrefix_of_initialDigits_le_cycleIndex
    (g : Ray) (q candidate length : ℕ) (hq : 5 ≤ q)
    (hbinary : g.core (3 * q) ≡ candidate
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : g.core (3 * q) ≡ candidate
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : candidate <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11))
    (hcycle : (Nat.log 2 (g.core 0)).succ ≤ q) :
    EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g q) length candidate := by
  have hbranch : q ≤ g.branch (3 * q - 1) :=
    g.cycleIndex_le_predecessorBranch q (by omega)
  apply g.normalizedCRT_candidate_admitsPrefix_of_threshold
    q candidate length hq hbinary hternary hcandidate
  omega

/-- Family-level converse to the cofinal-failure consumer: for any supplied
canonical CRT row at every cycle, a hypothetical ray forces an eventual tail
on which every candidate admits the requested finite replay. -/
theorem normalizedCRT_eventually_admitsPrefix
    (g : Ray) (candidate length : ℕ → ℕ)
    (hbinary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 2 ^ sharpUpperBudget g q])
    (hternary : ∀ q, g.core (3 * q) ≡ candidate q
      [MOD 3 ^ (6 * g.branch (3 * q - 1) + 11)])
    (hcandidate : ∀ q, candidate q <
      2 ^ sharpUpperBudget g q *
        3 ^ (6 * g.branch (3 * q - 1) + 11)) :
    ∃ Q, ∀ q, Q ≤ q →
      EtherCounterResidueBound.AdmitsNaturalPrefix
        (shiftedBranch g q) (length q) (candidate q) := by
  let Q := max 5 (Nat.log 2 (g.core 0)).succ
  refine ⟨Q, ?_⟩
  intro q hq
  apply g.normalizedCRT_candidate_admitsPrefix_of_initialDigits_le_cycleIndex
    q (candidate q) (length q) (by simpa [Q] using (le_max_left 5 _).trans hq)
      (hbinary q) (hternary q) (hcandidate q)
  simpa [Q] using (le_max_right 5 (Nat.log 2 (g.core 0)).succ).trans hq

/-- QM107: canonical normalized CRT failures along unbounded cycle indices
exclude the period-three ray.  The family of required predicates may vary by
row; every finite certificate still has to discharge all hypotheses of
QM106 exactly. -/
theorem false_of_unbounded_normalizedCRTFailures
    (g : Ray) (q candidate : ℕ → ℕ) (Required : ℕ → ℕ → Prop)
    (hq : ∀ j, 5 ≤ q j)
    (hbinary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 2 ^ sharpUpperBudget g (q j)])
    (hternary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hcandidate : ∀ j, candidate j <
      2 ^ sharpUpperBudget g (q j) *
        3 ^ (6 * g.branch (3 * q j - 1) + 11))
    (hrequired : ∀ j, Required j (g.core (3 * q j)))
    (hfail : ∀ j, ¬ Required j (candidate j))
    (hunbounded : ∀ M, ∃ j, M < q j) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (Nat.log 2 (g.core 0)).succ
  have hbranch : q j ≤ g.branch (3 * q j - 1) :=
    g.cycleIndex_le_predecessorBranch (q j) (by omega)
  have hbound := g.normalizedCRTFailure_predecessorExponent_lt_initialDigits
    (q j) (candidate j) (Required j) (hq j) (hbinary j) (hternary j)
      (hcandidate j) (hrequired j) (hfail j)
  omega

/-- Replay-specialized QM107.  This is the direct target for the two exact
finite failure-certificate types in `EtherCounterResidueBound`. -/
theorem false_of_unbounded_normalizedCRTReplayFailures
    (g : Ray) (q candidate length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbinary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 2 ^ sharpUpperBudget g (q j)])
    (hternary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hcandidate : ∀ j, candidate j <
      2 ^ sharpUpperBudget g (q j) *
        3 ^ (6 * g.branch (3 * q j - 1) + 11))
    (hfail : ∀ j, ¬ EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g (q j)) (length j) (candidate j))
    (hunbounded : ∀ M, ∃ j, M < q j) :
    False := by
  apply g.false_of_unbounded_normalizedCRTFailures q candidate
    (fun j => EtherCounterResidueBound.AdmitsNaturalPrefix
      (shiftedBranch g (q j)) (length j)) hq hbinary hternary hcandidate
  · intro j
    exact g.shiftedCore_admitsNaturalPrefix (q j) (length j)
  · exact hfail
  · exact hunbounded

/-- Cofinal compact under-divisibility certificates exclude a period-three
ray.  Every row remains independently kernel-checkable from one composed
replay identity and one failed divisibility test. -/
theorem false_of_unbounded_normalizedCRTCompactNondivisibleFailures
    (g : Ray) (q candidate length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbinary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 2 ^ sharpUpperBudget g (q j)])
    (hternary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hcandidate : ∀ j, candidate j <
      2 ^ sharpUpperBudget g (q j) *
        3 ^ (6 * g.branch (3 * q j - 1) + 11))
    (certificate : ∀ j,
      EtherCounterResidueBound.CompactNondivisibleReplayFailure
        (shiftedBranch g (q j)) (candidate j))
    (hstep : ∀ j, (certificate j).step < length j)
    (hunbounded : ∀ M, ∃ j, M < q j) :
    False := by
  apply g.false_of_unbounded_normalizedCRTReplayFailures
    q candidate length hq hbinary hternary hcandidate
  · intro j
    exact (certificate j).not_admitsNaturalPrefix (hstep j)
  · exact hunbounded

/-- Cofinal compact even-quotient certificates exclude a period-three ray.
The family interface retains the extra-transition guard on every row. -/
theorem false_of_unbounded_normalizedCRTCompactEvenFailures
    (g : Ray) (q candidate length : ℕ → ℕ)
    (hq : ∀ j, 5 ≤ q j)
    (hbinary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 2 ^ sharpUpperBudget g (q j)])
    (hternary : ∀ j, g.core (3 * q j) ≡ candidate j
      [MOD 3 ^ (6 * g.branch (3 * q j - 1) + 11)])
    (hcandidate : ∀ j, candidate j <
      2 ^ sharpUpperBudget g (q j) *
        3 ^ (6 * g.branch (3 * q j - 1) + 11))
    (certificate : ∀ j,
      EtherCounterResidueBound.CompactEvenQuotientReplayFailure
        (shiftedBranch g (q j)) (candidate j))
    (hnext : ∀ j, (certificate j).step + 1 < length j)
    (hunbounded : ∀ M, ∃ j, M < q j) :
    False := by
  apply g.false_of_unbounded_normalizedCRTReplayFailures
    q candidate length hq hbinary hternary hcandidate
  · intro j
    exact (certificate j).not_admitsNaturalPrefix (hnext j)
  · exact hunbounded

set_option maxRecDepth 1000

/-- An explicit superlinear endpoint for the literal core size.  Given any
starting cycle `Q` and affine bit budget `C*q+B`, the displayed cycle already
exceeds that budget.  This rejects fixed-output-rate literal encodings; it
does not reject a compressed symbolic representation of the growing core. -/
theorem binaryDigits_exceeds_affine_after
    (g : Ray) (Q C B : ℕ) :
    let q := Q + C + B + 5
    Q ≤ q ∧ C * q + B < (Nat.log 2 (g.core (3 * q))).succ := by
  let q := Q + C + B + 5
  have hq : 5 ≤ q := by simp [q]
  have hQ : Q ≤ q := by dsimp [q]; omega
  have hC : C ≤ q := by dsimp [q]; omega
  have hB : B ≤ q := by dsimp [q]; omega
  have hq_pos : 0 < q := by omega
  have hCq : C * q ≤ q * q := Nat.mul_le_mul_right q hC
  have hBq : B ≤ q * q := by nlinarith
  have hbudget : 41 * (C * q + B) ≤ q * (84 * q + 23) := by
    nlinarith
  have hgain : 84 * q - 412 ≤
      g.cycleGain * (84 * q - 412) :=
    Nat.le_mul_of_pos_left _ g.cycleGain_pos
  have hinner : 84 * q + 23 ≤
      435 + g.cycleGain * (84 * q - 412) := by
    omega
  have hexponent : 41 * (C * q + B) ≤
      q * (435 + g.cycleGain * (84 * q - 412)) :=
    hbudget.trans (Nat.mul_le_mul_left q hinner)
  have hdiv : C * q + B ≤
      (q * (435 + g.cycleGain * (84 * q - 412))) / 41 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 41)).2
    simpa [mul_comm] using hexponent
  refine ⟨hQ, hdiv.trans_lt (g.quadratic_binaryDigits_growth q hq)⟩

/-- Consequently no period-three survivor has an eventually affine upper
bound on the ordinary binary length of its core. -/
theorem no_eventually_affine_binaryDigits_bound
    (g : Ray) (Q C B : ℕ) :
    ¬ ∀ q, Q ≤ q →
      (Nat.log 2 (g.core (3 * q))).succ ≤ C * q + B := by
  intro hlinear
  obtain ⟨hQ, hgrowth⟩ := g.binaryDigits_exceeds_affine_after Q C B
  exact (not_lt_of_ge (hlinear _ hQ)) hgrowth

def binaryScale (g : Ray) : ℕ := 2 ^ (8 * g.cycleGain)
def ternaryScale (g : Ray) : ℕ := 3 ^ (6 * g.cycleGain)

def binaryPhase0 (g : Ray) : ℕ := 2 ^ (8 * g.branch 1 + 15)
def binaryPhase1 (g : Ray) : ℕ := 2 ^ (8 * g.branch 2 + 15)
/-- The third binary phase reads the next cycle's phase-zero branch. -/
def binaryPhase2 (g : Ray) : ℕ :=
  2 ^ (8 * (g.branch 0 + g.cycleGain) + 15)

def ternaryPhase0 (g : Ray) : ℕ := 3 ^ (6 * g.branch 0 + 11)
def ternaryPhase1 (g : Ray) : ℕ := 3 ^ (6 * g.branch 1 + 11)
def ternaryPhase2 (g : Ray) : ℕ := 3 ^ (6 * g.branch 2 + 11)

/-- The literal balance rewritten through the public factor definitions. -/
theorem factor_balance (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.binaryFactor t * g.core (t + 1) =
      g.ternaryFactor t * g.core t + 17 := by
  simpa [EtherCounterStateNoRepeat.Orbit.binaryFactor,
    EtherCounterStateNoRepeat.Orbit.ternaryFactor] using g.balance t

/-- Three literal EC17 steps composed before imposing any periodic law. -/
theorem compose_three (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.binaryFactor t * g.binaryFactor (t + 1) * g.binaryFactor (t + 2) *
        g.core (t + 3) =
      g.ternaryFactor t * g.ternaryFactor (t + 1) *
          g.ternaryFactor (t + 2) * g.core t +
        17 * (g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by
  have h0 := factor_balance g t
  have h1 : g.binaryFactor (t + 1) * g.core (t + 2) =
      g.ternaryFactor (t + 1) * g.core (t + 1) + 17 := by
    simpa only [show t + 1 + 1 = t + 2 by omega] using factor_balance g (t + 1)
  have h2 : g.binaryFactor (t + 2) * g.core (t + 3) =
      g.ternaryFactor (t + 2) * g.core (t + 2) + 17 := by
    simpa only [show t + 2 + 1 = t + 3 by omega] using factor_balance g (t + 2)
  calc
    g.binaryFactor t * g.binaryFactor (t + 1) * g.binaryFactor (t + 2) *
          g.core (t + 3) =
        g.binaryFactor t * g.binaryFactor (t + 1) *
          (g.ternaryFactor (t + 2) * g.core (t + 2) + 17) := by
      rw [← h2]
      ring
    _ = g.binaryFactor t * g.ternaryFactor (t + 2) *
          (g.binaryFactor (t + 1) * g.core (t + 2)) +
        17 * (g.binaryFactor t * g.binaryFactor (t + 1)) := by ring
    _ = g.binaryFactor t * g.ternaryFactor (t + 2) *
          (g.ternaryFactor (t + 1) * g.core (t + 1) + 17) +
        17 * (g.binaryFactor t * g.binaryFactor (t + 1)) := by
      rw [h1]
    _ = g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) *
          (g.binaryFactor t * g.core (t + 1)) +
        17 * (g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by ring
    _ = g.ternaryFactor (t + 1) * g.ternaryFactor (t + 2) *
          (g.ternaryFactor t * g.core t + 17) +
        17 * (g.binaryFactor t * g.ternaryFactor (t + 2) +
          g.binaryFactor t * g.binaryFactor (t + 1)) := by
      rw [h0]
    _ = _ := by ring

theorem binaryFactor_zero (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q) = g.binaryPhase0 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 1 = 3 * q + 1 by rfl, g.branch_one q]
  rw [show 8 * (g.branch 1 + g.cycleGain * q) + 15 =
      (8 * g.branch 1 + 15) + (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem binaryFactor_one (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q + 1) =
      g.binaryPhase1 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 1 + 1 = 3 * q + 2 by omega, g.branch_two q]
  rw [show 8 * (g.branch 2 + g.cycleGain * q) + 15 =
      (8 * g.branch 2 + 15) + (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem binaryFactor_two (g : Ray) (q : ℕ) :
    g.toOrbit.binaryFactor (3 * q + 2) =
      g.binaryPhase2 * g.binaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.binaryFactor]
  rw [show 3 * q + 2 + 1 = 3 * (q + 1) by ring, g.branch_zero (q + 1)]
  rw [show 8 * (g.branch 0 + g.cycleGain * (q + 1)) + 15 =
      (8 * (g.branch 0 + g.cycleGain) + 15) +
        (8 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_zero (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q) =
      g.ternaryPhase0 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_zero q]
  rw [show 6 * (g.branch 0 + g.cycleGain * q) + 11 =
      (6 * g.branch 0 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_one (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q + 1) =
      g.ternaryPhase1 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_one q]
  rw [show 6 * (g.branch 1 + g.cycleGain * q) + 11 =
      (6 * g.branch 1 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

theorem ternaryFactor_two (g : Ray) (q : ℕ) :
    g.toOrbit.ternaryFactor (3 * q + 2) =
      g.ternaryPhase2 * g.ternaryScale ^ q := by
  rw [EtherCounterStateNoRepeat.Orbit.ternaryFactor, g.branch_two q]
  rw [show 6 * (g.branch 2 + g.cycleGain * q) + 11 =
      (6 * g.branch 2 + 11) + (6 * g.cycleGain) * q by ring,
    pow_add, pow_mul]
  rfl

/-- QM65: the exact three-phase composition.  The three defect monomials
are `Y^(2q)`, `(XY)^q`, and `X^(2q)` respectively. -/
theorem cycle_balance (g : Ray) (q : ℕ) :
    (g.binaryPhase0 * g.binaryPhase1 * g.binaryPhase2) *
        g.binaryScale ^ (3 * q) * g.core (3 * q + 3) =
      (g.ternaryPhase0 * g.ternaryPhase1 * g.ternaryPhase2) *
          g.ternaryScale ^ (3 * q) * g.core (3 * q) +
        17 * (g.ternaryPhase1 * g.ternaryPhase2 *
            g.ternaryScale ^ (2 * q) +
          g.binaryPhase0 * g.ternaryPhase2 *
            (g.binaryScale * g.ternaryScale) ^ q +
          g.binaryPhase0 * g.binaryPhase1 *
            g.binaryScale ^ (2 * q)) := by
  have h := compose_three g.toOrbit (3 * q)
  rw [g.binaryFactor_zero q, g.binaryFactor_one q, g.binaryFactor_two q,
    g.ternaryFactor_zero q, g.ternaryFactor_one q, g.ternaryFactor_two q] at h
  have hX3 : g.binaryScale ^ (3 * q) = (g.binaryScale ^ q) ^ 3 := by
    rw [show 3 * q = q * 3 by omega, pow_mul]
  have hY3 : g.ternaryScale ^ (3 * q) = (g.ternaryScale ^ q) ^ 3 := by
    rw [show 3 * q = q * 3 by omega, pow_mul]
  have hX2 : g.binaryScale ^ (2 * q) = (g.binaryScale ^ q) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul]
  have hY2 : g.ternaryScale ^ (2 * q) = (g.ternaryScale ^ q) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul]
  rw [hX3, hY3, hX2, hY2, mul_pow]
  convert h using 1 <;> ring

end Ray
end EtherCounterPeriodThree
end KontoroC
