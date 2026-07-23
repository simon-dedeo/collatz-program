/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterStateNoRepeat
import KontoroC.EtherCounterGeometricMahler

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
