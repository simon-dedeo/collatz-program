/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodThree

/-!
# The concrete nine-cycle period-three carry

This file isolates the arithmetic interface QM119 for the period-three EC17
schedule with phases `8,9,10` and cycle gain `2`.  Finite computed carry rows
are deliberately not imported: the remaining all-cycle nondivisibility claim
is an explicit open premise.
-/

namespace KontoroC
namespace EtherCounterNineCycle

open EtherCounterPeriodThree

set_option maxRecDepth 10000

def IsTargetSchedule (g : EtherCounterPeriodThree.Ray) : Prop :=
  g.branch 0 = 8 ∧ g.branch 1 = 9 ∧ g.branch 2 = 10 ∧ g.cycleGain = 2

def cycleBinaryExponent (q : ℕ) : ℕ := 277 + 48 * q
def cycleTernaryExponent (q : ℕ) : ℕ := 195 + 36 * q

def cycleDefect (q : ℕ) : ℕ :=
  17 * (3 ^ (136 + 24 * q) +
    2 ^ (87 + 16 * q) * 3 ^ (71 + 12 * q) +
    2 ^ (182 + 32 * q))

def nineCycleBinaryExponent (q : ℕ) : ℕ := 432 * q + 4221
def nineCycleTernaryExponent (q : ℕ) : ℕ := 324 * q + 3051

def prefixBinaryExponent (q n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, cycleBinaryExponent (q + j)

def prefixTernaryExponent (q n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, cycleTernaryExponent (q + j)

/-- Additive defect after composing `n` complete three-step cycles. -/
def composedDefect (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      3 ^ cycleTernaryExponent (q + n) * composedDefect q n +
        2 ^ prefixBinaryExponent q n * cycleDefect (q + n)

def nineCycleDefect (q : ℕ) : ℕ := composedDefect q 9

theorem prefixBinaryExponent_succ (q n : ℕ) :
    prefixBinaryExponent q (n + 1) =
      prefixBinaryExponent q n + cycleBinaryExponent (q + n) := by
  simp [prefixBinaryExponent, Finset.sum_range_succ]

theorem prefixTernaryExponent_succ (q n : ℕ) :
    prefixTernaryExponent q (n + 1) =
      prefixTernaryExponent q n + cycleTernaryExponent (q + n) := by
  simp [prefixTernaryExponent, Finset.sum_range_succ]

theorem sum_cycleBinaryExponent_nine (q : ℕ) :
    ∑ j ∈ Finset.range 9, cycleBinaryExponent (q + j) =
      nineCycleBinaryExponent q := by
  norm_num [cycleBinaryExponent, nineCycleBinaryExponent,
    Finset.sum_range_succ]
  ring

theorem sum_cycleTernaryExponent_nine (q : ℕ) :
    ∑ j ∈ Finset.range 9, cycleTernaryExponent (q + j) =
      nineCycleTernaryExponent q := by
  norm_num [cycleTernaryExponent, nineCycleTernaryExponent,
    Finset.sum_range_succ]
  ring

/-- The exact one-cycle EC17 identity for the target schedule (QM119a). -/
theorem target_cycle_balance (g : EtherCounterPeriodThree.Ray)
    (hs : IsTargetSchedule g) (q : ℕ) :
    2 ^ cycleBinaryExponent q * g.core (3 * (q + 1)) =
      3 ^ cycleTernaryExponent q * g.core (3 * q) + cycleDefect q := by
  rcases hs with ⟨h0, h1, h2, hK⟩
  have h := g.cycle_balance q
  simp only [EtherCounterPeriodThree.Ray.binaryPhase0,
    EtherCounterPeriodThree.Ray.binaryPhase1,
    EtherCounterPeriodThree.Ray.binaryPhase2,
    EtherCounterPeriodThree.Ray.binaryScale,
    EtherCounterPeriodThree.Ray.ternaryPhase0,
    EtherCounterPeriodThree.Ray.ternaryPhase1,
    EtherCounterPeriodThree.Ray.ternaryPhase2,
    EtherCounterPeriodThree.Ray.ternaryScale] at h
  rw [h0, h1, h2, hK] at h
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  rw [show 3 * q + 3 = 3 * (q + 1) by ring] at h
  have hB :
      (2 ^ 87 * 2 ^ 95 * 2 ^ 95) * (2 ^ 16) ^ (3 * q) =
        2 ^ (277 + 48 * q) := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    ring
  have hA :
      (3 ^ 59 * 3 ^ 65 * 3 ^ 71) * (3 ^ 12) ^ (3 * q) =
        3 ^ (195 + 36 * q) := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    ring
  have hD0 : 3 ^ 65 * 3 ^ 71 * (3 ^ 12) ^ (2 * q) =
      3 ^ (136 + 24 * q) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hD1 : 2 ^ 87 * 3 ^ 71 * (2 ^ 16 * 3 ^ 12) ^ q =
      2 ^ (87 + 16 * q) * 3 ^ (71 + 12 * q) := by
    rw [mul_pow]
    calc
      2 ^ 87 * 3 ^ 71 * ((2 ^ 16) ^ q * (3 ^ 12) ^ q) =
          (2 ^ 87 * (2 ^ 16) ^ q) *
            (3 ^ 71 * (3 ^ 12) ^ q) := by ring
      _ = 2 ^ (87 + 16 * q) * 3 ^ (71 + 12 * q) := by
        rw [← pow_mul, ← pow_add, ← pow_mul, ← pow_add]
  have hD2 : 2 ^ 87 * 2 ^ 95 * (2 ^ 16) ^ (2 * q) =
      2 ^ (182 + 32 * q) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    ring
  simp only [cycleBinaryExponent, cycleTernaryExponent, cycleDefect]
  calc
    2 ^ (277 + 48 * q) * g.core (3 * (q + 1)) =
        (2 ^ 87 * 2 ^ 95 * 2 ^ 95) * (2 ^ 16) ^ (3 * q) *
          g.core (3 * (q + 1)) := by
      rw [hB]
    _ = (3 ^ 59 * 3 ^ 65 * 3 ^ 71) * (3 ^ 12) ^ (3 * q) *
          g.core (3 * q) +
        17 * (3 ^ 65 * 3 ^ 71 * (3 ^ 12) ^ (2 * q) +
          2 ^ 87 * 3 ^ 71 * (2 ^ 16 * 3 ^ 12) ^ q +
          2 ^ 87 * 2 ^ 95 * (2 ^ 16) ^ (2 * q)) := h
    _ = 3 ^ (195 + 36 * q) * g.core (3 * q) +
        17 * (3 ^ (136 + 24 * q) +
          2 ^ (87 + 16 * q) * 3 ^ (71 + 12 * q) +
          2 ^ (182 + 32 * q)) := by
      rw [hA, hD0, hD1, hD2]

/-- Exact composition of any finite number of target cycles, proved directly
from the one-cycle EC17 identity. -/
theorem target_prefix_balance (g : EtherCounterPeriodThree.Ray)
    (hs : IsTargetSchedule g) (q n : ℕ) :
    2 ^ prefixBinaryExponent q n * g.core (3 * (q + n)) =
      3 ^ prefixTernaryExponent q n * g.core (3 * q) +
        composedDefect q n := by
  induction n with
  | zero => simp [prefixBinaryExponent, prefixTernaryExponent, composedDefect]
  | succ n ih =>
      have hnext := target_cycle_balance g hs (q + n)
      rw [prefixBinaryExponent_succ, prefixTernaryExponent_succ,
        pow_add, pow_add]
      simp only [composedDefect]
      rw [show q + (n + 1) = (q + n) + 1 by omega]
      calc
        (2 ^ prefixBinaryExponent q n *
              2 ^ cycleBinaryExponent (q + n)) *
            g.core (3 * ((q + n) + 1)) =
            2 ^ prefixBinaryExponent q n *
              (2 ^ cycleBinaryExponent (q + n) *
                g.core (3 * ((q + n) + 1))) := by ring
        _ = 2 ^ prefixBinaryExponent q n *
              (3 ^ cycleTernaryExponent (q + n) *
                g.core (3 * (q + n)) + cycleDefect (q + n)) := by
          rw [hnext]
        _ = 3 ^ cycleTernaryExponent (q + n) *
              (2 ^ prefixBinaryExponent q n * g.core (3 * (q + n))) +
            2 ^ prefixBinaryExponent q n * cycleDefect (q + n) := by ring
        _ = 3 ^ cycleTernaryExponent (q + n) *
              (3 ^ prefixTernaryExponent q n * g.core (3 * q) +
                composedDefect q n) +
            2 ^ prefixBinaryExponent q n * cycleDefect (q + n) := by
          rw [ih]
        _ = (3 ^ prefixTernaryExponent q n *
              3 ^ cycleTernaryExponent (q + n)) * g.core (3 * q) +
            (3 ^ cycleTernaryExponent (q + n) * composedDefect q n +
              2 ^ prefixBinaryExponent q n * cycleDefect (q + n)) := by ring

/-- The exact nine-cycle composition QM119b.  `nineCycleDefect` is the
recursively audited version of the displayed nine-summand `D9(q)`. -/
theorem target_nineCycle_balance (g : EtherCounterPeriodThree.Ray)
    (hs : IsTargetSchedule g) (q : ℕ) :
    2 ^ nineCycleBinaryExponent q * g.core (3 * (q + 9)) =
      3 ^ nineCycleTernaryExponent q * g.core (3 * q) +
        nineCycleDefect q := by
  have h := target_prefix_balance g hs q 9
  simpa [prefixBinaryExponent, prefixTernaryExponent,
    nineCycleDefect, sum_cycleBinaryExponent_nine,
    sum_cycleTernaryExponent_nine] using h

theorem nineCycleBinary_cast_eq_neg_one (q : ℕ) :
    ((2 ^ nineCycleBinaryExponent q : ℕ) : ZMod 27) = -1 := by
  have hM : nineCycleBinaryExponent q = 18 * (24 * q + 234) + 9 := by
    dsimp only [nineCycleBinaryExponent]
    ring
  have hz : (2 : ZMod 27) ^ nineCycleBinaryExponent q = -1 := by
    rw [hM, pow_add, pow_mul]
    rw [show (2 : ZMod 27) ^ 18 = 1 by decide, one_pow]
    exact (show (2 : ZMod 27) ^ 9 = -1 by decide)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem nineCycleTernary_cast_eq_zero (q : ℕ) :
    ((3 ^ nineCycleTernaryExponent q : ℕ) : ZMod 27) = 0 := by
  have hQ : nineCycleTernaryExponent q = 3 + (nineCycleTernaryExponent q - 3) := by
    dsimp only [nineCycleTernaryExponent]
    omega
  have hz : (3 : ZMod 27) ^ nineCycleTernaryExponent q = 0 := by
    rw [hQ, pow_add]
    change (27 : ZMod 27) * 3 ^ (nineCycleTernaryExponent q - 3) = 0
    rw [show (27 : ZMod 27) = 0 by decide, zero_mul]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz

theorem three_pow_cast_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (3 : ZMod 27) ^ n = 0 := by
  have h : n = 3 + (n - 3) := by omega
  rw [h, pow_add]
  change (27 : ZMod 27) * 3 ^ (n - 3) = 0
  rw [show (27 : ZMod 27) = 0 by decide, zero_mul]

theorem composedDefect_succ_cast (q n : ℕ) :
    (composedDefect q (n + 1) : ZMod 27) =
      (2 : ZMod 27) ^ prefixBinaryExponent q n *
        (cycleDefect (q + n) : ZMod 27) := by
  simp only [composedDefect, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have hz : (3 : ZMod 27) ^ cycleTernaryExponent (q + n) = 0 :=
    three_pow_cast_eq_zero _ (by simp only [cycleTernaryExponent]; omega)
  change (3 : ZMod 27) ^ cycleTernaryExponent (q + n) *
      (composedDefect q n : ZMod 27) +
        (2 : ZMod 27) ^ prefixBinaryExponent q n *
          (cycleDefect (q + n) : ZMod 27) = _
  rw [hz]
  simp

theorem cycleDefect_cast (q : ℕ) :
    (cycleDefect q : ZMod 27) =
      17 * (2 : ZMod 27) ^ (182 + 32 * q) := by
  simp only [cycleDefect, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [three_pow_cast_eq_zero _ (by omega),
    three_pow_cast_eq_zero _ (by omega)]
  ring

theorem prefixBinaryExponent_eight (q : ℕ) :
    prefixBinaryExponent q 8 = 384 * q + 3560 := by
  norm_num [prefixBinaryExponent, cycleBinaryExponent,
    Finset.sum_range_succ]
  ring

/-- The displayed nine-cycle defect is `14 mod 27` on the clock phase
`q=0 mod 9`.  This proves the modular arithmetic part of QM119b--c without
using any computed residue row. -/
theorem nineCycleDefect_cast_eq_fourteen (q : ℕ) (hq : q % 9 = 0) :
    (nineCycleDefect q : ZMod 27) = 14 := by
  rw [nineCycleDefect, show 9 = 8 + 1 by omega,
    composedDefect_succ_cast, cycleDefect_cast,
    prefixBinaryExponent_eight]
  rw [show
      (2 : ZMod 27) ^ (384 * q + 3560) *
          (17 * 2 ^ (182 + 32 * (q + 8))) =
        17 * 2 ^ ((384 * q + 3560) + (182 + 32 * (q + 8))) by
      rw [pow_add]; ring]
  obtain ⟨k, rfl⟩ := (Nat.dvd_iff_mod_eq_zero).2 hq
  have hexp : 384 * (9 * k) + 3560 + (182 + 32 * (9 * k + 8)) =
      18 * (208 * k + 222) + 2 := by ring
  rw [hexp, pow_add, pow_mul]
  rw [show (2 : ZMod 27) ^ 18 = 1 by decide, one_pow]
  decide

/-- The sharp normalized precision is beyond the nine-cycle binary mass from
`q=99` onward (QM119d). -/
theorem nineCycleBinaryExponent_lt_sharpUpperBudget
    (g : EtherCounterPeriodThree.Ray) (hs : IsTargetSchedule g)
    (q : ℕ) (hq : 99 ≤ q) :
    nineCycleBinaryExponent q < g.sharpUpperBudget q := by
  rcases hs with ⟨h0, h1, h2, hK⟩
  have hgrowth : g.sharpGrowthExponent q = q * (1386 * q + 8427) := by
    let s := q - 99
    have hqrep : q = s + 99 := by dsimp only [s]; omega
    simp only [EtherCounterPeriodThree.Ray.sharpGrowthExponent,
      EtherCounterPeriodThree.Ray.phaseSum]
    rw [h0, h1, h2, hK]
    rw [hqrep]
    rw [show 693 * (s + 99) - 3141 = 693 * s + 65466 by omega]
    ring
  rw [EtherCounterPeriodThree.Ray.sharpUpperBudget, hgrowth]
  apply (Nat.lt_div_iff_mul_lt (by norm_num : 0 < 306)).2
  simp only [nineCycleBinaryExponent]
  have hpoly :
      306 * (432 * q + 4221) < q * (1386 * q + 8427) := by
    nlinarith
  calc
    (432 * q + 4221) * 306 = 306 * (432 * q + 4221) := by ring
    _ < q * (1386 * q + 8427) := hpoly
    _ = q * (1386 * q + 8427) + 305 - (306 - 1) := by omega

/-- Modulo `27`, a nine-cycle balance with binary coefficient `-1`, vanished
ternary coefficient, and defect `14` forces the output class `13` (QM119c). -/
theorem output_mod_twentySeven
    (M Q D x y : ℕ)
    (hbalance : 2 ^ M * y = 3 ^ Q * x + D)
    (hbinary : ((2 ^ M : ℕ) : ZMod 27) = -1)
    (hternary : ((3 ^ Q : ℕ) : ZMod 27) = 0)
    (hdefect : (D : ZMod 27) = 14) :
    y % 27 = 13 := by
  have h := congrArg (fun n : ℕ => (n : ZMod 27)) hbalance
  simp only [Nat.cast_mul, Nat.cast_add] at h
  rw [hbinary, hternary, hdefect] at h
  norm_num at h
  have hy : (y : ZMod 27) = 13 := by
    calc
      (y : ZMod 27) = -14 := by linear_combination -h
      _ = 13 := by decide
  exact_mod_cast congrArg ZMod.val hy

/-- Every actual target-schedule ray has output core `13 mod 27` after the
nine-cycle block beginning in clock phase zero. -/
theorem target_nineCycle_output_mod_twentySeven
    (g : EtherCounterPeriodThree.Ray) (hs : IsTargetSchedule g)
    (q : ℕ) (hq : q % 9 = 0) :
    g.core (3 * (q + 9)) % 27 = 13 := by
  exact output_mod_twentySeven
    (nineCycleBinaryExponent q) (nineCycleTernaryExponent q)
      (nineCycleDefect q) (g.core (3 * q)) (g.core (3 * (q + 9)))
      (target_nineCycle_balance g hs q)
      (nineCycleBinary_cast_eq_neg_one q)
      (nineCycleTernary_cast_eq_zero q)
      (nineCycleDefect_cast_eq_fourteen q hq)

/-- The arithmetic core of QM119e.  Dividing an exact affine transition by
`2^M` consumes exactly `M` bits of source congruence and no more.  This is
stated over the integers so it applies to either sign of the later carry. -/
theorem exact_forward_images_compatible
    (P M : ℕ) (A D x r y z : ℤ) (hMP : M ≤ P)
    (hsource : (2 : ℤ) ^ P ∣ x - r)
    (hy : (2 : ℤ) ^ M * y = A * x + D)
    (hz : (2 : ℤ) ^ M * z = A * r + D) :
    (2 : ℤ) ^ (P - M) ∣ y - z := by
  obtain ⟨k, hk⟩ := hsource
  refine ⟨A * k, ?_⟩
  have hP : P = M + (P - M) := by omega
  have hpows : (2 : ℤ) ^ P = 2 ^ M * 2 ^ (P - M) := by
    calc
      (2 : ℤ) ^ P = 2 ^ (M + (P - M)) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) hP
      _ = 2 ^ M * 2 ^ (P - M) := pow_add 2 M (P - M)
  have hscaled :
      (2 : ℤ) ^ M * (y - z) =
        (2 : ℤ) ^ M * ((2 : ℤ) ^ (P - M) * (A * k)) := by
    calc
      (2 : ℤ) ^ M * (y - z) = A * (x - r) := by
        rw [mul_sub]
        nlinarith [hy, hz]
      _ = A * ((2 : ℤ) ^ P * k) := by rw [hk]
      _ = (2 : ℤ) ^ M * ((2 : ℤ) ^ (P - M) * (A * k)) := by
        rw [hpows]
        ring
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)) hscaled

/-- QM119f, stated without any computational premise.  If the exact forward
image is `13 mod 27`, then the future residue is in the same class exactly
when the signed carry is divisible by `27`. -/
theorem residue_eq_required_iff_carry_eq_zero
    (N required p : ℕ) (r y C : ℤ)
    (htwo : IsUnit (2 : ZMod N))
    (hy : (y : ZMod N) = required)
    (hcarry : r - y = (2 : ℤ) ^ p * C) :
    (r : ZMod N) = required ↔ (C : ZMod N) = 0 := by
  have hpow : IsUnit ((2 : ZMod N) ^ p) := htwo.pow _
  have h := congrArg (fun z : ℤ => (z : ZMod N)) hcarry
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  rw [hy] at h
  constructor
  · intro hr
    rw [hr, sub_self, eq_comm] at h
    apply (hpow.mul_right_inj).mp
    simpa using h
  · intro hC
    rw [hC, mul_zero] at h
    exact sub_eq_zero.mp h

/-- Explicit form of the same reduction: modulo an odd target modulus, the
signed carry is merely the target-residue mismatch multiplied by a unit.  In
particular the block composition contributes no independent nonvanishing
mechanism; that must come from the canonical future-residue sequence. -/
theorem carry_cast_eq_inv_pow_mul_residue_sub
    (N required p : ℕ) (r y C : ℤ)
    (htwo : IsUnit (2 : ZMod N))
    (hy : (y : ZMod N) = required)
    (hcarry : r - y = (2 : ℤ) ^ p * C) :
    (C : ZMod N) = ((2 : ZMod N) ^ p)⁻¹ *
      ((r : ZMod N) - required) := by
  have hpow : IsUnit ((2 : ZMod N) ^ p) := htwo.pow _
  have h := congrArg (fun z : ℤ => (z : ZMod N)) hcarry
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  rw [hy] at h
  calc
    (C : ZMod N) = 1 * C := by simp
    _ = (((2 : ZMod N) ^ p)⁻¹ * 2 ^ p) * C := by
      rw [ZMod.inv_mul_of_unit _ hpow]
    _ = ((2 : ZMod N) ^ p)⁻¹ * (2 ^ p * C) := by ring
    _ = ((2 : ZMod N) ^ p)⁻¹ * ((r : ZMod N) - required) := by
      rw [← h]

/-- Local arithmetic alone always admits the zero-carry branch: take the
future residue equal to the exact forward image. -/
theorem zero_carry_locally_compatible (p : ℕ) (y : ℤ) :
    y - y = (2 : ℤ) ^ p * 0 := by ring

/-- Formal guardrail: the signed carry equation by itself can never imply a
nonzero carry modulo any modulus.  Any such theorem must use an additional
property selecting the canonical future residue. -/
theorem local_carry_relation_does_not_force_nonzero
    (N p : ℕ) (y : ℤ) :
    ¬ ∀ r C : ℤ,
      r - y = (2 : ℤ) ^ p * C → (C : ZMod N) ≠ 0 := by
  intro h
  exact h y 0 (zero_carry_locally_compatible p y) (by norm_num)

theorem residue_eq_thirteen_iff_carry_eq_zero
    (p : ℕ) (r y C : ℤ)
    (hy : (y : ZMod 27) = 13)
    (hcarry : r - y = (2 : ℤ) ^ p * C) :
    (r : ZMod 27) = 13 ↔ (C : ZMod 27) = 0 := by
  exact residue_eq_required_iff_carry_eq_zero 27 13 p r y C
    ((ZMod.isUnit_iff_coprime 2 27).2 (by norm_num)) hy hcarry

end EtherCounterNineCycle
end KontoroC
