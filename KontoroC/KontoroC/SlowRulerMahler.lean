/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PublicPayloadPressure
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.RingTheory.Algebraic.Basic

/-!
# The slow 17-ruler public theta value

This file formalizes the elementary Collatz-specific reduction in QM152.
The cited Wang value theorem is not reproduced here: its conclusion can be
supplied through the explicit irrational-value premise at the end.
-/

namespace KontoroC
namespace SelfWritingKL
namespace SlowRuler

open PublicTheta

def schedule (j n : ℕ) : ℕ :=
  j + 8 * padicValNat 17 (n + 1)

def a : ℚ := (2 : ℚ) ^ 15 / 3 ^ 11
def b : ℚ := (2 : ℚ) ^ 8 / 3 ^ 6
def c : ℚ := b ^ 8
def z (j : ℕ) : ℚ := a * b ^ j
def x (j : ℕ) : ℚ := (2 : ℚ) ^ (19 + 8 * j) / 3 ^ (14 + 6 * j)
def kappa : ℚ := 16 / 27

theorem schedule_pos {j n : ℕ} (hj : 0 < j) : 0 < schedule j n := by
  simp [schedule]
  omega

theorem padicVal_factorial_succ (n : ℕ) :
    padicValNat 17 (n + 1).factorial =
      padicValNat 17 (n + 1) + padicValNat 17 n.factorial := by
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [show n + 1 = n.succ by omega, Nat.factorial_succ,
    padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]

/-- QM152a. -/
theorem branchSum_eq (j N : ℕ) :
    publicBranchSum (schedule j) N =
      j * N + 8 * padicValNat 17 N.factorial := by
  induction N with
  | zero => simp [publicBranchSum]
  | succ N ih =>
      rw [publicBranchSum_succ, ih, schedule, padicVal_factorial_succ]
      rw [Nat.mul_succ]
      omega

/-- The inclusive prefix products are the factorial-valuation Mahler
coefficients from QM152b. -/
theorem prefixProduct_eq (j N : ℕ) :
    publicPrefixProduct (schedule j) N =
      c ^ padicValNat 17 N.factorial * z j ^ N := by
  rw [publicPrefixProduct_factor, branchSum_eq]
  simp only [a, b, c, z]
  rw [pow_add, pow_mul, pow_mul]
  ring

/-- QM152's elementary Legendre block identity. -/
theorem padicVal_factorial_block (n r : ℕ) (hr : r < 17) :
    padicValNat 17 (17 * n + r).factorial =
      n + padicValNat 17 n.factorial := by
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [padicValNat_factorial_mul_add n hr,
    padicValNat_factorial_mul]
  omega

noncomputable def termAt (Z : ℚ_[2]) (n : ℕ) : ℚ_[2] :=
  (c : ℚ_[2]) ^ padicValNat 17 n.factorial * Z ^ n

noncomputable def valueAt (Z : ℚ_[2]) : ℚ_[2] :=
  ∑' n, termAt Z n

noncomputable def P17 (Z : ℚ_[2]) : ℚ_[2] :=
  ∑ r : ZMod 17, Z ^ r.val

theorem norm_c : ‖(c : ℚ_[2])‖ = ((2 : ℝ)⁻¹) ^ 64 := by
  rw [c, b, Rat.cast_pow, norm_pow]
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_pow, norm_div, norm_pow,
    norm_pow]
  change (‖(2 : ℚ_[2])‖ ^ 8 / ‖(3 : ℚ_[2])‖ ^ 6) ^ 8 = _
  rw [htwo, hthree, one_pow, div_one, ← pow_mul]

theorem termAt_summable (Z : ℚ_[2]) (hZ : ‖Z‖ < 1) :
    Summable (termAt Z) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have hbound : ∀ n : ℕ, ‖termAt Z n‖ ≤ ‖Z‖ ^ n := by
    intro n
    rw [termAt, norm_mul, norm_pow, norm_pow, norm_c]
    have hc : (((2 : ℝ)⁻¹) ^ 64) ^
        padicValNat 17 n.factorial ≤ 1 := by
      exact pow_le_one₀ (by positivity) (by norm_num)
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg Z) n) hc
  exact squeeze_zero_norm hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg Z) hZ)

theorem termAt_block (Z : ℚ_[2]) (n : ℕ) (r : ZMod 17) :
    termAt Z (r.val + 17 * n) =
      Z ^ r.val * termAt ((c : ℚ_[2]) * Z ^ 17) n := by
  unfold termAt
  rw [show r.val + 17 * n = 17 * n + r.val by omega,
    padicVal_factorial_block n r.val r.val_lt,
    pow_add, pow_add, pow_mul, mul_pow]
  ring

/-- QM152c as an identity of convergent `Q_2` series. -/
theorem valueAt_functional (Z : ℚ_[2]) (hZ : ‖Z‖ < 1) :
    valueAt Z = P17 Z * valueAt ((c : ℚ_[2]) * Z ^ 17) := by
  have hs := termAt_summable Z hZ
  have hc : ‖(c : ℚ_[2])‖ ≤ 1 := by rw [norm_c]; norm_num
  have hnext : ‖(c : ℚ_[2]) * Z ^ 17‖ < 1 := by
    rw [norm_mul, norm_pow]
    have hzpow : ‖Z‖ ^ 17 < 1 := pow_lt_one₀ (norm_nonneg Z) hZ (by norm_num)
    exact (mul_le_mul_of_nonneg_right hc
      (pow_nonneg (norm_nonneg Z) 17)).trans_lt (by simpa using hzpow)
  have hsnext := termAt_summable ((c : ℚ_[2]) * Z ^ 17) hnext
  rw [valueAt, Nat.sumByResidueClasses hs 17]
  simp_rw [termAt_block]
  calc
    (∑ r : ZMod 17,
        ∑' m : ℕ, Z ^ r.val *
          termAt ((c : ℚ_[2]) * Z ^ 17) m) =
        ∑ r : ZMod 17, Z ^ r.val *
          valueAt ((c : ℚ_[2]) * Z ^ 17) := by
      apply Finset.sum_congr rfl
      intro r _
      exact hsnext.tsum_mul_left (Z ^ r.val)
    _ = P17 Z * valueAt ((c : ℚ_[2]) * Z ^ 17) := by
      simp only [P17, Finset.sum_mul]

noncomputable def mahlerTerm (j n : ℕ) : ℚ_[2] :=
  (c : ℚ_[2]) ^ padicValNat 17 n.factorial * (z j : ℚ_[2]) ^ n

noncomputable def value (j : ℕ) : ℚ_[2] :=
  ∑' n, mahlerTerm j n

theorem mahlerTerm_eq_prefix (j n : ℕ) :
    mahlerTerm j n =
      (publicPrefixProduct (schedule j) n : ℚ_[2]) := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (prefixProduct_eq j n)
  simpa only [mahlerTerm, Rat.cast_mul, Rat.cast_pow] using h.symm

theorem mahlerTerm_summable (j : ℕ) (hj : 0 < j) :
    Summable (mahlerTerm j) := by
  have heq : mahlerTerm j = fun n =>
      (publicPrefixProduct (schedule j) n : ℚ_[2]) := by
    funext n
    exact mahlerTerm_eq_prefix j n
  rw [heq]
  refine (summable_nat_add_iff
    (f := fun n : ℕ =>
      (publicPrefixProduct (schedule j) n : ℚ_[2])) 1).mp ?_
  change Summable (padicTerm (schedule j))
  exact padicTerm_summable (schedule j) (fun n => schedule_pos hj)

/-- QM152b: the inclusive factorial-valuation Mahler value is exactly
`1 + Theta` for the slow ruler schedule. -/
theorem value_eq_one_add_padicSum (j : ℕ) (hj : 0 < j) :
    value j = 1 + padicSum (schedule j) := by
  have hsum := (mahlerTerm_summable j hj).sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, mahlerTerm_eq_prefix,
    publicPrefixProduct_zero] at hsum
  have htail : (∑' n : ℕ, mahlerTerm j (n + 1)) =
      padicSum (schedule j) := by
    apply tsum_congr
    intro n
    rw [mahlerTerm_eq_prefix]
    rfl
  rw [htail] at hsum
  exact hsum.symm

/-- The rational specialization in QM152d. -/
theorem x_eq_kappa_mul_z (j : ℕ) : x j = kappa * z j := by
  simp only [x, kappa, z, a, b]
  rw [show (2 : ℚ) ^ (19 + 8 * j) =
      2 ^ 19 * (2 ^ 8) ^ j by rw [pow_add, pow_mul],
    show (3 : ℚ) ^ (14 + 6 * j) =
      3 ^ 14 * (3 ^ 6) ^ j by rw [pow_add, pow_mul],
    div_pow]
  norm_num
  ring

theorem c_eq_kappa_pow : c = kappa ^ 16 := by
  have hb : b = kappa ^ 2 := by norm_num [b, kappa, div_pow]
  rw [c, hb, ← pow_mul]

noncomputable def GValue (X : ℚ_[2]) : ℚ_[2] :=
  valueAt (X / (kappa : ℚ_[2]))

theorem GValue_functional (X : ℚ_[2])
    (hX : ‖X / (kappa : ℚ_[2])‖ < 1) :
    GValue X = P17 (X / (kappa : ℚ_[2])) * GValue (X ^ 17) := by
  have hk : (kappa : ℚ_[2]) ≠ 0 := by norm_num [kappa]
  have hc := congrArg (fun q : ℚ => (q : ℚ_[2])) c_eq_kappa_pow
  norm_num only [Rat.cast_pow] at hc
  have harg : (c : ℚ_[2]) * (X / (kappa : ℚ_[2])) ^ 17 =
      X ^ 17 / (kappa : ℚ_[2]) := by
    rw [hc]
    field_simp
  rw [GValue, valueAt_functional _ hX, harg]
  rfl

theorem value_eq_valueAt (j : ℕ) : value j = valueAt (z j : ℚ_[2]) := by
  rfl

/-- QM152d at the eight rational specialization points: the rescaled Wang
value is literally the inclusive public theta value. -/
theorem GValue_x_eq_value (j : ℕ) : GValue (x j : ℚ_[2]) = value j := by
  have hk : (kappa : ℚ_[2]) ≠ 0 := by norm_num [kappa]
  have hx := congrArg (fun q : ℚ => (q : ℚ_[2])) (x_eq_kappa_mul_z j)
  rw [GValue, hx, Rat.cast_mul, mul_div_cancel_left₀ _ hk]
  exact (value_eq_valueAt j).symm

/-- Irrationality of the cited Wang value is more than enough for the
Collatz consumer.  This predicate states only the consequence Lean uses. -/
def IrrationalValue (j : ℕ) : Prop :=
  ∀ q : ℚ, GValue (x j : ℚ_[2]) ≠ (q : ℚ_[2])

theorem padicSum_irrational_of_value
    (j : ℕ) (hj : 0 < j) (hirr : IrrationalValue j) :
    ∀ q : ℚ, padicSum (schedule j) ≠ (q : ℚ_[2]) := by
  intro q hq
  apply hirr (q + 1)
  rw [GValue_x_eq_value, value_eq_one_add_padicSum j hj, hq]
  norm_num
  ring

/-- Conditional QM153d for one rail.  Wang's theorem is isolated in the
single premise `IrrationalValue j`. -/
theorem no_orbit_of_irrational_value
    (j : ℕ) (hj : 0 < j) (hirr : IrrationalValue j) :
    ¬ ∃ o : Orbit, (fun t => o.branch (t + 1)) = schedule j := by
  apply no_orbit_with_targetBranch_of_padic_irrational
  exact padicSum_irrational_of_value j hj hirr

/-- All eight public residue rails are excluded once the eight cited Wang
value conclusions are supplied. -/
theorem no_orbit_on_eight_slow_rulers
    (hWang : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → IrrationalValue j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 8 →
      ¬ ∃ o : Orbit, (fun t => o.branch (t + 1)) = schedule j := by
  intro j hj h8
  exact no_orbit_of_irrational_value j (by omega) (hWang j hj h8)

/-- Exact interface for the externally cited Wang theorem. -/
def WangTranscendencePremise : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ 8 →
    Transcendental ℚ (GValue (x j : ℚ_[2]))

theorem irrationalValue_of_transcendental
    (j : ℕ) (htr : Transcendental ℚ (GValue (x j : ℚ_[2]))) :
    IrrationalValue j := by
  intro q hq
  have halg : IsAlgebraic ℚ (GValue (x j : ℚ_[2])) := by
    rw [hq]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℚ_[2]) q
  exact htr halg

/-- Conditional QM153d with the literature input stated at its natural
strength.  There is no axiom or theorem in this project asserting the Wang
premise. -/
theorem no_orbit_on_eight_slow_rulers_of_Wang
    (hWang : WangTranscendencePremise) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 8 →
      ¬ ∃ o : Orbit, (fun t => o.branch (t + 1)) = schedule j := by
  apply no_orbit_on_eight_slow_rulers
  intro j hj h8
  exact irrationalValue_of_transcendental j (hWang j hj h8)

end SlowRuler
end SelfWritingKL
end KontoroC
