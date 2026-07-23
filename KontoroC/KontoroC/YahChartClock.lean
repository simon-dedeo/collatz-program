/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahChartTowerNoGo

/-!
# The abstract normalized YAH chart clock

This file formalizes the leading-scale dynamics independently of enormous
lasso words.  It proves the three canonical branches, the exact
scale/register-slope factorization, and the geometric obstruction behind the
aperiodicity claim.

The results concern the abstract scale clock.  Identifying every abstract
head with the head of one exact infinite finite-word execution still requires
the additive-correction gap estimate described in the research ledger.
-/

namespace KontoroC
namespace YahChartClock

inductive Head where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

def width : Head → ℕ
  | .zero => 1
  | .one | .two => 2

def nextScale (rho : ℚ) (head : Head) : ℚ :=
  rho * 3 / 2 ^ width head

def Selects (rho : ℚ) : Head → Prop
  | .zero => 1 ≤ rho ∧ rho < 4 / 3
  | .one => 4 / 3 ≤ rho ∧ rho < 5 / 3
  | .two => 5 / 3 ≤ rho ∧ rho < 2

theorem zero_branch (rho : ℚ) (h : Selects rho .zero) :
    nextScale rho .zero = 3 * rho / 2 ∧
      1 ≤ nextScale rho .zero ∧ nextScale rho .zero < 2 := by
  norm_num [Selects, nextScale, width] at h ⊢
  constructor
  · ring
  · constructor <;> linarith

theorem one_branch (rho : ℚ) (h : Selects rho .one) :
    nextScale rho .one = 3 * rho / 4 ∧
      1 ≤ nextScale rho .one ∧ nextScale rho .one < 2 := by
  norm_num [Selects, nextScale, width] at h ⊢
  constructor
  · ring
  · constructor <;> linarith

theorem two_branch (rho : ℚ) (h : Selects rho .two) :
    nextScale rho .two = 3 * rho / 4 ∧
      1 ≤ nextScale rho .two ∧ nextScale rho .two < 2 := by
  norm_num [Selects, nextScale, width] at h ⊢
  constructor
  · ring
  · constructor <;> linarith

/-- Every canonical scale belongs to exactly one half-open head interval. -/
theorem exists_unique_selected (rho : ℚ) (hlower : 1 ≤ rho) (hupper : rho < 2) :
    ∃! head, Selects rho head := by
  by_cases hzero : rho < 4 / 3
  · refine ⟨.zero, ⟨hlower, hzero⟩, ?_⟩
    intro head hhead
    cases head with
    | zero => rfl
    | one => norm_num [Selects] at hhead ⊢; linarith
    | two => norm_num [Selects] at hhead ⊢; linarith
  · by_cases hone : rho < 5 / 3
    · refine ⟨.one, ⟨le_of_not_gt hzero, hone⟩, ?_⟩
      intro head hhead
      cases head with
      | zero => norm_num [Selects] at hhead ⊢; linarith
      | one => rfl
      | two => norm_num [Selects] at hhead ⊢; linarith
    · refine ⟨.two, ⟨le_of_not_gt hone, hupper⟩, ?_⟩
      intro head hhead
      cases head with
      | zero => norm_num [Selects] at hhead ⊢; linarith
      | one => norm_num [Selects] at hhead ⊢; linarith
      | two => rfl

/-- QM40's exact algebraic identity.  Here `J=M+G` records
`G=J-M`, and `hscale` is the closed scale update over the segment. -/
theorem slope_factorization (rhoStart rhoEnd : ℚ) (M S J G : ℕ)
    (hstart : rhoStart ≠ 0)
    (hscale : rhoEnd = rhoStart * 3 ^ M / 2 ^ S)
    (hgain : J = M + G) :
    3 ^ J / 2 ^ S = 3 ^ G * (rhoEnd / rhoStart) := by
  rw [hgain, pow_add, hscale]
  field_simp

/-- Positive word-space gain forces the affine register slope above `3/2`
whenever both endpoint scales are canonical. -/
theorem three_halves_lt_slope_of_positive_gain
    (rhoStart rhoEnd slope : ℚ) (G : ℕ)
    (hstartLower : 1 ≤ rhoStart) (hstartUpper : rhoStart < 2)
    (hendLower : 1 ≤ rhoEnd) (_hendUpper : rhoEnd < 2)
    (hG : 1 ≤ G)
    (hslope : slope = 3 ^ G * (rhoEnd / rhoStart)) :
    3 / 2 < slope := by
  have hstartPos : 0 < rhoStart := lt_of_lt_of_le (by norm_num) hstartLower
  have hratio : (1 / 2 : ℚ) < rhoEnd / rhoStart := by
    rw [lt_div_iff₀ hstartPos]
    nlinarith
  have hpow : (3 : ℚ) ≤ 3 ^ G := by
    have hpowNat : (3 : ℕ) ≤ 3 ^ G := by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (n := 3) (by norm_num) hG)
    exact_mod_cast hpowNat
  have hratioNonneg : 0 ≤ rhoEnd / rhoStart := by nlinarith
  calc
    (3 / 2 : ℚ) = 3 * (1 / 2) := by ring
    _ < 3 * (rhoEnd / rhoStart) := by nlinarith
    _ ≤ 3 ^ G * (rhoEnd / rhoStart) := by
      exact mul_le_mul_of_nonneg_right hpow hratioNonneg
    _ = slope := hslope.symm

private theorem bounded_geometric_forces_one (x ratio : ℚ)
    (hx : 0 < x) (hratio : 0 < ratio)
    (hbounds : ∀ k : ℕ, 1 ≤ x * ratio ^ k ∧ x * ratio ^ k < 2) :
    ratio = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < ratio⁻¹ := (one_lt_inv₀ hratio).2 hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x hinv
    have hcancel : (ratio⁻¹) ^ k * ratio ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hratio.ne', one_pow]
    have hpowpos : 0 < ratio ^ k := pow_pos hratio k
    have hsmall : x * ratio ^ k < 1 := by nlinarith
    exact (not_lt_of_ge (hbounds k).1) hsmall
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / x) hgt
    have hlarge : 2 < x * ratio ^ k := by
      have := (div_lt_iff₀ hx).1 hk
      simpa only [mul_comm] using this
    exact (not_lt_of_ge (le_of_lt hlarge)) (hbounds k).2

/-- The geometric core of QM36.  A positive bounded scale cannot be
multiplied forever by `3^p/2^q` when `p>0`. -/
theorem no_bounded_periodic_scale_ratio (x : ℚ) (p q : ℕ)
    (hx : 0 < x) (hp : 0 < p)
    (hbounds : ∀ k : ℕ,
      1 ≤ x * ((3 : ℚ) ^ p / 2 ^ q) ^ k ∧
        x * ((3 : ℚ) ^ p / 2 ^ q) ^ k < 2) :
    False := by
  let ratio : ℚ := (3 : ℚ) ^ p / 2 ^ q
  have hratio : 0 < ratio := by dsimp [ratio]; positivity
  have hone : ratio = 1 := bounded_geometric_forces_one x ratio hx hratio hbounds
  have hpowQ : (3 : ℚ) ^ p = 2 ^ q := by
    have hden : (2 : ℚ) ^ q ≠ 0 := by positivity
    exact (div_eq_one_iff_eq hden).mp hone
  have hpowN : (3 : ℕ) ^ p = 2 ^ q := by exact_mod_cast hpowQ
  have hcop : ((3 : ℕ) ^ p).Coprime (2 ^ q) :=
    Nat.Coprime.pow p q (by norm_num)
  rw [hpowN] at hcop
  have honeNat : (2 : ℕ) ^ q = 1 := (Nat.coprime_self _).mp hcop
  have hthree : 1 < (3 : ℕ) ^ p := Nat.one_lt_pow (Nat.ne_of_gt hp) (by norm_num)
  rw [hpowN, honeNat] at hthree
  omega

/-- QM36 in periodic-block form.  An eventually repeated block of `p>0`
macros and `q` shortcut sweeps would impose the displayed recurrence on the
bounded scale tail, which is impossible.  A periodic head tail supplies this
recurrence by multiplying the per-head updates in QM35. -/
theorem no_eventually_periodic_bounded_clock
    (rho : ℕ → ℚ) (N p q : ℕ)
    (hp : 0 < p)
    (hrhoPos : 0 < rho N)
    (hcanonical : ∀ n, 1 ≤ rho n ∧ rho n < 2)
    (hperiodBlock : ∀ k,
      rho (N + (k + 1) * p) =
        rho (N + k * p) * ((3 : ℚ) ^ p / 2 ^ q)) :
    False := by
  let ratio : ℚ := (3 : ℚ) ^ p / 2 ^ q
  have hgeometric : ∀ k,
      rho (N + k * p) = rho N * ratio ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hperiodBlock k, ih, pow_succ]
        ring
  apply no_bounded_periodic_scale_ratio (rho N) p q hrhoPos hp
  intro k
  have hb := hcanonical (N + k * p)
  rw [hgeometric k] at hb
  exact hb

end YahChartClock
end KontoroC
