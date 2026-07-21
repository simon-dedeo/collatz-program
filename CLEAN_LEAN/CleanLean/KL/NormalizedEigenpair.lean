/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.AnnealedIrreducible

/-!
# Normalizing the finite nonlinear KL operator

This file discharges the elementary parts of the finite nonlinear Perron
existence argument.  On the nonnegative unit simplex, positive transport makes
the total mass of the nonlinear image positive.  A fixed point of the
normalized operator therefore gives an eigenpair, and the full concrete
transport cycle upgrades its nonnegative eigenvector to strict positivity.

The remaining existence step is precisely a finite-simplex fixed-point
theorem (Brouwer).  The pinned mathlib release does not currently provide that
theorem, so no existence axiom is introduced here.
-/

namespace CleanLean.KL

open scoped BigOperators

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- The positive transport summand is bounded by the nonlinear operator when
the branch weights and vector are nonnegative. -/
theorem transport_term_le_operator
    (w : Weights ℝ) (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced)
    (x : S.State → ℝ) (hx : ∀ q, 0 ≤ x q) (q : S.State) :
    w.transport * x (S.transport q) ≤ S.operator w x q := by
  have hf : 0 ≤ S.fiberMin x (S.refinementTarget q) :=
    S.fiberMin_nonneg x hx _
  cases hb : S.branch q with
  | retarded =>
      simp only [operator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hret hf)
  | neutral => simp [operator, hb]
  | advanced =>
      simp only [operator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hadv hf)

/-- Total nonlinear image mass is at least transport weight times input mass. -/
theorem transport_mul_totalMass_le_operator_totalMass
    (w : Weights ℝ) (hret : 0 ≤ w.retarded) (hadv : 0 ≤ w.advanced)
    (x : S.State → ℝ) (hx : ∀ q, 0 ≤ x q) :
    w.transport * S.totalMass x ≤ S.totalMass (S.operator w x) := by
  calc
    w.transport * S.totalMass x =
        ∑ q, w.transport * x (S.transport q) := by
          rw [← Finset.mul_sum, S.transport.sum_comp]
          rfl
    _ ≤ ∑ q, S.operator w x q := by
      apply Finset.sum_le_sum
      intro q hq
      exact S.transport_term_le_operator w hret hadv x hx q
    _ = S.totalMass (S.operator w x) := rfl

/-- Projective normalization by total nonlinear image mass. -/
def normalizedOperator (w : Weights ℝ) (x : S.State → ℝ) : S.State → ℝ :=
  fun q => S.operator w x q / S.totalMass (S.operator w x)

theorem normalizedOperator_nonneg
    (w : Weights ℝ)
    (hwt : 0 ≤ w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (x : S.State → ℝ) (hx : ∀ q, 0 ≤ x q)
    (hmass : 0 ≤ S.totalMass (S.operator w x)) :
    ∀ q, 0 ≤ S.normalizedOperator w x q := by
  intro q
  exact div_nonneg (S.operator_nonneg w hwt hret hadv x hx q) hmass

theorem totalMass_normalizedOperator
    (w : Weights ℝ) (x : S.State → ℝ)
    (hmass : S.totalMass (S.operator w x) ≠ 0) :
    S.totalMass (S.normalizedOperator w x) = 1 := by
  unfold totalMass normalizedOperator
  rw [← Finset.sum_div]
  exact div_self hmass

/-- Positive transport makes projective normalization a self-map of the
nonnegative unit simplex. -/
theorem normalizedOperator_maps_unitSimplex
    (w : Weights ℝ)
    (hwt : 0 < w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (x : S.State → ℝ) (hx : ∀ q, 0 ≤ x q)
    (hxmass : S.totalMass x = 1) :
    (∀ q, 0 ≤ S.normalizedOperator w x q) ∧
      S.totalMass (S.normalizedOperator w x) = 1 := by
  have hlower := S.transport_mul_totalMass_le_operator_totalMass
    w hret hadv x hx
  rw [hxmass, mul_one] at hlower
  have himage : 0 < S.totalMass (S.operator w x) := hwt.trans_le hlower
  exact ⟨S.normalizedOperator_nonneg w hwt.le hret hadv x hx himage.le,
    S.totalMass_normalizedOperator w x himage.ne'⟩

/-- A fixed point of projective normalization is an eigenvector of the
original homogeneous operator, with eigenvalue equal to its image mass. -/
theorem eigen_equation_of_normalized_fixed
    (w : Weights ℝ) (x : S.State → ℝ)
    (hmass : S.totalMass (S.operator w x) ≠ 0)
    (hfixed : S.normalizedOperator w x = x) :
    S.operator w x =
      fun q => S.totalMass (S.operator w x) * x q := by
  funext q
  have hq := congrFun hfixed q
  unfold normalizedOperator at hq
  simpa only [mul_comm] using (div_eq_iff hmass).mp hq

end

end FiniteSystem

namespace ResidueSystem

noncomputable section

/-- Every nonzero nonnegative nonlinear eigenvector with positive eigenvalue
is strictly positive.  Only the positive transport summand and the full
transport cycle are used. -/
theorem nonlinear_eigenvector_pos_of_nonnegative_nonzero
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    {x : State k → ℝ} {r : ℝ}
    (hx : ∀ q, 0 ≤ x q) (hxne : x ≠ 0) (hr : 0 < r)
    (heigen : (system k).operator w x = fun q => r * x q) :
    ∀ q, 0 < x q := by
  have hexists : ∃ s, 0 < x s := by
    by_contra hnot
    push Not at hnot
    apply hxne
    funext s
    exact le_antisymm (hnot s) (hx s)
  obtain ⟨s, hs⟩ := hexists
  have hback (q : State k) (hq : 0 < x (transport k q)) : 0 < x q := by
    have htransport : 0 < w.transport * x (transport k q) :=
      mul_pos hwt hq
    have hle := (system k).transport_term_le_operator
      w hret hadv x hx q
    rw [congrFun heigen q] at hle
    have : 0 < r * x q := htransport.trans_le hle
    nlinarith
  intro q
  obtain ⟨n, hn⟩ := exists_transport_iterate_eq k hk q s
  have hiterate : ∀ m : ℕ,
      0 < x ((transport k)^[m] q) → 0 < x q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        apply ih
        apply hback
        simpa [Function.iterate_succ_apply'] using hm
  apply hiterate n.val
  simpa [hn] using hs

/-- All algebraic and irreducibility obligations after the simplex fixed point
are discharged here.  The existential premise is exactly the Brouwer step. -/
theorem exists_positive_eigenpair_of_normalized_fixed
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hret : 0 ≤ w.retarded)
    (hadv : 0 ≤ w.advanced)
    (hfixed : ∃ x : State k → ℝ,
      (∀ q, 0 ≤ x q) ∧ (system k).totalMass x = 1 ∧
        (system k).normalizedOperator w x = x) :
    ∃ x r,
      (∀ q, 0 < x q) ∧ 0 < r ∧
        (system k).totalMass x = 1 ∧
        (system k).operator w x = fun q => r * x q := by
  obtain ⟨x, hx, hxmass, hnorm⟩ := hfixed
  have himage_lower := (system k).transport_mul_totalMass_le_operator_totalMass
    w hret hadv x hx
  rw [hxmass, mul_one] at himage_lower
  let r := (system k).totalMass ((system k).operator w x)
  have hr : 0 < r := hwt.trans_le himage_lower
  have heigen : (system k).operator w x = fun q => r * x q :=
    (system k).eigen_equation_of_normalized_fixed w x hr.ne' hnorm
  have hxne : x ≠ 0 := by
    intro hxzero
    rw [hxzero] at hxmass
    change (∑ m : State k, (0 : State k → ℝ) m) = 1 at hxmass
    have hzeroone : (0 : ℝ) = 1 := by
      simpa only [Pi.zero_apply, Finset.sum_const_zero] using hxmass
    norm_num at hzeroone
  have hxpos := nonlinear_eigenvector_pos_of_nonnegative_nonzero
    k hk w hwt hret hadv hx hxne hr heigen
  exact ⟨x, r, hxpos, hr, hxmass, heigen⟩

end

end ResidueSystem

end CleanLean.KL
