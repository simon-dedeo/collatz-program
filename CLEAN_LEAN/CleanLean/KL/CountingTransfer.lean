/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.PredecessorCount
import CleanLean.KL.ConcreteLimit
import CleanLean.KL.CriticalParameter
import CleanLean.KL.PredecessorTransfer

/-!
# From KL exponents to almost-linear predecessor counting

This file formalizes the last elementary asymptotic step in the proposed KL
program.  A positive constant in a bound `C * X^gamma` can be absorbed by
lowering the exponent, and `lambda_k → 2` implies
`log₂(lambda_k) → 1`.

The substantive Krasikov--Lagarias difference-inequality theorem is exposed
as the hypothesis `HasPredecessorExponent`; it is not smuggled into the
analytic argument below.
-/

namespace CleanLean.KL

open Filter
open CleanLean.Collatz

/-- The predecessor-counting exponent corresponding to a KL parameter. -/
noncomputable def klExponent (lam : ℝ) : ℝ :=
  Real.logb 2 lam

/-- A fixed target has a predecessor lower bound with exponent `gamma`, up to
a positive target-dependent multiplicative constant. -/
def HasPredecessorExponent (a : ℕ) (gamma : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ gamma ≤ (predecessorCount a X : ℝ)

/-- A positive multiplicative constant can be absorbed by any strict decrease
in the power exponent. -/
theorem eventually_rpow_le_of_constant_mul_rpow_le
    {count : ℕ → ℝ} {C gamma' gamma : ℝ}
    (hC : 0 < C) (hgamma : gamma' < gamma)
    (hbound : ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ gamma ≤ count X) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ gamma' ≤ count X := by
  have hgrowth : ∀ᶠ X : ℕ in atTop,
      C⁻¹ < (X : ℝ) ^ (gamma - gamma') := by
    have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ (gamma - gamma')) atTop atTop :=
      (tendsto_rpow_atTop (sub_pos.mpr hgamma)).comp
        tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_gt_atTop C⁻¹)
  filter_upwards [hbound, hgrowth, eventually_ge_atTop (1 : ℕ)] with X hX hg hX1
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX1
  have hone : 1 ≤ C * (X : ℝ) ^ (gamma - gamma') := by
    have hmul := mul_lt_mul_of_pos_left hg hC
    simpa [ne_of_gt hC] using hmul.le
  calc
    (X : ℝ) ^ gamma' = 1 * (X : ℝ) ^ gamma' := by ring
    _ ≤ (C * (X : ℝ) ^ (gamma - gamma')) * (X : ℝ) ^ gamma' := by
      gcongr
    _ = C * (X : ℝ) ^ gamma := by
      rw [mul_assoc, mul_comm ((X : ℝ) ^ (gamma - gamma'))]
      rw [← Real.rpow_add hXpos]
      congr 2
      linarith
    _ ≤ count X := hX

theorem hasPredecessorExponent_mono {a : ℕ} {gamma' gamma : ℝ}
    (hgamma : gamma' < gamma) (h : HasPredecessorExponent a gamma) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ gamma' ≤ (predecessorCount a X : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := h
  exact eventually_rpow_le_of_constant_mul_rpow_le hC hgamma hbound

/-- A predecessor exponent transfers backward along any finite target orbit.
This is the exact ordinary-count inclusion used after choosing a suitable
doubled target in the corrected all-target argument. -/
theorem hasPredecessorExponent_of_target_reaches
    {a b : ℕ} {gamma : ℝ}
    (hba : IsSyracusePredecessor a b)
    (hbound : HasPredecessorExponent b gamma) :
    HasPredecessorExponent a gamma := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with X hX
  exact hX.trans (by
    exact_mod_cast predecessorCount_mono_of_target_reaches
      (X := X) hba)

/-- Specialization to the target `2^r*a`. -/
theorem hasPredecessorExponent_of_two_pow_mul
    {a : ℕ} {gamma : ℝ} (r : ℕ)
    (hbound : HasPredecessorExponent (2 ^ r * a) gamma) :
    HasPredecessorExponent a gamma := by
  apply hasPredecessorExponent_of_target_reaches
    (b := 2 ^ r * a)
  · exact ⟨r, iterate_syracuse_two_pow_mul a r⟩
  · exact hbound

/-- `lambda_k → 2` gives convergence of the corresponding base-two
counting exponents to one. -/
theorem klExponent_tendsto_one (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop (nhds 2)) :
    Tendsto (fun k => klExponent (lam k)) atTop (nhds 1) := by
  have hcont : ContinuousAt (Real.logb 2) (2 : ℝ) :=
    Real.continuousAt_logb (by norm_num)
  simpa [klExponent, Function.comp_def,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
    hcont.tendsto.comp hlam

/-- The purely analytic endgame: if every finite KL exponent supplies the
corresponding predecessor lower bound and the exponents tend to one, then
predecessor counting is `X^(1-epsilon)` for every positive epsilon. -/
theorem almostLinearPredecessorCounting_of_exponents
    (gamma : ℕ → ℝ)
    (hgamma : Tendsto gamma atTop (nhds 1))
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (gamma k)) :
    AlmostLinearPredecessorCounting := by
  intro a ha ha3 ε hε
  have hnear : ∀ᶠ k : ℕ in atTop, gamma k ∈ Set.Ioi (1 - ε) :=
    hgamma.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨k, hk⟩ := hnear.exists
  exact hasPredecessorExponent_mono hk (hbound a ha ha3 k)

/-- The exact public-facing KL implication.  All analytic limit and
constant-absorption steps are proved here; `hbound` is precisely the
literature transfer theorem that remains to formalize from KL's difference
inequalities. -/
theorem almostLinearPredecessorCounting_of_klLambda
    (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop (nhds 2))
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (klExponent (lam k))) :
    AlmostLinearPredecessorCounting :=
  almostLinearPredecessorCounting_of_exponents
    (fun k => klExponent (lam k)) (klExponent_tendsto_one lam hlam) hbound

/-- Fully direct route from a cofinal family of exact feasible vectors to
almost-linear predecessor counting.  This avoids critical eigenvector
existence and localization; the sole literature hypothesis is the KL
difference-inequality transfer from exact finite feasibility to the power
lower bound. -/
theorem almostLinearPredecessorCounting_of_feasible_sequence
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (nhds 2))
    (hfeasible : ∀ k, LevelFeasible k (mu k))
    (htransfer : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 → ∀ k : ℕ,
      LevelFeasible k (mu k) →
        HasPredecessorExponent a (klExponent (mu k))) :
    AlmostLinearPredecessorCounting := by
  apply almostLinearPredecessorCounting_of_klLambda mu hmu
  intro a ha ha3 k
  exact htransfer a ha ha3 k (hfeasible k)

/-- A convenience composition with the already formalized concrete
defect-to-endpoint theorem. -/
theorem almostLinearPredecessorCounting_of_klDefect
    (lam delta : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hdelta : Tendsto delta atTop (nhds 0))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k)
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (klExponent (lam k))) :
    AlmostLinearPredecessorCounting :=
  almostLinearPredecessorCounting_of_klLambda lam
    (klLambda_tendsto_two_of_defect lam delta hlam hdelta0 hdelta hidentity)
    hbound

end CleanLean.KL
