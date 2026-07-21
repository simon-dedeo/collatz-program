/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Comparison for difference systems with only retarded terms

This is the analytic core of Krasikov--Lagarias Theorem 5.1.  A right-hand
side is represented by a finite expression made from leaves, addition, and
minimum.  Every leaf evaluates one state at a positive backward time shift.
If the corresponding exponential coefficient inequalities are feasible,
an exponential lower bound propagates from one initial time strip to all
nonnegative times.

The advanced-term elimination which constructs these expressions is a
separate theorem.  Keeping the comparison principle independent makes the
remaining literature bridge explicit.
-/

namespace CleanLean.KL

/-- A nested sum/min expression whose leaves carry a state and a backward
time lag. -/
inductive RetardedExpr (ι : Type) where
  | leaf (state : ι) (lag : ℝ)
  | add (left right : RetardedExpr ι)
  | min (left right : RetardedExpr ι)

namespace RetardedExpr

variable {ι : Type}

/-- Evaluate a retarded expression on a family of real functions. -/
def eval (e : RetardedExpr ι) (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  match e with
  | .leaf i lag => φ i (y - lag)
  | .add a b => a.eval φ y + b.eval φ y
  | .min a b => _root_.min (a.eval φ y) (b.eval φ y)

/-- Substitute the exponential ansatz `c_i * lambda^t` and remove the common
factor `lambda^y`. -/
noncomputable def coeffEval (e : RetardedExpr ι) (c : ι → ℝ) (lam : ℝ) : ℝ :=
  match e with
  | .leaf i lag => c i * lam ^ (-lag)
  | .add a b => a.coeffEval c lam + b.coeffEval c lam
  | .min a b => _root_.min (a.coeffEval c lam) (b.coeffEval c lam)

/-- Every leaf lag lies in the closed interval `[mu, nu]`. -/
def LagsIn (e : RetardedExpr ι) (mu nu : ℝ) : Prop :=
  match e with
  | .leaf _ lag => mu ≤ lag ∧ lag ≤ nu
  | .add a b => a.LagsIn mu nu ∧ b.LagsIn mu nu
  | .min a b => a.LagsIn mu nu ∧ b.LagsIn mu nu

/-- Addition and minimum preserve a common nonnegative factor in lower-bound
comparisons. -/
theorem factor_coeffEval_le_eval
    (e : RetardedExpr ι) (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (lam A mu nu y : ℝ) (hA : 0 ≤ A) (hlags : e.LagsIn mu nu)
    (hleaf : ∀ i lag, mu ≤ lag → lag ≤ nu →
      A * (c i * lam ^ (-lag)) ≤ φ i (y - lag)) :
    A * e.coeffEval c lam ≤ e.eval φ y := by
  induction e with
  | leaf i lag =>
      exact hleaf i lag hlags.1 hlags.2
  | add a b iha ihb =>
      rw [coeffEval, eval, mul_add]
      exact add_le_add (iha hlags.1) (ihb hlags.2)
  | min a b iha ihb =>
      rw [coeffEval, eval, mul_min_of_nonneg _ _ hA]
      exact min_le_min (iha hlags.1) (ihb hlags.2)

/-- Exponential powers split across a backward real shift. -/
theorem rpow_sub_lag {lam y lag : ℝ} (hlam : 0 < lam) :
    lam ^ (y - lag) = lam ^ y * lam ^ (-lag) := by
  rw [Real.rpow_sub hlam, Real.rpow_neg hlam.le]
  rfl

/-- One strip of an exponential lower bound propagates across all later
strips when every difference term is delayed by at least `mu > 0` and at most
`nu`. -/
theorem exponential_lower_bound_of_retarded
    (tree : ι → RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (lam Δ mu nu : ℝ)
    (hlam : 0 < lam) (hΔ : 0 ≤ Δ) (hmu : 0 < mu) (hnu : 0 ≤ nu)
    (hlags : ∀ i, (tree i).LagsIn mu nu)
    (hdiff : ∀ i y, nu ≤ y → (tree i).eval φ y ≤ φ i y)
    (hlp : ∀ i, c i ≤ (tree i).coeffEval c lam)
    (hinitial : ∀ i y, 0 ≤ y → y ≤ nu → Δ * c i * lam ^ y ≤ φ i y) :
    ∀ i y, 0 ≤ y → Δ * c i * lam ^ y ≤ φ i y := by
  have hstrips : ∀ n : ℕ, ∀ i y, 0 ≤ y →
      y ≤ nu + (n : ℝ) * mu → Δ * c i * lam ^ y ≤ φ i y := by
    intro n
    induction n with
    | zero =>
        intro i y hy0 hy
        apply hinitial i y hy0
        simpa using hy
    | succ n ih =>
        intro i y hy0 hy
        by_cases hold : y ≤ nu + (n : ℝ) * mu
        · exact ih i y hy0 hold
        · have hyold : nu + (n : ℝ) * mu < y := lt_of_not_ge hold
          have hyν : nu ≤ y := by
            have : nu ≤ nu + (n : ℝ) * mu := by positivity
            exact this.trans hyold.le
          let A := Δ * lam ^ y
          have hA : 0 ≤ A := mul_nonneg hΔ (Real.rpow_nonneg hlam.le _)
          have hleaf : ∀ state lag, mu ≤ lag → lag ≤ nu →
              A * (c state * lam ^ (-lag)) ≤ φ state (y - lag) := by
            intro state lag hlagμ hlagν
            have htime0 : 0 ≤ y - lag := by linarith
            have htimeUpper : y - lag ≤ nu + (n : ℝ) * mu := by
              norm_num [Nat.cast_succ] at hy
              linarith
            have hbound := ih state (y - lag) htime0 htimeUpper
            have hpow := rpow_sub_lag (lam := lam) (y := y) (lag := lag) hlam
            calc
              A * (c state * lam ^ (-lag)) =
                  Δ * c state * lam ^ (y - lag) := by
                    rw [hpow]
                    simp only [A]
                    ring
              _ ≤ φ state (y - lag) := hbound
          have htree := factor_coeffEval_le_eval (tree i) φ c lam A mu nu y hA
            (hlags i) hleaf
          calc
            Δ * c i * lam ^ y = A * c i := by simp only [A]; ring
            _ ≤ A * (tree i).coeffEval c lam :=
              mul_le_mul_of_nonneg_left (hlp i) hA
            _ ≤ (tree i).eval φ y := htree
            _ ≤ φ i y := hdiff i y hyν
  intro i y hy0
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (y / mu)
  have hyn : y < (n : ℝ) * mu := (div_lt_iff₀ hmu).mp hn
  apply hstrips n i y hy0
  linarith

end RetardedExpr

end CleanLean.KL
