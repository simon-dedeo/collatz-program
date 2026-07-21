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
  | inf (left right : RetardedExpr ι)

namespace RetardedExpr

variable {ι : Type}

/-- Evaluate a retarded expression on a family of real functions. -/
def eval (e : RetardedExpr ι) (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  match e with
  | .leaf i lag => φ i (y - lag)
  | .add a b => a.eval φ y + b.eval φ y
  | .inf a b => min (a.eval φ y) (b.eval φ y)

/-- Substitute the exponential ansatz `c_i * lambda^t` and remove the common
factor `lambda^y`. -/
noncomputable def coeffEval (e : RetardedExpr ι) (c : ι → ℝ) (lam : ℝ) : ℝ :=
  match e with
  | .leaf i lag => c i * lam ^ (-lag)
  | .add a b => a.coeffEval c lam + b.coeffEval c lam
  | .inf a b => min (a.coeffEval c lam) (b.coeffEval c lam)

/-- Every leaf lag lies in the closed interval `[mu, nu]`. -/
def LagsIn (e : RetardedExpr ι) (mu nu : ℝ) : Prop :=
  match e with
  | .leaf _ lag => mu ≤ lag ∧ lag ≤ nu
  | .add a b => a.LagsIn mu nu ∧ b.LagsIn mu nu
  | .inf a b => a.LagsIn mu nu ∧ b.LagsIn mu nu

/-- Lowering the common lower lag bound preserves `LagsIn`. -/
theorem LagsIn.mono_lower {e : RetardedExpr ι} {mu mu' nu : ℝ}
    (h : e.LagsIn mu nu) (hle : mu' ≤ mu) : e.LagsIn mu' nu := by
  induction e with
  | leaf state lag => exact ⟨hle.trans h.1, h.2⟩
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | inf left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩

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
  | inf a b iha ihb =>
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
            have hnonneg : 0 ≤ (n : ℝ) * mu :=
              mul_nonneg (Nat.cast_nonneg n) hmu.le
            exact (le_add_of_nonneg_right hnonneg).trans hyold.le
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

/-- KL-style specialization: monotonicity and uniform lower/upper constants
produce the initial strip automatically.  Taking `p0 = min_i φ_i(0)` and
`C = max_i c_i` gives exactly the constant in Theorem 5.1. -/
theorem exponential_lower_bound_of_retarded_with_constants
    (tree : ι → RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (lam mu nu p0 C : ℝ)
    (hlam : 1 < lam) (hmu : 0 < mu) (hnu : 0 ≤ nu)
    (hp0 : 0 ≤ p0) (hC : 0 < C)
    (hc0 : ∀ i, 0 ≤ c i) (hcC : ∀ i, c i ≤ C)
    (hφ0 : ∀ i, p0 ≤ φ i 0) (hmono : ∀ i, Monotone (φ i))
    (hlags : ∀ i, (tree i).LagsIn mu nu)
    (hdiff : ∀ i y, nu ≤ y → (tree i).eval φ y ≤ φ i y)
    (hlp : ∀ i, c i ≤ (tree i).coeffEval c lam) :
    ∀ i y, 0 ≤ y →
      (lam ^ (-nu) * p0 / C) * c i * lam ^ y ≤ φ i y := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hΔ : 0 ≤ lam ^ (-nu) * p0 / C :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg hlam0.le _) hp0) hC.le
  apply exponential_lower_bound_of_retarded tree φ c lam
    (lam ^ (-nu) * p0 / C) mu nu hlam0 hΔ hmu hnu hlags hdiff hlp
  intro i y hy0 hyν
  have hpow : lam ^ y ≤ lam ^ nu :=
    Real.rpow_le_rpow_of_exponent_le hlam.le hyν
  have hneg : 0 ≤ lam ^ (-nu) := Real.rpow_nonneg hlam0.le _
  have hratio0 : 0 ≤ c i / C := div_nonneg (hc0 i) hC.le
  have hratio1 : c i / C ≤ 1 := (div_le_one hC).2 (hcC i)
  have hshift : lam ^ (-nu) * lam ^ y ≤ lam ^ (-nu) * lam ^ nu :=
    mul_le_mul_of_nonneg_left hpow hneg
  have hcombined :
      (c i / C) * (lam ^ (-nu) * lam ^ y) ≤
        1 * (lam ^ (-nu) * lam ^ nu) :=
    mul_le_mul hratio1 hshift
      (mul_nonneg hneg (Real.rpow_nonneg hlam0.le _)) zero_le_one
  have hone : lam ^ (-nu) * lam ^ nu = 1 := by
    rw [← Real.rpow_add hlam0, neg_add_cancel, Real.rpow_zero]
  calc
    (lam ^ (-nu) * p0 / C) * c i * lam ^ y =
        p0 * ((c i / C) * (lam ^ (-nu) * lam ^ y)) := by ring
    _ ≤ p0 * (1 * (lam ^ (-nu) * lam ^ nu)) :=
      mul_le_mul_of_nonneg_left hcombined hp0
    _ = p0 := by rw [hone]; ring
    _ ≤ φ i 0 := hφ0 i
    _ ≤ φ i y := hmono i hy0

/-- The numerical simplification used in KL Theorem 2.2: if
`1 < lambda ≤ 2`, `nu ≤ 2`, and the initial minimum is at least one, then the
comparison constant is at least `1 / (4*C)`. -/
theorem quarter_div_le_retarded_constant
    {lam nu p0 C : ℝ} (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (hnu2 : nu ≤ 2) (hp0 : 1 ≤ p0) (hC : 0 < C) :
    1 / (4 * C) ≤ lam ^ (-nu) * p0 / C := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam1
  have hpowExp : lam ^ nu ≤ lam ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlam1.le hnu2
  have hpowBase : lam ^ (2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow hlam0.le hlam2 (by norm_num)
  have hpow : lam ^ nu ≤ 4 := by
    calc
      lam ^ nu ≤ lam ^ (2 : ℝ) := hpowExp
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := hpowBase
      _ = 4 := by norm_num [Real.rpow_two]
  have hpowPos : 0 < lam ^ nu := Real.rpow_pos_of_pos hlam0 _
  have hinv : (1 : ℝ) / 4 ≤ (lam ^ nu)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hpowPos).2
    nlinarith
  have hneg : lam ^ (-nu) = (lam ^ nu)⁻¹ := Real.rpow_neg hlam0.le nu
  have hquarter : (1 : ℝ) / 4 ≤ lam ^ (-nu) := by simpa [hneg] using hinv
  have hretNonneg : 0 ≤ lam ^ (-nu) := Real.rpow_nonneg hlam0.le _
  have hp : lam ^ (-nu) ≤ lam ^ (-nu) * p0 := by
    nlinarith [mul_le_mul_of_nonneg_left hp0 hretNonneg]
  have hconst : (1 : ℝ) / 4 ≤ lam ^ (-nu) * p0 := hquarter.trans hp
  have hdiv := div_le_div_of_nonneg_right hconst hC.le
  have heq : (1 : ℝ) / (4 * C) = ((1 : ℝ) / 4) / C := by
    field_simp [hC.ne']
  rw [heq]
  exact hdiv

/-- Theorem-5.1 comparison with the exact coarse constant used by KL
Theorem 2.2.  What remains outside this theorem is the construction of the
retarded trees and proof that their LP is feasible. -/
theorem quarter_exponential_lower_bound_of_retarded
    (tree : ι → RetardedExpr ι)
    (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (lam mu nu p0 C : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (hmu : 0 < mu) (hnu0 : 0 ≤ nu) (hnu2 : nu ≤ 2)
    (hp0 : 1 ≤ p0) (hC : 0 < C)
    (hc0 : ∀ i, 0 ≤ c i) (hcC : ∀ i, c i ≤ C)
    (hφ0 : ∀ i, p0 ≤ φ i 0) (hmono : ∀ i, Monotone (φ i))
    (hlags : ∀ i, (tree i).LagsIn mu nu)
    (hdiff : ∀ i y, nu ≤ y → (tree i).eval φ y ≤ φ i y)
    (hlp : ∀ i, c i ≤ (tree i).coeffEval c lam) :
    ∀ i y, 0 ≤ y → (1 / (4 * C)) * c i * lam ^ y ≤ φ i y := by
  have hstrong := exponential_lower_bound_of_retarded_with_constants
    tree φ c lam mu nu p0 C hlam1 hmu hnu0 (zero_le_one.trans hp0) hC
    hc0 hcC hφ0 hmono hlags hdiff hlp
  have hconst := quarter_div_le_retarded_constant hlam1 hlam2 hnu2 hp0 hC
  intro i y hy
  have hfactor : 0 ≤ c i * lam ^ y :=
    mul_nonneg (hc0 i) (Real.rpow_nonneg (zero_lt_one.trans hlam1).le _)
  have hscaled := mul_le_mul_of_nonneg_right hconst hfactor
  calc
    (1 / (4 * C)) * c i * lam ^ y = (1 / (4 * C)) * (c i * lam ^ y) := by ring
    _ ≤ (lam ^ (-nu) * p0 / C) * (c i * lam ^ y) := hscaled
    _ = (lam ^ (-nu) * p0 / C) * c i * lam ^ y := by ring
    _ ≤ φ i y := hstrong i y hy

end RetardedExpr

end CleanLean.KL
