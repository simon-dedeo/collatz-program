/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Algebraic core of the Väänänen--Wallisser theta function

The 1989 paper studies

`f_q(x) = sum n, q^(-n(n+1)/2) x^n`

through the functional equation `f_q(q*x)=x*f_q(x)+1`.  This file begins an
independent formalization of the cited theorem.  It kernel-checks the exact
finite identity and derives the completed functional equation from explicit
summability hypotheses.  No linear-independence theorem is assumed here.

Keeping the finite identity separate is useful for the eventual Skolem--
Hermite proof: all analytic and p-adic convergence obligations can be audited
without changing the polynomial algebra.
-/

namespace KontoroC
namespace VaananenWallisser

/-- The paper's exponent `n(n+1)/2`, represented without division. -/
def exponent (n : ℕ) : ℕ := n.choose 2 + n

theorem exponent_zero : exponent 0 = 0 := by simp [exponent]

theorem exponent_succ (n : ℕ) :
    exponent (n + 1) = exponent n + (n + 1) := by
  simp only [exponent]
  rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
  simp
  omega

/-- The `n`th term of the Väänänen--Wallisser theta series. -/
def thetaTerm {K : Type*} [Field K] (q x : K) (n : ℕ) : K :=
  q⁻¹ ^ exponent n * x ^ n

theorem thetaTerm_zero {K : Type*} [Field K] (q x : K) :
    thetaTerm q x 0 = 1 := by simp [thetaTerm, exponent]

/-- Coefficientwise form of the paper's functional equation. -/
theorem thetaTerm_shift {K : Type*} [Field K] (q x : K) (hq : q ≠ 0)
    (n : ℕ) :
    thetaTerm q (q * x) (n + 1) = x * thetaTerm q x n := by
  simp only [thetaTerm, exponent_succ, pow_add, mul_pow]
  field_simp
  simp [hq]

/-- Finite truncation of the theta series. -/
def thetaPartial {K : Type*} [Field K] (q x : K) (N : ℕ) : K :=
  ∑ n ∈ Finset.range N, thetaTerm q x n

/-- Exact finite functional equation, including its single terminal error. -/
theorem thetaPartial_functional {K : Type*} [Field K]
    (q x : K) (hq : q ≠ 0) (N : ℕ) :
    thetaPartial q (q * x) (N + 1) = 1 + x * thetaPartial q x N := by
  calc
    thetaPartial q (q * x) (N + 1) =
        (∑ n ∈ Finset.range N, thetaTerm q (q * x) (n + 1)) +
          thetaTerm q (q * x) 0 := by
      rw [thetaPartial, Finset.sum_range_succ']
    _ = (∑ n ∈ Finset.range N, x * thetaTerm q x n) + 1 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro n _
        exact thetaTerm_shift q x hq n
      · exact thetaTerm_zero q (q * x)
    _ = 1 + x * thetaPartial q x N := by
      rw [thetaPartial, Finset.mul_sum]
      ac_rfl

/-- The completed theta value in any topological field where the series is
summable.  For this project the intended field is `ℚ_[2]`. -/
noncomputable def thetaSum {K : Type*} [Field K] [TopologicalSpace K]
    (q x : K) : K := ∑' n, thetaTerm q x n

/-- The exact infinite functional equation.  Convergence is deliberately an
explicit hypothesis: proving it from the paper's arithmetic assumptions is a
separate, reusable analytic layer. -/
theorem thetaSum_functional {K : Type*} [NormedField K]
    [CompleteSpace K] (q x : K) (hq : q ≠ 0)
    (hs : Summable (thetaTerm q x)) :
    thetaSum q (q * x) = 1 + x * thetaSum q x := by
  have htail : HasSum (fun n => thetaTerm q (q * x) (n + 1))
      (x * thetaSum q x) := by
    have hmul : HasSum (fun n => x * thetaTerm q x n)
        (x * thetaSum q x) := hs.hasSum.mul_left x
    exact hmul.congr_fun (fun n => thetaTerm_shift q x hq n)
  have hall : HasSum (thetaTerm q (q * x))
      (1 + x * thetaSum q x) := by
    have h := (hasSum_nat_add_iff 1).mp htail
    simpa [thetaTerm_zero, add_comm] using h
  exact hall.tsum_eq

/-! ## The Skolem--Hermite polynomial recurrence -/

open Polynomial

/-- Equation (11) of the paper.  `Polynomial.divX` removes the constant
coefficient without introducing a field-division algorithm. -/
noncomputable def hermiteStep {K : Type*} [Field K]
    (q : K) (P : K[X]) : K[X] :=
  Polynomial.divX (P.comp (C q * X))

noncomputable def hermiteIter {K : Type*} [Field K]
    (q : K) (μ : ℕ) (P : K[X]) : K[X] :=
  (hermiteStep q)^[μ] P

/-- Exact polynomial form of `(P(qx)-P(0))/x`; this avoids informal
division by `x` at the zero coefficient. -/
theorem X_mul_hermiteStep_add {K : Type*} [Field K]
    (q : K) (P : K[X]) :
    X * hermiteStep q P + C (P.eval 0) = P.comp (C q * X) := by
  have h := Polynomial.X_mul_divX_add (P.comp (C q * X))
  simpa [hermiteStep, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp] using h

/-- One closed recurrence step on the monomial-times-polynomial shape used
in (12).  This is the algebraic engine behind the paper's formula (15). -/
theorem hermiteStep_C_mul_X_pow_succ_mul {K : Type*} [Field K]
    (q κ : K) (s : ℕ) (R : K[X]) :
    hermiteStep q (C κ * X ^ (s + 1) * R) =
      C (κ * q ^ (s + 1)) * X ^ s * R.comp (C q * X) := by
  apply mul_left_cancel₀ (a := X) Polynomial.X_ne_zero
  have h := X_mul_hermiteStep_add q (C κ * X ^ (s + 1) * R)
  have heval : (C κ * X ^ (s + 1) * R).eval 0 = 0 := by simp
  rw [heval, map_zero, add_zero] at h
  rw [h]
  simp [pow_succ]
  ring

/-- Scalar accumulated through `μ` Hermite steps starting from degree shift
`S`.  It is kept as a finite product so the closed polynomial identity does
not depend on delicate natural-subtraction normalization. -/
def hermiteScale {K : Type*} [Field K]
    (q κ : K) (S μ : ℕ) : K :=
  κ * ∏ i ∈ Finset.range μ, q ^ (S - i)

theorem hermiteScale_succ {K : Type*} [Field K]
    (q κ : K) (S μ : ℕ) :
    hermiteScale q κ S (μ + 1) =
      hermiteScale q κ S μ * q ^ (S - μ) := by
  simp [hermiteScale, Finset.prod_range_succ, mul_assoc]

/-- Closed form of the paper's polynomial recurrence through every step
before the initial power of `X` is exhausted.  This is the structural part
of formula (15), specialized only in that the remaining root polynomial is
left abstract. -/
theorem hermiteIter_C_mul_X_pow_mul {K : Type*} [Field K]
    (q κ : K) (S μ : ℕ) (R : K[X]) (hμ : μ ≤ S) :
    hermiteIter q μ (C κ * X ^ S * R) =
      C (hermiteScale q κ S μ) * X ^ (S - μ) *
        R.comp (C (q ^ μ) * X) := by
  induction μ with
  | zero => simp [hermiteIter, hermiteScale]
  | succ μ ih =>
      have hprev : μ ≤ S := Nat.le_trans (Nat.le_succ μ) hμ
      rw [hermiteIter, Function.iterate_succ_apply']
      change hermiteStep q (hermiteIter q μ (C κ * X ^ S * R)) = _
      rw [ih hprev]
      have hshift : S - μ = (S - (μ + 1)) + 1 := by omega
      rw [hshift, hermiteStep_C_mul_X_pow_succ_mul,
        hermiteScale_succ]
      simp [Polynomial.comp_assoc, pow_succ]
      rw [show S - μ = S - (1 + μ) + 1 by omega, pow_succ]
      ring

/-! ## Source polynomial for the first required specialization -/

/-- The untapered root product in (13) when `ell=1` and `sigma=0`:
`prod_(a<ν) (x/q^a-alpha)`. -/
noncomputable def skolemRootProduct {K : Type*} [Field K]
    (q α : K) (ν : ℕ) : K[X] :=
  ∏ a ∈ Finset.range ν, (C ((q ^ a)⁻¹) * X - C α)

/-- Formula (12) in the one-value, zero-derivative case.  The arithmetic
normalization of `κ` is intentionally separate from this polynomial shape. -/
noncomputable def skolemInitial {K : Type*} [Field K]
    (q α κ : K) (ν t : ℕ) : K[X] :=
  C κ * X ^ (ν + t + 1) * skolemRootProduct q α ν

/-- Structural specialization of formula (15).  The remaining work in the
1989 theorem is arithmetic: choose `κ`, prove valuation separation, and
establish the height/remainder estimates. -/
theorem hermiteIter_skolemInitial {K : Type*} [Field K]
    (q α κ : K) (ν t μ : ℕ) (hμ : μ ≤ ν + t + 1) :
    hermiteIter q μ (skolemInitial q α κ ν t) =
      C (hermiteScale q κ (ν + t + 1) μ) *
        X ^ (ν + t + 1 - μ) *
        (skolemRootProduct q α ν).comp (C (q ^ μ) * X) := by
  exact hermiteIter_C_mul_X_pow_mul q κ (ν + t + 1) μ
    (skolemRootProduct q α ν) hμ

/-- Before the Hermite index reaches `ν`, the shifted root product still
vanishes at `α`: its factor with address `a=μ` is exactly zero.  This is the
algebraic vanishing that isolates the first nonzero term in Hilfssatz 1. -/
theorem eval_skolemRootProduct_comp_eq_zero {K : Type*} [Field K]
    (q α : K) (hq : q ≠ 0) (ν μ : ℕ) (hμ : μ < ν) :
    ((skolemRootProduct q α ν).comp (C (q ^ μ) * X)).eval α = 0 := by
  rw [Polynomial.eval_comp]
  simp only [eval_mul, eval_C, eval_X]
  let factor : ℕ → K[X] := fun a => C ((q ^ a)⁻¹) * X - C α
  have hdiv : factor μ ∣ skolemRootProduct q α ν := by
    rw [skolemRootProduct]
    exact Finset.dvd_prod_of_mem factor (Finset.mem_range.mpr hμ)
  obtain ⟨R, hR⟩ := hdiv
  rw [hR, eval_mul]
  have hqμ : q ^ μ ≠ 0 := pow_ne_zero μ hq
  have hzero : (factor μ).eval (q ^ μ * α) = 0 := by
    simp [factor, hqμ]
  rw [hzero, zero_mul]

/-- Consequently every source polynomial `P_μ(α)` with `μ<ν` vanishes
exactly.  This proves the zero pattern used before the paper's genuinely
arithmetic valuation calculation; no p-adic estimate is involved. -/
theorem eval_hermiteIter_skolemInitial_eq_zero {K : Type*} [Field K]
    (q α κ : K) (hq : q ≠ 0) (ν t μ : ℕ) (hμ : μ < ν) :
    (hermiteIter q μ (skolemInitial q α κ ν t)).eval α = 0 := by
  rw [hermiteIter_skolemInitial q α κ ν t μ (by omega)]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [eval_skolemRootProduct_comp_eq_zero q α hq ν μ hμ]
  simp

end VaananenWallisser
end KontoroC
