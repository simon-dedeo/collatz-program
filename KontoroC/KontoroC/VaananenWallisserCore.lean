/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

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

end VaananenWallisser
end KontoroC
