/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.SpecificLimits.Normed

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

open Filter Topology

/-- The paper's exponent `n(n+1)/2`, represented without division. -/
def exponent (n : ℕ) : ℕ := n.choose 2 + n

theorem exponent_zero : exponent 0 = 0 := by simp [exponent]

theorem exponent_succ (n : ℕ) :
    exponent (n + 1) = exponent n + (n + 1) := by
  simp only [exponent]
  rw [show n + 1 = n.succ by omega, Nat.choose_succ_succ]
  simp
  omega

theorem self_le_exponent (n : ℕ) : n ≤ exponent n := by
  simp [exponent]

/-- The `n`th term of the Väänänen--Wallisser theta series. -/
def thetaTerm {K : Type*} [Field K] (q x : K) (n : ℕ) : K :=
  q⁻¹ ^ exponent n * x ^ n

/-- In the natural non-Archimedean convergence range, the quadratic theta
term is bounded by an ordinary geometric sequence.  The deliberately weaker
linear bound `n ≤ exponent n` is already sufficient. -/
theorem norm_thetaTerm_le_geometric {K : Type*} [NormedField K]
    (q x : K) (hq : 1 < ‖q‖) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ‖thetaTerm q x n‖ ≤ ‖q‖⁻¹ ^ n := by
  have hqinv0 : 0 ≤ ‖q‖⁻¹ := by positivity
  have hqinv1 : ‖q‖⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hq).le
  rw [thetaTerm, norm_mul, norm_pow, norm_pow, norm_inv]
  calc
    ‖q‖⁻¹ ^ exponent n * ‖x‖ ^ n ≤
        ‖q‖⁻¹ ^ exponent n * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg x) hx)
        (by positivity)
    _ = ‖q‖⁻¹ ^ exponent n := by ring
    _ ≤ ‖q‖⁻¹ ^ n :=
      pow_le_pow_of_le_one hqinv0 hqinv1 (self_le_exponent n)

theorem thetaTerm_tendsto_zero_of_norm {K : Type*} [NormedField K]
    (q x : K) (hq : 1 < ‖q‖) (hx : ‖x‖ ≤ 1) :
    Tendsto (thetaTerm q x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_thetaTerm_le_geometric q x hq hx)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ hq)

/-- Over a complete non-Archimedean field, the Väänänen--Wallisser theta
series converges throughout the norm range used by the project's 2-adic
applications. -/
theorem thetaTerm_summable_of_norm {K : Type*} [NormedField K]
    [CompleteSpace K] [NonarchimedeanAddGroup K]
    (q x : K) (hq : 1 < ‖q‖) (hx : ‖x‖ ≤ 1) :
    Summable (thetaTerm q x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using
    thetaTerm_tendsto_zero_of_norm q x hq hx

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

/-- The completed functional equation with convergence discharged by the
standard non-Archimedean norm hypotheses. -/
theorem thetaSum_functional_of_norm {K : Type*} [NormedField K]
    [CompleteSpace K] [NonarchimedeanAddGroup K]
    (q x : K) (hq : 1 < ‖q‖) (hx : ‖x‖ ≤ 1) :
    thetaSum q (q * x) = 1 + x * thetaSum q x := by
  have hq0 : q ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hq)
  exact thetaSum_functional q x hq0
    (thetaTerm_summable_of_norm q x hq hx)

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

/-- Exact value of the shifted Skolem root product at the distinguished
point.  This is the finite product hidden behind the valuation calculation
in Hilfssatz 1 of Väänänen--Wallisser.  In particular, at the first index
outside the planted zero range (`μ = ν`), every factor is a multiplicative
gap between two powers of `q`.

Keeping the factors in the paper's original address order avoids any
reindexing convention: later arithmetic specializations can compute the
valuation of each term independently. -/
theorem eval_skolemRootProduct_comp_exact {K : Type*} [Field K]
    (q α : K) (ν μ : ℕ) :
    ((skolemRootProduct q α ν).comp (C (q ^ μ) * X)).eval α =
      α ^ ν * ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ μ - 1) := by
  rw [Polynomial.eval_comp]
  simp only [eval_mul, eval_C, eval_X, skolemRootProduct,
    Polynomial.eval_prod]
  simp_rw [eval_sub, eval_mul, eval_C, eval_X]
  calc
    (∏ a ∈ Finset.range ν,
        ((q ^ a)⁻¹ * (q ^ μ * α) - α)) =
        ∏ a ∈ Finset.range ν,
          (α * ((q ^ a)⁻¹ * q ^ μ - 1)) := by
      apply Finset.prod_congr rfl
      intro a _ha
      ring
    _ = (∏ _a ∈ Finset.range ν, α) *
        ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ μ - 1) := by
      rw [Finset.prod_mul_distrib]
    _ = α ^ ν *
        ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ μ - 1) := by
      simp

/-- The exact first nonzero Hermite specialization.  All dependence on the
analytic theta series has disappeared: the value is a scalar, one power of
the distinguished point, and a finite power-gap product.  This is the right
interface for the missing p-adic normalization and valuation layer of the
1989 proof. -/
theorem eval_hermiteIter_skolemInitial_boundary_exact
    {K : Type*} [Field K] (q α κ : K) (ν t : ℕ) :
    (hermiteIter q ν (skolemInitial q α κ ν t)).eval α =
      hermiteScale q κ (ν + t + 1) ν * α ^ (ν + t + 1) *
        ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ ν - 1) := by
  rw [hermiteIter_skolemInitial q α κ ν t ν (by omega)]
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    eval_skolemRootProduct_comp_exact]
  rw [show ν + t + 1 - ν = t + 1 by omega]
  have hpow : α ^ (t + 1) * α ^ ν = α ^ (ν + t + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    hermiteScale q κ (ν + t + 1) ν * α ^ (t + 1) *
        (α ^ ν * ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ ν - 1)) =
      hermiteScale q κ (ν + t + 1) ν *
        (α ^ (t + 1) * α ^ ν) *
          ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ ν - 1) := by ring
    _ = hermiteScale q κ (ν + t + 1) ν * α ^ (ν + t + 1) *
        ∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ ν - 1) := by
      rw [hpow]

/-! ## The first arithmetic specialization used by the project -/

/-- At the project's Väänänen--Wallisser parameter `q = 3/2`, every
positive power gap has exactly the negative 2-adic valuation contributed by
its denominator.  There is no hidden cancellation: `3^d - 2^d` is odd.

This is the local arithmetic input behind the valuation of the finite gap
product in the preceding boundary formula. -/
theorem padicValRat_threeHalves_pow_sub_one (d : ℕ) (hd : 0 < d) :
    padicValRat 2 (((3 : ℚ) / 2) ^ d - 1) = -(d : ℤ) := by
  have hq : (3 : ℚ) / 2 ≠ 0 := by norm_num
  have hpow : ((3 : ℚ) / 2) ^ d ≠ 0 := pow_ne_zero d hq
  have hgt : (1 : ℚ) < ((3 : ℚ) / 2) ^ d := by
    exact one_lt_pow₀ (by norm_num) hd.ne'
  have hgap : ((3 : ℚ) / 2) ^ d + (-1) ≠ 0 := by
    simpa only [sub_eq_add_neg] using
      (sub_ne_zero.mpr (ne_of_gt hgt))
  have hvalq : padicValRat 2 ((3 : ℚ) / 2) = -1 := by
    rw [padicValRat.div (by norm_num) (by norm_num)]
    have hval3 : padicValRat 2 (3 : ℚ) = 0 := by
      rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num,
        padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd
        (p := 2) (n := 3) (by norm_num)
    have hval2 : padicValRat 2 (2 : ℚ) = 1 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
        padicValRat.of_nat]
      simpa using (padicValNat.prime_pow (p := 2) 1)
    rw [hval3, hval2]
    norm_num
  have hvalpow : padicValRat 2 (((3 : ℚ) / 2) ^ d) = -(d : ℤ) := by
    rw [padicValRat.pow, hvalq]
    omega
  have hlt : padicValRat 2 (((3 : ℚ) / 2) ^ d) <
      padicValRat 2 (-1 : ℚ) := by
    rw [hvalpow, padicValRat.neg, padicValRat.one]
    omega
  rw [sub_eq_add_neg]
  rw [padicValRat.add_eq_of_lt hgap hpow (by norm_num) hlt, hvalpow]

/-- The auxiliary prime in the Skolem--Hermite proof divides the numerator
of `q`.  For the project's `q=3/2` specialization this is `rho=3`, not the
target-field prime two.  Every power gap is a 3-adic unit, so the entire gap
product contributes no hidden `rho`-valuation. -/
theorem padicValRat_three_threeHalves_pow_sub_one (d : ℕ) (hd : 0 < d) :
    padicValRat 3 (((3 : ℚ) / 2) ^ d - 1) = 0 := by
  have hq : (3 : ℚ) / 2 ≠ 0 := by norm_num
  have hpow : ((3 : ℚ) / 2) ^ d ≠ 0 := pow_ne_zero d hq
  have hgt : (1 : ℚ) < ((3 : ℚ) / 2) ^ d := by
    exact one_lt_pow₀ (by norm_num) hd.ne'
  have hgap : (-1 : ℚ) + ((3 : ℚ) / 2) ^ d ≠ 0 := by
    rw [add_comm]
    simpa only [sub_eq_add_neg] using sub_ne_zero.mpr (ne_of_gt hgt)
  have hvalq : padicValRat 3 ((3 : ℚ) / 2) = 1 := by
    rw [padicValRat.div (by norm_num) (by norm_num)]
    have hval3 : padicValRat 3 (3 : ℚ) = 1 := by
      rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num,
        padicValRat.of_nat]
      simpa using (padicValNat.prime_pow (p := 3) 1)
    have hval2 : padicValRat 3 (2 : ℚ) = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
        padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd
        (p := 3) (n := 2) (by norm_num)
    rw [hval3, hval2]
    norm_num
  have hvalpow : padicValRat 3 (((3 : ℚ) / 2) ^ d) = (d : ℤ) := by
    rw [padicValRat.pow, hvalq]
    simp
  have hlt : padicValRat 3 (-1 : ℚ) <
      padicValRat 3 (((3 : ℚ) / 2) ^ d) := by
    rw [padicValRat.neg, padicValRat.one, hvalpow]
    exact_mod_cast hd
  rw [sub_eq_add_neg, add_comm]
  rw [padicValRat.add_eq_of_lt hgap (by norm_num) hpow hlt,
    padicValRat.neg, padicValRat.one]

/-- The same noncancellation fact without mentioning valuations. -/
theorem threeHalves_pow_sub_one_ne_zero (d : ℕ) (hd : 0 < d) :
    ((3 : ℚ) / 2) ^ d - 1 ≠ 0 := by
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num) hd.ne'))

/-- The power-gap product occurring at the first nonzero Skolem index,
written in increasing rather than decreasing address order. -/
def threeHalvesGapProduct (ν : ℕ) : ℚ :=
  ∏ d ∈ Finset.range ν, (((3 : ℚ) / 2) ^ (d + 1) - 1)

theorem threeHalvesGapProduct_ne_zero (ν : ℕ) :
    threeHalvesGapProduct ν ≠ 0 := by
  rw [threeHalvesGapProduct]
  apply Finset.prod_ne_zero_iff.mpr
  intro d _hd
  exact threeHalves_pow_sub_one_ne_zero (d + 1) (by omega)

/-- Exact valuation of the complete boundary gap product.  The successive
costs are `-1,-2,...,-ν`, so the total is the negative triangular exponent
of the theta series.  This identifies a quadratic term of Hilfssatz 1
without estimates or asymptotics. -/
theorem padicValRat_threeHalvesGapProduct (ν : ℕ) :
    padicValRat 2 (threeHalvesGapProduct ν) = -(exponent ν : ℤ) := by
  induction ν with
  | zero => simp [threeHalvesGapProduct, exponent_zero]
  | succ ν ih =>
      have hsucc : threeHalvesGapProduct (ν + 1) =
          threeHalvesGapProduct ν * (((3 : ℚ) / 2) ^ (ν + 1) - 1) := by
        rw [threeHalvesGapProduct, show ν + 1 = ν.succ by omega,
          Finset.prod_range_succ]
        rfl
      rw [hsucc]
      rw [padicValRat.mul
        (threeHalvesGapProduct_ne_zero ν)
        (threeHalves_pow_sub_one_ne_zero (ν + 1) (by omega))]
      rw [ih, padicValRat_threeHalves_pow_sub_one (ν + 1) (by omega)]
      rw [show exponent (ν + 1) = exponent ν + (ν + 1) by
        exact exponent_succ ν]
      push_cast
      omega

/-- At the paper's auxiliary prime `rho=3`, the complete boundary gap
product is a unit. -/
theorem padicValRat_three_threeHalvesGapProduct (ν : ℕ) :
    padicValRat 3 (threeHalvesGapProduct ν) = 0 := by
  induction ν with
  | zero => simp [threeHalvesGapProduct]
  | succ ν ih =>
      have hsucc : threeHalvesGapProduct (ν + 1) =
          threeHalvesGapProduct ν * (((3 : ℚ) / 2) ^ (ν + 1) - 1) := by
        rw [threeHalvesGapProduct, show ν + 1 = ν.succ by omega,
          Finset.prod_range_succ]
        rfl
      rw [hsucc]
      rw [padicValRat.mul
        (threeHalvesGapProduct_ne_zero ν)
        (threeHalves_pow_sub_one_ne_zero (ν + 1) (by omega))]
      rw [ih, padicValRat_three_threeHalves_pow_sub_one
        (ν + 1) (by omega)]
      norm_num

/-- The decreasing address order produced by the Hermite recurrence is
exactly the increasing gap product above.  This is the bookkeeping bridge
between the generic boundary formula and its 2-adic specialization. -/
theorem boundaryGapProduct_threeHalves (ν : ℕ) :
    (∏ a ∈ Finset.range ν,
      ((((3 : ℚ) / 2) ^ a)⁻¹ * ((3 : ℚ) / 2) ^ ν - 1)) =
        threeHalvesGapProduct ν := by
  let q : ℚ := (3 : ℚ) / 2
  have hq : q ≠ 0 := by norm_num [q]
  calc
    (∏ a ∈ Finset.range ν, ((q ^ a)⁻¹ * q ^ ν - 1)) =
        ∏ a ∈ Finset.range ν, (q ^ (ν - 1 - a + 1) - 1) := by
      apply Finset.prod_congr rfl
      intro a ha
      have ha' : a < ν := Finset.mem_range.mp ha
      have hpow := pow_sub₀ q hq (Nat.le_of_lt ha')
      have hindex : ν - a = ν - 1 - a + 1 := by omega
      calc
        (q ^ a)⁻¹ * q ^ ν - 1 = q ^ ν * (q ^ a)⁻¹ - 1 := by ring
        _ = q ^ (ν - a) - 1 := by rw [hpow]
        _ = q ^ (ν - 1 - a + 1) - 1 := by rw [hindex]
    _ = ∏ d ∈ Finset.range ν, (q ^ (d + 1) - 1) := by
      exact Finset.prod_range_reflect (fun d => q ^ (d + 1) - 1) ν
    _ = threeHalvesGapProduct ν := by rfl

/-- Exact valuation of the literal gap product in the generic first-nonzero
formula. -/
theorem padicValRat_boundaryGapProduct_threeHalves (ν : ℕ) :
    padicValRat 2
      (∏ a ∈ Finset.range ν,
        ((((3 : ℚ) / 2) ^ a)⁻¹ * ((3 : ℚ) / 2) ^ ν - 1)) =
      -(exponent ν : ℤ) := by
  rw [boundaryGapProduct_threeHalves,
    padicValRat_threeHalvesGapProduct]

/-- The literal decreasing-order boundary product is likewise a unit at the
paper's auxiliary prime. -/
theorem padicValRat_three_boundaryGapProduct_threeHalves (ν : ℕ) :
    padicValRat 3
      (∏ a ∈ Finset.range ν,
        ((((3 : ℚ) / 2) ^ a)⁻¹ * ((3 : ℚ) / 2) ^ ν - 1)) = 0 := by
  rw [boundaryGapProduct_threeHalves,
    padicValRat_three_threeHalvesGapProduct]

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

/-- Away from the deliberately planted roots, the shifted Skolem root
product is nonzero.  This is the algebraic separation input used at the first
nonvanishing Hermite index in Hilfssatz 1. -/
theorem eval_skolemRootProduct_comp_ne_zero {K : Type*} [Field K]
    (q α : K) (hq : q ≠ 0) (hα : α ≠ 0) (ν μ : ℕ)
    (hsep : ∀ a < ν, q ^ μ ≠ q ^ a) :
    ((skolemRootProduct q α ν).comp (C (q ^ μ) * X)).eval α ≠ 0 := by
  rw [Polynomial.eval_comp]
  simp only [eval_mul, eval_C, eval_X, skolemRootProduct,
    Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  simp only [Finset.mem_range] at ha
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  have hqa : q ^ a ≠ 0 := pow_ne_zero a hq
  intro hzero
  apply hsep a ha
  rw [sub_eq_zero] at hzero
  have hscaled := congrArg (fun z : K => q ^ a * z) hzero
  field_simp [hqa] at hscaled
  exact hscaled

theorem hermiteScale_ne_zero {K : Type*} [Field K]
    (q κ : K) (hq : q ≠ 0) (hκ : κ ≠ 0) (S μ : ℕ) :
    hermiteScale q κ S μ ≠ 0 := by
  rw [hermiteScale]
  apply mul_ne_zero hκ
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact pow_ne_zero _ hq

/-- The first index after the forced zero range is genuinely nonzero.  The
remaining content of the 1989 theorem is therefore quantitative: compare its
valuation against the other specializations and bound the Hermite remainder. -/
theorem eval_hermiteIter_skolemInitial_boundary_ne_zero
    {K : Type*} [Field K]
    (q α κ : K) (hq : q ≠ 0) (hα : α ≠ 0) (hκ : κ ≠ 0)
    (ν t : ℕ) (hsep : ∀ a < ν, q ^ ν ≠ q ^ a) :
    (hermiteIter q ν (skolemInitial q α κ ν t)).eval α ≠ 0 := by
  rw [hermiteIter_skolemInitial q α κ ν t ν (by omega)]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  exact mul_ne_zero
    (mul_ne_zero (hermiteScale_ne_zero q κ hq hκ (ν + t + 1) ν)
      (pow_ne_zero _ hα))
    (eval_skolemRootProduct_comp_ne_zero q α hq hα ν ν hsep)

end VaananenWallisser
end KontoroC
