/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.SoftKLOperator

/-!
# Exact natural-power thresholds for cold KL certificates

The cold-to-hard theorem is stated with the analytic threshold
`3^(1 / beta) < r`.  For a natural inverse temperature, a portable rational
certificate should instead prove the finite exact inequality `3 < r^beta`.
This file supplies that conversion and composes it with the existing
soft-to-hard and predecessor-counting endpoints.

The PSC K1b rows are floating diagnostics and do not instantiate these
theorems.  A future certificate must provide a positive rational vector and
an exact natural-power comparison.
-/

namespace KontoroC
namespace KLColdPowerCertificate

open Filter
open CleanLean.KL
open CleanLean.KL.ResidueSystem

noncomputable section

/-- Raising both positive sides to a positive natural power converts the
cold analytic threshold into a finite power inequality. -/
theorem three_rpow_inv_nat_lt_of_pow_gt
    (beta : Nat) (hbeta : 0 < beta) (r : Real) (hr : 0 <= r)
    (hpow : (3 : Real) < r ^ beta) :
    (3 : Real) ^ (1 / (beta : Real)) < r := by
  rw [← Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (by norm_num) _) hr (by positivity : (0 : Real) < beta)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 3)]
  rw [one_div_mul_cancel (by exact_mod_cast hbeta.ne')]
  rw [Real.rpow_one, Real.rpow_natCast]
  exact hpow

/-- Exact finite-level cold certificate interface using `3 < r^beta` rather
than a transcendental comparison. -/
theorem levelFeasible_of_coldSubeigen_natPower
    (k : Nat) (lam r : Real) (beta : Nat)
    (x : State k -> Real)
    (hlam : 0 <= lam) (hbeta : 0 < beta) (hr : 0 <= r)
    (hx : forall s, 0 < x s)
    (hpow : (3 : Real) < r ^ beta)
    (hsoft : forall s, r * x s <=
      (system k).coldOperator (beta : Real) (klWeights lam) x s) :
    LevelFeasible k lam := by
  apply levelFeasible_of_coldSubeigen
    k lam (beta : Real) r x hlam (by positivity) hx
  · exact three_rpow_inv_nat_lt_of_pow_gt beta hbeta r hr hpow
  · exact hsoft

/-- Sparse exact-power cold certificates at parameters tending to two imply
almost-linear predecessor counting. -/
theorem almostLinearPredecessorCounting_of_coldSubeigen_natPower_sequence
    (mu r : Nat -> Real) (beta level : Nat -> Nat)
    (x : (n : Nat) -> State (level n) -> Real)
    (hmu : Tendsto mu atTop (nhds 2))
    (hmuLower : forall n, 1 < mu n)
    (hmuUpper : forall n, mu n <= 2)
    (hlevel : forall n, 2 <= level n)
    (hbeta : forall n, 0 < beta n)
    (hr : forall n, 0 <= r n)
    (hx : forall n s, 0 < x n s)
    (hpow : forall n, (3 : Real) < (r n) ^ (beta n))
    (hsoft : forall n s, r n * x n s <=
      (system (level n)).coldOperator (beta n : Real)
        (klWeights (mu n)) (x n) s) :
    CleanLean.Collatz.AlmostLinearPredecessorCounting := by
  apply almostLinearPredecessorCounting_of_coldSubeigen_sequence
    mu (fun n => (beta n : Real)) r level x hmu hmuLower hmuUpper
    hlevel (fun n => by exact_mod_cast hbeta n) hx
  · intro n
    exact three_rpow_inv_nat_lt_of_pow_gt
      (beta n) (hbeta n) (r n) (hr n) (hpow n)
  · exact hsoft

end

end KLColdPowerCertificate
end KontoroC
