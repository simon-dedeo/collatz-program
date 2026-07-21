/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.WeightedTail

/-!
# Charged Lyapunov certificates for normalized oscillation

The carrier relevant to fiber geometry is `Phi / mean`, not `Phi` alone.
This file states the correctly normalized cross-multiplied inequality, proves
its path iteration, and combines persistence with a tilted pressure moment.
-/

namespace CleanLean.KL

open scoped BigOperators

/-- Cross-multiplication turns a homogeneous carrier inequality into a bound
on the mean-normalized carrier.  Both mean factors are load-bearing. -/
theorem relativeCarrier_step
    {phiIn phiOut meanIn meanOut rho z : ℝ} {e : ℕ}
    (hmeanIn : 0 < meanIn) (hmeanOut : 0 < meanOut)
    (hcross : phiOut * meanIn ≤ rho * z ^ e * phiIn * meanOut) :
    phiOut / meanOut ≤ rho * z ^ e * (phiIn / meanIn) := by
  rw [div_le_iff₀ hmeanOut, div_eq_mul_inv]
  have heq :
      rho * z ^ e * (phiIn * meanIn⁻¹) * meanOut =
        (rho * z ^ e * phiIn * meanOut) / meanIn := by
    field_simp [ne_of_gt hmeanIn]
  rw [heq]
  exact (le_div_iff₀ hmeanIn).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross)

/-- Total integer charge accumulated in the first `n` transitions. -/
def chargeSum (e : ℕ → ℕ) (n : ℕ) : ℕ := Finset.sum (Finset.range n) e

@[simp] theorem chargeSum_zero (e : ℕ → ℕ) : chargeSum e 0 = 0 := by
  simp [chargeSum]

theorem chargeSum_succ (e : ℕ → ℕ) (n : ℕ) :
    chargeSum e (n + 1) = chargeSum e n + e n := by
  simp [chargeSum, Finset.sum_range_succ]

/-- Iteration of a correctly normalized contraction-or-charge inequality. -/
theorem chargedCarrier_iterate
    (A : ℕ → ℝ) (e : ℕ → ℕ) (rho z : ℝ)
    (hrho : 0 ≤ rho) (hz : 0 ≤ z)
    (hstep : ∀ n, A (n + 1) ≤ rho * z ^ (e n) * A n) :
    ∀ n, A n ≤ rho ^ n * z ^ (chargeSum e n) * A 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        A (n + 1) ≤ rho * z ^ (e n) * A n := hstep n
        _ ≤ rho * z ^ (e n) *
            (rho ^ n * z ^ (chargeSum e n) * A 0) :=
          mul_le_mul_of_nonneg_left ih (mul_nonneg hrho (pow_nonneg hz _))
        _ = rho ^ (n + 1) * z ^ (chargeSum e (n + 1)) * A 0 := by
          rw [chargeSum_succ, pow_add, pow_succ]
          ring

/-- Persistent normalized oscillation forces the accumulated charge to pay
for any contraction. -/
theorem persistence_forces_charged_growth
    (A : ℕ → ℝ) (e : ℕ → ℕ) (rho z c C : ℝ) (n : ℕ)
    (hiter : A n ≤ rho ^ n * z ^ (chargeSum e n) * A 0)
    (hinitial : A 0 ≤ C) (hc : c ≤ A n)
    (hrho : 0 ≤ rho) (hz : 0 ≤ z) :
    c ≤ C * rho ^ n * z ^ (chargeSum e n) := by
  calc
    c ≤ A n := hc
    _ ≤ rho ^ n * z ^ (chargeSum e n) * A 0 := hiter
    _ ≤ rho ^ n * z ^ (chargeSum e n) * C :=
      mul_le_mul_of_nonneg_left hinitial
        (mul_nonneg (pow_nonneg hrho n) (pow_nonneg hz _))
    _ = C * rho ^ n * z ^ (chargeSum e n) := by ring

section FinitePressureCombination

variable {I : Type} [Fintype I]

/-- Finite charged-Lyapunov/pressure combination.  `bad i` may mean that the
final normalized fiber oscillation exceeds a fixed threshold.  The first
hypothesis is supplied by the relative carrier iteration; the second is the
tilted pressure moment. -/
theorem badMass_le_of_chargedCarrier_and_pressure
    (mu : I → ℝ) (bad : I → Prop) [DecidablePred bad]
    (charge : I → ℕ) (n : ℕ) (c C rho z D R : ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hc : 0 < c)
    (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hz : 0 ≤ z)
    (hpersist : ∀ i, bad i → c ≤ C * rho ^ n * z ^ (charge i))
    (hmoment : (∑ i, mu i * z ^ (charge i)) ≤ D * R ^ n) :
    (∑ i, if bad i then mu i else 0) ≤
      (C * D / c) * (R * rho) ^ n := by
  have hpoint : ∀ i, (if bad i then mu i else 0) ≤
      (C * rho ^ n / c) * (mu i * z ^ (charge i)) := by
    intro i
    by_cases hi : bad i
    · have hp := hpersist i hi
      have hscale : 1 ≤ (C * rho ^ n / c) * z ^ (charge i) := by
        rw [show (C * rho ^ n / c) * z ^ (charge i) =
          (C * rho ^ n * z ^ (charge i)) / c by ring]
        exact (le_div_iff₀ hc).2 (by simpa using hp)
      have := mul_le_mul_of_nonneg_left hscale (hmu i)
      simpa [hi, mul_assoc, mul_left_comm, mul_comm] using this
    · simp only [hi, if_false]
      exact mul_nonneg
        (div_nonneg (mul_nonneg hC (pow_nonneg hrho n)) hc.le)
        (mul_nonneg (hmu i) (pow_nonneg hz _))
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
  calc
    (∑ i, if bad i then mu i else 0) ≤
        ∑ i, (C * rho ^ n / c) * (mu i * z ^ (charge i)) := hsum
    _ = (C * rho ^ n / c) * ∑ i, mu i * z ^ (charge i) := by
      rw [Finset.mul_sum]
    _ ≤ (C * rho ^ n / c) * (D * R ^ n) :=
      mul_le_mul_of_nonneg_left hmoment
        (div_nonneg (mul_nonneg hC (pow_nonneg hrho n)) hc.le)
    _ = (C * D / c) * (R * rho) ^ n := by
      rw [mul_pow]
      field_simp [ne_of_gt hc]

end FinitePressureCombination

end CleanLean.KL
