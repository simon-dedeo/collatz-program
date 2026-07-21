/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.WeightedTail

/-!
# Finite restricted-pressure certificates

A positive potential `h` satisfying `K h ≤ R h` gives a certified upper bound
`K^n h ≤ R^n h`.  Exceptional tilts and policy domination are intended to be
compiled into the finite nonnegative kernel `K`; this theorem checks the final
certificate without invoking eigenvalue computation.
-/

namespace CleanLean.KL

open scoped BigOperators

section Pressure

variable {Q : Type} [Fintype Q]

/-- Exact rational row inequality used by the pressure-search scripts. -/
def PressureCertificateRat (K : Q → Q → ℚ) (h : Q → ℚ) (R : ℚ) : Prop :=
  ∀ q, (∑ r, K q r * h r) ≤ R * h q

/-- Executable exact checker for a rational pressure certificate. -/
def checkPressureCertificateRat [DecidableEq Q]
    (K : Q → Q → ℚ) (h : Q → ℚ) (R : ℚ) : Bool :=
  decide (∀ q ∈ (Finset.univ : Finset Q), (∑ r, K q r * h r) ≤ R * h q)

theorem checkPressureCertificateRat_eq_true_iff [DecidableEq Q]
    (K : Q → Q → ℚ) (h : Q → ℚ) (R : ℚ) :
    checkPressureCertificateRat K h R = true ↔ PressureCertificateRat K h R := by
  simp [checkPressureCertificateRat, PressureCertificateRat]

/-- A checked rational row certificate supplies the real inequality used by
the analytic iteration theorem. -/
theorem real_pressureCertificate_of_checkRat [DecidableEq Q]
    (K : Q → Q → ℚ) (h : Q → ℚ) (R : ℚ)
    (hcheck : checkPressureCertificateRat K h R = true) :
    ∀ q, (∑ r, (K q r : ℝ) * (h r : ℝ)) ≤ (R : ℝ) * (h q : ℝ) := by
  have hrat : PressureCertificateRat K h R :=
    (checkPressureCertificateRat_eq_true_iff K h R).1 hcheck
  intro q
  exact_mod_cast hrat q

/-- Exact integer-power version of the Chernoff gap
`R * z^(-a/b) < 1`: no irrational root is needed in a certificate. -/
def checkChernoffGapRat (R z : ℚ) (a b : ℕ) : Bool :=
  decide (R ^ b < z ^ a)

theorem checkChernoffGapRat_eq_true_iff (R z : ℚ) (a b : ℕ) :
    checkChernoffGapRat R z a b = true ↔ R ^ b < z ^ a := by
  simp [checkChernoffGapRat]

/-- Iteration of a finite nonnegative transfer kernel on a terminal potential. -/
noncomputable def pressureIter (K : Q → Q → ℝ) (h : Q → ℝ) : ℕ → Q → ℝ
  | 0 => h
  | n + 1 => fun q => ∑ r, K q r * pressureIter K h n r

@[simp] theorem pressureIter_zero (K : Q → Q → ℝ) (h : Q → ℝ) :
    pressureIter K h 0 = h := rfl

@[simp] theorem pressureIter_succ (K : Q → Q → ℝ) (h : Q → ℝ)
    (n : ℕ) (q : Q) :
    pressureIter K h (n + 1) q = ∑ r, K q r * pressureIter K h n r := rfl

theorem pressureIter_nonneg (K : Q → Q → ℝ) (h : Q → ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hh : ∀ q, 0 ≤ h q) :
    ∀ n q, 0 ≤ pressureIter K h n q := by
  intro n
  induction n with
  | zero => simpa using hh
  | succ n ih =>
      intro q
      exact Finset.sum_nonneg fun r _ => mul_nonneg (hK q r) (ih r)

/-- Collatz--Wielandt-style finite certificate for a restricted pressure bound. -/
theorem pressureIter_le_of_certificate
    (K : Q → Q → ℝ) (h : Q → ℝ) (R : ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hR : 0 ≤ R)
    (hcert : ∀ q, (∑ r, K q r * h r) ≤ R * h q) :
    ∀ n q, pressureIter K h n q ≤ R ^ n * h q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro q
      rw [pressureIter_succ]
      calc
        (∑ r, K q r * pressureIter K h n r) ≤
            ∑ r, K q r * (R ^ n * h r) :=
          Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (ih r) (hK q r)
        _ = R ^ n * ∑ r, K q r * h r := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ ≤ R ^ n * (R * h q) :=
          mul_le_mul_of_nonneg_left (hcert q) (pow_nonneg hR n)
        _ = R ^ (n + 1) * h q := by rw [pow_succ]; ring

/-- A strict certified pressure bound forces the restricted iterates to vanish. -/
theorem pressureIter_tendsto_zero
    (K : Q → Q → ℝ) (h : Q → ℝ) (R : ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hh : ∀ q, 0 ≤ h q)
    (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hcert : ∀ q, (∑ r, K q r * h r) ≤ R * h q) (q : Q) :
    Filter.Tendsto (fun n => pressureIter K h n q) Filter.atTop (nhds 0) := by
  apply tail_tendsto_zero_of_geometric_bound
      (fun n => pressureIter K h n q) (h q) R hR0 hR1
  · exact fun n => pressureIter_nonneg K h hK hh n q
  · intro n
    simpa [mul_comm] using pressureIter_le_of_certificate K h R hK hR0 hcert n q

end Pressure

end CleanLean.KL
