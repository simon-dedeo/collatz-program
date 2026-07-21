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

/-- Total path mass obtained by putting terminal value one at every state. -/
noncomputable def pressureMass (K : Q → Q → ℝ) (n : ℕ) (q : Q) : ℝ :=
  pressureIter K (fun _ => 1) n q

/-- The explicit terminal-potential comparison missing from a bare row
certificate.  A positive lower bound on `h` costs exactly the condition-number
factor `h(q)/hmin`; no empirical eigenvector normalization is used. -/
theorem pressureMass_le_of_certificate
    (K : Q → Q → ℝ) (h : Q → ℝ) (R hmin : ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hR : 0 ≤ R) (hhmin : 0 < hmin)
    (hh : ∀ q, hmin ≤ h q)
    (hcert : ∀ q, (∑ r, K q r * h r) ≤ R * h q) :
    ∀ n q, pressureMass K n q ≤ R ^ n * h q / hmin := by
  intro n
  induction n with
  | zero =>
      intro q
      rw [pressureMass, pressureIter_zero, pow_zero, one_mul]
      exact (le_div_iff₀ hhmin).2 (by simpa using hh q)
  | succ n ih =>
      intro q
      rw [pressureMass, pressureIter_succ]
      calc
        (∑ r, K q r * pressureIter K (fun _ => 1) n r) ≤
            ∑ r, K q r * (R ^ n * h r / hmin) :=
          Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (ih r) (hK q r)
        _ = (R ^ n / hmin) * ∑ r, K q r * h r := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ ≤ (R ^ n / hmin) * (R * h q) :=
          mul_le_mul_of_nonneg_left (hcert q) (div_nonneg (pow_nonneg hR n) hhmin.le)
        _ = R ^ (n + 1) * h q / hmin := by
          rw [pow_succ]
          ring

/-- The exact integer-power Chernoff gap produces a genuine geometric ratio.
This is the analytic meaning of the Boolean check `R^b < z^a`. -/
theorem chernoffRatio_nonneg_lt_one
    (R z : ℝ) (a b : ℕ) (hR : 0 ≤ R) (hz : 0 < z)
    (hgap : R ^ b < z ^ a) :
    0 ≤ R ^ b / z ^ a ∧ R ^ b / z ^ a < 1 := by
  constructor
  · exact div_nonneg (pow_nonneg hR b) (pow_pos hz a).le
  · exact (div_lt_one (pow_pos hz a)).2 hgap

/-- Soundness of a checked rational Chernoff gap after casting to the reals. -/
theorem real_chernoffRatio_nonneg_lt_one
    (R z : ℚ) (a b : ℕ) (hR : 0 ≤ R) (hz : 0 < z)
    (hcheck : checkChernoffGapRat R z a b = true) :
    0 ≤ (R : ℝ) ^ b / (z : ℝ) ^ a ∧
      (R : ℝ) ^ b / (z : ℝ) ^ a < 1 := by
  have hgapQ := (checkChernoffGapRat_eq_true_iff R z a b).1 hcheck
  have hgapR : (R : ℝ) ^ b < (z : ℝ) ^ a := by exact_mod_cast hgapQ
  exact chernoffRatio_nonneg_lt_one (R : ℝ) (z : ℝ) a b
    (by exact_mod_cast hR) (by exact_mod_cast hz) hgapR

/-- Abstract block-Chernoff conclusion.  The sole application-specific input
`hdom` says that paths with at least `a*m` charged visits in `b*m` moves are
dominated by the tilted path mass divided by `z^(a*m)`.  A portable pressure
certificate supplies every other hypothesis. -/
theorem blockTail_le_geometric_of_pressure
    (K : Q → Q → ℝ) (h : Q → ℝ) (R z hmin : ℝ)
    (a b : ℕ) (q₀ : Q) (tail : ℕ → ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hR : 0 ≤ R) (hz : 0 < z)
    (hhmin : 0 < hmin) (hh : ∀ q, hmin ≤ h q)
    (hcert : ∀ q, (∑ r, K q r * h r) ≤ R * h q)
    (hdom : ∀ m, tail m ≤ pressureMass K (b * m) q₀ / z ^ (a * m)) :
    ∀ m, tail m ≤ (h q₀ / hmin) * (R ^ b / z ^ a) ^ m := by
  intro m
  have hmass := pressureMass_le_of_certificate K h R hmin hK hR hhmin hh hcert
    (b * m) q₀
  calc
    tail m ≤ pressureMass K (b * m) q₀ / z ^ (a * m) := hdom m
    _ ≤ (R ^ (b * m) * h q₀ / hmin) / z ^ (a * m) :=
      div_le_div_of_nonneg_right hmass (pow_nonneg hz.le _)
    _ = (h q₀ / hmin) * (R ^ b / z ^ a) ^ m := by
      rw [pow_mul R b m, pow_mul z a m, div_pow]
      field_simp [ne_of_gt hhmin, ne_of_gt hz]

/-- With the checked strict gap, the block tail tends to zero. -/
theorem blockTail_tendsto_zero_of_pressure
    (K : Q → Q → ℝ) (h : Q → ℝ) (R z hmin : ℝ)
    (a b : ℕ) (q₀ : Q) (tail : ℕ → ℝ)
    (hK : ∀ q r, 0 ≤ K q r) (hR : 0 ≤ R) (hz : 0 < z)
    (hhmin : 0 < hmin) (hh : ∀ q, hmin ≤ h q)
    (hcert : ∀ q, (∑ r, K q r * h r) ≤ R * h q)
    (hdom : ∀ m, tail m ≤ pressureMass K (b * m) q₀ / z ^ (a * m))
    (htail0 : ∀ m, 0 ≤ tail m) (hgap : R ^ b < z ^ a) :
    Filter.Tendsto tail Filter.atTop (nhds 0) := by
  obtain ⟨hq0, hq1⟩ := chernoffRatio_nonneg_lt_one R z a b hR hz hgap
  apply tail_tendsto_zero_of_geometric_bound tail (h q₀ / hmin)
    (R ^ b / z ^ a) hq0 hq1 htail0
  exact blockTail_le_geometric_of_pressure K h R z hmin a b q₀ tail
    hK hR hz hhmin hh hcert hdom

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

section SparsePressure

variable {Q E : Type} [Fintype Q] [DecidableEq Q] [Fintype E]

/-- A sparse rational kernel compiled from a finite edge table.  This is the
shape emitted by the portable pressure-certificate generator: edge identifiers
carry a source, target, and exact rational weight. -/
def sparseKernelRat (src tgt : E → Q) (weight : E → ℚ) (q r : Q) : ℚ :=
  ∑ e, if src e = q ∧ tgt e = r then weight e else 0

/-- Direct sparse evaluation of one certificate row. -/
def sparsePressureRowRat (src tgt : E → Q) (weight : E → ℚ)
    (h : Q → ℚ) (q : Q) : ℚ :=
  ∑ e, if src e = q then weight e * h (tgt e) else 0

/-- The executable predicate checked on a portable sparse edge table. -/
def checkSparsePressureCertificateRat
    (src tgt : E → Q) (weight : E → ℚ) (h : Q → ℚ) (R : ℚ) : Bool :=
  decide ((∀ e, 0 ≤ weight e) ∧
    ∀ q, sparsePressureRowRat src tgt weight h q ≤ R * h q)

theorem checkSparsePressureCertificateRat_eq_true_iff
    (src tgt : E → Q) (weight : E → ℚ) (h : Q → ℚ) (R : ℚ) :
    checkSparsePressureCertificateRat src tgt weight h R = true ↔
      ((∀ e, 0 ≤ weight e) ∧
        ∀ q, sparsePressureRowRat src tgt weight h q ≤ R * h q) := by
  simp [checkSparsePressureCertificateRat]

/-- Summing the dense kernel obtained from the sparse table gives exactly the
direct sparse row expression. -/
theorem sum_sparseKernelRat_mul
    (src tgt : E → Q) (weight : E → ℚ) (h : Q → ℚ) (q : Q) :
    (∑ r, sparseKernelRat src tgt weight q r * h r) =
      sparsePressureRowRat src tgt weight h q := by
  classical
  simp only [sparseKernelRat, sparsePressureRowRat, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : src e = q
  · simp [hs]
  · simp [hs]

/-- A successful sparse Boolean check supplies both nonnegativity of the
compiled real kernel and its real row inequalities. -/
theorem real_pressureCertificate_of_checkSparseRat
    (src tgt : E → Q) (weight : E → ℚ) (h : Q → ℚ) (R : ℚ)
    (hcheck : checkSparsePressureCertificateRat src tgt weight h R = true) :
    (∀ q r, 0 ≤ (sparseKernelRat src tgt weight q r : ℝ)) ∧
      ∀ q, (∑ r, (sparseKernelRat src tgt weight q r : ℝ) * (h r : ℝ)) ≤
        (R : ℝ) * (h q : ℝ) := by
  have hcert :=
    (checkSparsePressureCertificateRat_eq_true_iff src tgt weight h R).1 hcheck
  constructor
  · intro q r
    exact_mod_cast Finset.sum_nonneg (fun e _ => by
      split <;> simp_all)
  · intro q
    have hrow :
        (∑ r, sparseKernelRat src tgt weight q r * h r) ≤ R * h q := by
      rw [sum_sparseKernelRat_mul]
      exact hcert.2 q
    exact_mod_cast hrow

/-- Exact `R^8 < z` gap for the portable `lambda = 2` Lemma-5 pressure
certificate (`z = 5/4`, charge density `1/8`). -/
theorem lemma5_lamTwo_chernoff_gap :
    checkChernoffGapRat (2021589 / 1975507) (5 / 4) 1 8 = true := by
  norm_num [checkChernoffGapRat]

/-- Exact `R^4 < z` gap for the portable certificate uniform on the eight
parameter pieces from `lambda_18` to `2` (`z = 3/2`, density `1/4`). -/
theorem lemma5_uniform_chernoff_gap :
    checkChernoffGapRat
      (906732000000000000 / 826747309635292463) (3 / 2) 1 4 = true := by
  norm_num [checkChernoffGapRat]

end SparsePressure

end CleanLean.KL
