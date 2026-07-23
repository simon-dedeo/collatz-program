/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.BranchArrivalTermination

/-!
# Telescoping calibrated KL cycle inequalities

An edge inequality compares the exponential time shift with a positive
potential.  Along a path the intermediate potentials telescope.  Closing the
path therefore bounds its total outward shift by the product of its deviation
factors.  Selected edges have deviation one and hence cannot form a
positive-shift cycle.

The theorem is stated for an indexed path rather than a particular graph
library.  A finite directed cycle supplies exactly these data by enumerating
its vertices and edges.
-/

namespace KontoroC
namespace KLCalibratedCycle

/-- QM130a in its logarithm-free form: arbitrary nonnegative edge weights
and deviation factors telescope along every finite indexed path. -/
theorem multiplicative_path_telescoping
    (potential weight deviation : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdeviation : ∀ i, 0 ≤ deviation i)
    (hedge : ∀ i,
      weight i * potential (i + 1) ≤ deviation i * potential i)
    (n : ℕ) :
    (∏ i ∈ Finset.range n, weight i) * potential n ≤
      (∏ i ∈ Finset.range n, deviation i) * potential 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∏ i ∈ Finset.range (n + 1), weight i) * potential (n + 1) =
            (∏ i ∈ Finset.range n, weight i) *
              (weight n * potential (n + 1)) := by
                rw [Finset.prod_range_succ]
                ring
        _ ≤ (∏ i ∈ Finset.range n, weight i) *
              (deviation n * potential n) :=
                mul_le_mul_of_nonneg_left (hedge n)
                  (Finset.prod_nonneg fun i _ => hweight i)
        _ = deviation n *
              ((∏ i ∈ Finset.range n, weight i) * potential n) := by
                ring
        _ ≤ deviation n *
              ((∏ i ∈ Finset.range n, deviation i) * potential 0) :=
                mul_le_mul_of_nonneg_left ih (hdeviation n)
        _ = (∏ i ∈ Finset.range (n + 1), deviation i) * potential 0 := by
                rw [Finset.prod_range_succ]
                ring

/-- QM130b: on a finite state space, endpoint potentials cost only their
condition number.  The assumptions are stated directly as uniform bounds so
the lemma also applies outside finite graphs. -/
theorem multiplicative_path_condition_bound
    (potential weight deviation : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdeviation : ∀ i, 0 ≤ deviation i)
    (hedge : ∀ i,
      weight i * potential (i + 1) ≤ deviation i * potential i)
    {cmin cmax : ℝ} (hcmin : 0 < cmin)
    (hmin : ∀ i, cmin ≤ potential i)
    (hmax : ∀ i, potential i ≤ cmax)
    (n : ℕ) :
    ∏ i ∈ Finset.range n, weight i ≤
      (cmax / cmin) * ∏ i ∈ Finset.range n, deviation i := by
  have htel := multiplicative_path_telescoping potential weight deviation
    hweight hdeviation hedge n
  have hwprod : 0 ≤ ∏ i ∈ Finset.range n, weight i :=
    Finset.prod_nonneg fun i _ => hweight i
  have hdprod : 0 ≤ ∏ i ∈ Finset.range n, deviation i :=
    Finset.prod_nonneg fun i _ => hdeviation i
  have hlower :
      (∏ i ∈ Finset.range n, weight i) * cmin ≤
        (∏ i ∈ Finset.range n, weight i) * potential n :=
    mul_le_mul_of_nonneg_left (hmin n) hwprod
  have hupper :
      (∏ i ∈ Finset.range n, deviation i) * potential 0 ≤
        (∏ i ∈ Finset.range n, deviation i) * cmax :=
    mul_le_mul_of_nonneg_left (hmax 0) hdprod
  refine (mul_le_mul_iff_of_pos_right hcmin).mp ?_
  calc
    (∏ i ∈ Finset.range n, weight i) * cmin ≤
        (∏ i ∈ Finset.range n, weight i) * potential n := hlower
    _ ≤ (∏ i ∈ Finset.range n, deviation i) * potential 0 := htel
    _ ≤ (∏ i ∈ Finset.range n, deviation i) * cmax := hupper
    _ = (cmax / cmin * ∏ i ∈ Finset.range n, deviation i) * cmin := by
      field_simp

/-- Multiplication of the edge inequalities along an indexed path. -/
theorem path_telescoping
    {lambda : ℝ} (hlambda : 0 < lambda)
    (potential shift deviation : ℕ → ℝ)
    (_hpotential : ∀ i, 0 < potential i)
    (hdeviation : ∀ i, 0 ≤ deviation i)
    (hedge : ∀ i,
      lambda ^ shift i * potential (i + 1) ≤
        deviation i * potential i) (n : ℕ) :
    lambda ^ (∑ i ∈ Finset.range n, shift i) * potential n ≤
      (∏ i ∈ Finset.range n, deviation i) * potential 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        lambda ^ (∑ i ∈ Finset.range (n + 1), shift i) * potential (n + 1) =
            lambda ^ (∑ i ∈ Finset.range n, shift i) *
              (lambda ^ shift n * potential (n + 1)) := by
                rw [Finset.sum_range_succ, Real.rpow_add hlambda]
                ring
        _ ≤ lambda ^ (∑ i ∈ Finset.range n, shift i) *
              (deviation n * potential n) :=
                mul_le_mul_of_nonneg_left (hedge n)
                  (Real.rpow_nonneg hlambda.le _)
        _ = deviation n *
              (lambda ^ (∑ i ∈ Finset.range n, shift i) * potential n) := by
                ring
        _ ≤ deviation n *
              ((∏ i ∈ Finset.range n, deviation i) * potential 0) :=
                mul_le_mul_of_nonneg_left ih (hdeviation n)
        _ = (∏ i ∈ Finset.range (n + 1), deviation i) * potential 0 := by
                rw [Finset.prod_range_succ]
                ring

/-- QM130c: exponential KL weights satisfy the same endpoint condition-
number bound along arbitrary, not necessarily periodic, finite paths. -/
theorem rpow_path_condition_bound
    {lambda : ℝ} (hlambda : 0 < lambda)
    (potential shift deviation : ℕ → ℝ)
    (hpotential : ∀ i, 0 < potential i)
    (hdeviation : ∀ i, 0 ≤ deviation i)
    (hedge : ∀ i,
      lambda ^ shift i * potential (i + 1) ≤
        deviation i * potential i)
    {cmin cmax : ℝ} (hcmin : 0 < cmin)
    (hmin : ∀ i, cmin ≤ potential i)
    (hmax : ∀ i, potential i ≤ cmax)
    (n : ℕ) :
    lambda ^ (∑ i ∈ Finset.range n, shift i) ≤
      (cmax / cmin) * ∏ i ∈ Finset.range n, deviation i := by
  have htel := path_telescoping hlambda potential shift deviation
    hpotential hdeviation hedge n
  have hq : 0 ≤ lambda ^ (∑ i ∈ Finset.range n, shift i) :=
    Real.rpow_nonneg hlambda.le _
  have hdprod : 0 ≤ ∏ i ∈ Finset.range n, deviation i :=
    Finset.prod_nonneg fun i _ => hdeviation i
  have hlower :
      lambda ^ (∑ i ∈ Finset.range n, shift i) * cmin ≤
        lambda ^ (∑ i ∈ Finset.range n, shift i) * potential n :=
    mul_le_mul_of_nonneg_left (hmin n) hq
  have hupper :
      (∏ i ∈ Finset.range n, deviation i) * potential 0 ≤
        (∏ i ∈ Finset.range n, deviation i) * cmax :=
    mul_le_mul_of_nonneg_left (hmax 0) hdprod
  refine (mul_le_mul_iff_of_pos_right hcmin).mp ?_
  calc
    lambda ^ (∑ i ∈ Finset.range n, shift i) * cmin ≤
        lambda ^ (∑ i ∈ Finset.range n, shift i) * potential n := hlower
    _ ≤ (∏ i ∈ Finset.range n, deviation i) * potential 0 := htel
    _ ≤ (∏ i ∈ Finset.range n, deviation i) * cmax := hupper
    _ = (cmax / cmin * ∏ i ∈ Finset.range n, deviation i) * cmin := by
      field_simp

/-- At fixed precision, an always-selected path has a uniform cumulative
shift ceiling, not merely nonpositive asymptotic mean.  The real parameter
`budget` can be any certified exponent with `cmax/cmin ≤ lambda^budget`. -/
theorem selected_path_shift_le_condition_budget
    {lambda : ℝ} (hlambda : 1 < lambda)
    (potential shift : ℕ → ℝ)
    (hpotential : ∀ i, 0 < potential i)
    (hedge : ∀ i,
      lambda ^ shift i * potential (i + 1) ≤ potential i)
    {cmin cmax budget : ℝ} (hcmin : 0 < cmin)
    (hmin : ∀ i, cmin ≤ potential i)
    (hmax : ∀ i, potential i ≤ cmax)
    (hbudget : cmax / cmin ≤ lambda ^ budget)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, shift i ≤ budget := by
  let deviation : ℕ → ℝ := fun _ => 1
  have hcondition := rpow_path_condition_bound
    (lt_trans zero_lt_one hlambda) potential shift deviation
    hpotential (fun _ => by simp [deviation])
    (fun i => by simpa [deviation] using hedge i)
    hcmin hmin hmax n
  simp only [deviation, Finset.prod_const_one, mul_one] at hcondition
  have hpow :
      lambda ^ (∑ i ∈ Finset.range n, shift i) ≤ lambda ^ budget :=
    hcondition.trans hbudget
  exact (Real.strictMono_rpow_of_base_gt_one hlambda).le_iff_le.mp hpow

/-- QM127c: after a path closes, its positive potential cancels.  Every
outward cycle must be paid for by the product of its deviation factors. -/
theorem calibrated_cycle_tax
    {lambda : ℝ} (hlambda : 0 < lambda)
    (potential shift deviation : ℕ → ℝ)
    (hpotential : ∀ i, 0 < potential i)
    (hdeviation : ∀ i, 0 ≤ deviation i)
    (hedge : ∀ i,
      lambda ^ shift i * potential (i + 1) ≤
        deviation i * potential i)
    {n : ℕ} (hclose : potential n = potential 0) :
    lambda ^ (∑ i ∈ Finset.range n, shift i) ≤
      ∏ i ∈ Finset.range n, deviation i := by
  have hpath := path_telescoping hlambda potential shift deviation
    hpotential hdeviation hedge n
  rw [hclose] at hpath
  exact (mul_le_mul_iff_of_pos_right (hpotential 0)).mp hpath

/-- QM127b: on selected edges all deviation factors are one, so a cycle's
total shift is nonpositive whenever `lambda > 1`. -/
theorem selected_cycle_shift_nonpos
    {lambda : ℝ} (hlambda : 1 < lambda)
    (potential shift : ℕ → ℝ)
    (hpotential : ∀ i, 0 < potential i)
    (hedge : ∀ i,
      lambda ^ shift i * potential (i + 1) ≤ potential i)
    {n : ℕ} (hclose : potential n = potential 0) :
    ∑ i ∈ Finset.range n, shift i ≤ 0 := by
  let deviation : ℕ → ℝ := fun _ => 1
  have htax := calibrated_cycle_tax (lt_trans zero_lt_one hlambda)
    potential shift deviation
    hpotential (fun _ => by simp [deviation])
    (fun i => by simpa [deviation] using hedge i) hclose
  simp only [deviation, Finset.prod_const_one] at htax
  have hpow :
      lambda ^ (∑ i ∈ Finset.range n, shift i) ≤ lambda ^ (0 : ℝ) := by
    simpa using htax
  exact (Real.strictMono_rpow_of_base_gt_one hlambda).le_iff_le.mp hpow

/-! ## Strictness of the KL logarithmic weight -/

open CleanLean.KL

/-- A nonzero natural multiple of `log_2(3)` cannot be a positive integer;
the zero-multiple case is excluded directly by `B>0`. -/
theorem kl_log_weight_ne_zero {A B : ℕ} (hB : 0 < B) :
    (A : ℝ) * alpha - B ≠ 0 := by
  intro hzero
  by_cases hA : A = 0
  · subst A
    norm_num at hzero
    omega
  · have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have halpha : alpha = (B : ℝ) / A := by
      apply (eq_div_iff hAR).2
      nlinarith
    have hrat : alpha = (((B : ℚ) / A : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
      exact halpha
    exact alpha_irrational.ne_rat ((B : ℚ) / A) hrat

/-- Every nonempty KL policy cycle whose symbolic weight is
`A*log_2(3)-B`, with `B>0`, is strictly negative once telescoping supplies
the nonpositive inequality. -/
theorem kl_selected_cycle_weight_strict {A B : ℕ} (hB : 0 < B)
    (hnonpos : (A : ℝ) * alpha - B ≤ 0) :
    (A : ℝ) * alpha - B < 0 :=
  lt_of_le_of_ne hnonpos (kl_log_weight_ne_zero hB)

end KLCalibratedCycle
end KontoroC
