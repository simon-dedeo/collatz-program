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
