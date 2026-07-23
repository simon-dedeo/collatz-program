/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SelfWritingKL

/-!
# The variable-exponent public-payload theta series in `ℚ₂`

This file completes the analytic endpoint of QM150.  It proves convergence
and the exact rational-lattice value forced by any supplied self-writing
orbit.  It deliberately contains no irrationality assertion for arbitrary
variable exponent positions.
-/

namespace KontoroC
namespace SelfWritingKL
namespace PublicTheta

open Filter Topology

noncomputable def padicTerm (m : ℕ → ℕ) (j : ℕ) : ℚ_[2] :=
  (publicPrefixProduct m (j + 1) : ℚ_[2])

noncomputable def padicSum (m : ℕ → ℕ) : ℚ_[2] :=
  ∑' j, padicTerm m j

noncomputable def padicPartial (m : ℕ → ℕ) (N : ℕ) : ℚ_[2] :=
  (publicInteriorSum m N : ℚ_[2])

theorem norm_publicAlpha (m : ℕ) :
    ‖(publicAlpha m : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ (8 * m + 15) := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [publicAlpha, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_publicAlpha_le {m : ℕ} (hm : 0 < m) :
    ‖(publicAlpha m : ℚ_[2])‖ ≤ ((2 : ℝ)⁻¹) ^ 23 := by
  rw [norm_publicAlpha]
  have hexp : 23 ≤ 8 * m + 15 := by omega
  exact pow_le_pow_of_le_one (by positivity) (by norm_num) hexp

theorem norm_publicPrefixProduct_le
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (N : ℕ) :
    ‖(publicPrefixProduct m N : ℚ_[2])‖ ≤
      (((2 : ℝ)⁻¹) ^ 23) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [publicPrefixProduct_succ, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (norm_publicAlpha_le (hm N))
        (norm_nonneg _) (by positivity)

theorem norm_padicTerm_le
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (j : ℕ) :
    ‖padicTerm m j‖ ≤ (((2 : ℝ)⁻¹) ^ 23) ^ (j + 1) := by
  exact norm_publicPrefixProduct_le m hm (j + 1)

theorem padicTerm_tendsto_zero
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    Tendsto (padicTerm m) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_padicTerm_le m hm)
  have hrho : (((2 : ℝ)⁻¹) ^ 23) < 1 := by norm_num
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hrho).comp
    (Filter.tendsto_add_atTop_nat 1)

theorem padicTerm_summable
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) : Summable (padicTerm m) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using padicTerm_tendsto_zero m hm

theorem padicPartial_eq_sum (m : ℕ → ℕ) (N : ℕ) :
    padicPartial m N = ∑ j ∈ Finset.range N, padicTerm m j := by
  induction N with
  | zero => simp [padicPartial]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [padicPartial, publicInteriorSum_succ, padicTerm, Rat.cast_add]

theorem padicPartial_tendsto_sum
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    Tendsto (padicPartial m) atTop (𝓝 (padicSum m)) := by
  have hsum := (padicTerm_summable m hm).hasSum.tendsto_sum_nat
  have heq : padicPartial m = fun N =>
      ∑ j ∈ Finset.range N, padicTerm m j := by
    funext N
    exact padicPartial_eq_sum m N
  rw [heq]
  simpa only [padicSum] using hsum

theorem norm_padic_publicB : ‖(publicB : ℚ_[2])‖ = (2 : ℝ) ^ 20 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have h473 : ‖(473 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hnum : ‖(494251421 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hden : ‖(495976448 : ℚ_[2])‖ = ((2 : ℝ)⁻¹) ^ 20 := by
    rw [show (495976448 : ℚ_[2]) = 473 * 2 ^ 20 by norm_num,
      norm_mul, norm_pow, h473, htwo, one_mul]
  rw [publicB]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, norm_div]
  rw [hnum, hden]
  norm_num

theorem norm_padic_publicEpsilon :
    ‖(publicEpsilon : ℚ_[2])‖ = (2 : ℝ) ^ 20 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h473 : ‖(473 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h17 : ‖(17 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hden : ‖(473 * 2 ^ 20 * 3 ^ 11 : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ 20 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, h473, htwo, hthree]
    norm_num
  have hdenLiteral : ‖(87860739833856 : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ 20 := by
    convert hden using 1 <;> norm_num
  rw [publicEpsilon_eq]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, norm_div]
  rw [h17, hdenLiteral]
  norm_num

theorem norm_payload_center_div_epsilon_le_two (q : ℕ) :
    ‖((((q : ℚ) + publicB) / publicEpsilon : ℚ_[2]))‖ ≤ 2 := by
  have hq : ‖(q : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat q)
  have hsum : ‖(q : ℚ_[2]) + (publicB : ℚ_[2])‖ ≤
      1 + (2 : ℝ) ^ 20 :=
    (norm_add_le _ _).trans (add_le_add hq (norm_padic_publicB.le))
  rw [norm_div, norm_padic_publicEpsilon]
  calc
    ‖(q : ℚ_[2]) + (publicB : ℚ_[2])‖ / (2 : ℝ) ^ 20 ≤
        (1 + (2 : ℝ) ^ 20) / (2 : ℝ) ^ 20 := by
      exact div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ 2 := by norm_num

noncomputable def orbitPadicTerminal (o : Orbit) (N : ℕ) : ℚ_[2] :=
  (publicPrefixProduct (fun t => o.branch (t + 1)) (N + 1) : ℚ_[2]) *
    ((((o.payload (N + 1) : ℚ) + publicB) /
      publicEpsilon : ℚ_[2]))

noncomputable def orbitPadicLattice (o : Orbit) : ℚ_[2] :=
  (-((2 : ℚ) ^ 20 * W (o.payload 0) / 17) : ℚ_[2])

theorem norm_orbitPadicTerminal_le (o : Orbit) (N : ℕ) :
    ‖orbitPadicTerminal o N‖ ≤
      2 * (((2 : ℝ)⁻¹) ^ 23) ^ (N + 1) := by
  rw [orbitPadicTerminal, norm_mul]
  have hprefix := norm_publicPrefixProduct_le
    (fun t => o.branch (t + 1)) (fun t => o.branch_pos (t + 1)) (N + 1)
  have hcenter := norm_payload_center_div_epsilon_le_two (o.payload (N + 1))
  calc
    ‖(publicPrefixProduct (fun t => o.branch (t + 1)) (N + 1) : ℚ_[2])‖ *
          ‖((((o.payload (N + 1) : ℚ) + publicB) /
            publicEpsilon : ℚ_[2]))‖ ≤
        (((2 : ℝ)⁻¹) ^ 23) ^ (N + 1) * 2 :=
      mul_le_mul hprefix hcenter (norm_nonneg _) (by positivity)
    _ = 2 * (((2 : ℝ)⁻¹) ^ 23) ^ (N + 1) := by ring

theorem orbitPadicTerminal_tendsto_zero (o : Orbit) :
    Tendsto (orbitPadicTerminal o) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_orbitPadicTerminal_le o)
  have hrho : (((2 : ℝ)⁻¹) ^ 23) < 1 := by norm_num
  have hpow : Tendsto
      (fun N : ℕ => (((2 : ℝ)⁻¹) ^ 23) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hrho).comp
      (Filter.tendsto_add_atTop_nat 1)
  simpa using hpow.const_mul 2

theorem orbit_padic_finite_lattice (o : Orbit) (N : ℕ) :
    padicPartial (fun t => o.branch (t + 1)) N =
      orbitPadicLattice o + orbitPadicTerminal o N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (o.finite_public_theta_lattice N)
  unfold padicPartial orbitPadicLattice orbitPadicTerminal
  simp only [Rat.cast_add, Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at h ⊢
  rw [h]
  ring

/-- Full QM150d: the convergent variable-exponent theta series of every
supplied ordinary self-writing orbit lands on the explicit rational lattice.
No assertion is made that arbitrary exponent sequences avoid this lattice. -/
theorem orbit_padicSum_eq_lattice (o : Orbit) :
    padicSum (fun t => o.branch (t + 1)) = orbitPadicLattice o := by
  have hpartial := padicPartial_tendsto_sum
    (fun t => o.branch (t + 1)) (fun t => o.branch_pos (t + 1))
  have heq : padicPartial (fun t => o.branch (t + 1)) =
      fun N => orbitPadicLattice o + orbitPadicTerminal o N := by
    funext N
    exact orbit_padic_finite_lattice o N
  have hlattice : Tendsto
      (padicPartial (fun t => o.branch (t + 1))) atTop
      (𝓝 (orbitPadicLattice o)) := by
    rw [heq]
    simpa using tendsto_const_nhds.add (orbitPadicTerminal_tendsto_zero o)
  exact tendsto_nhds_unique hpartial hlattice

/-- QM150d-unit: on the invariant payload slice the lattice value is an
embedded integer, with the collision factor `17` cancelled exactly. -/
theorem orbit_padicSum_eq_unit_lattice (o : Orbit) (r : ℕ)
    (hpayload : o.payload 0 = 17 * r) :
    padicSum (fun t => o.branch (t + 1)) =
      (-((2 : ℤ) ^ 20 * Wbar r) : ℚ_[2]) := by
  rw [orbit_padicSum_eq_lattice, orbitPadicLattice, hpayload,
    W_seventeen_mul]
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  push_cast
  field_simp

/-- Exact adversarial endpoint for a proposed target-branch schedule. -/
def AvoidsOrdinaryLattice (m : ℕ → ℕ) : Prop :=
  ∀ q : ℕ,
    padicSum m ≠ (-((2 : ℚ) ^ 20 * W q / 17) : ℚ_[2])

theorem no_orbit_with_targetBranch_of_avoidsOrdinaryLattice
    (m : ℕ → ℕ) (havoid : AvoidsOrdinaryLattice m) :
    ¬ ∃ o : Orbit, (fun t => o.branch (t + 1)) = m := by
  rintro ⟨o, hbranch⟩
  have hsum := orbit_padicSum_eq_lattice o
  rw [hbranch] at hsum
  exact havoid (o.payload 0) hsum

/-- Irrationality of the one variable-exponent sum is sufficient, but is
left as an explicit hypothesis rather than silently generalized from the
fixed-exponent 1989 theorem. -/
theorem no_orbit_with_targetBranch_of_padic_irrational
    (m : ℕ → ℕ)
    (hirr : ∀ r : ℚ, padicSum m ≠ (r : ℚ_[2])) :
    ¬ ∃ o : Orbit, (fun t => o.branch (t + 1)) = m := by
  apply no_orbit_with_targetBranch_of_avoidsOrdinaryLattice m
  intro q hq
  apply hirr (-((2 : ℚ) ^ 20 * W q / 17))
  simpa [Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using hq

end PublicTheta
end SelfWritingKL
end KontoroC
