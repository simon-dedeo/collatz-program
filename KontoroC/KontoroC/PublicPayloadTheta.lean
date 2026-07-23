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

@[simp] theorem padicTerm_zero (m : ℕ → ℕ) :
    padicTerm m 0 = (publicAlpha (m 0) : ℚ_[2]) := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (publicPrefixProduct_succ_shift m 0)
  simpa [padicTerm] using h

theorem padicTerm_succ (m : ℕ → ℕ) (j : ℕ) :
    padicTerm m (j + 1) =
      (publicAlpha (m 0) : ℚ_[2]) *
        padicTerm (fun k => m (k + 1)) j := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (publicPrefixProduct_succ_shift m (j + 1))
  simpa [padicTerm, Rat.cast_mul] using h

/-- QM150f: removing the first public branch from the convergent theta
series gives the exact affine tail equation. -/
theorem padicSum_functional
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    padicSum m = (publicAlpha (m 0) : ℚ_[2]) *
      (1 + padicSum (fun k => m (k + 1))) := by
  have hsum := (padicTerm_summable m hm).sum_add_tsum_nat_add 1
  have hshift :
      (∑' j : ℕ, padicTerm m (j + 1)) =
        (publicAlpha (m 0) : ℚ_[2]) *
          padicSum (fun k => m (k + 1)) := by
    rw [show (fun j : ℕ => padicTerm m (j + 1)) =
        fun j => (publicAlpha (m 0) : ℚ_[2]) *
          padicTerm (fun k => m (k + 1)) j by
      funext j
      exact padicTerm_succ m j]
    exact (padicTerm_summable (fun k => m (k + 1))
      (fun k => hm (k + 1))).tsum_mul_left _
  rw [Finset.sum_range_one, padicTerm_zero, hshift] at hsum
  change (∑' j : ℕ, padicTerm m j) = _
  rw [← hsum]
  ring

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

theorem norm_padicSum_le_rho
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    ‖padicSum m‖ ≤ ((2 : ℝ)⁻¹) ^ 23 := by
  let ρ : ℝ := ((2 : ℝ)⁻¹) ^ 23
  have hρnonneg : 0 ≤ ρ := by positivity
  have hρle : ρ ≤ 1 := by
    dsimp [ρ]
    norm_num
  have hterm : ∀ j : ℕ, ‖padicTerm m j‖ ≤ ρ := by
    intro j
    apply (norm_padicTerm_le m hm j).trans
    rw [pow_succ]
    exact mul_le_of_le_one_left hρnonneg (pow_le_one₀ hρnonneg hρle)
  have hpartial : ∀ N : ℕ, ‖padicPartial m N‖ ≤ ρ := by
    intro N
    rw [padicPartial_eq_sum]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρnonneg
      (fun j _ => hterm j)
  have htendsto : Tendsto (fun N => ‖padicPartial m N‖) atTop
      (nhds ‖padicSum m‖) :=
    (padicPartial_tendsto_sum m hm).norm
  exact le_of_tendsto htendsto (Eventually.of_forall hpartial)

theorem norm_padicSum_lt_one
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    ‖padicSum m‖ < 1 :=
  (norm_padicSum_le_rho m hm).trans_lt (by norm_num)

/-- The valuation clause in QM150f, stated without any convention-dependent
valuation API: the tail factor is a 2-adic unit, so the theta norm is exactly
the norm of its first public multiplier. -/
theorem norm_padicSum_eq_first
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) :
    ‖padicSum m‖ = ((2 : ℝ)⁻¹) ^ (8 * m 0 + 15) := by
  have hmshift : ∀ k, 0 < m (k + 1) := fun k => hm (k + 1)
  have htail := norm_padicSum_lt_one (fun k => m (k + 1)) hmshift
  have hunit : ‖1 + padicSum (fun k => m (k + 1))‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
    · simp [max_eq_left htail.le]
    · simpa only [norm_one] using ne_of_gt htail
  rw [padicSum_functional m hm, norm_mul, norm_publicAlpha, hunit, mul_one]

noncomputable def padicTail (m : ℕ → ℕ) (t : ℕ) : ℚ_[2] :=
  padicSum (fun j => m (t + j))

theorem padicTail_functional
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (t : ℕ) :
    padicTail m t = (publicAlpha (m t) : ℚ_[2]) *
      (1 + padicTail m (t + 1)) := by
  have h := padicSum_functional (fun j => m (t + j))
    (fun j => hm (t + j))
  unfold padicTail
  have htail :
      padicSum (fun k => m (t + (k + 1))) =
        padicSum (fun j => m (t + 1 + j)) := by
    congr 1
    funext k
    congr 1
    omega
  simpa only [Nat.add_zero, htail] using h

theorem norm_padicTail_eq_branch
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (t : ℕ) :
    ‖padicTail m t‖ = ((2 : ℝ)⁻¹) ^ (8 * m t + 15) := by
  simpa only [padicTail, Nat.add_zero] using
    norm_padicSum_eq_first (fun j => m (t + j)) (fun j => hm (t + j))

/-- QM151a, one suffix at a time: if a public theta suffix happens to be a
negative ordinary integer, its exact 2-adic norm forces the required power
of two to divide that integer, and the next suffix is automatically a
negative ordinary integer as well. -/
theorem negative_integer_tail_step
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (t X : ℕ)
    (hX : padicTail m t = -(X : ℚ_[2])) :
    ∃ h : ℕ,
      X = 2 ^ (8 * m t + 15) * h ∧
      padicTail m (t + 1) =
        -((3 ^ (6 * m t + 11) * h + 1 : ℕ) : ℚ_[2]) := by
  let P := 8 * m t + 15
  let Q := 6 * m t + 11
  have hnorm := norm_padicTail_eq_branch m hm t
  rw [hX, norm_neg] at hnorm
  have hle : ‖((X : ℤ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(P : ℤ)) := by
    change ‖(X : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(P : ℤ))
    rw [hnorm]
    simp only [P, zpow_neg, zpow_natCast, inv_pow]
    exact le_rfl
  have hdvdInt : ((2 : ℤ) ^ P) ∣ (X : ℤ) :=
    (Padic.norm_int_le_pow_iff_dvd (p := 2) (X : ℤ) P).mp hle
  have hdvd : 2 ^ P ∣ X := by
    exact_mod_cast hdvdInt
  obtain ⟨h, hfactor⟩ := hdvd
  refine ⟨h, ?_, ?_⟩
  · simpa [P] using hfactor
  · have hfun := padicTail_functional m hm t
    rw [hX, hfactor] at hfun
    unfold publicAlpha at hfun
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hfun ⊢
    change -(2 ^ P * (h : ℚ_[2])) =
      (2 ^ P / 3 ^ Q) * (1 + padicTail m (t + 1)) at hfun
    field_simp at hfun
    have hnext : padicTail m (t + 1) =
        -(3 ^ Q * (h : ℚ_[2]) + 1) := by
      calc
        padicTail m (t + 1) =
            (1 + padicTail m (t + 1)) - 1 := by ring
        _ = -((h : ℚ_[2]) * 3 ^ Q) - 1 := by rw [← hfun]
        _ = -(3 ^ Q * (h : ℚ_[2]) + 1) := by ring
    exact hnext

/-- The first half of the QM151 converse: one ordinary negative value at
the initial suffix propagates to every later suffix.  No separate suffix
integrality hypothesis is used. -/
theorem all_tails_negative_integers_of_initial
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (X₀ : ℕ)
    (h₀ : padicTail m 0 = -(X₀ : ℚ_[2])) :
    ∀ t : ℕ, ∃ X : ℕ, padicTail m t = -(X : ℚ_[2]) := by
  intro t
  induction t with
  | zero => exact ⟨X₀, h₀⟩
  | succ t ih =>
      obtain ⟨X, hX⟩ := ih
      obtain ⟨h, _, hnext⟩ := negative_integer_tail_step m hm t X hX
      exact ⟨3 ^ (6 * m t + 11) * h + 1, hnext⟩

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
