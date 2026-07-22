/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.MersenneShadow
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The 2-adic boundary of Mersenne packet renewal

This file isolates the size-independent limit step suggested by the exact
finite backward series.  It does not assert that the resulting 2-adic series
is irrational or that no ordinary packet renewal exists.
-/

namespace KontoroC.MersennePacketRenewal

open Filter Topology

theorem norm_backwardCoeff (g : MersennePacketRenewal) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ (g.level0 + t + g.extra t) := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat]
  rw [norm_div, norm_pow, norm_pow, htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (g : MersennePacketRenewal) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [g.norm_backwardCoeff t]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Nat.add_pos_left g.level0_pos (t + g.extra t)))
  have hn' : g.level0 + t + g.extra t = n + 1 := by omega
  rw [hn', pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

/-- The terminal term in the finite backward series, now viewed in `ℚ₂`. -/
noncomputable def padicTerminal (g : MersennePacketRenewal) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff n : ℚ_[2]) *
    ((g.state n : ℚ_[2]) + 1)

theorem norm_backwardPrefixProduct_le (g : MersennePacketRenewal) (n : ℕ) :
    ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ n := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (g.norm_backwardCoeff_le_half n)
        (norm_nonneg _) (by positivity)

theorem norm_shifted_state_le_one (g : MersennePacketRenewal) (n : ℕ) :
    ‖(g.state n : ℚ_[2]) + 1‖ ≤ 1 := by
  rw [← Nat.cast_one, ← Nat.cast_add]
  simpa using Padic.norm_int_le_one (p := 2) (g.state n + 1)

theorem norm_padicTerminal_le (g : MersennePacketRenewal) (n : ℕ) :
    ‖g.padicTerminal n‖ ≤ ((2 : ℝ)⁻¹) ^ n := by
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ *
          ‖(g.state n : ℚ_[2]) + 1‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (g.norm_shifted_state_le_one n) (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff n : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ n := g.norm_backwardPrefixProduct_le n

/-- The terminal contribution vanishes 2-adically.  This bound is independent
of the Archimedean size of the packet states. -/
theorem padicTerminal_tendsto_zero (g : MersennePacketRenewal) :
    Tendsto g.padicTerminal atTop (𝓝 0) := by
  apply squeeze_zero_norm (g.norm_padicTerminal_le)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

/-- Partial sum of the weighted defects, embedded from `ℚ` into `ℚ₂`. -/
noncomputable def padicDefectPartial
    (g : MersennePacketRenewal) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect n : ℚ_[2])

/-- The rational finite-series theorem transported faithfully into `ℚ₂`. -/
theorem padic_finite_series (g : MersennePacketRenewal) (n : ℕ) :
    (g.state 0 : ℚ_[2]) + 1 =
      g.padicTerminal n - g.padicDefectPartial n := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.shifted_state_finite_series n)
  simpa [padicTerminal, padicDefectPartial, Rat.cast_add, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_natCast] using h

/-- The weighted-defect partial sums converge to the unique 2-adic candidate
`-(x₀+1)`.  Existence of the limit is therefore proved without any assumption
on the Archimedean size or growth rate of the states. -/
theorem padicDefectPartial_tendsto (g : MersennePacketRenewal) :
    Tendsto g.padicDefectPartial atTop (𝓝 (-((g.state 0 : ℚ_[2]) + 1))) := by
  have heq : g.padicDefectPartial = fun n =>
      g.padicTerminal n - ((g.state 0 : ℚ_[2]) + 1) := by
    funext n
    have h := g.padic_finite_series n
    linear_combination h
  rw [heq]
  have hconst : Tendsto
      (fun _ : ℕ => ((g.state 0 : ℚ_[2]) + 1)) atTop
      (𝓝 ((g.state 0 : ℚ_[2]) + 1)) := tendsto_const_nhds
  simpa only [zero_sub] using g.padicTerminal_tendsto_zero.sub hconst

/-- The coefficient prescribed by a level and an extra stream, independently
of any proposed packet realization. -/
def prescribedBackwardCoeff
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ (level0 + t + extra t) / (3 : ℚ) ^ (level0 + t)

/-- The corresponding prescribed defect. -/
def prescribedBackwardDefect
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) : ℚ :=
  ((2 : ℚ) ^ (level0 + t) * ((2 ^ extra t - 1 : ℕ) : ℚ)) /
    (3 : ℚ) ^ (level0 + t)

theorem norm_prescribedBackwardCoeff
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) :
    ‖(prescribedBackwardCoeff level0 extra t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ (level0 + t + extra t) := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  rw [prescribedBackwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat]
  rw [norm_div, norm_pow, norm_pow, htwo, hthree, one_pow, div_one]

theorem norm_prescribedBackwardCoeff_le_half
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) (t : ℕ) :
    ‖(prescribedBackwardCoeff level0 extra t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [norm_prescribedBackwardCoeff]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Nat.add_pos_left hlevel (t + extra t)))
  have hn' : level0 + t + extra t = n + 1 := by omega
  rw [hn', pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_prescribedPrefixProduct_le
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) (n : ℕ) :
    ‖(backwardPrefixProduct (prescribedBackwardCoeff level0 extra) n : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ n := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih
        (norm_prescribedBackwardCoeff_le_half hlevel extra n)
        (norm_nonneg _) (by positivity)

theorem norm_prescribedBackwardDefect_le_one
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) :
    ‖(prescribedBackwardDefect level0 extra t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [prescribedBackwardDefect, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat,
    norm_div, norm_mul, norm_pow,
    norm_pow, hthree, one_pow, div_one]
  have htwo : ‖(2 : ℚ_[2])‖ ≤ 1 :=
    (Padic.norm_p_lt_one (p := 2)).le
  have hleft : ‖(2 : ℚ_[2])‖ ^ (level0 + t) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) htwo
  have hright : ‖((2 ^ extra t - 1 : ℕ) : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2)
      (Int.ofNat (2 ^ extra t - 1))
  exact (mul_le_mul hleft hright (norm_nonneg _) (by positivity)).trans
    (by norm_num)

/-- Finite 2-adic candidate determined solely by the symbolic extra stream. -/
noncomputable def prescribedPadicDefectPartial
    (level0 : ℕ) (extra : ℕ → ℕ) (n : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect
    (prescribedBackwardCoeff level0 extra)
    (prescribedBackwardDefect level0 extra) n : ℚ_[2])

/-- One weighted term of the prescribed 2-adic defect series. -/
noncomputable def prescribedPadicDefectTerm
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct (prescribedBackwardCoeff level0 extra) t *
    prescribedBackwardDefect level0 extra t : ℚ_[2])

theorem norm_prescribedPadicDefectTerm_le
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) (t : ℕ) :
    ‖prescribedPadicDefectTerm level0 extra t‖ ≤ ((2 : ℝ)⁻¹) ^ t := by
  rw [prescribedPadicDefectTerm, norm_mul]
  calc
    ‖(backwardPrefixProduct (prescribedBackwardCoeff level0 extra) t : ℚ_[2])‖ *
          ‖(prescribedBackwardDefect level0 extra t : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct
            (prescribedBackwardCoeff level0 extra) t : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_prescribedBackwardDefect_le_one level0 extra t) (norm_nonneg _)
    _ = ‖(backwardPrefixProduct
          (prescribedBackwardCoeff level0 extra) t : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ t :=
      norm_prescribedPrefixProduct_le hlevel extra t

theorem prescribedPadicDefectTerm_tendsto_zero
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) :
    Tendsto (prescribedPadicDefectTerm level0 extra) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_prescribedPadicDefectTerm_le hlevel extra)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem prescribedPadicDefectTerm_summable
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) :
    Summable (prescribedPadicDefectTerm level0 extra) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using
    prescribedPadicDefectTerm_tendsto_zero hlevel extra

/-- The canonical 2-adic number selected by a positive initial level and an
arbitrary symbolic extra stream. -/
noncomputable def prescribedPadicCandidate
    (level0 : ℕ) (extra : ℕ → ℕ) : ℚ_[2] :=
  ∑' t, prescribedPadicDefectTerm level0 extra t

theorem prescribedPadicDefectPartial_eq_sum
    (level0 : ℕ) (extra : ℕ → ℕ) (n : ℕ) :
    prescribedPadicDefectPartial level0 extra n =
      ∑ t ∈ Finset.range n, prescribedPadicDefectTerm level0 extra t := by
  induction n with
  | zero => simp [prescribedPadicDefectPartial, backwardPrefixDefect]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [prescribedPadicDefectPartial, backwardPrefixDefect,
        prescribedPadicDefectTerm, Rat.cast_add, Rat.cast_mul]

theorem prescribedPadicDefectPartial_tendsto_candidate
    {level0 : ℕ} (hlevel : 0 < level0) (extra : ℕ → ℕ) :
    Tendsto (prescribedPadicDefectPartial level0 extra) atTop
      (𝓝 (prescribedPadicCandidate level0 extra)) := by
  have hsum := (prescribedPadicDefectTerm_summable hlevel extra).hasSum
    |>.tendsto_sum_nat
  have heq : prescribedPadicDefectPartial level0 extra = fun n =>
      ∑ t ∈ Finset.range n, prescribedPadicDefectTerm level0 extra t := by
    funext n
    exact prescribedPadicDefectPartial_eq_sum level0 extra n
  rw [heq]
  simpa only [prescribedPadicCandidate] using hsum

theorem padicDefectPartial_eq_prescribed (g : MersennePacketRenewal) :
    g.padicDefectPartial =
      prescribedPadicDefectPartial g.level0 g.extra := by
  have ha : g.backwardCoeff =
      prescribedBackwardCoeff g.level0 g.extra := by
    funext t
    rfl
  have hb : g.backwardDefect =
      prescribedBackwardDefect g.level0 g.extra := by
    funext t
    rfl
  funext n
  simp only [padicDefectPartial, prescribedPadicDefectPartial]
  rw [ha, hb]

/-- Any ordinary packet realization forces the independently prescribed
2-adic partial sums to converge to the negative integer `-(x₀+1)`. -/
theorem prescribedPadicDefectPartial_tendsto_of_renewal
    (g : MersennePacketRenewal) :
    Tendsto (prescribedPadicDefectPartial g.level0 g.extra) atTop
      (𝓝 (-((g.state 0 : ℚ_[2]) + 1))) := by
  rw [← g.padicDefectPartial_eq_prescribed]
  exact g.padicDefectPartial_tendsto

/-- An ordinary realization can exist only when the canonical 2-adic
candidate is exactly the negative ordinary integer `-(x₀+1)`. -/
theorem prescribedPadicCandidate_eq_negativeNatural_of_renewal
    (g : MersennePacketRenewal) :
    prescribedPadicCandidate g.level0 g.extra =
      -((g.state 0 : ℚ_[2]) + 1) :=
  tendsto_nhds_unique
    (prescribedPadicDefectPartial_tendsto_candidate g.level0_pos g.extra)
    g.prescribedPadicDefectPartial_tendsto_of_renewal

/-- A clean arithmetic obstruction endpoint.  To exclude every renewal with
a fixed symbolic extra stream, it is enough to compute its 2-adic limit and
prove that limit is not any negative ordinary integer `-(x+1)`. -/
theorem no_renewal_of_padic_limit_avoids_negativeNaturals
    {level0 : ℕ} {extra : ℕ → ℕ} {z : ℚ_[2]}
    (hlim : Tendsto (prescribedPadicDefectPartial level0 extra) atTop (𝓝 z))
    (havoid : ∀ x : ℕ, z ≠ -((x : ℚ_[2]) + 1)) :
    ¬∃ g : MersennePacketRenewal,
      g.level0 = level0 ∧ g.extra = extra := by
  rintro ⟨g, hlevel, hextra⟩
  have hg := g.prescribedPadicDefectPartial_tendsto_of_renewal
  rw [hlevel, hextra] at hg
  exact havoid (g.state 0) (tendsto_nhds_unique hlim hg)

/-- Final size-independent obstruction: if the canonical candidate misses
the discrete set of negative ordinary integers, no packet recurrence with
that symbolic schedule exists. -/
theorem no_renewal_of_padicCandidate_avoids_negativeNaturals
    {level0 : ℕ} (hlevel : 0 < level0) {extra : ℕ → ℕ}
    (havoid : ∀ x : ℕ,
      prescribedPadicCandidate level0 extra ≠ -((x : ℚ_[2]) + 1)) :
    ¬∃ g : MersennePacketRenewal,
      g.level0 = level0 ∧ g.extra = extra :=
  no_renewal_of_padic_limit_avoids_negativeNaturals
    (prescribedPadicDefectPartial_tendsto_candidate hlevel extra) havoid

end KontoroC.MersennePacketRenewal
