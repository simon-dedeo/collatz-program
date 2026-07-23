/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterLinearTheta

/-!
# Geometric ether schedules and a Mahler-value obstruction

For a one-based geometric branch schedule `n_t = n₀ * d^t`, the forced
ternary core of the autonomous ether register obeys

`2^(8*n_(t+1)+15) u_(t+1) = 3^(6*n_t+11) u_t + 17`.

This file proves the exact finite backward expansion and identifies its
`Q_2` limit with the lacunary Mahler series

`G(x) = sum_j (2^15/3^11)^j * x^(1+d+...+d^(j-1))`.

It also proves the functional equation `G(x)=1+a*x*G(x^d)` and the
conditional endpoint saying that p-adic irrationality of the displayed value
excludes an ordinary natural orbit.  No transcendence theorem is postulated:
the published Mahler-value theorem remains an explicit external premise.
-/

namespace KontoroC
namespace EtherCounterGeometricMahler

open Filter Topology MersennePacketRenewal

def branch (n₀ d t : ℕ) : ℕ := n₀ * d ^ t

def binaryExponent (n₀ d t : ℕ) : ℕ :=
  8 * branch n₀ d (t + 1) + 15

def ternaryExponent (n₀ d t : ℕ) : ℕ :=
  6 * branch n₀ d t + 11

/-- `1+d+⋯+d^(j-1)`, defined without natural-number division. -/
def geometricExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + d * geometricExponent d j

@[simp] theorem geometricExponent_zero (d : ℕ) :
    geometricExponent d 0 = 0 := rfl

@[simp] theorem geometricExponent_succ (d j : ℕ) :
    geometricExponent d (j + 1) = 1 + d * geometricExponent d j := rfl

theorem geometricExponent_add_power (d j : ℕ) :
    geometricExponent d j + d ^ j = geometricExponent d (j + 1) := by
  induction j with
  | zero => simp [geometricExponent]
  | succ j ih =>
      calc
        geometricExponent d (j + 1) + d ^ (j + 1) =
            (1 + d * geometricExponent d j) + d * d ^ j := by
          rw [geometricExponent_succ, pow_succ]
          ring
        _ = 1 + d * (geometricExponent d j + d ^ j) := by ring
        _ = 1 + d * geometricExponent d (j + 1) := by rw [ih]
        _ = geometricExponent d (j + 2) := by
          simp [geometricExponent]

theorem geometricExponent_eq_sum (d j : ℕ) :
    geometricExponent d j = ∑ k ∈ Finset.range j, d ^ k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact (geometricExponent_add_power d j).symm

/-- A necessary arithmetic projection of an infinite EC17 core orbit on a
positive geometric branch schedule. -/
structure Ray where
  initialBranch : ℕ
  multiplier : ℕ
  initialBranch_pos : 0 < initialBranch
  multiplier_ge_two : 2 ≤ multiplier
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  balance : ∀ t,
    2 ^ binaryExponent initialBranch multiplier t * core (t + 1) =
      3 ^ ternaryExponent initialBranch multiplier t * core t + 17

namespace Ray

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
    (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t

def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  17 / (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t

theorem step_backward (g : Ray) (t : ℕ) :
    (g.core t : ℚ) =
      g.backwardCoeff t * g.core (t + 1) - g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t *
          g.core (t + 1) =
        (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t *
          g.core t + 17 := by
    exact_mod_cast g.balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree :
      (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t ≠ 0 := by
    positivity
  field_simp
  nlinarith

theorem finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff N * g.core N -
        backwardPrefixDefect g.backwardCoeff g.backwardDefect N :=
  backward_affine_unroll (fun t => g.step_backward t) N

theorem backwardPrefixDefect_eq_sum (g : Ray) (N : ℕ) :
    backwardPrefixDefect g.backwardCoeff g.backwardDefect N =
      ∑ t ∈ Finset.range N,
        backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect, Finset.sum_range_succ, ih]

/-- Closed product exponent underlying QM78. -/
theorem backwardPrefixProduct_eq_closed (g : Ray) (N : ℕ) :
    backwardPrefixProduct g.backwardCoeff N =
      (2 : ℚ) ^
          (8 * g.initialBranch * g.multiplier *
            geometricExponent g.multiplier N + 15 * N) /
        (3 : ℚ) ^
          (6 * g.initialBranch * geometricExponent g.multiplier N + 11 * N) := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, ih]
      simp only [backwardCoeff, binaryExponent, ternaryExponent, branch]
      rw [div_mul_div_comm, ← pow_add, ← pow_add]
      congr 2
      · rw [pow_succ]
        calc
          8 * g.initialBranch * g.multiplier *
                  geometricExponent g.multiplier N + 15 * N +
                (8 * (g.initialBranch *
                    (g.multiplier ^ N * g.multiplier)) + 15) =
              8 * g.initialBranch * g.multiplier *
                  (geometricExponent g.multiplier N + g.multiplier ^ N) +
                15 * (N + 1) := by ring
          _ = 8 * g.initialBranch * g.multiplier *
                  geometricExponent g.multiplier (N + 1) + 15 * (N + 1) := by
            rw [geometricExponent_add_power]
      · calc
          6 * g.initialBranch * geometricExponent g.multiplier N + 11 * N +
                (6 * (g.initialBranch * g.multiplier ^ N) + 11) =
              6 * g.initialBranch *
                  (geometricExponent g.multiplier N + g.multiplier ^ N) +
                11 * (N + 1) := by ring
          _ = 6 * g.initialBranch * geometricExponent g.multiplier (N + 1) +
                11 * (N + 1) := by
            rw [geometricExponent_add_power]

def coefficient (_g : Ray) : ℚ := (2 : ℚ) ^ 15 / (3 : ℚ) ^ 11

def argument (g : Ray) : ℚ :=
  (2 : ℚ) ^ (8 * g.initialBranch * g.multiplier) /
    (3 : ℚ) ^ (6 * g.initialBranch * g.multiplier)

def mahlerTerm (g : Ray) (j : ℕ) : ℚ :=
  g.coefficient ^ j * g.argument ^ geometricExponent g.multiplier j

def candidateScale (g : Ray) : ℚ :=
  17 / (3 : ℚ) ^ (6 * g.initialBranch + 11)

/-- QM78 in coefficient form: the `j`th accumulated defect is exactly the
scaled `j`th term of the lacunary Mahler series. -/
theorem weightedDefect_eq_scaled_mahlerTerm (g : Ray) (j : ℕ) :
    backwardPrefixProduct g.backwardCoeff j * g.backwardDefect j =
      g.candidateScale * g.mahlerTerm j := by
  rw [g.backwardPrefixProduct_eq_closed j]
  have he := geometricExponent_add_power g.multiplier j
  simp only [backwardDefect, ternaryExponent, branch, candidateScale,
    mahlerTerm, coefficient, argument]
  simp only [div_pow, pow_add, pow_mul]
  field_simp
  simp only [← pow_mul, ← pow_add]
  congr 1
  calc
    6 * g.initialBranch +
          6 * g.initialBranch * g.multiplier *
            geometricExponent g.multiplier j =
        6 * g.initialBranch *
          (1 + g.multiplier * geometricExponent g.multiplier j) := by ring
    _ = 6 * g.initialBranch * geometricExponent g.multiplier (j + 1) := by
      rw [geometricExponent_succ]
    _ = 6 * g.initialBranch *
          (geometricExponent g.multiplier j + g.multiplier ^ j) := by rw [he]
    _ = 6 * g.initialBranch * geometricExponent g.multiplier j +
          6 * g.initialBranch * g.multiplier ^ j := by ring

end Ray

/-! ## The p-adic Mahler function -/

noncomputable def padicCoefficient : ℚ_[2] :=
  (2 : ℚ_[2]) ^ 15 / (3 : ℚ_[2]) ^ 11

noncomputable def padicMahlerTerm (d : ℕ) (x : ℚ_[2]) (j : ℕ) : ℚ_[2] :=
  padicCoefficient ^ j * x ^ geometricExponent d j

theorem padicMahlerTerm_zero (d : ℕ) (x : ℚ_[2]) :
    padicMahlerTerm d x 0 = 1 := by simp [padicMahlerTerm]

/-- The coefficient-level identity behind `G(x)=1+a*x*G(x^d)`. -/
theorem padicMahlerTerm_succ (d : ℕ) (x : ℚ_[2]) (j : ℕ) :
    padicMahlerTerm d x (j + 1) =
      padicCoefficient * x * padicMahlerTerm d (x ^ d) j := by
  simp only [padicMahlerTerm, geometricExponent_succ, pow_succ, pow_add,
    pow_mul]
  ring

theorem norm_padicCoefficient :
    ‖padicCoefficient‖ = ((2 : ℝ)⁻¹) ^ 15 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [padicCoefficient, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_padicMahlerTerm_le (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1)
    (j : ℕ) :
    ‖padicMahlerTerm d x j‖ ≤ (((2 : ℝ)⁻¹) ^ 15) ^ j := by
  rw [padicMahlerTerm, norm_mul, norm_pow, norm_pow, norm_padicCoefficient]
  have hxpow : ‖x‖ ^ geometricExponent d j ≤ 1 :=
    pow_le_one₀ (norm_nonneg x) hx
  simpa using mul_le_mul_of_nonneg_left hxpow (by positivity :
    0 ≤ (((2 : ℝ)⁻¹) ^ 15) ^ j)

theorem padicMahlerTerm_tendsto_zero (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    Tendsto (padicMahlerTerm d x) atTop (nhds 0) := by
  apply squeeze_zero_norm (norm_padicMahlerTerm_le d hx)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicMahlerTerm_summable (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    Summable (padicMahlerTerm d x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using padicMahlerTerm_tendsto_zero d hx

noncomputable def padicMahler (d : ℕ) (x : ℚ_[2]) : ℚ_[2] :=
  ∑' j, padicMahlerTerm d x j

/-- QM80: the literal p-adic Mahler functional equation on the closed unit
ball. -/
theorem padicMahler_functionalEquation (d : ℕ) (x : ℚ_[2])
    (hx : ‖x‖ ≤ 1) :
    padicMahler d x = 1 + padicCoefficient * x * padicMahler d (x ^ d) := by
  have hxd : ‖x ^ d‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg x) hx
  unfold padicMahler
  rw [(padicMahlerTerm_summable d hx).tsum_eq_zero_add,
    padicMahlerTerm_zero]
  congr 1
  rw [← (padicMahlerTerm_summable d hxd).tsum_mul_left
    (padicCoefficient * x)]
  apply tsum_congr
  intro j
  exact padicMahlerTerm_succ d x j

/-! ## The exact EC17 endpoint -/

namespace Ray

noncomputable def padicArgument (g : Ray) : ℚ_[2] := (g.argument : ℚ_[2])

theorem norm_padicArgument (g : Ray) :
    ‖g.padicArgument‖ =
      ((2 : ℝ)⁻¹) ^ (8 * g.initialBranch * g.multiplier) := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [padicArgument, argument, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_padicArgument_le_one (g : Ray) : ‖g.padicArgument‖ ≤ 1 := by
  rw [g.norm_padicArgument]
  exact pow_le_one₀ (by positivity) (by norm_num)

noncomputable def padicMahlerValue (g : Ray) : ℚ_[2] :=
  padicMahler g.multiplier g.padicArgument

theorem padicMahlerValue_functionalEquation (g : Ray) :
    g.padicMahlerValue =
      1 + padicCoefficient * g.padicArgument *
        padicMahler g.multiplier (g.padicArgument ^ g.multiplier) :=
  padicMahler_functionalEquation g.multiplier g.padicArgument
    g.norm_padicArgument_le_one

noncomputable def padicDefectTerm (g : Ray) (j : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff j * g.backwardDefect j : ℚ_[2])

theorem binaryExponent_pos (g : Ray) (t : ℕ) :
    0 < binaryExponent g.initialBranch g.multiplier t := by
  simp [binaryExponent]

theorem norm_backwardCoeff (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ binaryExponent g.initialBranch g.multiplier t := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [g.norm_backwardCoeff]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (g.binaryExponent_pos t).ne'
  rw [hn, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_backwardPrefixProduct_le (g : Ray) (N : ℕ) :
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ N := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (g.norm_backwardCoeff_le_half N)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one (g : Ray) (t : ℕ) :
    ‖(g.backwardDefect t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖((3 : ℚ) : ℚ_[2])‖ = 1 := by
    norm_num only [Rat.cast_ofNat]
    exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h17 : ‖(17 : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat 17 : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one (p := 2) (Int.ofNat 17)
  rw [backwardDefect, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    norm_div, norm_pow, hthree, one_pow, div_one]
  exact h17

theorem norm_padicDefectTerm_le (g : Ray) (j : ℕ) :
    ‖g.padicDefectTerm j‖ ≤ ((2 : ℝ)⁻¹) ^ j := by
  rw [padicDefectTerm, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ *
          ‖(g.backwardDefect j : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (g.norm_backwardDefect_le_one j)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ j := g.norm_backwardPrefixProduct_le j

theorem padicDefectTerm_tendsto_zero (g : Ray) :
    Tendsto g.padicDefectTerm atTop (nhds 0) := by
  apply squeeze_zero_norm g.norm_padicDefectTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicDefectTerm_summable (g : Ray) : Summable g.padicDefectTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using g.padicDefectTerm_tendsto_zero

noncomputable def padicDefectSum (g : Ray) : ℚ_[2] :=
  ∑' j, g.padicDefectTerm j

theorem padicDefectTerm_eq_scaled_mahlerTerm (g : Ray) (j : ℕ) :
    g.padicDefectTerm j =
      (g.candidateScale : ℚ_[2]) *
        padicMahlerTerm g.multiplier g.padicArgument j := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.weightedDefect_eq_scaled_mahlerTerm j)
  simpa [padicDefectTerm, padicMahlerTerm, padicCoefficient,
    padicArgument, mahlerTerm, coefficient, argument, Rat.cast_mul,
    Rat.cast_pow] using h

theorem padicDefectSum_eq_scaled_mahlerValue (g : Ray) :
    g.padicDefectSum =
      (g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by
  have hs := (padicMahlerTerm_summable g.multiplier
    g.norm_padicArgument_le_one).hasSum.mul_left (g.candidateScale : ℚ_[2])
  have hfun :
      (fun j => (g.candidateScale : ℚ_[2]) *
        padicMahlerTerm g.multiplier g.padicArgument j) = g.padicDefectTerm := by
    funext j
    exact (g.padicDefectTerm_eq_scaled_mahlerTerm j).symm
  rw [hfun] at hs
  exact g.padicDefectTerm_summable.hasSum.unique hs

noncomputable def padicDefectPartial (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect N : ℚ_[2])

theorem padicDefectPartial_eq_sum (g : Ray) (N : ℕ) :
    g.padicDefectPartial N =
      ∑ j ∈ Finset.range N, g.padicDefectTerm j := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.backwardPrefixDefect_eq_sum N)
  simpa [padicDefectPartial, padicDefectTerm, map_sum, Rat.cast_mul] using h

theorem padicDefectPartial_tendsto_sum (g : Ray) :
    Tendsto g.padicDefectPartial atTop (nhds g.padicDefectSum) := by
  have hsum := g.padicDefectTerm_summable.hasSum.tendsto_sum_nat
  have heq : g.padicDefectPartial = fun N =>
      ∑ j ∈ Finset.range N, g.padicDefectTerm j := by
    funext N
    exact g.padicDefectPartial_eq_sum N
  rw [heq]
  simpa only [padicDefectSum] using hsum

noncomputable def padicTerminal (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff N : ℚ_[2]) * g.core N

theorem norm_padicTerminal_le (g : Ray) (N : ℕ) :
    ‖g.padicTerminal N‖ ≤ ((2 : ℝ)⁻¹) ^ N := by
  have hcore : ‖(g.core N : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.core N))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ *
          ‖(g.core N : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hcore (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ N := g.norm_backwardPrefixProduct_le N

theorem padicTerminal_tendsto_zero (g : Ray) :
    Tendsto g.padicTerminal atTop (nhds 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ_[2]) =
      g.padicTerminal N - g.padicDefectPartial N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series N)
  simpa [padicTerminal, padicDefectPartial, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast] using h

/-- QM79: every ordinary geometric EC17 ray forces its initial core to equal
the negative scaled Mahler value in `Q_2`. -/
theorem initial_eq_negative_scaled_mahlerValue (g : Ray) :
    (g.core 0 : ℚ_[2]) =
      -(g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by
  have heq : g.padicDefectPartial = fun N =>
      g.padicTerminal N - (g.core 0 : ℚ_[2]) := by
    funext N
    have h := g.padic_finite_series N
    linear_combination h
  have hlim : Tendsto g.padicDefectPartial atTop
      (nhds (-(g.core 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.padicDefectSum = -(g.core 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.padicDefectPartial_tendsto_sum hlim
  rw [g.padicDefectSum_eq_scaled_mahlerValue] at hsum
  calc
    (g.core 0 : ℚ_[2]) =
        -((g.candidateScale : ℚ_[2]) * g.padicMahlerValue) := by
      rw [hsum]
      simp
    _ = -(g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by ring

theorem candidateScale_ne_zero (g : Ray) : g.candidateScale ≠ 0 := by
  simp [candidateScale]

theorem padic_candidateScale_ne_zero (g : Ray) :
    (g.candidateScale : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.candidateScale_ne_zero

/-- QM81, with the published transcendence input exposed as a premise. -/
theorem false_of_mahlerValue_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicMahlerValue) : False := by
  apply hirr (-(g.core 0 : ℚ) / g.candidateScale)
  rw [Rat.cast_div, Rat.cast_neg]
  apply (eq_div_iff g.padic_candidateScale_ne_zero).2
  have h := g.initial_eq_negative_scaled_mahlerValue
  have hcast : (((g.core 0 : ℚ) : ℚ_[2])) = (g.core 0 : ℚ_[2]) := by
    norm_num
  rw [hcast]
  rw [h]
  ring

end Ray

end EtherCounterGeometricMahler

/-! ## Connection to the executable ether normalization -/

open EtherCounterGeometricMahler

namespace EtherCounterAperiodic.TernaryCoreOrbit

/-- A literal ternary-core orbit on a geometric one-based level schedule is
exactly the abstract EC17 ray used by the Mahler reduction. -/
def toGeometricMahlerRay
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (n₀ d : ℕ)
    (hn₀ : 0 < n₀) (hd : 2 ≤ d)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterGeometricMahler.branch n₀ d t) :
    EtherCounterGeometricMahler.Ray where
  initialBranch := n₀
  multiplier := d
  initialBranch_pos := hn₀
  multiplier_ge_two := hd
  core := o.core
  core_pos := o.core_pos
  balance t := by
    have h := o.balance t
    have hB :
        EtherCounterGeometricMahler.binaryExponent n₀ d t =
          8 * o.level (t + 1) + 23 := by
      simp only [EtherCounterGeometricMahler.binaryExponent]
      rw [← hschedule (t + 1)]
      omega
    have hA :
        EtherCounterGeometricMahler.ternaryExponent n₀ d t =
          6 * o.level t + 17 := by
      simp only [EtherCounterGeometricMahler.ternaryExponent]
      rw [← hschedule t]
      omega
    rw [hB, hA]
    exact h

/-- Conditional closure at the concrete ternary-core level.  The sole open
premise is irrationality of the explicit p-adic Mahler value. -/
theorem no_geometric_schedule_of_irrational
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (n₀ d : ℕ)
    (hn₀ : 0 < n₀) (hd : 2 ≤ d)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterGeometricMahler.branch n₀ d t)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      (o.toGeometricMahlerRay n₀ d hn₀ hd hschedule).padicMahlerValue) : False :=
  (o.toGeometricMahlerRay n₀ d hn₀ hd hschedule).false_of_mahlerValue_irrational hirr

end EtherCounterAperiodic.TernaryCoreOrbit
end KontoroC
