/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePhaseSwap

/-!
# Total affine gauges spend dyadic slope

Coefficientwise handoff between two total affine node gauges forces every
new dyadic source denominator to divide the original slope.  Along an
infinite rail, a fixed positive natural slope would therefore be divisible by
arbitrarily large powers of two.  This excludes everywhere-defined
one-register affine gauges, while leaving cylinder-restricted, nonlinear, and
multi-rail updates open.
-/

namespace KontoroC
namespace ChargeTotalAffineGaugeNoGo

/-- DL2: one direct handoff solution generates its full nonnegative solution
progression. -/
theorem direct_handoff_progression
    {sigma rho ternary binary u₀ v₀ : ℕ}
    (hbase : sigma + ternary * u₀ = rho + binary * v₀) (t : ℕ) :
    sigma + ternary * (u₀ + binary * t) =
      rho + binary * (v₀ + ternary * t) := by
  calc
    sigma + ternary * (u₀ + binary * t) =
        (sigma + ternary * u₀) + ternary * binary * t := by ring
    _ = (rho + binary * v₀) + ternary * binary * t := by rw [hbase]
    _ = rho + binary * (v₀ + ternary * t) := by ring

def prefixSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixSum f n + f n

def prefixProduct (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => prefixProduct f n * f n

/-- Product form of DL3. -/
theorem accumulated_slope_balance
    (Q P slope updateSlope : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n →
      3 ^ Q i * slope i =
        2 ^ P (i + 1) * slope (i + 1) * updateSlope i) :
    3 ^ prefixSum Q n * slope 0 =
      2 ^ prefixSum (fun i => P (i + 1)) n * slope n *
        prefixProduct updateSlope n := by
  induction n with
  | zero => simp [prefixSum, prefixProduct]
  | succ n ih =>
      have hprev : ∀ i, i < n →
          3 ^ Q i * slope i =
            2 ^ P (i + 1) * slope (i + 1) * updateSlope i := by
        intro i hi
        exact h i (by omega)
      have hi := ih hprev
      have hn := h n (by omega)
      simp only [prefixSum, prefixProduct]
      rw [pow_add, pow_add]
      calc
        3 ^ (prefixSum Q n) * 3 ^ Q n * slope 0 =
            3 ^ Q n * (3 ^ prefixSum Q n * slope 0) := by ring
        _ = 3 ^ Q n *
            (2 ^ prefixSum (fun i => P (i + 1)) n * slope n *
              prefixProduct updateSlope n) := by rw [hi]
        _ = 2 ^ prefixSum (fun i => P (i + 1)) n *
            (3 ^ Q n * slope n) * prefixProduct updateSlope n := by ring
        _ = 2 ^ prefixSum (fun i => P (i + 1)) n *
            (2 ^ P (n + 1) * slope (n + 1) * updateSlope n) *
              prefixProduct updateSlope n := by rw [hn]
        _ = 2 ^ prefixSum (fun i => P (i + 1)) n * 2 ^ P (n + 1) *
            slope (n + 1) *
              (prefixProduct updateSlope n * updateSlope n) := by ring

/-- DL4: all dyadic source precision accumulated through depth `n` divides
the initial total-affine slope. -/
theorem accumulated_two_power_dvd_initial_slope
    (Q P slope updateSlope : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n →
      3 ^ Q i * slope i =
        2 ^ P (i + 1) * slope (i + 1) * updateSlope i) :
    2 ^ prefixSum (fun i => P (i + 1)) n ∣ slope 0 := by
  have hbalance := accumulated_slope_balance Q P slope updateSlope n h
  have hdvd : 2 ^ prefixSum (fun i => P (i + 1)) n ∣
      3 ^ prefixSum Q n * slope 0 := by
    refine ⟨slope n * prefixProduct updateSlope n, ?_⟩
    simpa only [mul_assoc] using hbalance
  have hcop : (2 ^ prefixSum (fun i => P (i + 1)) n).Coprime
      (3 ^ prefixSum Q n) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem depth_power_dvd_initial_slope
    (Q P slope updateSlope : ℕ → ℕ) (n : ℕ)
    (hP : ∀ i, 0 < P (i + 1))
    (h : ∀ i, i < n →
      3 ^ Q i * slope i =
        2 ^ P (i + 1) * slope (i + 1) * updateSlope i) :
    2 ^ n ∣ slope 0 := by
  have hsum : n ≤ prefixSum (fun i => P (i + 1)) n := by
    induction n with
    | zero => simp [prefixSum]
    | succ n ih =>
        simp only [prefixSum]
        have ih' := ih (fun i hi => h i (by omega))
        have hp := hP n
        have hone : 1 ≤ P (n + 1) := by omega
        calc
          n + 1 ≤ prefixSum (fun i => P (i + 1)) n + 1 :=
            Nat.add_le_add_right ih' 1
          _ ≤ prefixSum (fun i => P (i + 1)) n + P (n + 1) :=
            Nat.add_le_add_left hone _
  exact (Nat.pow_dvd_pow 2 hsum).trans
    (accumulated_two_power_dvd_initial_slope Q P slope updateSlope n h)

/-- No positive natural initial slope supports an infinite total-affine gauge
rail satisfying DL3. -/
theorem no_positive_infinite_total_affine_gauge
    (Q P slope updateSlope : ℕ → ℕ)
    (hslope : 0 < slope 0) (hP : ∀ i, 0 < P (i + 1))
    (h : ∀ i,
      3 ^ Q i * slope i =
        2 ^ P (i + 1) * slope (i + 1) * updateSlope i) : False := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (slope 0)
    (by norm_num : (1 : ℕ) < 2)
  have hdvd : 2 ^ n ∣ slope 0 :=
    depth_power_dvd_initial_slope Q P slope updateSlope n hP
      (fun i _ => h i)
  have hle : 2 ^ n ≤ slope 0 := Nat.le_of_dvd hslope hdvd
  omega

end ChargeTotalAffineGaugeNoGo
end KontoroC
