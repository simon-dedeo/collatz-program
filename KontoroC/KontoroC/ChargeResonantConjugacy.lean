/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePublicCofactor

/-!
# Determinant-four resonant tail conjugacies

This file kernel-checks the general algebra behind the proposed phase-glider
charts.  A parallel affine conjugacy maps an entire source balance and source
cylinder to the target; it is still only one commutative square, not an
infinite compatible orbit.
-/

namespace KontoroC
namespace ChargeResonantConjugacy

def binaryExponent (h m' : ℕ) : ℕ := 154 * h + 23 * m'
def ternaryExponent (m h : ℕ) : ℕ := 17 * m + 114 * h

/-- The positive-parameter form of the determinant-four resonance.  Moving
`391*k` recharge cells into `2622*k` source cells and `2618*k` target cells
preserves both public tail exponents. -/
theorem resonance_exponents (m h m' k : ℕ) :
    ternaryExponent (m + 2622 * k) h =
        ternaryExponent m (h + 391 * k) ∧
      binaryExponent h (m' + 2618 * k) =
        binaryExponent (h + 391 * k) m' := by
  constructor <;> simp [ternaryExponent, binaryExponent] <;> omega

theorem resonance_phase_slip (r k : ℕ) :
    (r + 2622 * k) - (r + 2618 * k) = 4 * k := by
  omega

/-- A subtraction-free certificate for an affine conjugacy between parallel
tail balances.  The identity is equivalent to
`(ternary-binary)*intercept = slope*kappaA-kappaB` whenever the displayed
subtractions are defined. -/
structure ParallelTailConjugacy where
  binary : ℕ
  ternary : ℕ
  kappaA : ℕ
  kappaB : ℕ
  slope : ℕ
  intercept : ℕ
  identity :
    ternary * intercept + kappaB =
      binary * intercept + slope * kappaA

namespace ParallelTailConjugacy

def embed (E : ParallelTailConjugacy) (t : ℕ) : ℕ :=
  E.slope * t + E.intercept

/-- RG2 implies the full commutative square without using division: every
source branch member maps to a target branch member. -/
theorem maps_balance (E : ParallelTailConjugacy) {x y : ℕ}
    (hsource : E.binary * y = E.ternary * x + E.kappaA) :
    E.binary * E.embed y = E.ternary * E.embed x + E.kappaB := by
  dsimp [embed]
  calc
    E.binary * (E.slope * y + E.intercept) =
        E.slope * (E.binary * y) + E.binary * E.intercept := by ring
    _ = E.slope * (E.ternary * x + E.kappaA) +
        E.binary * E.intercept := by rw [hsource]
    _ = E.ternary * (E.slope * x) +
        (E.binary * E.intercept + E.slope * E.kappaA) := by ring
    _ = E.ternary * (E.slope * x) +
        (E.ternary * E.intercept + E.kappaB) := by rw [E.identity]
    _ = E.ternary * (E.slope * x + E.intercept) + E.kappaB := by ring

/-- Cylinder compatibility is not an extra assumption: divisibility of the
source numerator implies divisibility of the embedded target numerator. -/
theorem maps_sourceCylinder (E : ParallelTailConjugacy) {rho : ℕ}
    (hsource : E.binary ∣ E.ternary * rho + E.kappaA) :
    E.binary ∣ E.ternary * E.embed rho + E.kappaB := by
  obtain ⟨q, hq⟩ := hsource
  refine ⟨E.slope * q + E.intercept, ?_⟩
  dsimp [embed]
  calc
    E.ternary * (E.slope * rho + E.intercept) + E.kappaB =
        E.ternary * (E.slope * rho) +
          (E.ternary * E.intercept + E.kappaB) := by ring
    _ = E.ternary * (E.slope * rho) +
          (E.binary * E.intercept + E.slope * E.kappaA) := by rw [E.identity]
    _ =
        E.slope * (E.ternary * rho + E.kappaA) +
          E.binary * E.intercept := by ring
    _ = E.slope * (E.binary * q) + E.binary * E.intercept := by rw [hq]
    _ = E.binary * (E.slope * q + E.intercept) := by ring

/-- Two affine embeddings which agree on two distinct ordinary inputs have
the same slope. -/
theorem slope_eq_of_agree_two (E F : ParallelTailConjugacy) {x y : ℕ}
    (hxy : x < y) (hx : E.embed x = F.embed x)
    (hy : E.embed y = F.embed y) : E.slope = F.slope := by
  have hx' : (E.slope : ℤ) * x + E.intercept =
      (F.slope : ℤ) * x + F.intercept := by exact_mod_cast hx
  have hy' : (E.slope : ℤ) * y + E.intercept =
      (F.slope : ℤ) * y + F.intercept := by exact_mod_cast hy
  have hprod : ((E.slope : ℤ) - F.slope) * ((y : ℤ) - x) = 0 := by
    linear_combination hy' - hx'
  have hdiff : (y : ℤ) - x ≠ 0 := by omega
  have hs : (E.slope : ℤ) - F.slope = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hdiff
  exact_mod_cast (sub_eq_zero.mp hs)

theorem intercept_eq_of_agree_two (E F : ParallelTailConjugacy) {x y : ℕ}
    (hxy : x < y) (hx : E.embed x = F.embed x)
    (hy : E.embed y = F.embed y) : E.intercept = F.intercept := by
  have hs := slope_eq_of_agree_two E F hxy hx hy
  dsimp [embed] at hx
  rw [hs] at hx
  exact Nat.add_left_cancel hx

/-- Hence two phase charts with the same parallel source data but different
target constants cannot be silently identified on a full cylinder. -/
theorem kappaB_eq_of_agree_two (E F : ParallelTailConjugacy)
    (hbinary : E.binary = F.binary) (hternary : E.ternary = F.ternary)
    (hkappaA : E.kappaA = F.kappaA) {x y : ℕ} (hxy : x < y)
    (hx : E.embed x = F.embed x) (hy : E.embed y = F.embed y) :
    E.kappaB = F.kappaB := by
  have hs := slope_eq_of_agree_two E F hxy hx hy
  have hc := intercept_eq_of_agree_two E F hxy hx hy
  have hE := E.identity
  have hF := F.identity
  rw [hbinary, hternary, hkappaA, hs, hc] at hE
  omega

end ParallelTailConjugacy
end ChargeResonantConjugacy
end KontoroC
