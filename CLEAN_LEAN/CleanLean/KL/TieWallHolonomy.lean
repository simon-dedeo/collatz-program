/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ArgminFrustration

/-!
# Three-cycle carry holonomy and tie-wall escape

A fixed-point-free composite carry cannot transport three selected minimizing
labels consistently around a three-edge cycle.  Consequently at least one
edge pays its local frustration cost.  This is only a combinatorial reduction:
the bound can vanish when the relevant second-label gap tends to zero, exactly
as in the slowly rotating tie-wall counterexample.
-/

namespace CleanLean.KL

/-- Relabeling the three coordinates by a carry permutation does not change
their minimum. -/
theorem ternaryMin_comp_perm (z : Fin 3 → ℝ) (pi : Equiv.Perm (Fin 3)) :
    ternaryMin (z ∘ pi) = ternaryMin z := by
  apply le_antisymm
  · apply le_ternaryMin
    intro d
    simpa using ternaryMin_le (z ∘ pi) (pi.symm d)
  · apply le_ternaryMin
    intro d
    exact ternaryMin_le z (pi d)

/-- A selected minimizing label is transported by the inverse carry under
coordinate relabeling. -/
theorem isTernaryArgmin_comp_perm
    (z : Fin 3 → ℝ) (sigma : Fin 3) (pi : Equiv.Perm (Fin 3))
    (h : IsTernaryArgmin z sigma) :
    IsTernaryArgmin (z ∘ pi) (pi.symm sigma) := by
  intro d
  simpa using h (pi d)

/-- If the composite carry moves the initial label, the three edgewise label
matching equations cannot all hold. -/
theorem three_cycle_argmin_mismatch_of_holonomy
    (sigma₀ sigma₁ sigma₂ : Fin 3)
    (pi₀ pi₁ pi₂ : Equiv.Perm (Fin 3))
    (hhol : pi₂ (pi₁ (pi₀ sigma₀)) ≠ sigma₀) :
    pi₀ sigma₀ ≠ sigma₁ ∨ pi₁ sigma₁ ≠ sigma₂ ∨
      pi₂ sigma₂ ≠ sigma₀ := by
  by_contra hmatch
  push Not at hmatch
  obtain ⟨h₀, h₁, h₂⟩ := hmatch
  apply hhol
  rw [h₀, h₁, h₂]

theorem localFrustration_nonneg
    (tau w gapA gapZ : ℝ) (sigmaA sigmaZ : Fin 3)
    (pi : Equiv.Perm (Fin 3))
    (hA : 0 ≤ tau * gapA) (hZ : 0 ≤ w * gapZ) :
    0 ≤ localFrustration tau w gapA gapZ sigmaA sigmaZ pi := by
  unfold localFrustration
  split_ifs
  · exact le_rfl
  · exact le_min hA hZ

/-- A fixed-point-free three-edge holonomy forces the total local
frustration to pay at least the smallest of the three edge costs.  The result
is deliberately stated with the exact `localFrustration` quantity used by the
coarse-minimum interface. -/
theorem min_edgeCost_le_three_cycle_localFrustration
    (tau₀ tau₁ tau₂ w₀ w₁ w₂ : ℝ)
    (gapA₀ gapA₁ gapA₂ gapZ₀ gapZ₁ gapZ₂ : ℝ)
    (sigma₀ sigma₁ sigma₂ : Fin 3)
    (pi₀ pi₁ pi₂ : Equiv.Perm (Fin 3))
    (hA₀ : 0 ≤ tau₀ * gapA₀) (hA₁ : 0 ≤ tau₁ * gapA₁)
    (hA₂ : 0 ≤ tau₂ * gapA₂)
    (hZ₀ : 0 ≤ w₀ * gapZ₀) (hZ₁ : 0 ≤ w₁ * gapZ₁)
    (hZ₂ : 0 ≤ w₂ * gapZ₂)
    (hhol : pi₂ (pi₁ (pi₀ sigma₀)) ≠ sigma₀) :
    min (min (tau₀ * gapA₀) (w₀ * gapZ₀))
        (min (min (tau₁ * gapA₁) (w₁ * gapZ₁))
          (min (tau₂ * gapA₂) (w₂ * gapZ₂))) ≤
      localFrustration tau₀ w₀ gapA₀ gapZ₀ sigma₀ sigma₁ pi₀ +
        localFrustration tau₁ w₁ gapA₁ gapZ₁ sigma₁ sigma₂ pi₁ +
        localFrustration tau₂ w₂ gapA₂ gapZ₂ sigma₂ sigma₀ pi₂ := by
  have hnonneg₀ := localFrustration_nonneg tau₀ w₀ gapA₀ gapZ₀
    sigma₀ sigma₁ pi₀ hA₀ hZ₀
  have hnonneg₁ := localFrustration_nonneg tau₁ w₁ gapA₁ gapZ₁
    sigma₁ sigma₂ pi₁ hA₁ hZ₁
  have hnonneg₂ := localFrustration_nonneg tau₂ w₂ gapA₂ gapZ₂
    sigma₂ sigma₀ pi₂ hA₂ hZ₂
  rcases three_cycle_argmin_mismatch_of_holonomy
      sigma₀ sigma₁ sigma₂ pi₀ pi₁ pi₂ hhol with h₀ | h₁ | h₂
  · have hcost₀ :
        min (min (tau₀ * gapA₀) (w₀ * gapZ₀))
            (min (min (tau₁ * gapA₁) (w₁ * gapZ₁))
              (min (tau₂ * gapA₂) (w₂ * gapZ₂))) ≤
          min (tau₀ * gapA₀) (w₀ * gapZ₀) := min_le_left _ _
    have heq₀ : localFrustration tau₀ w₀ gapA₀ gapZ₀ sigma₀ sigma₁ pi₀ =
        min (tau₀ * gapA₀) (w₀ * gapZ₀) := by
      simp [localFrustration, h₀]
    linarith
  · have hcost₁ :
        min (min (tau₀ * gapA₀) (w₀ * gapZ₀))
            (min (min (tau₁ * gapA₁) (w₁ * gapZ₁))
              (min (tau₂ * gapA₂) (w₂ * gapZ₂))) ≤
          min (tau₁ * gapA₁) (w₁ * gapZ₁) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have heq₁ : localFrustration tau₁ w₁ gapA₁ gapZ₁ sigma₁ sigma₂ pi₁ =
        min (tau₁ * gapA₁) (w₁ * gapZ₁) := by
      simp [localFrustration, h₁]
    linarith
  · have hcost₂ :
        min (min (tau₀ * gapA₀) (w₀ * gapZ₀))
            (min (min (tau₁ * gapA₁) (w₁ * gapZ₁))
              (min (tau₂ * gapA₂) (w₂ * gapZ₂))) ≤
          min (tau₂ * gapA₂) (w₂ * gapZ₂) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have heq₂ : localFrustration tau₂ w₂ gapA₂ gapZ₂ sigma₂ sigma₀ pi₂ =
        min (tau₂ * gapA₂) (w₂ * gapZ₂) := by
      simp [localFrustration, h₂]
    linarith

/-- A three-profile tie-wall cycle: profile `j` has value one at label `j`
and zero at the other two labels. -/
def rotatingTieProfile (j d : Fin 3) : ℝ :=
  if d = j then 1 else 0

/-- Exact small kill test for any coercivity theorem that uses only cyclic
neighboring joint minima.  Every profile is nonconstant with total mass one,
but each neighboring pair shares a zero label and hence the complete
three-edge hard production is zero. -/
theorem rotatingTieWall_counterexample :
    (∀ j d, 0 ≤ rotatingTieProfile j d) ∧
    (∀ j, ternaryMin (rotatingTieProfile j) = 0) ∧
    (∀ j, (∑ d, rotatingTieProfile j d) = 1) ∧
    ternaryMin (fun d => rotatingTieProfile 0 d + rotatingTieProfile 1 d) +
      ternaryMin (fun d => rotatingTieProfile 1 d + rotatingTieProfile 2 d) +
      ternaryMin (fun d => rotatingTieProfile 2 d + rotatingTieProfile 0 d) = 0 := by
  constructor
  · intro j d
    fin_cases j <;> fin_cases d <;>
      norm_num [rotatingTieProfile, Fin.ext_iff]
  constructor
  · intro j
    fin_cases j <;> simp [rotatingTieProfile, ternaryMin]
  constructor
  · intro j
    fin_cases j <;> simp [rotatingTieProfile]
  · norm_num [rotatingTieProfile, ternaryMin, Fin.ext_iff]

end CleanLean.KL
