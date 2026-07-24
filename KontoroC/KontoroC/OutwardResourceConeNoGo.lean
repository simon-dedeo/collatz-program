/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteStateKraftGap

/-!
# Exact resource-cone dual certificates for finite first-passage grammars

A recurrent finite macro grammar has a nonzero nonnegative conserved edge
flow.  This module proves the exact dual obstruction used by a rational
resource-cone preflight: if a vertex potential plus a scalar resource score
strictly decreases on every edge, but every admissible recurrent flow is
required to have nonnegative total resource score, then no such flow exists.

The scalar score may already be a rational linear combination of height,
dyadic precision, triadic precision, carry, or other exact resource changes.
The theorem concerns finite grammar architecture only; it neither supplies a
flow from bounded search nor turns a feasible flow into an ordered orbit.
-/

namespace KontoroC
namespace OutwardResourceConeNoGo

open scoped BigOperators
open OutwardFiniteStateKraftGap

variable {State Edge : Type*}
variable [Fintype State] [Nonempty State] [DecidableEq State]
variable [Fintype Edge] [DecidableEq Edge]

namespace FirstPassageGrammar

/-- Edges entering a specified state. -/
def incoming (G : FirstPassageGrammar State Edge) (i : State) : Finset Edge :=
  Finset.univ.filter fun e => G.target e = i

noncomputable def sourceFlow
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ) (i : State) : ℚ :=
  ∑ e ∈ G.outgoing i, flow e

noncomputable def targetFlow
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ) (i : State) : ℚ :=
  ∑ e ∈ incoming G i, flow e

/-- A nonzero nonnegative circulation on the finite macro graph. -/
def IsNonzeroCirculation
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ) : Prop :=
  (∀ e, 0 ≤ flow e) ∧
  (∃ e, 0 < flow e) ∧
  ∀ i, sourceFlow G flow i = targetFlow G flow i

theorem sum_by_source
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ)
    (potential : State → ℚ) :
    (∑ e, flow e * potential (G.source e)) =
      ∑ i, sourceFlow G flow i * potential i := by
  classical
  symm
  calc
    (∑ i, sourceFlow G flow i * potential i) =
        ∑ i, ∑ e ∈ Finset.univ with G.source e = i,
          flow e * potential i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sourceFlow,
              OutwardFiniteStateKraftGap.FirstPassageGrammar.outgoing,
              Finset.sum_mul]
    _ = ∑ i, ∑ e ∈ Finset.univ with G.source e = i,
          flow e * potential (G.source e) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro e he
            rw [(Finset.mem_filter.mp he).2]
    _ = ∑ e, flow e * potential (G.source e) := by
      simpa using Finset.sum_fiberwise Finset.univ G.source
        (fun e => flow e * potential (G.source e))

theorem sum_by_target
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ)
    (potential : State → ℚ) :
    (∑ e, flow e * potential (G.target e)) =
      ∑ i, targetFlow G flow i * potential i := by
  classical
  symm
  calc
    (∑ i, targetFlow G flow i * potential i) =
        ∑ i, ∑ e ∈ Finset.univ with G.target e = i,
          flow e * potential i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [targetFlow, incoming, Finset.sum_mul]
    _ = ∑ i, ∑ e ∈ Finset.univ with G.target e = i,
          flow e * potential (G.target e) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro e he
            rw [(Finset.mem_filter.mp he).2]
    _ = ∑ e, flow e * potential (G.target e) := by
      simpa using Finset.sum_fiberwise Finset.univ G.target
        (fun e => flow e * potential (G.target e))

/-- Vertex potentials telescope to zero against any conserved flow. -/
theorem circulation_potential_sum_eq_zero
    (G : FirstPassageGrammar State Edge) (flow : Edge → ℚ)
    (potential : State → ℚ)
    (hbalance : ∀ i, sourceFlow G flow i = targetFlow G flow i) :
    ∑ e, flow e * (potential (G.target e) - potential (G.source e)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_by_target G flow potential,
    sum_by_source G flow potential]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  rw [← hbalance i]

/-- Exact Farkas-style no-go.  `score` is the chosen rational dual
combination of edge resources. -/
theorem no_nonzeroCirculation_of_strict_resource_dual
    (G : FirstPassageGrammar State Edge)
    (flow : Edge → ℚ) (potential : State → ℚ) (score : Edge → ℚ)
    (hflow : IsNonzeroCirculation G flow)
    (hresource : 0 ≤ ∑ e, flow e * score e)
    (hdual : ∀ e,
      potential (G.target e) - potential (G.source e) + score e < 0) :
    False := by
  rcases hflow with ⟨hflow_nonneg, ⟨e₀, he₀⟩, hbalance⟩
  have hterm_le : ∀ e,
      flow e * (potential (G.target e) - potential (G.source e) + score e) ≤ 0 := by
    intro e
    exact mul_nonpos_of_nonneg_of_nonpos (hflow_nonneg e) (hdual e).le
  have hterm_lt :
      flow e₀ * (potential (G.target e₀) - potential (G.source e₀) + score e₀) < 0 :=
    mul_neg_of_pos_of_neg he₀ (hdual e₀)
  have hsum_lt :
      (∑ e, flow e *
        (potential (G.target e) - potential (G.source e) + score e)) < 0 := by
    have hsum := Finset.sum_lt_sum
      (fun e (_ : e ∈ (Finset.univ : Finset Edge)) => hterm_le e)
      ⟨e₀, Finset.mem_univ e₀, hterm_lt⟩
    simpa using hsum
  have hpotential := circulation_potential_sum_eq_zero G
    flow potential hbalance
  have hsplit :
      (∑ e, flow e *
        (potential (G.target e) - potential (G.source e) + score e)) =
      (∑ e, flow e *
        (potential (G.target e) - potential (G.source e))) +
      ∑ e, flow e * score e := by
    simp_rw [mul_add]
    exact Finset.sum_add_distrib
  rw [hsplit, hpotential, zero_add] at hsum_lt
  exact (not_lt_of_ge hresource) hsum_lt

/-- Contradiction form suitable for a preflight worker: no admissible
nonzero circulation can satisfy the required nonnegative resource budget. -/
theorem no_resource_admissible_nonzeroCirculation_of_strict_dual
    (G : FirstPassageGrammar State Edge)
    (potential : State → ℚ) (score : Edge → ℚ)
    (hdual : ∀ e,
      potential (G.target e) - potential (G.source e) + score e < 0) :
    ¬ ∃ flow : Edge → ℚ,
      IsNonzeroCirculation G flow ∧ 0 ≤ ∑ e, flow e * score e := by
  rintro ⟨flow, hflow, hresource⟩
  exact no_nonzeroCirculation_of_strict_resource_dual G
    flow potential score hflow hresource hdual

/-! ## Several named resources and a nonnegative dual multiplier -/

/-- Rational linear combination of a finite resource vector. -/
noncomputable def combinedScore {d : ℕ}
    (resource : Edge → Fin d → ℚ) (multiplier : Fin d → ℚ) (e : Edge) : ℚ :=
  ∑ k, multiplier k * resource e k

theorem combinedScore_total_nonneg {d : ℕ}
    (flow : Edge → ℚ) (resource : Edge → Fin d → ℚ)
    (multiplier : Fin d → ℚ)
    (hmultiplier : ∀ k, 0 ≤ multiplier k)
    (hresource : ∀ k, 0 ≤ ∑ e, flow e * resource e k) :
    0 ≤ ∑ e, flow e * combinedScore resource multiplier e := by
  calc
    0 ≤ ∑ k, multiplier k * (∑ e, flow e * resource e k) := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (hmultiplier k) (hresource k)
    _ = ∑ k, ∑ e,
        multiplier k * (flow e * resource e k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ e, ∑ k,
        multiplier k * (flow e * resource e k) := Finset.sum_comm
    _ = ∑ e, flow e * combinedScore resource multiplier e := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [combinedScore, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Multi-resource Farkas certificate.  Nonnegative dual multipliers combine
coordinatewise nonnegative recurrent budgets into the scalar obstruction. -/
theorem no_nonzeroCirculation_of_strict_vector_resource_dual {d : ℕ}
    (G : FirstPassageGrammar State Edge)
    (flow : Edge → ℚ) (potential : State → ℚ)
    (resource : Edge → Fin d → ℚ) (multiplier : Fin d → ℚ)
    (hflow : IsNonzeroCirculation G flow)
    (hmultiplier : ∀ k, 0 ≤ multiplier k)
    (hresource : ∀ k, 0 ≤ ∑ e, flow e * resource e k)
    (hdual : ∀ e,
      potential (G.target e) - potential (G.source e) +
        combinedScore resource multiplier e < 0) :
    False := by
  exact no_nonzeroCirculation_of_strict_resource_dual G flow potential
    (combinedScore resource multiplier) hflow
    (combinedScore_total_nonneg flow resource multiplier
      hmultiplier hresource)
    hdual

end FirstPassageGrammar
end OutwardResourceConeNoGo
end KontoroC
