/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardNonEscapeCompactness
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Coercive resource bounds force first-passage non-escape

This module turns a proposed Collatz resource ledger into the exact
Archimedean non-escape condition.  A nonnegative resource on natural seeds is
`CoerciveOnNat` when sufficiently large seeds have arbitrarily large
resource.  Markov's inequality then says that a uniform finite moment bound
for carried probability measures forces a common tail cutoff of mass below
one.  The existing non-escape compactness theorem converts that directly into
an ordinary all-depth first-passage seed and hence a Collatz counterexample.

No resource or measure family is constructed here.
-/

namespace KontoroC
namespace OutwardResourceTightness

open MeasureTheory Set
open OutwardCodeCompactness OutwardNonEscapeCompactness OutwardOddSlice

/-- Archimedean coercivity of a nonnegative resource on natural seeds. -/
def CoerciveOnNat (resource : ℕ → ENNReal) : Prop :=
  ∀ threshold : ℕ, ∃ B, ∀ x, B < x → (threshold : ENNReal) ≤ resource x

/-- One finite upper bound for every depth-dependent resource moment. -/
def UniformMomentBound
    (resource : ℕ → ENNReal) (μ : ℕ → Measure ℕ) (bound : ENNReal) : Prop :=
  ∀ n, ∫⁻ x, resource x ∂μ n ≤ bound

/-- A finite uniform moment bound for a coercive resource forces one common
natural cutoff whose probability tail has mass strictly below one. -/
theorem uniformTailBelowOne_of_coercive_uniformMomentBound
    (resource : ℕ → ENNReal) (μ : ℕ → Measure ℕ)
    (hresource : Measurable resource)
    (hcoercive : CoerciveOnNat resource)
    {bound : ENNReal} (hboundTop : bound ≠ ⊤)
    (hmoment : UniformMomentBound resource μ bound) :
    UniformTailBelowOne μ := by
  obtain ⟨threshold, hthreshold⟩ := ENNReal.exists_nat_gt hboundTop
  obtain ⟨B, hB⟩ := hcoercive threshold
  refine ⟨B, fun n => ?_⟩
  have hmarkov :
      (threshold : ENNReal) * μ n {x | (threshold : ENNReal) ≤ resource x} ≤
        ∫⁻ x, resource x ∂μ n :=
    mul_meas_ge_le_lintegral hresource threshold
  have htailSubset : {x | B < x} ⊆
      {x | (threshold : ENNReal) ≤ resource x} := by
    intro x hx
    exact hB x hx
  have htailBound :
      (threshold : ENNReal) * μ n {x | B < x} ≤ bound := by
    calc
      (threshold : ENNReal) * μ n {x | B < x} ≤
          (threshold : ENNReal) *
            μ n {x | (threshold : ENNReal) ≤ resource x} := by
        gcongr
      _ ≤ ∫⁻ x, resource x ∂μ n := hmarkov
      _ ≤ bound := hmoment n
  by_contra hnot
  have hone : 1 ≤ μ n {x | B < x} := not_lt.mp hnot
  have hthresholdLe : (threshold : ENNReal) ≤
      (threshold : ENNReal) * μ n {x | B < x} := by
    calc
      (threshold : ENNReal) = (threshold : ENNReal) * 1 := by simp
      _ ≤ (threshold : ENNReal) * μ n {x | B < x} := by gcongr
  exact (not_le_of_gt hthreshold) (hthresholdLe.trans htailBound)

/-- The ordinary seed height is coercive. -/
theorem natCast_coerciveOnNat :
    CoerciveOnNat (fun x : ℕ => (x : ENNReal)) := by
  intro threshold
  refine ⟨threshold, fun x hx => ?_⟩
  change (threshold : ENNReal) ≤ (x : ENNReal)
  exact_mod_cast hx.le

/-- A uniformly bounded first moment of the ordinary seed itself forces the
weak non-escape tail condition. -/
theorem uniformTailBelowOne_of_uniformFirstMomentBound
    (μ : ℕ → Measure ℕ)
    {bound : ENNReal} (hboundTop : bound ≠ ⊤)
    (hmoment : UniformMomentBound (fun x : ℕ => (x : ENNReal)) μ bound) :
    UniformTailBelowOne μ :=
  uniformTailBelowOne_of_coercive_uniformMomentBound
    (fun x : ℕ => (x : ENNReal)) μ Measurable.of_discrete
    natCast_coerciveOnNat hboundTop hmoment

/-- The same resource hypotheses produce an explicit Syracuse
counterexample seed. -/
theorem exists_not_syracuseReachesOne_of_coercive_uniformMomentBound
    (resource : ℕ → ENNReal) (μ : ℕ → Measure ℕ)
    [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hresource : Measurable resource)
    (hcoercive : CoerciveOnNat resource)
    {bound : ENNReal} (hboundTop : bound ≠ ⊤)
    (hmoment : UniformMomentBound resource μ bound) :
    ∃ start, ¬ CleanLean.Collatz.SyracuseReachesOne start :=
  exists_not_syracuseReachesOne_of_nonEscaping_firstPassage_measures
    μ hcarried
    (uniformlyNonEscaping_of_probability_tailBelowOne μ
      (uniformTailBelowOne_of_coercive_uniformMomentBound
        resource μ hresource hcoercive hboundTop hmoment))

/-- A coercive uniformly moment-bounded family carried by finite-depth
first-passage survivors refutes the standard Collatz conjecture. -/
theorem not_collatz_of_coercive_uniformMomentBound
    (resource : ℕ → ENNReal) (μ : ℕ → Measure ℕ)
    [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    (hresource : Measurable resource)
    (hcoercive : CoerciveOnNat resource)
    {bound : ENNReal} (hboundTop : bound ≠ ⊤)
    (hmoment : UniformMomentBound resource μ bound) :
    ¬ CleanLean.Collatz.Conjecture :=
  not_collatz_of_tailBelowOne_firstPassage_probability_measures μ hcarried
    (uniformTailBelowOne_of_coercive_uniformMomentBound
      resource μ hresource hcoercive hboundTop hmoment)

/-- Concrete ordinary-first-moment endpoint. -/
theorem not_collatz_of_uniformFirstMomentBound
    (μ : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (μ n)]
    (hcarried : ∀ n,
      CarriedBy (RealizesDepth FirstPassageCode n) (μ n))
    {bound : ENNReal} (hboundTop : bound ≠ ⊤)
    (hmoment : UniformMomentBound (fun x : ℕ => (x : ENNReal)) μ bound) :
    ¬ CleanLean.Collatz.Conjecture :=
  not_collatz_of_coercive_uniformMomentBound
    (fun x : ℕ => (x : ENNReal)) μ hcarried Measurable.of_discrete
    natCast_coerciveOnNat hboundTop hmoment

end OutwardResourceTightness
end KontoroC
