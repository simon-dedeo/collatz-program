/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCoherentSeedTower

/-!
# Exact ordinary-root dichotomy for coherent finite shadows

For compatible representatives modulo growing mixed dyadic--triadic
precision, bounded Archimedean height is not merely one convenient sufficient
condition: it is exactly equivalent to eventual literal constancy.  Hence a
coherent tower which does not encode one ordinary natural must escape every
fixed natural window.

There is an equivalent local criterion.  Under compatibility, the
representatives stabilize exactly when their consecutive ordinary difference
is eventually smaller than the current modulus.  This is the zero-extension-
carry gate.  It is exact, but not automatically easier: proving it is proving
that all sufficiently late extension carries vanish.

The final theorems promote this local condition through an arbitrary nested
predicate and then specialize it to literal outward first-passage execution.
No compatible tower or zero-carry estimate is constructed here.
-/

namespace KontoroC
namespace OutwardOrdinaryRootDichotomy

open OutwardCodeCompactness OutwardSArithmeticStabilization
  OutwardCoherentSeedTower OutwardCodeCounterexample OutwardOddSlice
open CleanLean.Collatz

/-- Every eventually constant natural sequence has bounded range; no
monotonicity hypothesis is needed. -/
theorem boundedRange_of_eventuallyConstant
    {representative : ℕ → ℕ}
    (hconstant : EventuallyConstant representative) :
    BoundedRange representative := by
  obtain ⟨K, hK⟩ := hconstant
  let bound := ∑ k ∈ Finset.range (K + 1), representative k
  refine ⟨bound, fun k ↦ ?_⟩
  by_cases hk : K ≤ k
  · rw [hK k hk]
    exact Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le (representative i))
      (Finset.mem_range.mpr (Nat.lt_succ_self K))
  · have hkRange : k ∈ Finset.range (K + 1) := by
      rw [Finset.mem_range]
      omega
    exact Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le (representative i)) hkRange

/-- Exact all-place dichotomy: for compatible representatives at precision
tending to infinity, one ordinary stabilized root exists exactly when their
ordinary heights remain bounded. -/
theorem eventuallyConstant_iff_boundedRange
    (representative dyadic triadic : ℕ → ℕ)
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    EventuallyConstant representative ↔
      BoundedRange representative := by
  constructor
  · exact boundedRange_of_eventuallyConstant
  · intro hbounded
    exact eventuallyConstant_of_compatible_bounded_representatives
      representative dyadic triadic hcompatible hbounded hprecision

/-- Therefore a compatible growing-precision tower which does not stabilize
must have representatives above every ordinary bound. -/
theorem not_eventuallyConstant_iff_unbounded
    (representative dyadic triadic : ℕ → ℕ)
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    ¬ EventuallyConstant representative ↔
      ∀ bound, ∃ k, bound < representative k := by
  rw [eventuallyConstant_iff_boundedRange representative dyadic triadic
    hcompatible hprecision]
  simp only [BoundedRange]
  push Not
  rfl

/-- Under exact mixed congruence, eventual literal constancy is equivalent to
eventual strict Archimedean smallness of every extension relative to its
current modulus. -/
theorem eventuallyConstant_iff_eventually_small_extensions
    (representative dyadic triadic : ℕ → ℕ)
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k]) :
    EventuallyConstant representative ↔
      ∃ K, ∀ k, K ≤ k →
        |(representative (k + 1) : ℤ) - representative k| <
          (2 ^ dyadic k * 3 ^ triadic k : ℕ) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun k hk ↦ ?_⟩
    rw [hK k hk, hK (k + 1) (by omega)]
    simp only [sub_self, abs_zero, Nat.cast_pos]
    positivity
  · exact eventuallyConstant_of_sArithmetic_extension_bounds
      representative dyadic triadic hcompatible

/-- An eventually stabilized representative of nested finite-depth witnesses
is one ordinary witness valid at every depth. -/
theorem exists_global_witness_of_eventuallyConstant_representatives
    (P : ℕ → ℕ → Prop)
    (hnested : ∀ depth seed, P (depth + 1) seed → P depth seed)
    (representative : ℕ → ℕ)
    (hwitness : ∀ depth, P depth (representative depth))
    (hconstant : EventuallyConstant representative) :
    ∃ seed, ∀ depth, P depth seed := by
  obtain ⟨K, hK⟩ := hconstant
  refine ⟨representative K, fun depth ↦ ?_⟩
  let later := max K depth
  have hKlater : K ≤ later := Nat.le_max_left K depth
  have hdepthLater : depth ≤ later := Nat.le_max_right K depth
  have hlater : P later (representative K) := by
    rw [← hK later hKlater]
    exact hwitness later
  exact nested_of_le P hnested hdepthLater hlater

/-- The local zero-extension-carry criterion promotes any nested tower to one
ordinary global witness. -/
theorem exists_global_witness_of_compatible_small_extensions
    (P : ℕ → ℕ → Prop)
    (hnested : ∀ depth seed, P (depth + 1) seed → P depth seed)
    (representative dyadic triadic : ℕ → ℕ)
    (hwitness : ∀ depth, P depth (representative depth))
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hsmall : ∃ K, ∀ k, K ≤ k →
      |(representative (k + 1) : ℤ) - representative k| <
        (2 ^ dyadic k * 3 ^ triadic k : ℕ)) :
    ∃ seed, ∀ depth, P depth seed := by
  apply exists_global_witness_of_eventuallyConstant_representatives
    P hnested representative hwitness
  exact (eventuallyConstant_iff_eventually_small_extensions
    representative dyadic triadic hcompatible).mpr hsmall

/-- Literal specialization: compatible finite executions whose extension
carries eventually vanish yield one ordinary infinite execution. -/
theorem exists_infiniteExecution_of_compatible_small_extensions
    (C : Set (List Bool))
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth, RealizesDepth C depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hsmall : ∃ K, ∀ k, K ≤ k →
      |(start (k + 1) : ℤ) - start k| <
        (2 ^ dyadic k * 3 ^ triadic k : ℕ)) :
    ∃ ordinaryStart, InfiniteExecution C ordinaryStart := by
  exact exists_global_witness_of_compatible_small_extensions
    (RealizesDepth C) (realizesDepth_nested C)
    start dyadic triadic hdepth hcompatible hsmall

/-- Outward first-passage specialization at the Syracuse endpoint. -/
theorem exists_not_syracuseReachesOne_of_compatible_small_extensions
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth,
      RealizesDepth FirstPassageCode depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hsmall : ∃ K, ∀ k, K ≤ k →
      |(start (k + 1) : ℤ) - start k| <
        (2 ^ dyadic k * 3 ^ triadic k : ℕ)) :
    ∃ ordinaryStart, ¬ SyracuseReachesOne ordinaryStart := by
  obtain ⟨ordinaryStart, hinfinite⟩ :=
    exists_infiniteExecution_of_compatible_small_extensions
      FirstPassageCode start dyadic triadic hdepth hcompatible hsmall
  exact ⟨ordinaryStart,
    not_syracuseReachesOne_of_infiniteExecution
      (fun _ hw ↦ hw.1) hinfinite⟩

/-- Outward first-passage specialization at the standard unaccelerated
Collatz endpoint. -/
theorem not_collatz_of_compatible_small_extensions
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth,
      RealizesDepth FirstPassageCode depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hsmall : ∃ K, ∀ k, K ≤ k →
      |(start (k + 1) : ℤ) - start k| <
        (2 ^ dyadic k * 3 ^ triadic k : ℕ)) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨ordinaryStart, hinfinite⟩ :=
    exists_infiniteExecution_of_compatible_small_extensions
      FirstPassageCode start dyadic triadic hdepth hcompatible hsmall
  exact not_conjecture_of_infiniteExecution (fun _ hw ↦ hw.1) hinfinite

end OutwardOrdinaryRootDichotomy
end KontoroC
