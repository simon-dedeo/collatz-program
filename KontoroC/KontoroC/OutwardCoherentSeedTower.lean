/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSArithmeticStabilization
import KontoroC.OutwardCodeCounterexample

/-!
# Coherent finite shadows promote to one ordinary seed

Independent finite-depth witnesses can form only a profinite tape.  This file
states a sufficient positive promotion theorem.  Suppose the chosen ordinary
representatives at consecutive depths are compatible modulo
`2 ^ dyadic k * 3 ^ triadic k`, those moduli eventually exceed every fixed
natural bound, and all representatives lie in one fixed ordinary window.
Then the representatives are eventually literally constant.

If each representative witnesses its corresponding member of a nested
predicate family, the stabilized natural witnesses every depth.  The final
specialization applies this to literal first-passage execution and derives
the existing conditional Syracuse/Collatz consequences.

The uniform ordinary bound is essential.  Compatibility modulo increasing
moduli alone admits nonordinary profinite sequences.  This file does not
construct the compatible bounded representatives.
-/

namespace KontoroC
namespace OutwardCoherentSeedTower

open OutwardCodeCompactness OutwardSArithmeticStabilization
  OutwardCodeCounterexample OutwardOddSlice
open CleanLean.Collatz

/-- Growing mixed precision plus a uniform ordinary bound turns compatible
representatives into an eventually constant sequence. -/
theorem eventuallyConstant_of_compatible_bounded_representatives
    (representative dyadic triadic : ℕ → ℕ)
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hbounded : BoundedRange representative)
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    EventuallyConstant representative := by
  obtain ⟨bound, hbound⟩ := hbounded
  obtain ⟨K, hK⟩ := hprecision bound
  apply eventuallyConstant_of_sArithmetic_extension_bounds
    representative dyadic triadic hcompatible
  refine ⟨K, fun k hk ↦ ?_⟩
  have hkBound := hbound k
  have hkSuccBound := hbound (k + 1)
  have hdifference :
      |(representative (k + 1) : ℤ) - representative k| ≤ bound := by
    rw [abs_le]
    constructor <;> omega
  exact hdifference.trans_lt (by exact_mod_cast hK k hk)

/-- Promotion theorem for an arbitrary nested finite-depth property.  The
eventual representative is one ordinary natural satisfying every depth. -/
theorem exists_global_witness_of_compatible_bounded_representatives
    (P : ℕ → ℕ → Prop)
    (hnested : ∀ depth seed, P (depth + 1) seed → P depth seed)
    (representative dyadic triadic : ℕ → ℕ)
    (hwitness : ∀ depth, P depth (representative depth))
    (hcompatible : ∀ k,
      representative (k + 1) ≡ representative k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hbounded : BoundedRange representative)
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    ∃ seed, ∀ depth, P depth seed := by
  obtain ⟨K, hconstant⟩ :=
    eventuallyConstant_of_compatible_bounded_representatives
      representative dyadic triadic hcompatible hbounded hprecision
  refine ⟨representative K, fun depth ↦ ?_⟩
  let later := max K depth
  have hKlater : K ≤ later := Nat.le_max_left K depth
  have hdepthLater : depth ≤ later := Nat.le_max_right K depth
  have hlaterWitness : P later (representative K) := by
    rw [← hconstant later hKlater]
    exact hwitness later
  exact nested_of_le P hnested hdepthLater hlaterWitness

/-- Literal specialization: compatible bounded finite-depth starting values
produce one ordinary start with an infinite execution of the same code. -/
theorem exists_infiniteExecution_of_compatible_bounded_starts
    (C : Set (List Bool))
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth, RealizesDepth C depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hbounded : BoundedRange start)
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    ∃ ordinaryStart, InfiniteExecution C ordinaryStart := by
  exact exists_global_witness_of_compatible_bounded_representatives
    (RealizesDepth C) (realizesDepth_nested C)
    start dyadic triadic hdepth hcompatible hbounded hprecision

/-- For the outward first-passage code, the coherent bounded seed tower
already refutes Syracuse for its stabilized ordinary start. -/
theorem exists_not_syracuseReachesOne_of_compatible_bounded_starts
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth,
      RealizesDepth FirstPassageCode depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hbounded : BoundedRange start)
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    ∃ ordinaryStart, ¬SyracuseReachesOne ordinaryStart := by
  obtain ⟨ordinaryStart, hinfinite⟩ :=
    exists_infiniteExecution_of_compatible_bounded_starts
      FirstPassageCode start dyadic triadic
      hdepth hcompatible hbounded hprecision
  exact ⟨ordinaryStart,
    not_syracuseReachesOne_of_infiniteExecution (fun _ hw ↦ hw.1) hinfinite⟩

/-- The same coherent bounded tower conditionally refutes the standard
unaccelerated Collatz conjecture via the existing outward-code bridge. -/
theorem not_collatz_of_compatible_bounded_starts
    (start dyadic triadic : ℕ → ℕ)
    (hdepth : ∀ depth,
      RealizesDepth FirstPassageCode depth (start depth))
    (hcompatible : ∀ k,
      start (k + 1) ≡ start k
        [MOD 2 ^ dyadic k * 3 ^ triadic k])
    (hbounded : BoundedRange start)
    (hprecision : ∀ bound, ∃ K, ∀ k, K ≤ k →
      bound < 2 ^ dyadic k * 3 ^ triadic k) :
    ¬CleanLean.Collatz.Conjecture := by
  obtain ⟨ordinaryStart, hinfinite⟩ :=
    exists_infiniteExecution_of_compatible_bounded_starts
      FirstPassageCode start dyadic triadic
      hdepth hcompatible hbounded hprecision
  exact not_conjecture_of_infiniteExecution (fun _ hw ↦ hw.1) hinfinite

end OutwardCoherentSeedTower
end KontoroC
