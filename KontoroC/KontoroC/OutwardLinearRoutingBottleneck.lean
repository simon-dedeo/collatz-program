/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFeaturePolicyGap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Shrunk-subspace certificates for finite linear routing families

A family of exact macro-template matrices can have a collective information
bottleneck invisible to coordinate Hall cuts.  A shrunk-subspace certificate
consists of source and target subspaces `U,U'` such that every template maps
`U` into `U'`, while `finrank U > finrank U'`.

This file proves the exact certificate semantics.  Every scalar linear
combination of the templates still maps `U` into `U'`, and hence is not
injective.  Thus no ordinary element of the template span is invertible.

The converse is deliberately absent.  Invertibility of a matrix blow-up or
full noncommutative rank uses linear superposition and auxiliary matrices; it
does not choose one literal directed Collatz macro for each state.  This module
is an obstruction verifier, not a routing or counterexample theorem.
-/

namespace KontoroC
namespace OutwardLinearRoutingBottleneck

variable {FieldType Index Source Target : Type*}
variable [Field FieldType]
variable [AddCommGroup Source] [Module FieldType Source]
variable [AddCommGroup Target] [Module FieldType Target]

/-- One linear map sends the declared source subspace into the declared
target subspace. -/
def MapsSubspace
    (linear : Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target) : Prop :=
  ∀ source ∈ sourceSpace, linear source ∈ targetSpace

/-- Every template in the exact finite family shares the same subspace
bottleneck. -/
def IsShrunkFamily [DecidableEq Index]
    (indices : Finset Index)
    (template : Index → Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target) : Prop :=
  ∀ index ∈ indices,
    MapsSubspace (template index) sourceSpace targetSpace

/-- The ordinary scalar linear combination represented by a coefficient
assignment on the finite template table. -/
def linearCombination [DecidableEq Index]
    (indices : Finset Index) (coefficient : Index → FieldType)
    (template : Index → Source →ₗ[FieldType] Target) :
    Source →ₗ[FieldType] Target :=
  ∑ index ∈ indices, coefficient index • template index

/-- A common subspace bottleneck is preserved by every ordinary scalar
linear combination of the templates. -/
theorem linearCombination_mapsSubspace
    [DecidableEq Index]
    (indices : Finset Index) (coefficient : Index → FieldType)
    (template : Index → Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target)
    (hshrunk : IsShrunkFamily indices template sourceSpace targetSpace) :
    MapsSubspace (linearCombination indices coefficient template)
      sourceSpace targetSpace := by
  intro source hsource
  simp only [linearCombination, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro index hindex
  exact targetSpace.smul_mem (coefficient index)
    (hshrunk index hindex source hsource)

/-- A linear map carrying a strictly larger finite-dimensional source
subspace into a smaller target subspace cannot be injective. -/
theorem not_injective_of_mapsSubspace_of_finrank_lt
    [FiniteDimensional FieldType Source]
    [FiniteDimensional FieldType Target]
    (linear : Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target)
    (hmaps : MapsSubspace linear sourceSpace targetSpace)
    (hfinrank : Module.finrank FieldType targetSpace <
      Module.finrank FieldType sourceSpace) :
    ¬ Function.Injective linear := by
  intro hinjective
  let restricted : sourceSpace →ₗ[FieldType] Target :=
    linear.domRestrict sourceSpace
  have hrestrictedInjective : Function.Injective restricted := by
    intro x y hxy
    apply Subtype.ext
    exact hinjective hxy
  have hrangeLe : LinearMap.range restricted ≤ targetSpace := by
    rintro target ⟨source, rfl⟩
    exact hmaps source source.property
  have hfinrankLe : Module.finrank FieldType (LinearMap.range restricted) ≤
      Module.finrank FieldType targetSpace :=
    Submodule.finrank_mono hrangeLe
  have hfinrankEq : Module.finrank FieldType (LinearMap.range restricted) =
      Module.finrank FieldType sourceSpace :=
    LinearMap.finrank_range_of_inj hrestrictedInjective
  omega

/-- A shrunk-family certificate excludes injectivity of every scalar
combination in the ordinary template span. -/
theorem linearCombination_not_injective_of_shrunk
    [DecidableEq Index]
    [FiniteDimensional FieldType Source]
    [FiniteDimensional FieldType Target]
    (indices : Finset Index) (coefficient : Index → FieldType)
    (template : Index → Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target)
    (hshrunk : IsShrunkFamily indices template sourceSpace targetSpace)
    (hfinrank : Module.finrank FieldType targetSpace <
      Module.finrank FieldType sourceSpace) :
    ¬ Function.Injective
      (linearCombination indices coefficient template) := by
  apply not_injective_of_mapsSubspace_of_finrank_lt
    (linearCombination indices coefficient template)
    sourceSpace targetSpace
  · exact linearCombination_mapsSubspace indices coefficient template
      sourceSpace targetSpace hshrunk
  · exact hfinrank

/-- In particular, no scalar combination certified by the shrunk family can
be bijective. -/
theorem linearCombination_not_bijective_of_shrunk
    [DecidableEq Index]
    [FiniteDimensional FieldType Source]
    [FiniteDimensional FieldType Target]
    (indices : Finset Index) (coefficient : Index → FieldType)
    (template : Index → Source →ₗ[FieldType] Target)
    (sourceSpace : Submodule FieldType Source)
    (targetSpace : Submodule FieldType Target)
    (hshrunk : IsShrunkFamily indices template sourceSpace targetSpace)
    (hfinrank : Module.finrank FieldType targetSpace <
      Module.finrank FieldType sourceSpace) :
    ¬ Function.Bijective
      (linearCombination indices coefficient template) := by
  intro hbijective
  exact linearCombination_not_injective_of_shrunk
    indices coefficient template sourceSpace targetSpace
    hshrunk hfinrank hbijective.1

end OutwardLinearRoutingBottleneck
end KontoroC
