/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSelectorIndistinguishability

/-!
# Exact faithfulness gates for finite outward shadows

A residue, representation, or spectral shadow is useful for an ordinary
first-passage construction only if the information needed by the literal
construction can be recovered from it.  This file separates two exact finite
claims:

* `CoordinateRecoverableOn states shadow coordinate` says that one required
  coordinate (for example the ordinary seed) factors through the shadow;
* `FaithfulOn states shadow` says that the entire exact state can be recovered.

Both properties have executable collision tables.  If the ordinary-seed
coordinate is injective on the exact state set, coordinate recovery and full
faithfulness coincide.  Without that injectivity hypothesis, full
faithfulness is deliberately stronger: two auxiliary records may describe
the same ordinary seed.

These are finite-level gates.  A separately chosen decoder at every precision
is not thereby one coherent unbounded decoder, and none of the results below
supplies literal recharge closure or an ordinary infinite execution.
-/

namespace KontoroC
namespace OutwardFiniteShadowFaithfulness

open OutwardSelectorIndistinguishability

variable {State Shadow Coordinate : Type*}

/-- The shadow has trivial kernel on the presented exact state set. -/
def FaithfulOn (states : Finset State) (shadow : State → Shadow) : Prop :=
  ∀ x ∈ states, ∀ y ∈ states, shadow x = shadow y → x = y

/-- One required coordinate of the state is recoverable from the shadow on
the presented exact state set. -/
def CoordinateRecoverableOn (states : Finset State)
    (shadow : State → Shadow) (coordinate : State → Coordinate) : Prop :=
  ∃ decode : Shadow → Coordinate,
    ∀ x ∈ states, coordinate x = decode (shadow x)

/-- Full faithfulness is precisely functionality of the identity coordinate.
This connects the kernel language to the exact selector interface. -/
theorem faithfulOn_iff_functionalOn_id
    (states : Finset State) (shadow : State → Shadow) :
    FaithfulOn states shadow ↔ FunctionalOn states shadow id := by
  rfl

/-- Recoverability of a coordinate is exactly factorization through the
shadow. -/
theorem coordinateRecoverableOn_iff_functionalOn
    [Nonempty Coordinate]
    (states : Finset State) (shadow : State → Shadow)
    (coordinate : State → Coordinate) :
    CoordinateRecoverableOn states shadow coordinate ↔
      FunctionalOn states shadow coordinate := by
  rw [functionalOn_iff_exists_decoder]
  exact Iff.symm Iff.rfl

/-- A faithful shadow permits recovery of every requested coordinate. -/
theorem coordinateRecoverableOn_of_faithfulOn
    [Nonempty Coordinate]
    (states : Finset State) (shadow : State → Shadow)
    (coordinate : State → Coordinate)
    (hfaithful : FaithfulOn states shadow) :
    CoordinateRecoverableOn states shadow coordinate := by
  rw [coordinateRecoverableOn_iff_functionalOn]
  intro x hx y hy hxy
  exact congrArg coordinate (hfaithful x hx y hy hxy)

/-- If the requested coordinate itself separates the exact states, then
recovering that coordinate forces the whole shadow to be faithful.  For an
ordinary-seed coordinate this is the precise hypothesis needed to replace a
seed-kernel check by full-state injectivity. -/
theorem faithfulOn_of_coordinateRecoverableOn_of_injective
    (states : Finset State) (shadow : State → Shadow)
    (coordinate : State → Coordinate)
    (hrecover : CoordinateRecoverableOn states shadow coordinate)
    (hinjective : ∀ x ∈ states, ∀ y ∈ states,
      coordinate x = coordinate y → x = y) :
    FaithfulOn states shadow := by
  obtain ⟨decode, hdecode⟩ := hrecover
  intro x hx y hy hshadow
  apply hinjective x hx y hy
  rw [hdecode x hx, hdecode y hy, hshadow]

/-- When the ordinary coordinate labels exact states injectively, recovering
it and recovering the entire state are equivalent. -/
theorem faithfulOn_iff_coordinateRecoverableOn_of_injective
    [Nonempty Coordinate]
    (states : Finset State) (shadow : State → Shadow)
    (coordinate : State → Coordinate)
    (hinjective : ∀ x ∈ states, ∀ y ∈ states,
      coordinate x = coordinate y → x = y) :
    FaithfulOn states shadow ↔
      CoordinateRecoverableOn states shadow coordinate := by
  constructor
  · exact coordinateRecoverableOn_of_faithfulOn states shadow coordinate
  · intro hrecover
    exact faithfulOn_of_coordinateRecoverableOn_of_injective
      states shadow coordinate hrecover hinjective

/-- An explicit shadow collision with distinct required coordinates refutes
every proposed coordinate decoder. -/
theorem no_coordinateDecoder_of_collision
    (states : Finset State) (shadow : State → Shadow)
    (coordinate : State → Coordinate)
    {x y : State} (hx : x ∈ states) (hy : y ∈ states)
    (hshadow : shadow x = shadow y)
    (hcoordinate : coordinate x ≠ coordinate y) :
    ¬CoordinateRecoverableOn states shadow coordinate := by
  rintro ⟨decode, hdecode⟩
  apply hcoordinate
  rw [hdecode x hx, hdecode y hy, hshadow]

/-- A nontrivial kernel pair refutes every full-state reifier. -/
theorem no_reifier_of_kernelPair
    (states : Finset State) (shadow : State → Shadow)
    {x y : State} (hx : x ∈ states) (hy : y ∈ states)
    (hshadow : shadow x = shadow y) (hne : x ≠ y) :
    ¬ ∃ reify : Shadow → State,
      ∀ z ∈ states, z = reify (shadow z) := by
  exact no_coordinateDecoder_of_collision states shadow id
    hx hy hshadow (by simpa using hne)

/-- Full faithfulness is equivalent to existence of a state reifier on the
presented finite set. -/
theorem faithfulOn_iff_exists_reifier
    [Nonempty State]
    (states : Finset State) (shadow : State → Shadow) :
    FaithfulOn states shadow ↔
      ∃ reify : Shadow → State,
        ∀ x ∈ states, x = reify (shadow x) := by
  rw [faithfulOn_iff_functionalOn_id,
    functionalOn_iff_exists_decoder]
  simp only [id_eq]

section Decidable

variable [DecidableEq State] [DecidableEq Shadow]

/-- Executable table of all nontrivial kernel pairs of the shadow. -/
def kernelPairs (states : Finset State) (shadow : State → Shadow) :
    Finset (State × State) :=
  witnessPairs states shadow id

@[simp] theorem mem_kernelPairs_iff
    {states : Finset State} {shadow : State → Shadow} {x y : State} :
    (x, y) ∈ kernelPairs states shadow ↔
      x ∈ states ∧ y ∈ states ∧ shadow x = shadow y ∧ x ≠ y := by
  simp [kernelPairs, IsIndistinguishableWitness]

/-- The executable kernel table is empty exactly when the finite shadow is
faithful. -/
theorem kernelPairs_eq_empty_iff_faithfulOn
    (states : Finset State) (shadow : State → Shadow) :
    kernelPairs states shadow = ∅ ↔ FaithfulOn states shadow := by
  simpa [kernelPairs, FaithfulOn, FunctionalOn] using
    (witnessPairs_eq_empty_iff_functionalOn states shadow id)

/-- A nonempty kernel table is an exact finite countercertificate to
faithfulness. -/
theorem kernelPairs_nonempty_iff_not_faithfulOn
    (states : Finset State) (shadow : State → Shadow) :
    (kernelPairs states shadow).Nonempty ↔ ¬FaithfulOn states shadow := by
  simpa [kernelPairs, FaithfulOn, FunctionalOn] using
    (witnessPairs_nonempty_iff_not_functionalOn states shadow id)

end Decidable

/-- Faithfulness survives a genuine refinement: equality of refined shadows
must imply equality of the old shadows on the exact state set. -/
theorem FaithfulOn.of_refinement
    (states : Finset State)
    (coarse : State → Shadow) (fine : State → Coordinate)
    (hrefines : ∀ x ∈ states, ∀ y ∈ states,
      fine x = fine y → coarse x = coarse y)
    (hfaithful : FaithfulOn states coarse) :
    FaithfulOn states fine := by
  intro x hx y hy hxy
  exact hfaithful x hx y hy (hrefines x hx y hy hxy)

/-- A coarse kernel pair remains a kernel pair for every alleged refinement
which still fails to separate that pair. -/
theorem kernelPair_survives_unseparating_refinement
    (fine : State → Coordinate)
    {x y : State} (hne : x ≠ y)
    (hfine : fine x = fine y) :
    fine x = fine y ∧ x ≠ y :=
  ⟨hfine, hne⟩

end OutwardFiniteShadowFaithfulness
end KontoroC
