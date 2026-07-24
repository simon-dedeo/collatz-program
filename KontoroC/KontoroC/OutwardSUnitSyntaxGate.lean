/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSelectorIndistinguishability

/-!
# Conditional fixed-syntax gate from nondegenerate finiteness

A fixed-shape recharge identity expands into a fixed finite tuple of signed
arithmetic terms whose total is zero.  Classical fixed-`S` unit-equation
theorems say, after projective normalization, that only finitely many such
tuples can be nondegenerate (have no vanishing proper subsum).

This file formalizes the exact elementary transfer from that finiteness input.
It does **not** postulate or prove the deep `S`-unit theorem.  The finiteness
statement is an explicit hypothesis.  Under it, a family with infinitely many
projective normal forms must contain infinitely many tuples with an exact
vanishing proper subsum.  Thus an unbounded fixed-term macro family must expose
a compositional split; smoothness or equidistribution alone is not enough.
-/

namespace KontoroC
namespace OutwardSUnitSyntaxGate

open scoped BigOperators

variable {TermIndex R NormalForm Parameter : Type*}
variable [Fintype TermIndex] [DecidableEq TermIndex]
variable [AddCommMonoid R]

/-- A tuple has an exact zero proper subsum.  Nonemptiness excludes the
vacuous empty sum, and inequality with `univ` makes the subsum proper. -/
def HasVanishingProperSubsum (u : TermIndex → R) : Prop :=
  ∃ support : Finset TermIndex,
    support.Nonempty ∧ support ≠ Finset.univ ∧
      ∑ i ∈ support, u i = 0

/-- A zero-sum tuple is nondegenerate precisely when no proper nonempty
subsum vanishes. -/
def IsNondegenerateZeroSum (u : TermIndex → R) : Prop :=
  (∑ i, u i) = 0 ∧ ¬HasVanishingProperSubsum u

/-- A proper decomposition of the full identity into two nonempty exact
zero-sum identities.  This is the compositional-factor output relevant to a
macro grammar, rather than merely a Boolean degeneracy flag. -/
def HasProperZeroSumPartition (u : TermIndex → R) : Prop :=
  ∃ support : Finset TermIndex,
    support.Nonempty ∧ supportᶜ.Nonempty ∧
      (∑ i ∈ support, u i) = 0 ∧
      (∑ i ∈ supportᶜ, u i) = 0

/-- For a zero-sum tuple, a vanishing proper subsum really does split the
whole relation into two nonempty zero-sum factors. -/
theorem hasProperZeroSumPartition_of_vanishingProperSubsum
    (u : TermIndex → R) (hzero : (∑ i, u i) = 0)
    (hsplit : HasVanishingProperSubsum u) :
    HasProperZeroSumPartition u := by
  rcases hsplit with ⟨support, hsupportNonempty, hsupportProper, hsupportSum⟩
  have hcomplNonempty : supportᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.compl_eq_empty_iff]
    exact hsupportProper
  have hparts := Finset.sum_add_sum_compl support u
  rw [hsupportSum, hzero] at hparts
  refine ⟨support, hsupportNonempty, hcomplNonempty, hsupportSum, ?_⟩
  simpa using hparts

/-- The exact interface supplied by a fixed-`S` unit-equation theorem:
among admissible nondegenerate zero-sum tuples, only finitely many chosen
projective normal forms occur.

`admissible` is where a caller records that every term is, for example, a
signed `2`-`3` unit.  `normalize` records removal of the common projective
scale. -/
def NondegenerateNormalFormsFinite
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm) : Prop :=
  Set.Finite {p | ∃ u, admissible u ∧
    IsNondegenerateZeroSum u ∧ normalize u = p}

omit [DecidableEq TermIndex] in
/-- If every member of a family is admissible, zero-sum, and nondegenerate,
then its projective normal forms have finite range. -/
theorem finite_normalForm_range_of_non_degenerate
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm)
    (family : Parameter → (TermIndex → R))
    (hfinite : NondegenerateNormalFormsFinite admissible normalize)
    (hadmissible : ∀ n, admissible (family n))
    (hzero : ∀ n, (∑ i, family n i) = 0)
    (hnondegenerate : ∀ n, ¬HasVanishingProperSubsum (family n)) :
    Set.Finite (Set.range fun n ↦ normalize (family n)) := by
  apply hfinite.subset
  rintro p ⟨n, rfl⟩
  exact ⟨family n, hadmissible n, ⟨hzero n, hnondegenerate n⟩, rfl⟩

omit [DecidableEq TermIndex] in
/-- The basic fixed-syntax gate: infinitely many normalized shapes force at
least one exact compositional split. -/
theorem exists_vanishingProperSubsum_of_infinite_normalForms
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm)
    (family : Parameter → (TermIndex → R))
    (hfinite : NondegenerateNormalFormsFinite admissible normalize)
    (hadmissible : ∀ n, admissible (family n))
    (hzero : ∀ n, (∑ i, family n i) = 0)
    (hinfinite : Set.Infinite (Set.range fun n ↦ normalize (family n))) :
    ∃ n, HasVanishingProperSubsum (family n) := by
  by_contra hnone
  push Not at hnone
  exact hinfinite (finite_normalForm_range_of_non_degenerate
    admissible normalize family hfinite hadmissible hzero hnone)

omit [DecidableEq TermIndex] in
/-- Strong form: the exceptional split cannot occur only at finitely many
parameters.  Otherwise their finite image, together with the finite set of
nondegenerate normal forms, would make the whole normalized family finite. -/
theorem infinite_vanishingProperSubsum_indices
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm)
    (family : Parameter → (TermIndex → R))
    (hfinite : NondegenerateNormalFormsFinite admissible normalize)
    (hadmissible : ∀ n, admissible (family n))
    (hzero : ∀ n, (∑ i, family n i) = 0)
    (hinfinite : Set.Infinite (Set.range fun n ↦ normalize (family n))) :
    Set.Infinite {n | HasVanishingProperSubsum (family n)} := by
  intro hsplitFinite
  let split : Set Parameter := {n | HasVanishingProperSubsum (family n)}
  let allowed : Set NormalForm := {p | ∃ u, admissible u ∧
    IsNondegenerateZeroSum u ∧ normalize u = p}
  have hallowedFinite : allowed.Finite := hfinite
  have hsplitImageFinite :
      (normalize ∘ family '' split).Finite := hsplitFinite.image _
  have hrangeSubset :
      Set.range (fun n ↦ normalize (family n)) ⊆
        allowed ∪ (normalize ∘ family '' split) := by
    rintro p ⟨n, rfl⟩
    by_cases hn : HasVanishingProperSubsum (family n)
    · exact Or.inr ⟨n, hn, rfl⟩
    · exact Or.inl ⟨family n, hadmissible n, ⟨hzero n, hn⟩, rfl⟩
  exact hinfinite ((hallowedFinite.union hsplitImageFinite).subset hrangeSubset)

/-- The architecture-facing form: infinitely many parameters admit an exact
partition into two nonempty zero-sum identities. -/
theorem infinite_properZeroSumPartition_indices
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm)
    (family : Parameter → (TermIndex → R))
    (hfinite : NondegenerateNormalFormsFinite admissible normalize)
    (hadmissible : ∀ n, admissible (family n))
    (hzero : ∀ n, (∑ i, family n i) = 0)
    (hinfinite : Set.Infinite (Set.range fun n ↦ normalize (family n))) :
    Set.Infinite {n | HasProperZeroSumPartition (family n)} := by
  apply (infinite_vanishingProperSubsum_indices
    admissible normalize family hfinite hadmissible hzero hinfinite).mono
  intro n hn
  exact hasProperZeroSumPartition_of_vanishingProperSubsum
    (family n) (hzero n) hn

omit [DecidableEq TermIndex] in
/-- Convenient contradiction form for a genuinely unbounded parameter: a
projectively injective fixed-shape family cannot remain nondegenerate. -/
theorem no_injective_non_degenerate_family
    [Infinite Parameter]
    (admissible : (TermIndex → R) → Prop)
    (normalize : (TermIndex → R) → NormalForm)
    (family : Parameter → (TermIndex → R))
    (hfinite : NondegenerateNormalFormsFinite admissible normalize)
    (hadmissible : ∀ n, admissible (family n))
    (hzero : ∀ n, (∑ i, family n i) = 0)
    (hinjective : Function.Injective (fun n ↦ normalize (family n))) :
    ¬∀ n, ¬HasVanishingProperSubsum (family n) := by
  intro hnondegenerate
  have hinfinite :
      Set.Infinite (Set.range fun n ↦ normalize (family n)) :=
    Set.infinite_range_of_injective hinjective
  exact hinfinite (finite_normalForm_range_of_non_degenerate
    admissible normalize family hfinite hadmissible hzero hnondegenerate)

end OutwardSUnitSyntaxGate
end KontoroC
