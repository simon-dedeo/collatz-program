/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFeaturePolicyGap

/-!
# Exact singleton-support gate for stochastic selector kernels

A stationary or randomized finite transition kernel describes a literal
pointwise successor only when every row has singleton support.  For a
normalized rational row, singleton support forces its unique nonzero weight
to equal one, so the whole kernel is exactly a `0/1` deterministic graph.

This file provides the executable support table and the exact alternative:
either the kernel yields a successor function, or one concrete row has at
least two supported targets.  Stationarity, entropy bounds, or a Doob transform
cannot remove the latter ambiguity; choosing one supported target requires a
separate legal selector and compatibility proof.
-/

namespace KontoroC
namespace OutwardKernelDecoderGap

variable {State : Type*}
variable [Fintype State] [DecidableEq State]

/-- Exact nonzero support of one row of a rational transition kernel. -/
def support (kernel : State → State → ℚ) (source : State) : Finset State :=
  Finset.univ.filter fun target ↦ kernel source target ≠ 0

omit [DecidableEq State] in
@[simp] theorem mem_support_iff
    {kernel : State → State → ℚ} {source target : State} :
    target ∈ support kernel source ↔ kernel source target ≠ 0 := by
  simp [support]

/-- Every row has total rational mass one.  Nonnegativity may additionally be
checked by a stochastic worker, but normalization alone is enough for the
support/decoder theorem. -/
def RowNormalized (kernel : State → State → ℚ) : Prop :=
  ∀ source, ∑ target : State, kernel source target = 1

/-- The kernel itself is a pointwise decoder: every row is exactly the Dirac
mass at one selected successor. -/
def IsPointwiseKernel (kernel : State → State → ℚ) : Prop :=
  ∃ next : State → State,
    ∀ source target,
      kernel source target = if target = next source then 1 else 0

/-- A pointwise kernel has singleton support at its decoded successor. -/
theorem support_eq_singleton_of_pointwise
    {kernel : State → State → ℚ}
    (hpointwise : IsPointwiseKernel kernel) :
    ∃ next : State → State,
      ∀ source, support kernel source = {next source} := by
  obtain ⟨next, hnext⟩ := hpointwise
  refine ⟨next, fun source ↦ Finset.ext fun target ↦ ?_⟩
  simp [support, hnext source target]

/-- Conversely, a normalized kernel with specified singleton row supports is
exactly the corresponding pointwise `0/1` kernel. -/
theorem pointwise_of_normalized_support_singleton
    {kernel : State → State → ℚ}
    (hnormalized : RowNormalized kernel)
    (next : State → State)
    (hsupport : ∀ source, support kernel source = {next source}) :
    IsPointwiseKernel kernel := by
  refine ⟨next, fun source target ↦ ?_⟩
  by_cases htarget : target = next source
  · subst target
    have hsum := hnormalized source
    have hunique : ∀ other ∈ (Finset.univ : Finset State),
        other ≠ next source → kernel source other = 0 := by
      intro other _ hother
      by_contra hnonzero
      have hmem : other ∈ support kernel source :=
        mem_support_iff.mpr hnonzero
      rw [hsupport source] at hmem
      exact hother (Finset.mem_singleton.mp hmem)
    have hone : kernel source (next source) = 1 := by
      calc
        kernel source (next source) =
            ∑ other ∈ (Finset.univ : Finset State),
              kernel source other := by
                symm
                exact Finset.sum_eq_single (next source) hunique (by simp)
        _ = ∑ other : State, kernel source other := by rfl
        _ = 1 := hsum
    simp [hone]
  · have hzero : kernel source target = 0 := by
      by_contra hnonzero
      have hmem : target ∈ support kernel source :=
        mem_support_iff.mpr hnonzero
      rw [hsupport source] at hmem
      exact htarget (Finset.mem_singleton.mp hmem)
    simp [htarget, hzero]

/-- Exact criterion: for normalized finite rational kernels, literal
pointwise decoding is equivalent to singleton support in every row. -/
theorem pointwise_iff_support_card_eq_one
    {kernel : State → State → ℚ}
    (hnormalized : RowNormalized kernel) :
    IsPointwiseKernel kernel ↔
      ∀ source, (support kernel source).card = 1 := by
  constructor
  · intro hpointwise
    obtain ⟨next, hsupport⟩ :=
      support_eq_singleton_of_pointwise hpointwise
    intro source
    rw [hsupport source]
    simp
  · intro hcard
    choose next hnext using fun source ↦
      Finset.card_eq_one.mp (hcard source)
    exact pointwise_of_normalized_support_singleton
      hnormalized next hnext

omit [DecidableEq State] in
/-- Normalization prevents an empty support row. -/
theorem support_nonempty_of_normalized
    {kernel : State → State → ℚ}
    (hnormalized : RowNormalized kernel) (source : State) :
    (support kernel source).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzero : ∀ target : State, kernel source target = 0 := by
    intro target
    by_contra hnonzero
    have : target ∈ support kernel source :=
      mem_support_iff.mpr hnonzero
    rw [hempty] at this
    simp at this
  have hsum := hnormalized source
  simp [hzero] at hsum

/-- Exact finite alternative for a normalized kernel: either it is already a
literal pointwise decoder, or a concrete source row supports at least two
different possible successors. -/
theorem pointwise_or_exists_nondeterministic_row
    {kernel : State → State → ℚ}
    (hnormalized : RowNormalized kernel) :
    IsPointwiseKernel kernel ∨
      ∃ source, 1 < (support kernel source).card := by
  by_cases hpointwise : IsPointwiseKernel kernel
  · exact Or.inl hpointwise
  · right
    have hnotCard : ¬ ∀ source, (support kernel source).card = 1 := by
      intro hcard
      exact hpointwise
        ((pointwise_iff_support_card_eq_one hnormalized).mpr hcard)
    push Not at hnotCard
    obtain ⟨source, hcardNe⟩ := hnotCard
    have hpositive : 0 < (support kernel source).card :=
      Finset.card_pos.mpr (support_nonempty_of_normalized hnormalized source)
    exact ⟨source, by omega⟩

/-- Executable table of exactly those source rows with more than one
supported successor. -/
def nondeterministicRows (kernel : State → State → ℚ) : Finset State :=
  Finset.univ.filter fun source ↦ 1 < (support kernel source).card

omit [DecidableEq State] in
@[simp] theorem mem_nondeterministicRows_iff
    {kernel : State → State → ℚ} {source : State} :
    source ∈ nondeterministicRows kernel ↔
      1 < (support kernel source).card := by
  simp [nondeterministicRows]

/-- For a normalized rational kernel, empty checker output is exactly the
existence of a literal pointwise decoder represented by the kernel itself. -/
theorem nondeterministicRows_eq_empty_iff_pointwise
    {kernel : State → State → ℚ}
    (hnormalized : RowNormalized kernel) :
    nondeterministicRows kernel = ∅ ↔ IsPointwiseKernel kernel := by
  constructor
  · intro hempty
    rcases pointwise_or_exists_nondeterministic_row hnormalized with
      hpointwise | ⟨source, hsource⟩
    · exact hpointwise
    · have : source ∈ nondeterministicRows kernel :=
        mem_nondeterministicRows_iff.mpr hsource
      rw [hempty] at this
      simp at this
  · intro hpointwise
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨source, hsource⟩
    have hlarge := mem_nondeterministicRows_iff.mp hsource
    have hcard := (pointwise_iff_support_card_eq_one hnormalized).mp
      hpointwise source
    omega

/-- Two distinct supported targets in one row are an explicit obstruction to
interpreting the kernel itself as a pointwise decoder. -/
theorem supported_pair_obstructs_pointwise
    {kernel : State → State → ℚ} {source left right : State}
    (hleft : left ∈ support kernel source)
    (hright : right ∈ support kernel source)
    (hne : left ≠ right) :
    ¬ IsPointwiseKernel kernel := by
  intro hpointwise
  obtain ⟨next, hsupport⟩ :=
    support_eq_singleton_of_pointwise hpointwise
  have hleftEq : left = next source := by
    rw [hsupport source] at hleft
    exact Finset.mem_singleton.mp hleft
  have hrightEq : right = next source := by
    rw [hsupport source] at hright
    exact Finset.mem_singleton.mp hright
  exact hne (hleftEq.trans hrightEq.symm)

end OutwardKernelDecoderGap
end KontoroC
