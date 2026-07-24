/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSemanticAliasNoGo
import KontoroC.OutwardDirectedPathExpansion

/-!
# Literal recharge cones are chains

The outward shortcut map is deterministic. Consequently two literal
first-passage recharge macros beginning at the same ordinary charge cannot
represent independent branches: their flattened parity words are comparable,
and prefix-free decoding upgrades this to comparability of their lists of
first-passage blocks.

More strongly, the block-prefix order is exactly the numerical order of the
boundary charges. If one target is smaller than the other, the unused suffix
is itself a literal positive recharge macro between the two targets.

This is an architecture audit for finite expansion and tree searches. A
graph may retain several transitive jumps from one charge, but those targets
all lie on one forced literal execution. Genuine branching can only occur in
an enlarged symbolic state space, and then every selected branch still needs
an independent literal ordinary-charge interpretation.
-/

namespace KontoroC
namespace OutwardRechargeChain

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardFiniteHeight OutwardInvariantBridge OutwardSemanticAliasNoGo
  OutwardDirectedPathExpansion OutwardCylinderRenewal OutwardOddSlice

/-- Two literal recharge block lists from one boundary source are comparable
in prefix order. -/
theorem RechargeMacro.words_comparable_of_common_source
    {H K L : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H K left)
    (hright : RechargeMacro H L right) :
    left <+: right ∨ right <+: left := by
  have hflatLeft := executesBlocksTo_iff_flatten.mp hleft.executesTo
  have hflatRight := executesBlocksTo_iff_flatten.mp hright.executesTo
  rcases executes_common_source_comparable hflatLeft hflatRight with
      hprefix | hprefix
  · exact Or.inl (wordsIn_prefix_of_flatten_prefix
      hleft.wordsIn hright.wordsIn hprefix)
  · exact Or.inr (wordsIn_prefix_of_flatten_prefix
      hright.wordsIn hleft.wordsIn hprefix)

/-- If one common-source presentation is a block prefix of another, then it
is either the same macro or the remaining nonempty block suffix is itself a
literal recharge between the two targets. -/
theorem RechargeMacro.eq_or_suffix_recharge_of_words_prefix
    {H K L : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H K left)
    (hright : RechargeMacro H L right)
    (hprefix : left <+: right) :
    (K = L ∧ left = right) ∨
      ∃ suffix, suffix ≠ [] ∧ left ++ suffix = right ∧
        RechargeMacro K L suffix := by
  rcases hprefix with ⟨suffix, hsuffix⟩
  by_cases hsuffixNil : suffix = []
  · subst suffix
    have hwords : left = right := by simpa using hsuffix
    have hend : 3 * K - 1 = 3 * L - 1 :=
      executes_target_unique (flattenWords left)
        (executesBlocksTo_iff_flatten.mp hleft.executesTo)
        (by simpa [hwords] using
          (executesBlocksTo_iff_flatten.mp hright.executesTo))
    exact Or.inl ⟨by omega, hwords⟩
  · have hrightExec :
        ExecutesBlocksTo (left ++ suffix) (3 * H - 1) (3 * L - 1) := by
      simpa [hsuffix] using hright.executesTo
    obtain ⟨middle, hleftExec, hsuffixExec⟩ :=
      (executesBlocksTo_append left suffix).mp hrightExec
    have hmiddle : middle = 3 * K - 1 :=
      executes_target_unique (flattenWords left)
        (executesBlocksTo_iff_flatten.mp hleftExec)
        (executesBlocksTo_iff_flatten.mp hleft.executesTo)
    subst middle
    have hsuffixWords : WordsIn FirstPassageCode suffix := by
      intro word hword
      apply hright.wordsIn word
      rw [← hsuffix]
      exact List.mem_append_right left hword
    exact Or.inr ⟨suffix, hsuffixNil, hsuffix,
      ⟨hleft.target_pos, hright.target_pos, hsuffixNil,
        hsuffixWords, hsuffixExec⟩⟩

/-- For two literal macros from a common source, block-prefix order is
exactly numerical order of the target boundary charges. -/
theorem RechargeMacro.words_prefix_iff_target_le
    {H K L : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H K left)
    (hright : RechargeMacro H L right) :
    left <+: right ↔ K ≤ L := by
  constructor
  · intro hprefix
    rcases RechargeMacro.eq_or_suffix_recharge_of_words_prefix
        hleft hright hprefix with
        ⟨hKL, _⟩ | ⟨suffix, _, _, hsuffix⟩
    · exact hKL.le
    · exact hsuffix.lt.le
  · intro hKL
    rcases RechargeMacro.words_comparable_of_common_source hleft hright with
        hprefix | hprefix
    · exact hprefix
    · rcases RechargeMacro.eq_or_suffix_recharge_of_words_prefix
          hright hleft hprefix with
          ⟨hLK, hwords⟩ | ⟨suffix, _, _, hsuffix⟩
      · simp [hwords.symm]
      · exact (not_lt_of_ge hKL hsuffix.lt).elim

/-- Strict target order exposes a nonempty literal suffix recharge between
the two targets. -/
theorem RechargeMacro.exists_suffix_recharge_of_target_lt
    {H K L : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H K left)
    (hright : RechargeMacro H L right)
    (hKL : K < L) :
    ∃ suffix, suffix ≠ [] ∧ left ++ suffix = right ∧
      RechargeMacro K L suffix := by
  have hprefix : left <+: right :=
    (RechargeMacro.words_prefix_iff_target_le hleft hright).mpr hKL.le
  rcases RechargeMacro.eq_or_suffix_recharge_of_words_prefix
      hleft hright hprefix with
      ⟨hEq, _⟩ | hsuffix
  · exact (Nat.ne_of_lt hKL hEq).elim
  · exact hsuffix

/-- Any two literal recharge targets from a common source are joined in the
appropriate direction by another literal recharge edge. -/
theorem RechargeEdge.eq_or_between_of_common_source
    {H K L : ℕ} (hHK : RechargeEdge H K) (hHL : RechargeEdge H L) :
    K = L ∨ RechargeEdge K L ∨ RechargeEdge L K := by
  obtain ⟨left, hleft⟩ := hHK
  obtain ⟨right, hright⟩ := hHL
  rcases lt_trichotomy K L with hKL | hEq | hLK
  · obtain ⟨suffix, _, _, hsuffix⟩ :=
      RechargeMacro.exists_suffix_recharge_of_target_lt hleft hright hKL
    exact Or.inr (Or.inl ⟨suffix, hsuffix⟩)
  · exact Or.inl hEq
  · obtain ⟨suffix, _, _, hsuffix⟩ :=
      RechargeMacro.exists_suffix_recharge_of_target_lt hright hleft hLK
    exact Or.inr (Or.inr ⟨suffix, hsuffix⟩)

/-- Strictly ordered common-source targets are related in the same direction.
This is the concise chain property used to audit purported branching. -/
theorem RechargeEdge.between_of_common_source_of_lt
    {H K L : ℕ} (hHK : RechargeEdge H K) (hHL : RechargeEdge H L)
    (hKL : K < L) : RechargeEdge K L := by
  rcases RechargeEdge.eq_or_between_of_common_source hHK hHL with
      hEq | hforward | hbackward
  · exact (Nat.ne_of_lt hKL hEq).elim
  · exact hforward
  · exact (not_lt_of_ge hKL.le hbackward.lt).elim

/-- Worker-facing pruning rule: two accepted literal children which are
incomparable by further literal recharge cannot be distinct children. -/
theorem RechargeEdge.target_eq_of_no_cross_edges
    {H K L : ℕ} (hHK : RechargeEdge H K) (hHL : RechargeEdge H L)
    (hnotKL : ¬RechargeEdge K L) (hnotLK : ¬RechargeEdge L K) :
    K = L := by
  rcases RechargeEdge.eq_or_between_of_common_source hHK hHL with
      hEq | hforward | hbackward
  · exact hEq
  · exact (hnotKL hforward).elim
  · exact (hnotLK hbackward).elim

/-- A finite family of pairwise recharge-incomparable literal descendants
of one ordinary charge has width at most one. -/
theorem commonSource_incomparableTargets_card_le_one
    (H : ℕ) (targets : Finset ℕ)
    (hroot : ∀ K ∈ targets, RechargeEdge H K)
    (hincomparable : ∀ K ∈ targets, ∀ L ∈ targets, K ≠ L →
      ¬RechargeEdge K L ∧ ¬RechargeEdge L K) :
    targets.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro K L hK hL
  by_contra hne
  obtain ⟨hnotKL, hnotLK⟩ :=
    hincomparable K hK L hL hne
  exact hne (RechargeEdge.target_eq_of_no_cross_edges
    (hroot K hK) (hroot L hL) hnotKL hnotLK)

end OutwardRechargeChain
end KontoroC
