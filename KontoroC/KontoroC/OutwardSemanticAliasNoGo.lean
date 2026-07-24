/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardStaircaseAddressNoGo

/-!
# Literal uniqueness for first-passage macro presentations

Symbolic phase/carry records may have redundant presentations, but two
positive literal first-passage macros with the same boundary source and target
cannot have different block lists.  Determinism makes their flattened parity
words prefix-comparable, prefix-free decoding aligns block boundaries, and an
extra nonempty suffix would strictly raise the boundary charge.

Thus an alias quotient is sound only after every claimed alias is proved to
decode to the same literal macro.  Tied but distinct executable choices must
not be averaged or silently identified.
-/

namespace KontoroC
namespace OutwardSemanticAliasNoGo

open ShortcutParityPeriodicNoGo PrefixKraft OutwardFirstPassage
  OutwardCodeCompactness OutwardFiniteHeight OutwardInvariantBridge
  OutwardOddSlice OutwardCylinderRenewal

/-- Prefix reflection for lists of first-passage blocks: if the flattened
parity stream of one block list is a prefix of another, then the block list
itself is a prefix. -/
theorem wordsIn_prefix_of_flatten_prefix
    {left right : List (List Bool)}
    (hleft : WordsIn FirstPassageCode left)
    (hright : WordsIn FirstPassageCode right)
    (hprefix : flattenWords left <+: flattenWords right) :
    left <+: right := by
  induction left generalizing right with
  | nil => simp
  | cons u us ih =>
      cases right with
      | nil =>
          have huFirst : FirstPassage u := hleft u (by simp)
          have huNonempty : u ≠ [] := firstPassage_ne_nil huFirst
          have hlen := hprefix.length_le
          simp only [flattenWords, List.length_append, List.length_nil] at hlen
          have huPos : 0 < u.length := List.length_pos_iff.mpr huNonempty
          omega
      | cons v vs =>
          have huFirst : FirstPassage u := hleft u (by simp)
          have hvFirst : FirstPassage v := hright v (by simp)
          have huPrefix : u <+: flattenWords (v :: vs) := by
            exact (List.prefix_append u (flattenWords us)).trans hprefix
          have hvPrefix : v <+: flattenWords (v :: vs) := by
            exact List.prefix_append v (flattenWords vs)
          have huv : u = v := by
            rcases comparable_of_common_prefix huPrefix hvPrefix with huv | hvu
            · exact prefixFree huFirst hvFirst huv
            · exact (prefixFree hvFirst huFirst hvu).symm
          subst v
          have hus : WordsIn FirstPassageCode us := by
            intro w hw
            exact hleft w (by simp [hw])
          have hvs : WordsIn FirstPassageCode vs := by
            intro w hw
            exact hright w (by simp [hw])
          rcases hprefix with ⟨tail, htail⟩
          have hcancel :
              flattenWords us ++ tail = flattenWords vs := by
            exact List.append_cancel_left
              (by simpa only [flattenWords, List.append_assoc] using htail)
          have htailPrefix : flattenWords us <+: flattenWords vs :=
            ⟨tail, hcancel⟩
          exact List.prefix_cons_inj u |>.mpr (ih hus hvs htailPrefix)

/-- A prefix between two recharge presentations with the same endpoints
cannot be proper: any remaining block suffix would be a positive nonempty
recharge from `H'` back to itself. -/
theorem RechargeMacro.words_eq_of_prefix
    {H H' : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H H' left)
    (hright : RechargeMacro H H' right)
    (hprefix : left <+: right) :
    left = right := by
  rcases hprefix with ⟨suffix, hsuffix⟩
  by_cases hsuffixNil : suffix = []
  · subst suffix
    simpa using hsuffix
  · have hrightExec :
        ExecutesBlocksTo (left ++ suffix) (3 * H - 1) (3 * H' - 1) := by
      simpa [hsuffix] using hright.executesTo
    obtain ⟨middle, hleftExec, hsuffixExec⟩ :=
      (executesBlocksTo_append left suffix).mp hrightExec
    have hmiddle : middle = 3 * H' - 1 := by
      exact executes_target_unique (flattenWords left)
        (executesBlocksTo_iff_flatten.mp hleftExec)
        (executesBlocksTo_iff_flatten.mp hleft.executesTo)
    subst middle
    have hsuffixWords : WordsIn FirstPassageCode suffix := by
      intro w hw
      apply hright.wordsIn w
      rw [← hsuffix]
      exact List.mem_append_right left hw
    have hloop : RechargeMacro H' H' suffix :=
      ⟨hleft.target_pos, hleft.target_pos, hsuffixNil,
        hsuffixWords, hsuffixExec⟩
    exfalso
    exact (Nat.lt_irrefl H') hloop.lt

/-- Main alias no-go: the literal first-passage block presentation between
fixed positive boundary endpoints is unique. -/
theorem RechargeMacro.words_unique
    {H H' : ℕ} {left right : List (List Bool)}
    (hleft : RechargeMacro H H' left)
    (hright : RechargeMacro H H' right) :
    left = right := by
  have hflatLeft := executesBlocksTo_iff_flatten.mp hleft.executesTo
  have hflatRight := executesBlocksTo_iff_flatten.mp hright.executesTo
  rcases executes_common_source_comparable hflatLeft hflatRight with
      hprefix | hprefix
  · exact RechargeMacro.words_eq_of_prefix hleft hright
      (wordsIn_prefix_of_flatten_prefix
        hleft.wordsIn hright.wordsIn hprefix)
  · exact (RechargeMacro.words_eq_of_prefix hright hleft
      (wordsIn_prefix_of_flatten_prefix
        hright.wordsIn hleft.wordsIn hprefix)).symm

/-- A claimed pair of distinct literal aliases is therefore an immediate
contradiction certificate. -/
theorem no_distinct_RechargeMacro_aliases
    {H H' : ℕ} {left right : List (List Bool)}
    (hne : left ≠ right) :
    ¬(RechargeMacro H H' left ∧ RechargeMacro H H' right) := by
  rintro ⟨hleft, hright⟩
  exact hne (RechargeMacro.words_unique hleft hright)

end OutwardSemanticAliasNoGo
end KontoroC
