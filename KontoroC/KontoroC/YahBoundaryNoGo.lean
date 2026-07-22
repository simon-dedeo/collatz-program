/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Data.List.Count

/-!
# Boundary obstruction to whole-word context loops

The mixed-base YAH words have two distinguished boundary markers, `/` and
`.`.  A whole-word context embedding can only be proper if it moves at least
one marker away from its original outer flank.  This file packages that fact
without trusting a search program: preservation of the left flank of `/` and
the right flank of `.` forces both advertised outer contexts to be empty.

The theorem is generic.  A YAH replay checker only needs to establish marker
count and the two flank invariants for its concrete rewrite relation.
-/

namespace KontoroC
namespace YahBoundaryNoGo

/-- Number of symbols preceding the first occurrence of `marker`; it is the
word length when the marker is absent. -/
def firstMarkerOffset {α : Type*} [DecidableEq α] (marker : α) : List α → ℕ
  | [] => 0
  | x :: xs => if x = marker then 0 else firstMarkerOffset marker xs + 1

theorem firstMarkerOffset_append_of_not_mem {α : Type*} [DecidableEq α]
    (marker : α) (left right : List α) (hleft : marker ∉ left) :
    firstMarkerOffset marker (left ++ right) =
      left.length + firstMarkerOffset marker right := by
  induction left with
  | nil => simp [firstMarkerOffset]
  | cons x xs ih =>
      have hx : x ≠ marker := by
        intro h
        subst x
        exact hleft (by simp)
      have hxs : marker ∉ xs := by
        intro hm
        exact hleft (by simp [hm])
      simp [firstMarkerOffset, hx, ih hxs, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem firstMarkerOffset_append_of_mem {α : Type*} [DecidableEq α]
    (marker : α) (left right : List α) (hleft : marker ∈ left) :
    firstMarkerOffset marker (left ++ right) =
      firstMarkerOffset marker left := by
  induction left with
  | nil => simp at hleft
  | cons x xs ih =>
      by_cases hx : x = marker
      · simp [firstMarkerOffset, hx]
      · have hxs : marker ∈ xs := by
          have hmx : marker ≠ x := Ne.symm hx
          simpa [hmx] using hleft
        simp [firstMarkerOffset, hx, ih hxs]

/-- Number of symbols following the last occurrence of `marker`. -/
def lastMarkerSuffix {α : Type*} [DecidableEq α] (marker : α)
    (word : List α) : ℕ :=
  firstMarkerOffset marker word.reverse

theorem lastMarkerSuffix_context {α : Type*} [DecidableEq α]
    (marker : α) (left core right : List α)
    (hcore : marker ∈ core) (hright : marker ∉ right) :
    lastMarkerSuffix marker (left ++ core ++ right) =
      right.length + lastMarkerSuffix marker core := by
  simp only [lastMarkerSuffix, List.reverse_append, List.length_reverse]
  rw [firstMarkerOffset_append_of_not_mem marker right.reverse
      (core.reverse ++ left.reverse) (by simpa using hright)]
  rw [firstMarkerOffset_append_of_mem marker core.reverse left.reverse
      (by simpa using hcore)]
  simp

/-- If `endpoint = left ++ start ++ right`, neither boundary marker occurs in
the added contexts, and the two outer flank lengths are unchanged, then the
embedding is not proper: both contexts are empty. -/
theorem contexts_empty_of_boundary_invariants
    {α : Type*} [DecidableEq α]
    (slash dot : α) (start endpoint left right : List α)
    (hslash : slash ∈ start) (hdot : dot ∈ start)
    (hslashLeft : slash ∉ left) (hdotRight : dot ∉ right)
    (hendpoint : endpoint = left ++ start ++ right)
    (hleftInvariant : firstMarkerOffset slash endpoint =
      firstMarkerOffset slash start)
    (hrightInvariant : lastMarkerSuffix dot endpoint =
      lastMarkerSuffix dot start) :
    left = [] ∧ right = [] := by
  have hleftLen : left.length = 0 := by
    rw [hendpoint, List.append_assoc,
      firstMarkerOffset_append_of_not_mem slash left (start ++ right)
        hslashLeft,
      firstMarkerOffset_append_of_mem slash start right hslash] at hleftInvariant
    omega
  have hrightLen : right.length = 0 := by
    rw [hendpoint, lastMarkerSuffix_context dot left start right hdot hdotRight]
      at hrightInvariant
    omega
  exact ⟨List.length_eq_zero_iff.mp hleftLen,
    List.length_eq_zero_iff.mp hrightLen⟩

/-- Marker counts in an embedding force the added contexts to contain no
copies of a marker whose total count is preserved. -/
theorem marker_not_mem_contexts_of_count_preserved
    {α : Type*} [DecidableEq α]
    (marker : α) (start endpoint left right : List α)
    (hendpoint : endpoint = left ++ start ++ right)
    (hcount : endpoint.count marker = start.count marker) :
    marker ∉ left ∧ marker ∉ right := by
  have hsum : left.count marker + start.count marker + right.count marker =
      start.count marker := by
    simpa [hendpoint, List.count_append, Nat.add_assoc] using hcount
  have hl : left.count marker = 0 := by omega
  have hr : right.count marker = 0 := by omega
  simpa [List.count_eq_zero] using And.intro hl hr

/-- Fully checkable boundary no-go.  Preserved marker counts supply the
marker-free contexts; preserved outer flank lengths then collapse a proposed
whole-word context loop to an ordinary cycle. -/
theorem no_proper_context_of_counts_and_flanks
    {α : Type*} [DecidableEq α]
    (slash dot : α) (start endpoint left right : List α)
    (hslash : slash ∈ start) (hdot : dot ∈ start)
    (hendpoint : endpoint = left ++ start ++ right)
    (hslashCount : endpoint.count slash = start.count slash)
    (hdotCount : endpoint.count dot = start.count dot)
    (hleftInvariant : firstMarkerOffset slash endpoint =
      firstMarkerOffset slash start)
    (hrightInvariant : lastMarkerSuffix dot endpoint =
      lastMarkerSuffix dot start) :
    left = [] ∧ right = [] := by
  have hs := marker_not_mem_contexts_of_count_preserved slash start endpoint
    left right hendpoint hslashCount
  have hd := marker_not_mem_contexts_of_count_preserved dot start endpoint
    left right hendpoint hdotCount
  exact contexts_empty_of_boundary_invariants slash dot start endpoint left right
    hslash hdot hs.1 hd.2 hendpoint hleftInvariant hrightInvariant

end YahBoundaryNoGo
end KontoroC
