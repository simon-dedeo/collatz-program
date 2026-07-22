/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahContextGlider
import KontoroC.YahBoundaryNoGo

/-!
# The eleven-rule Yolcu--Aaronson--Heule rewrite carrier

This is a small kernel-side carrier for certificates emitted by the Python
worker.  It pins the seven symbols and eleven oriented rules.  `Step` is the
usual contextual closure of one generating rule, and is proved context
closed.  The external theorem identifying termination of this system with
Collatz remains outside this file.
-/

namespace KontoroC
namespace YahRewriteSystem

inductive Symbol where
  | bin0 | bin1 | slash | dot | tri0 | tri1 | tri2
  deriving DecidableEq, Repr

abbrev Word := List Symbol

open Symbol

/-- The fixed eleven generating rules of YAH's system `T`. -/
inductive BasicRule : Word → Word → Prop
  | dt0 : BasicRule [bin0, dot] [dot]
  | dt1 : BasicRule [bin1, dot] [tri2, dot]
  | a00 : BasicRule [bin0, tri0] [tri0, bin0]
  | a01 : BasicRule [bin0, tri1] [tri0, bin1]
  | a02 : BasicRule [bin0, tri2] [tri1, bin0]
  | a10 : BasicRule [bin1, tri0] [tri1, bin1]
  | a11 : BasicRule [bin1, tri1] [tri2, bin0]
  | a12 : BasicRule [bin1, tri2] [tri2, bin1]
  | b0 : BasicRule [slash, tri0] [slash, bin1]
  | b1 : BasicRule [slash, tri1] [slash, bin0, bin0]
  | b2 : BasicRule [slash, tri2] [slash, bin0, bin1]

/-- One literal rule application at an arbitrary position. -/
inductive Step : Word → Word → Prop
  | context (left right : Word) {lhs rhs : Word} (rule : BasicRule lhs rhs) :
      Step (left ++ lhs ++ right) (left ++ rhs ++ right)

theorem contextClosed : YahContextGlider.ContextClosed Step := by
  intro outerLeft outerRight u v huv
  cases huv with
  | context left right rule =>
      have h := Step.context (outerLeft ++ left) (right ++ outerRight) rule
      simpa only [List.append_assoc] using h

theorem basicRule_slash_count {lhs rhs : Word} (h : BasicRule lhs rhs) :
    lhs.count slash = rhs.count slash := by
  cases h <;> decide

theorem basicRule_dot_count {lhs rhs : Word} (h : BasicRule lhs rhs) :
    lhs.count dot = rhs.count dot := by
  cases h <;> decide

theorem step_slash_count {u v : Word} (h : Step u v) :
    u.count slash = v.count slash := by
  cases h with
  | context left right rule =>
      simp only [List.count_append]
      rw [basicRule_slash_count rule]

theorem step_dot_count {u v : Word} (h : Step u v) :
    u.count dot = v.count dot := by
  cases h with
  | context left right rule =>
      simp only [List.count_append]
      rw [basicRule_dot_count rule]

theorem transGen_slash_count {u v : Word} (h : Relation.TransGen Step u v) :
    u.count slash = v.count slash := by
  induction h with
  | single huv => exact step_slash_count huv
  | tail hab hbc ih => exact ih.trans (step_slash_count hbc)

theorem transGen_dot_count {u v : Word} (h : Relation.TransGen Step u v) :
    u.count dot = v.count dot := by
  induction h with
  | single huv => exact step_dot_count huv
  | tail hab hbc ih => exact ih.trans (step_dot_count hbc)

/-- Concrete boundary filter for a replayed YAH derivation.  Delimiter-count
preservation is discharged from the pinned rules; a checker need only supply
the two exact flank equalities. -/
theorem context_eq_cycle_of_flank_invariants
    (start endpoint left right : Word)
    (h : Relation.TransGen Step start endpoint)
    (hslash : slash ∈ start) (hdot : dot ∈ start)
    (hendpoint : endpoint = left ++ start ++ right)
    (hleft : YahBoundaryNoGo.firstMarkerOffset slash endpoint =
      YahBoundaryNoGo.firstMarkerOffset slash start)
    (hright : YahBoundaryNoGo.lastMarkerSuffix dot endpoint =
      YahBoundaryNoGo.lastMarkerSuffix dot start) :
    left = [] ∧ right = [] := by
  exact YahBoundaryNoGo.no_proper_context_of_counts_and_flanks
    slash dot start endpoint left right hslash hdot hendpoint
    (transGen_slash_count h).symm (transGen_dot_count h).symm hleft hright

/-- A literal context-loop certificate over the pinned YAH rules produces
rewrite chunks at every scale. -/
def contextLoopGlider (u left right : Word)
    (h : Relation.TransGen Step u (left ++ u ++ right)) :
    YahContextGlider.ChunkedInfiniteDerivation Step :=
  YahContextGlider.of_context_loop contextClosed u left right h

/-- A morphic certificate over the pinned rules produces rewrite chunks at
every scale. -/
def morphicContextGlider (sigma : Symbol → Word)
    (hsim : YahContextGlider.RuleSimulation Step sigma)
    (u left right : Word)
    (h : Relation.TransGen Step u
      (left ++ YahContextGlider.wordMap sigma u ++ right)) :
    YahContextGlider.ChunkedInfiniteDerivation Step :=
  YahContextGlider.of_morphic_context_loop contextClosed sigma hsim
    u left right h

end YahRewriteSystem
end KontoroC
