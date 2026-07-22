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

/-- Total number of ternary digit symbols. -/
def ternaryCount (w : Word) : ℕ :=
  w.count tri0 + w.count tri1 + w.count tri2

/-- Away from the left delimiter, no rule decreases the number of ternary
symbols.  The B-rules are the only decreasing cases, and they require `/`. -/
theorem step_ternaryCount_mono {u v : Word} (h : Step u v)
    (hslash : u.count slash = 0) : ternaryCount u ≤ ternaryCount v := by
  cases h with
  | context left right rule =>
      cases rule <;>
        simp_all [ternaryCount, List.count_append] <;> omega

theorem transGen_ternaryCount_mono {u v : Word}
    (h : Relation.TransGen Step u v) (hslash : u.count slash = 0) :
    ternaryCount u ≤ ternaryCount v := by
  induction h with
  | single huv => exact step_ternaryCount_mono huv hslash
  | tail hab hbc ih =>
      exact Nat.le_trans ih (step_ternaryCount_mono hbc (by
        rw [← transGen_slash_count hab]
        exact hslash))

/-- If a slash-free step has zero ternary symbols on both sides, it preserves
the number of binary-one symbols.  This excludes A-rules and `dt1`; only
terminal binary-zero deletion can remain. -/
theorem step_bin1_count_eq_of_ternary_zero {u v : Word} (h : Step u v)
    (hslash : u.count slash = 0)
    (hu0 : ternaryCount u = 0) (hv0 : ternaryCount v = 0) :
    u.count bin1 = v.count bin1 := by
  cases h with
  | context left right rule =>
      cases rule <;>
        simp_all [ternaryCount, List.count_append] <;> omega

theorem transGen_bin1_count_eq_of_ternary_zero {u v : Word}
    (h : Relation.TransGen Step u v)
    (hslash : u.count slash = 0)
    (hu0 : ternaryCount u = 0) (hv0 : ternaryCount v = 0) :
    u.count bin1 = v.count bin1 := by
  induction h with
  | single huv =>
      exact step_bin1_count_eq_of_ternary_zero huv hslash hu0 hv0
  | tail hab hbc ih =>
      rename_i b c
      have hb0 : ternaryCount b = 0 := by
        have hmono := step_ternaryCount_mono hbc (by
          rw [← transGen_slash_count hab]
          exact hslash)
        omega
      exact (ih hb0).trans
        (step_bin1_count_eq_of_ternary_zero hbc (by
          rw [← transGen_slash_count hab]
          exact hslash) hb0 hv0)

/-- The five symbols allowed inside a uniform digit block. -/
def IsDigit : Symbol → Prop
  | bin0 | bin1 | tri0 | tri1 | tri2 => True
  | slash | dot => False

def DigitOnly (w : Word) : Prop := ∀ x ∈ w, IsDigit x

/-- A canonical mixed-base word has exactly the displayed outer delimiters
and only digit symbols in between. -/
def Canonical (w : Word) : Prop :=
  ∃ digits, DigitOnly digits ∧ w = [slash] ++ digits ++ [dot]

theorem canonical_slash_mem {w : Word} (hw : Canonical w) : slash ∈ w := by
  obtain ⟨digits, _, rfl⟩ := hw
  simp

theorem canonical_dot_mem {w : Word} (hw : Canonical w) : dot ∈ w := by
  obtain ⟨digits, _, rfl⟩ := hw
  simp

theorem canonical_first_slash_offset {w : Word} (hw : Canonical w) :
    YahBoundaryNoGo.firstMarkerOffset slash w = 0 := by
  obtain ⟨digits, _, rfl⟩ := hw
  simp [YahBoundaryNoGo.firstMarkerOffset]

theorem canonical_last_dot_suffix {w : Word} (hw : Canonical w) :
    YahBoundaryNoGo.lastMarkerSuffix dot w = 0 := by
  obtain ⟨digits, _, rfl⟩ := hw
  simp [YahBoundaryNoGo.lastMarkerSuffix,
    YahBoundaryNoGo.firstMarkerOffset]

theorem digitOnly_slash_count (w : Word) (hw : DigitOnly w) :
    w.count slash = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  have := hw slash hmem
  simp [IsDigit] at this

theorem digitOnly_dot_count (w : Word) (hw : DigitOnly w) :
    w.count dot = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  have := hw dot hmem
  simp [IsDigit] at this

theorem digitOnly_eq_bin0_of_counts_zero (w : Word) (hw : DigitOnly w)
    (hternary : ternaryCount w = 0) (hbin1 : w.count bin1 = 0) :
    w = List.replicate w.length bin0 := by
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  intro x hx
  have hdigit := hw x hx
  have hnotBin1 : x ≠ bin1 := by
    intro hx1
    subst x
    exact (List.count_eq_zero.mp hbin1) hx
  have htri0 : w.count tri0 = 0 := by
    unfold ternaryCount at hternary
    omega
  have htri1 : w.count tri1 = 0 := by
    unfold ternaryCount at hternary
    omega
  have htri2 : w.count tri2 = 0 := by
    unfold ternaryCount at hternary
    omega
  have hnotTri0 : x ≠ tri0 := by
    intro hx0
    subst x
    exact (List.count_eq_zero.mp htri0) hx
  have hnotTri1 : x ≠ tri1 := by
    intro hx1
    subst x
    exact (List.count_eq_zero.mp htri1) hx
  have hnotTri2 : x ≠ tri2 := by
    intro hx2
    subst x
    exact (List.count_eq_zero.mp htri2) hx
  cases x <;> simp_all [IsDigit]

/-- A digit block which rewrites, immediately before the right delimiter, all
the way to that delimiter is forced to be an all-binary-zero block.  This is
the discrete invariant behind the first uniform-morphism obstruction: no
rational slope calculation is needed. -/
theorem digit_word_reducing_to_dot_all_bin0 (digits : Word)
    (hdigits : DigitOnly digits)
    (h : Relation.TransGen Step (digits ++ [dot]) [dot]) :
    digits = List.replicate digits.length bin0 := by
  have hslash : (digits ++ [dot]).count slash = 0 := by
    simp [digitOnly_slash_count digits hdigits]
  have hternarySource : ternaryCount (digits ++ [dot]) = 0 := by
    have hmono := transGen_ternaryCount_mono h hslash
    simp [ternaryCount] at hmono ⊢
    exact hmono
  have hbin1Source : (digits ++ [dot]).count bin1 = 0 := by
    exact transGen_bin1_count_eq_of_ternary_zero h hslash
      hternarySource (by simp [ternaryCount])
  apply digitOnly_eq_bin0_of_counts_zero digits hdigits
  · simpa [ternaryCount, List.count_append] using hternarySource
  · simpa [List.count_append] using hbin1Source

/-- The mixed-base affine action used by the canonical YAH words.  The slash
resets the accumulator to one; the right delimiter is semantically inert. -/
def symbolAction : Symbol → ℕ → ℕ
  | bin0 => fun x => 2 * x
  | bin1 => fun x => 2 * x + 1
  | tri0 => fun x => 3 * x
  | tri1 => fun x => 3 * x + 1
  | tri2 => fun x => 3 * x + 2
  | slash => fun _ => 1
  | dot => fun x => x

def mixedEvalFrom (x : ℕ) (w : Word) : ℕ :=
  w.foldl (fun acc s => symbolAction s acc) x

def mixedEval (w : Word) : ℕ := mixedEvalFrom 1 w

/-- A- and B-rules preserve the represented integer.  With no dot in the
source, the dynamic terminal rules are unavailable, so every literal step
preserves `mixedEval`. -/
theorem step_mixedEval_eq_of_dot_free {u v : Word} (h : Step u v)
    (hdot : u.count dot = 0) : mixedEval u = mixedEval v := by
  cases h with
  | context left right rule =>
      cases rule <;>
        simp_all [mixedEval, mixedEvalFrom, symbolAction,
          List.foldl_append, List.count_append] <;>
        congr 1 <;> omega

theorem transGen_mixedEval_eq_of_dot_free {u v : Word}
    (h : Relation.TransGen Step u v) (hdot : u.count dot = 0) :
    mixedEval u = mixedEval v := by
  induction h with
  | single huv => exact step_mixedEval_eq_of_dot_free huv hdot
  | tail hab hbc ih =>
      exact ih.trans (step_mixedEval_eq_of_dot_free hbc (by
        rw [← transGen_dot_count hab]
        exact hdot))

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

/-- A stronger whole-word filter for the usual worker output: if both the
seed and claimed endpoint are canonical `/digits.` words, no separately
reported flank diagnostics are needed. -/
theorem context_eq_cycle_of_canonical_endpoints
    (start endpoint left right : Word)
    (h : Relation.TransGen Step start endpoint)
    (hstart : Canonical start) (hendpointCanonical : Canonical endpoint)
    (hendpoint : endpoint = left ++ start ++ right) :
    left = [] ∧ right = [] := by
  apply context_eq_cycle_of_flank_invariants start endpoint left right h
    (canonical_slash_mem hstart) (canonical_dot_mem hstart) hendpoint
  · rw [canonical_first_slash_offset hendpointCanonical,
      canonical_first_slash_offset hstart]
  · rw [canonical_last_dot_suffix hendpointCanonical,
      canonical_last_dot_suffix hstart]

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
