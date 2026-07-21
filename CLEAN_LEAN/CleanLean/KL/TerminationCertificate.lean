/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Finite rank certificates for elimination-path termination

If a proposed finite control quotient for KL elimination is correct, its
termination can be certified by a natural-number rank that decreases on every
admissible continuation edge.  This file supplies the executable checker and
the generic path-length theorem.  It deliberately does not assert that the
ancestor-dependent KL deletion grammar has such a finite quotient; that is
the remaining mathematical construction.
-/

namespace CleanLean.KL

section TerminationCertificate

variable {Q E : Type} [Fintype E]

/-- The transition relation represented by a finite edge table. -/
def EdgeRelation (src tgt : E → Q) (q r : Q) : Prop :=
  ∃ e, src e = q ∧ tgt e = r

/-- Executable verification that a natural rank decreases on every edge. -/
def checkRankCertificate (src tgt : E → Q) (rank : Q → ℕ) : Bool :=
  decide (∀ e, rank (tgt e) < rank (src e))

theorem checkRankCertificate_eq_true_iff
    (src tgt : E → Q) (rank : Q → ℕ) :
    checkRankCertificate src tgt rank = true ↔
      ∀ e, rank (tgt e) < rank (src e) := by
  simp [checkRankCertificate]

/-- A successful finite check decreases rank on the induced relation. -/
theorem rank_decreases_of_check
    (src tgt : E → Q) (rank : Q → ℕ)
    (hcheck : checkRankCertificate src tgt rank = true) :
    ∀ q r, EdgeRelation src tgt q r → rank r < rank q := by
  have hedges := (checkRankCertificate_eq_true_iff src tgt rank).1 hcheck
  intro q r hqr
  obtain ⟨e, rfl, rfl⟩ := hqr
  exact hedges e

/-- A list follows a binary transition relation. -/
def IsRelationPath (R : Q → Q → Prop) : List Q → Prop
  | [] => True
  | [_] => True
  | q :: r :: rest => R q r ∧ IsRelationPath R (r :: rest)

/-- A strictly decreasing natural rank gives an explicit bound on every
finite path beginning at `q`: at most `rank q` edges. -/
theorem relationPath_length_le_rank_add_one
    (R : Q → Q → Prop) (rank : Q → ℕ)
    (hdecrease : ∀ q r, R q r → rank r < rank q)
    (q : Q) (rest : List Q) (hpath : IsRelationPath R (q :: rest)) :
    (q :: rest).length ≤ rank q + 1 := by
  induction rest generalizing q with
  | nil => simp
  | cons r rest ih =>
      have hstep : R q r := hpath.1
      have htail : IsRelationPath R (r :: rest) := hpath.2
      have hlength := ih r htail
      have hrank := hdecrease q r hstep
      simp only [List.length_cons] at hlength ⊢
      omega

/-- End-to-end form for a checked edge table. -/
theorem edgePath_length_le_of_check
    (src tgt : E → Q) (rank : Q → ℕ)
    (hcheck : checkRankCertificate src tgt rank = true)
    (q : Q) (rest : List Q)
    (hpath : IsRelationPath (EdgeRelation src tgt) (q :: rest)) :
    (q :: rest).length ≤ rank q + 1 := by
  exact relationPath_length_le_rank_add_one (EdgeRelation src tgt) rank
    (rank_decreases_of_check src tgt rank hcheck) q rest hpath

end TerminationCertificate

end CleanLean.KL
