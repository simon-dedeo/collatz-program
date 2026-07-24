/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeDriftCertificate
import KontoroC.OutwardWriterDecoderLiteral

/-!
# Positive symbolic cycle drift does not supply literal recharge semantics

This file gives a minimal exact countermodel to a tempting first-passage
inference.  A one-state, one-edge finite grammar can use a genuine
first-passage word, admit an infinite symbolic loop, and carry a strictly
positive rational Bellman drift certificate.  Nevertheless it cannot attach
one ordinary boundary charge to its state so that the loop edge becomes a
literal positive recharge: literal recharge is irreflexive.

Thus codeword validity, symbolic recurrence, and positive minimum-cycle drift
remain insufficient for a Collatz counterexample.  A construction must also
provide a coherent unbounded ordinary-charge lift and literal macro replay.
-/

namespace KontoroC
namespace OutwardPositiveCycleSemanticGap

open OutwardFiniteStateKraftGap OutwardFirstPassage
  OutwardResourceConeNoGo OutwardRechargeDriftCertificate
  OutwardWriterDecoderLiteral

/-- The smallest recurrent first-passage grammar: one state and one loop
edge, labelled by the genuine first-passage word `[true]`. -/
def unitLoopGrammar : FirstPassageGrammar Unit Unit where
  source := fun _ ↦ ()
  target := fun _ ↦ ()
  word := fun _ ↦ [true]
  firstPassage := fun _ ↦ singleton_true_firstPassage
  word_injective_on_source := by
    intro e f _ _
    cases e
    cases f
    rfl

/-- Its unique edge is a nonempty closed symbolic walk. -/
theorem unitLoopWalk :
    OutwardResourceConeNoGo.FirstPassageGrammar.EdgeWalk
      unitLoopGrammar () () [()] := by
  apply OutwardResourceConeNoGo.FirstPassageGrammar.EdgeWalk.cons () [] rfl
  exact OutwardResourceConeNoGo.FirstPassageGrammar.EdgeWalk.nil ()

/-- The constant score `1`, zero potential, and margin `1` satisfy the exact
Bellman inequality on the loop. -/
theorem unitLoop_bellman_margin_one :
    ∀ e : Unit,
      (1 : ℚ) ≤ (1 : ℚ) +
        (0 : Unit → ℚ) (unitLoopGrammar.target e) -
        (0 : Unit → ℚ) (unitLoopGrammar.source e) := by
  intro e
  norm_num

/-- Consequently the exact cycle checker certifies strictly positive total
symbolic score. -/
theorem unitLoop_closed_score_pos :
    0 < ([()].map fun _ : Unit ↦ (1 : ℚ)).sum := by
  apply
    OutwardRechargeDriftCertificate.FirstPassageGrammar.EdgeWalk.closed_score_pos_of_bellman
      unitLoopGrammar (fun _ ↦ 0) (fun _ ↦ 1) 1
      (by norm_num) unitLoop_bellman_margin_one (by simp)
  exact unitLoopWalk

/-- The symbolic loop can plainly be followed forever at the graph level. -/
theorem unitLoop_has_infinite_symbolic_path :
    ∃ state : ℕ → Unit, ∃ edge : ℕ → Unit,
      (∀ n, unitLoopGrammar.source (edge n) = state n) ∧
      (∀ n, unitLoopGrammar.target (edge n) = state (n + 1)) := by
  exact ⟨fun _ ↦ (), fun _ ↦ (), by simp, by simp⟩

/-- But no fixed ordinary charge assignment can interpret its self-loop as
a literal positive recharge edge. -/
theorem unitLoop_no_literalRechargeSound :
    ¬ ∃ charge : Unit → ℕ,
      OutwardRechargeDriftCertificate.FirstPassageGrammar.LiteralRechargeSound
        unitLoopGrammar charge := by
  rintro ⟨charge, hsound⟩
  have hloop := hsound ()
  have hlt := hloop.lt
  change charge () < charge () at hlt
  exact (Nat.lt_irrefl _) hlt

/-- Packaged logical countermodel: genuine first-passage labels, an infinite
symbolic path, and positive exact cycle drift coexist with failure of literal
ordinary-charge semantics. -/
theorem positiveCycle_does_not_force_literalRecharge :
    (∀ e, FirstPassage (unitLoopGrammar.word e)) ∧
    (∃ state : ℕ → Unit, ∃ edge : ℕ → Unit,
      (∀ n, unitLoopGrammar.source (edge n) = state n) ∧
      (∀ n, unitLoopGrammar.target (edge n) = state (n + 1))) ∧
    0 < ([()].map fun _ : Unit ↦ (1 : ℚ)).sum ∧
    ¬ ∃ charge : Unit → ℕ,
      OutwardRechargeDriftCertificate.FirstPassageGrammar.LiteralRechargeSound
        unitLoopGrammar charge := by
  exact ⟨unitLoopGrammar.firstPassage,
    unitLoop_has_infinite_symbolic_path,
    unitLoop_closed_score_pos,
    unitLoop_no_literalRechargeSound⟩

end OutwardPositiveCycleSemanticGap
end KontoroC
