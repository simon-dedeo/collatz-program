/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.EliminationWitness
import CleanLean.KL.OccurrencePruning
import CleanLean.KL.RawHistoryTree

/-!
# From a two-phase history forest to the KL elimination witness

This module is the exact seam between the remaining concrete Phase-A builder
and the already checked retarded comparison theorem.  `TwoPhaseEliminationData`
does not assume the desired counting conclusion.  It stores the finite raw
occurrence trees, their deterministic pruned outputs, and the four properties
the builder must prove: local validity, mark soundness, functional root
comparison, and coefficient comparison.

`toRetardedEliminationWitness` proves that these fields suffice.  Thus the
remaining research obligation cannot drift into a cleaner but irrelevant
substitute: it must construct this data from the actual KL split grammar.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree
open EliminationTree.OccurrenceTree

/-- Output contract for the concrete finite two-phase construction at one KL
precision. -/
structure TwoPhaseEliminationData (k : ℕ) where
  raw : ResidueSystem.State k → OccurrenceTree (ResidueSystem.State k)
  output : ResidueSystem.State k → EliminationTree (ResidueSystem.State k)
  mu : ℝ
  mu_pos : 0 < mu
  pruned : ∀ state, (raw state).pruneOccurrences = .live (output state)
  lag_bounds : ∀ state, (eraseToRetarded (output state)).LagsIn mu 2
  locallyValid : ∀ (phi : ResidueSystem.State k → ℝ → ℝ),
    SatisfiesBaseSystem k phi →
    ∀ state y, 2 ≤ y → (raw state).erase.LocallyValid phi y
  raw_shift_lower : ∀ state,
    (raw state).erase.AllLeaves fun label => -2 ≤ label.shift
  markProvenance : ∀ state, (raw state).AllMarkProvenance
  functionalRaw : ∀ (phi : ResidueSystem.State k → ℝ → ℝ),
    SatisfiesBaseSystem k phi →
    ∀ state y, 2 ≤ y → (raw state).erase.eval phi y ≤ phi state y
  coefficientRaw : ∀ (c : ResidueSystem.State k → ℝ) (lam : ℝ),
    0 < lam →
    (ResidueSystem.system k).Feasible (klWeights lam) c →
    ∀ state, c state ≤
      (eraseToRetarded (raw state).erase).coeffEval c lam

/-- The substantially smaller contract now required from the concrete
well-founded builder.  Functional and coefficient soundness are not fields:
they are derived from the indexed raw-history grammar. -/
structure RawHistoryEliminationData (k : ℕ) where
  history : ∀ root : ResidueSystem.State k, RawHistoryTree k root []
  markProvenance : ∀ root, (history root).compile.AllMarkProvenance
  output : ResidueSystem.State k → EliminationTree (ResidueSystem.State k)
  pruned : ∀ root,
    (history root).compile.pruneOccurrences = .live (output root)
  mu : ℝ
  mu_pos : 0 < mu
  lag_bounds : ∀ state, (eraseToRetarded (output state)).LagsIn mu 2

/-- A finite indexed raw forest automatically supplies all analytic and LP
fields of `TwoPhaseEliminationData`. -/
noncomputable def RawHistoryEliminationData.toTwoPhaseEliminationData
    (D : RawHistoryEliminationData k) : TwoPhaseEliminationData k where
  raw := fun state => (D.history state).compile
  output := D.output
  mu := D.mu
  mu_pos := D.mu_pos
  pruned := D.pruned
  lag_bounds := D.lag_bounds
  locallyValid := by
    intro phi hbase state y hy
    exact (RawHistoryTree.compile_locallyValid_and_eval_le
      (D.history state) phi y hbase hy).1
  raw_shift_lower := fun state => (D.history state).compile_shift_lower
  markProvenance := D.markProvenance
  functionalRaw := by
    intro phi hbase state y hy
    have hsound := (RawHistoryTree.compile_locallyValid_and_eval_le
      (D.history state) phi y hbase hy).2
    simpa [OccurrenceId.labelAt, symbolicLabel, PrincipalLabel.value] using hsound
  coefficientRaw := by
    intro c lam hlam hfeasible state
    have hcoeff := RawHistoryTree.leaf_coeff_le_compile
      (D.history state) c lam hlam hfeasible
    simpa [OccurrenceId.labelAt, symbolicLabel, eraseToRetarded,
      RetardedExpr.coeffEval] using hcoeff

/-- The two-phase contract produces exactly the elimination witness consumed
by the retarded comparison theorem. -/
noncomputable def TwoPhaseEliminationData.toRetardedEliminationWitness
    (D : TwoPhaseEliminationData k) : RetardedEliminationWitness k where
  tree := D.output
  mu := D.mu
  mu_pos := D.mu_pos
  lag_bounds := D.lag_bounds
  functional_sound := by
    intro phi hbase hpos hmono state y hy
    have hvalid := D.locallyValid phi hbase state y hy
    have hmarks := markingSound_of_allMarkProvenance
      (D.raw state) phi y (D.markProvenance state)
        (D.raw_shift_lower state) hy hpos hmono
    have havoid : ∀ A : Assignment (D.raw state).erase,
        A.IsCritical phi y → ¬(D.raw state).Hits A := by
      intro A hcritical hhit
      exact hmarks A
        (A.respectsPrincipalBounds_of_locallyValid phi y hcritical hvalid) hhit
    have heq := eval_pruneOccurrences
      (D.raw state) (D.output state) (D.pruned state) phi y havoid
    rw [← heq]
    exact D.functionalRaw phi hbase state y hy
  coefficient_sound := by
    intro c lam hlam hfeasible state
    exact (D.coefficientRaw c lam hlam hfeasible state).trans
      (coeffEval_le_of_pruneOccurrences_live
        (D.raw state) (D.output state) (D.pruned state) c lam)

/-- Direct end-to-end counting comparison from the concrete two-phase data. -/
theorem quarter_lower_bound_of_twoPhaseElimination
    (D : TwoPhaseEliminationData k)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (c : ResidueSystem.State k → ℝ) (lam C : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (hbase : SatisfiesBaseSystem k phi)
    (hphi0 : ∀ state, 1 ≤ phi state 0)
    (hmono : ∀ state, Monotone (phi state))
    (hC : 0 < C) (hcC : ∀ state, c state ≤ C)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c) :
    ∀ state y, 0 ≤ y →
      (1 / (4 * C)) * c state * lam ^ y ≤ phi state y := by
  exact quarter_lower_bound_of_retardedElimination
    D.toRetardedEliminationWitness phi c lam C hlam1 hlam2 hbase hphi0 hmono
      hC hcC hfeasible

end ConcreteElimination

end CleanLean.KL
