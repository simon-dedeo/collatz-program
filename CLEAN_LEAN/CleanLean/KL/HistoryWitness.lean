/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.HistoryBuilder
import CleanLean.KL.RawZipper
import CleanLean.KL.TwoPhaseWitness

/-!
# The concrete KL elimination witness

The well-founded word-indexed history builder and its raw zipper now discharge
all fields of `RawHistoryEliminationData`.  Pruning is proved live at one
positive monotone solution; after that structural fact is known, the existing
two-phase theorem supplies functional and coefficient soundness universally.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree
open EliminationTree.OccurrenceTree

/-- The deterministic occurrence pruning of every built history is live. -/
theorem exists_prunedHistoryOutput
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    ∃ output : EliminationTree (ResidueSystem.State k),
      (buildHistory k root).compile.pruneOccurrences = .live output := by
  let history := buildHistory k root
  have hvalid : history.compile.erase.LocallyValid phi 2 :=
    (history.compile_locallyValid_and_eval_le phi 2 hbase le_rfl).1
  have hmarks : history.compile.MarkingSound phi 2 :=
    markingSound_of_allMarkProvenance history.compile phi 2
      history.allMarkProvenance_root history.compile_shift_lower le_rfl
      hpos hmono
  obtain ⟨output, hprune, _⟩ :=
    pruneOccurrences_sound history.compile phi 2 hvalid hmarks
  exact ⟨output, hprune⟩

/-- The canonical live output of the built history. -/
noncomputable def prunedHistoryOutput
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    EliminationTree (ResidueSystem.State k) :=
  Classical.choose (exists_prunedHistoryOutput k phi hbase hpos hmono root)

theorem prunedHistoryOutput_spec
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    (buildHistory k root).compile.pruneOccurrences =
      .live (prunedHistoryOutput k phi hbase hpos hmono root) :=
  Classical.choose_spec
    (exists_prunedHistoryOutput k phi hbase hpos hmono root)

/-- Each live output has a positive lag lower bound. -/
theorem exists_prunedHistoryLag
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    ∃ mu : ℝ, 0 < mu ∧
      (eraseToRetarded
        (prunedHistoryOutput k phi hbase hpos hmono root)).LagsIn mu 2 := by
  let history := buildHistory k root
  let output := prunedHistoryOutput k phi hbase hpos hmono root
  have hprune : history.compile.pruneOccurrences = .live output :=
    prunedHistoryOutput_spec k phi hbase hpos hmono root
  exact exists_lag_bounds_of_allLeaves output
    (history.pruned_allLeaves_shift_neg output hprune)
    (history.pruned_allLeaves_shift_lower output hprune)

/-- Positive lag bound chosen at one root. -/
noncomputable def prunedHistoryRootMu
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) : ℝ :=
  Classical.choose (exists_prunedHistoryLag k phi hbase hpos hmono root)

theorem prunedHistoryRootMu_pos
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    0 < prunedHistoryRootMu k phi hbase hpos hmono root :=
  (Classical.choose_spec
    (exists_prunedHistoryLag k phi hbase hpos hmono root)).1

theorem prunedHistoryRootMu_lags
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    (eraseToRetarded
      (prunedHistoryOutput k phi hbase hpos hmono root)).LagsIn
        (prunedHistoryRootMu k phi hbase hpos hmono root) 2 :=
  (Classical.choose_spec
    (exists_prunedHistoryLag k phi hbase hpos hmono root)).2

/-- Minimum of the finitely many root lag bounds. -/
noncomputable def prunedHistoryCommonMu
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state)) : ℝ :=
  (Finset.univ : Finset (ResidueSystem.State k)).inf'
    Finset.univ_nonempty
    (prunedHistoryRootMu k phi hbase hpos hmono)

theorem prunedHistoryCommonMu_pos
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state)) :
    0 < prunedHistoryCommonMu k phi hbase hpos hmono := by
  apply (Finset.lt_inf'_iff _).2
  intro root hroot
  exact prunedHistoryRootMu_pos k phi hbase hpos hmono root

theorem prunedHistoryCommonMu_lags
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state))
    (root : ResidueSystem.State k) :
    (eraseToRetarded
      (prunedHistoryOutput k phi hbase hpos hmono root)).LagsIn
        (prunedHistoryCommonMu k phi hbase hpos hmono) 2 := by
  exact (prunedHistoryRootMu_lags k phi hbase hpos hmono root).mono_lower
    (Finset.inf'_le _ (Finset.mem_univ root))

/-- The concrete builder supplies the complete raw-history elimination
contract; there is no remaining termination or mark-provenance hypothesis. -/
noncomputable def builtRawHistoryEliminationData
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state)) :
    RawHistoryEliminationData k where
  history := buildHistory k
  markProvenance := fun root =>
    (buildHistory k root).allMarkProvenance_root
  output := prunedHistoryOutput k phi hbase hpos hmono
  pruned := prunedHistoryOutput_spec k phi hbase hpos hmono
  mu := prunedHistoryCommonMu k phi hbase hpos hmono
  mu_pos := prunedHistoryCommonMu_pos k phi hbase hpos hmono
  lag_bounds := prunedHistoryCommonMu_lags k phi hbase hpos hmono

/-- The fully concrete retarded-elimination witness obtained from the built
history forest and its sound deterministic pruning. -/
noncomputable def builtRetardedEliminationWitness
    (k : ℕ)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ state t, 0 ≤ t → 0 < phi state t)
    (hmono : ∀ state, Monotone (phi state)) :
    RetardedEliminationWitness k :=
  (builtRawHistoryEliminationData k phi hbase hpos hmono).toTwoPhaseEliminationData
    |>.toRetardedEliminationWitness

/-- Fully discharged KL comparison theorem: finite feasibility alone supplies
the exponential lower bound for every positive monotone solution of the base
difference inequalities. -/
theorem quarter_lower_bound_of_feasible
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
  have hpos : ∀ state t, 0 ≤ t → 0 < phi state t := by
    intro state t ht
    exact lt_of_lt_of_le zero_lt_one
      ((hphi0 state).trans (hmono state ht))
  exact quarter_lower_bound_of_retardedElimination
    (builtRetardedEliminationWitness k phi hbase hpos hmono)
    phi c lam C hlam1 hlam2 hbase hphi0 hmono hC hcC hfeasible

end ConcreteElimination

end CleanLean.KL
