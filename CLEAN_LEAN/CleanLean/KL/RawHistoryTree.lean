/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.HistoryWords
import CleanLean.KL.OccurrencePruning

/-!
# Finite occurrence-indexed KL history trees

This inductive type is the target of the remaining well-founded Phase-A
builder.  It is indexed by the exact edge word of its root occurrence.  An
expanded node has exactly the concrete KL children; a marked terminal stores
its word-level repeat certificate; an ordinary terminal has a negative shift.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree
open EliminationTree.OccurrenceTree

/-- A finite raw history subtree rooted at one exact occurrence word. -/
inductive RawHistoryTree (k : ℕ) (root : ResidueSystem.State k) :
    OccurrenceId → Type
  | negative {word : OccurrenceId}
      (shift_neg : (OccurrenceId.shiftAt word).value < 0)
      (shift_lower : -2 ≤ (OccurrenceId.shiftAt word).value) :
      RawHistoryTree k root word
  | marked {word : OccurrenceId}
      (provenance : WordRepeatProvenance k root)
      (target_eq : provenance.targetWord = word)
      (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value) :
      RawHistoryTree k root word
  | neutral {word : OccurrenceId}
      (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value)
      (branch_eq : (ResidueSystem.system k).branch
        (OccurrenceId.stateAt k root word) = Branch.neutral)
      (transport : RawHistoryTree k root
        (word ++ [HistoryStep.transport])) :
      RawHistoryTree k root word
  | retarded {word : OccurrenceId}
      (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value)
      (branch_eq : (ResidueSystem.system k).branch
        (OccurrenceId.stateAt k root word) = Branch.retarded)
      (transport : RawHistoryTree k root
        (word ++ [HistoryStep.transport]))
      (branch0 : RawHistoryTree k root
        (word ++ [HistoryStep.retarded 0]))
      (branch1 : RawHistoryTree k root
        (word ++ [HistoryStep.retarded 1]))
      (branch2 : RawHistoryTree k root
        (word ++ [HistoryStep.retarded 2])) :
      RawHistoryTree k root word
  | advanced {word : OccurrenceId}
      (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value)
      (branch_eq : (ResidueSystem.system k).branch
        (OccurrenceId.stateAt k root word) = Branch.advanced)
      (transport : RawHistoryTree k root
        (word ++ [HistoryStep.transport]))
      (branch0 : RawHistoryTree k root
        (word ++ [HistoryStep.advanced 0]))
      (branch1 : RawHistoryTree k root
        (word ++ [HistoryStep.advanced 1]))
      (branch2 : RawHistoryTree k root
        (word ++ [HistoryStep.advanced 2])) :
      RawHistoryTree k root word

namespace RawHistoryTree

variable {k : ℕ} {root : ResidueSystem.State k} {word : OccurrenceId}

/-- Binary encoding of a three-way minimum for occurrence trees. -/
def occurrenceInf3 {ι : Type}
    (a b c : OccurrenceTree ι) : OccurrenceTree ι :=
  .inf a (.inf b c)

/-- Compile the history grammar to the occurrence-marked elimination syntax. -/
noncomputable def compile :
    {word : OccurrenceId} →
    RawHistoryTree k root word →
      OccurrenceTree (ResidueSystem.State k)
  | word, .negative _ _ => .leaf (OccurrenceId.labelAt k root word) false
  | word, .marked _ _ _ => .leaf (OccurrenceId.labelAt k root word) true
  | word, .neutral _ _ transport =>
      .principal (OccurrenceId.labelAt k root word) transport.compile
  | word, .retarded _ _ transport branch0 branch1 branch2 =>
      .principal (OccurrenceId.labelAt k root word)
        (.add transport.compile
          (occurrenceInf3 branch0.compile branch1.compile branch2.compile))
  | word, .advanced _ _ transport branch0 branch1 branch2 =>
      .principal (OccurrenceId.labelAt k root word)
        (.add transport.compile
          (occurrenceInf3 branch0.compile branch1.compile branch2.compile))

/-- Every raw terminal, including a mark, has shift at least `-2`. -/
theorem compile_shift_lower (tree : RawHistoryTree k root word) :
    tree.compile.erase.AllLeaves fun label => -2 ≤ label.shift := by
  induction tree with
  | negative hneg hlower => exact hlower
  | marked provenance targetEq hnonneg =>
      exact (by linarith : -2 ≤ (OccurrenceId.shiftAt _).value)
  | neutral hnonneg hbranch transport ih => exact ih
  | retarded hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      exact ⟨ihTransport, ih0, ih1, ih2⟩
  | advanced hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      exact ⟨ihTransport, ih0, ih1, ih2⟩

/-- Every unmarked raw terminal is strictly retarded. -/
theorem compile_unmarked_shift_neg (tree : RawHistoryTree k root word) :
    tree.compile.UnmarkedLeavesSatisfy fun label => label.shift < 0 := by
  induction tree with
  | negative hneg hlower => exact Or.inr hneg
  | marked provenance targetEq hnonneg => exact Or.inl rfl
  | neutral hnonneg hbranch transport ih => exact ih
  | retarded hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      exact ⟨ihTransport, ih0, ih1, ih2⟩
  | advanced hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      exact ⟨ihTransport, ih0, ih1, ih2⟩

/-- Split-only Phase A is locally valid, and each compiled subtree evaluates
below the principal value at its own occurrence. -/
theorem compile_locallyValid_and_eval_le
    (tree : RawHistoryTree k root word)
    (φ : ResidueSystem.State k → ℝ → ℝ) (y : ℝ)
    (hbase : SatisfiesBaseSystem k φ) (hy : 2 ≤ y) :
    tree.compile.erase.LocallyValid φ y ∧
      tree.compile.erase.eval φ y ≤
        (OccurrenceId.labelAt k root word).value φ y := by
  induction tree with
  | negative hneg hlower =>
      exact ⟨trivial, le_rfl⟩
  | marked provenance targetEq hnonneg =>
      exact ⟨trivial, le_rfl⟩
  | @neutral word hnonneg hbranch transport ih =>
      have htime : 2 ≤ y + (OccurrenceId.shiftAt word).value := by
        linarith
      have hroot :
          (splitBody k (OccurrenceId.labelAt k root word)).eval φ y ≤
            (OccurrenceId.labelAt k root word).value φ y := by
        rw [eval_splitBody_eq_base]
        exact hbase _ _ htime
      have htransport : transport.compile.erase.eval φ y ≤
          (transportLeaf k (OccurrenceId.labelAt k root word)).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [EliminationTree.eval, HistoryStep.nextState,
          HistoryStep.nextShift] using ih.2
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          transportLeaf k (OccurrenceId.labelAt k root word) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      have hbody : transport.compile.erase.eval φ y ≤
          (splitBody k (OccurrenceId.labelAt k root word)).eval φ y := by
        rw [hsplit]
        exact htransport
      constructor
      · exact ⟨hbody.trans hroot, ih.1⟩
      · exact hbody.trans hroot
  | @retarded word hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      have htime : 2 ≤ y + (OccurrenceId.shiftAt word).value := by
        linarith
      have hroot :
          (splitBody k (OccurrenceId.labelAt k root word)).eval φ y ≤
            (OccurrenceId.labelAt k root word).value φ y := by
        rw [eval_splitBody_eq_base]
        exact hbase _ _ htime
      have ht : transport.compile.erase.eval φ y ≤
          (transportLeaf k (OccurrenceId.labelAt k root word)).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [EliminationTree.eval, HistoryStep.nextState,
          HistoryStep.nextShift] using ihTransport.2
      have h0 : branch0.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 0).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih0.2
      have h1 : branch1.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 1).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih1.2
      have h2 : branch2.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 2).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih2.2
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          .add (transportLeaf k (OccurrenceId.labelAt k root word))
            (branchMinimum k (OccurrenceId.labelAt k root word) (alpha - 2)) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      have hbody :
          (OccurrenceTree.add transport.compile
            (occurrenceInf3 branch0.compile branch1.compile branch2.compile)).erase.eval φ y ≤
          (OccurrenceId.labelAt k root word).value φ y := by
        apply le_trans _ hroot
        rw [hsplit]
        simpa [compile, occurrenceInf3, OccurrenceTree.erase, branchMinimum,
          inf3, EliminationTree.eval] using
          add_le_add ht (min_le_min h0 (min_le_min h1 h2))
      constructor
      · refine ⟨hbody, ?_⟩
        exact ⟨ihTransport.1, ih0.1, ih1.1, ih2.1⟩
      · exact hbody
  | @advanced word hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      have htime : 2 ≤ y + (OccurrenceId.shiftAt word).value := by
        linarith
      have hroot :
          (splitBody k (OccurrenceId.labelAt k root word)).eval φ y ≤
            (OccurrenceId.labelAt k root word).value φ y := by
        rw [eval_splitBody_eq_base]
        exact hbase _ _ htime
      have ht : transport.compile.erase.eval φ y ≤
          (transportLeaf k (OccurrenceId.labelAt k root word)).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [EliminationTree.eval, HistoryStep.nextState,
          HistoryStep.nextShift] using ihTransport.2
      have h0 : branch0.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 0).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih0.2
      have h1 : branch1.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 1).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih1.2
      have h2 : branch2.compile.erase.eval φ y ≤
          (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 2).eval φ y := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic,
          EliminationTree.eval]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih2.2
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          .add (transportLeaf k (OccurrenceId.labelAt k root word))
            (branchMinimum k (OccurrenceId.labelAt k root word) (alpha - 1)) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      have hbody :
          (OccurrenceTree.add transport.compile
            (occurrenceInf3 branch0.compile branch1.compile branch2.compile)).erase.eval φ y ≤
          (OccurrenceId.labelAt k root word).value φ y := by
        apply le_trans _ hroot
        rw [hsplit]
        simpa [compile, occurrenceInf3, OccurrenceTree.erase, branchMinimum,
          inf3, EliminationTree.eval] using
          add_le_add ht (min_le_min h0 (min_le_min h1 h2))
      constructor
      · refine ⟨hbody, ?_⟩
        exact ⟨ihTransport.1, ih0.1, ih1.1, ih2.1⟩
      · exact hbody

/-- Feasibility makes recursive Phase-A substitution monotone in the opposite
coefficient direction: the coefficient of the current principal leaf is no
larger than that of the fully compiled raw subtree. -/
theorem leaf_coeff_le_compile
    (tree : RawHistoryTree k root word)
    (c : ResidueSystem.State k → ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c) :
    (eraseToRetarded (.leaf (OccurrenceId.labelAt k root word))).coeffEval c lam ≤
      (eraseToRetarded tree.compile.erase).coeffEval c lam := by
  induction tree with
  | negative hneg hlower => exact le_rfl
  | marked provenance targetEq hnonneg => exact le_rfl
  | @neutral word hnonneg hbranch transport ih =>
      have hroot := leaf_coeff_le_splitTree k
        (OccurrenceId.labelAt k root word) c hlam hfeasible
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          transportLeaf k (OccurrenceId.labelAt k root word) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      have hchild :
          (eraseToRetarded
            (transportLeaf k (OccurrenceId.labelAt k root word))).coeffEval c lam ≤
          (eraseToRetarded transport.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih
      exact hroot.trans (by
        simpa [splitTree, eraseToRetarded, hsplit, compile,
          OccurrenceTree.erase] using hchild)
  | @retarded word hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      have hroot := leaf_coeff_le_splitTree k
        (OccurrenceId.labelAt k root word) c hlam hfeasible
      have ht :
          (eraseToRetarded
            (transportLeaf k (OccurrenceId.labelAt k root word))).coeffEval c lam ≤
          (eraseToRetarded transport.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ihTransport
      have h0 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 0)).coeffEval c lam ≤
          (eraseToRetarded branch0.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih0
      have h1 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 1)).coeffEval c lam ≤
          (eraseToRetarded branch1.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih1
      have h2 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 2) 2)).coeffEval c lam ≤
          (eraseToRetarded branch2.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_retarded_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih2
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          .add (transportLeaf k (OccurrenceId.labelAt k root word))
            (branchMinimum k (OccurrenceId.labelAt k root word) (alpha - 2)) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      apply hroot.trans
      simpa [splitTree, hsplit, compile, occurrenceInf3,
        OccurrenceTree.erase, branchMinimum, inf3, eraseToRetarded,
        RetardedExpr.coeffEval] using
        add_le_add ht (min_le_min h0 (min_le_min h1 h2))
  | @advanced word hnonneg hbranch transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      have hroot := leaf_coeff_le_splitTree k
        (OccurrenceId.labelAt k root word) c hlam hfeasible
      have ht :
          (eraseToRetarded
            (transportLeaf k (OccurrenceId.labelAt k root word))).coeffEval c lam ≤
          (eraseToRetarded transport.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl,
          transportLeaf_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ihTransport
      have h0 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 0)).coeffEval c lam ≤
          (eraseToRetarded branch0.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih0
      have h1 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 1)).coeffEval c lam ≤
          (eraseToRetarded branch1.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih1
      have h2 :
          (eraseToRetarded
            (branchLeaf k (OccurrenceId.labelAt k root word) (alpha - 1) 2)).coeffEval c lam ≤
          (eraseToRetarded branch2.compile.erase).coeffEval c lam := by
        rw [show OccurrenceId.labelAt k root word =
          symbolicLabel (OccurrenceId.stateAt k root word)
            (OccurrenceId.shiftAt word) by rfl]
        simp only [branchLeaf, branchLabel_advanced_symbolic]
        simpa [HistoryStep.nextState, HistoryStep.nextShift] using ih2
      have hsplit : splitBody k (OccurrenceId.labelAt k root word) =
          .add (transportLeaf k (OccurrenceId.labelAt k root word))
            (branchMinimum k (OccurrenceId.labelAt k root word) (alpha - 1)) := by
        simp [splitBody, OccurrenceId.labelAt, symbolicLabel, hbranch]
      apply hroot.trans
      simpa [splitTree, hsplit, compile, occurrenceInf3,
        OccurrenceTree.erase, branchMinimum, inf3, eraseToRetarded,
        RetardedExpr.coeffEval] using
        add_le_add ht (min_le_min h0 (min_le_min h1 h2))
/-- Hence every live pruned output is fully retarded. -/
theorem pruned_allLeaves_shift_neg
    (tree : RawHistoryTree k root word)
    (output : EliminationTree (ResidueSystem.State k))
    (hprune : tree.compile.pruneOccurrences = .live output) :
    output.AllLeaves fun label => label.shift < 0 := by
  exact allLeaves_of_unmarkedLeavesSatisfy tree.compile output hprune _
    tree.compile_unmarked_shift_neg

/-- The lower shift bound also survives pruning. -/
theorem pruned_allLeaves_shift_lower
    (tree : RawHistoryTree k root word)
    (output : EliminationTree (ResidueSystem.State k))
    (hprune : tree.compile.pruneOccurrences = .live output) :
    output.AllLeaves fun label => -2 ≤ label.shift := by
  exact allLeaves_of_pruneOccurrences_live tree.compile output hprune _
    tree.compile_shift_lower

end RawHistoryTree

end ConcreteElimination

end CleanLean.KL
