/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CheckpointTermination
import CleanLean.KL.RawHistoryTree

/-!
# The finite concrete KL history builder

This file combines finite transport-spine recursion with the well-founded
compressed branch relation.  It constructs an actual `RawHistoryTree` for
every root state.  No numerical eigenvector or GPU certificate is involved.
-/

namespace CleanLean.KL

namespace ConcreteElimination

/-- Word at depth `transports` on a checkpoint's deterministic transport
spine. -/
def spineWord {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) (transports : ℕ) : OccurrenceId :=
  parent.word ++ List.replicate transports HistoryStep.transport

@[simp] theorem spineWord_zero
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) : spineWord parent 0 = parent.word := by
  simp [spineWord]

theorem spineWord_succ
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) (transports : ℕ) :
    spineWord parent (transports + 1) =
      spineWord parent transports ++ [HistoryStep.transport] := by
  simp only [spineWord]
  rw [show List.replicate (transports + 1) HistoryStep.transport =
      List.replicate transports HistoryStep.transport ++
        [HistoryStep.transport] by
    simpa using List.replicate_add transports 1 HistoryStep.transport,
    List.append_assoc]

theorem shiftAt_spineWord
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) (transports : ℕ) :
    OccurrenceId.shiftAt (spineWord parent transports) =
      SymbolicShift.transport^[transports]
        (OccurrenceId.shiftAt parent.word) := by
  exact OccurrenceId.shiftAt_append_transports parent.word transports

/-- Build one branch child.  Negative targets stop; nonnegative higher
repeats are marked; all remaining nonnegative targets are recursive calls in
the well-founded checkpoint relation. -/
noncomputable def buildBranch
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root)
    (recurse : ∀ child : BranchCheckpoint k root,
      BranchChild child parent → RawHistoryTree k root child.word)
    (transports : ℕ) (kind : ArrivalKind) (lift : Fin 3)
    (hsource : 0 ≤
      (OccurrenceId.shiftAt (spineWord parent transports)).value)
    (hbranch : (arrivalHistoryStep kind lift).ValidAt k
      (OccurrenceId.stateAt k root (spineWord parent transports))) :
    RawHistoryTree k root
      (spineWord parent transports ++
        [arrivalHistoryStep kind lift]) := by
  classical
  let target := spineWord parent transports ++
    [arrivalHistoryStep kind lift]
  by_cases hnegative : (OccurrenceId.shiftAt target).value < 0
  · exact .negative hnegative
      (branchTarget_shift_lower (spineWord parent transports) kind lift hsource)
  · have hnonnegative : 0 ≤ (OccurrenceId.shiftAt target).value :=
      le_of_not_gt hnegative
    by_cases hrecord : RecordAt k root target
    · let child := nextCheckpoint parent transports kind lift hbranch
          hnonnegative hrecord
      exact recurse child
        (nextCheckpoint_branchChild parent transports kind lift hbranch
          hnonnegative hrecord)
    · have hsourceValid : OccurrenceId.ValidFrom k root
          (spineWord parent transports) := by
        exact OccurrenceId.validFrom_append_transports
          k root parent.word transports parent.valid
      let hexists := exists_wordRepeatProvenance_of_not_recordAt
        (spineWord parent transports) kind lift hsourceValid hbranch hrecord
      let provenance := Classical.choose hexists
      have htarget := Classical.choose_spec hexists
      exact .marked provenance htarget hnonnegative

/-- Finite recursion down one transport spine.  The equation says the current
depth plus remaining fuel is the least negative transport depth. -/
noncomputable def buildSpine
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root)
    (recurse : ∀ child : BranchCheckpoint k root,
      BranchChild child parent → RawHistoryTree k root child.word)
    (transports fuel : ℕ)
    (hsum : transports + fuel =
      transportDepth (OccurrenceId.shiftAt parent.word)) :
    RawHistoryTree k root (spineWord parent transports) := by
  classical
  cases fuel with
  | zero =>
      have hdepth : transports =
          transportDepth (OccurrenceId.shiftAt parent.word) := by omega
      apply RawHistoryTree.negative
      · rw [shiftAt_spineWord, hdepth]
        exact transportDepth_spec _
      · rw [shiftAt_spineWord, hdepth]
        exact transportDepth_value_lower _ parent.nonnegative
  | succ fuel =>
      have hlt : transports <
          transportDepth (OccurrenceId.shiftAt parent.word) := by omega
      have hsource : 0 ≤
          (OccurrenceId.shiftAt (spineWord parent transports)).value := by
        rw [shiftAt_spineWord]
        exact transportDepth_nonnegative_before _ hlt
      have hnextSum : transports + 1 + fuel =
          transportDepth (OccurrenceId.shiftAt parent.word) := by omega
      have transportTree : RawHistoryTree k root
          (spineWord parent transports ++ [HistoryStep.transport]) := by
        rw [← spineWord_succ]
        exact buildSpine parent recurse (transports + 1) fuel hnextSum
      generalize hbranch : (ResidueSystem.system k).branch
        (OccurrenceId.stateAt k root (spineWord parent transports)) = branch
      cases branch with
      | neutral =>
          exact .neutral hsource hbranch transportTree
      | retarded =>
          have valid (lift : Fin 3) :
              (arrivalHistoryStep ArrivalKind.retarded lift).ValidAt k
                (OccurrenceId.stateAt k root
                  (spineWord parent transports)) := by
            simpa [arrivalHistoryStep, HistoryStep.ValidAt] using hbranch
          exact .retarded hsource hbranch transportTree
            (buildBranch parent recurse transports .retarded 0 hsource (valid 0))
            (buildBranch parent recurse transports .retarded 1 hsource (valid 1))
            (buildBranch parent recurse transports .retarded 2 hsource (valid 2))
      | advanced =>
          have valid (lift : Fin 3) :
              (arrivalHistoryStep ArrivalKind.advanced lift).ValidAt k
                (OccurrenceId.stateAt k root
                  (spineWord parent transports)) := by
            simpa [arrivalHistoryStep, HistoryStep.ValidAt] using hbranch
          exact .advanced hsource hbranch transportTree
            (buildBranch parent recurse transports .advanced 0 hsource (valid 0))
            (buildBranch parent recurse transports .advanced 1 hsource (valid 1))
            (buildBranch parent recurse transports .advanced 2 hsource (valid 2))
termination_by fuel

/-- One layer of the well-founded checkpoint fixpoint. -/
noncomputable def buildCheckpointBody
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root)
    (recurse : ∀ child : BranchCheckpoint k root,
      BranchChild child parent → RawHistoryTree k root child.word) :
    RawHistoryTree k root parent.word := by
  simpa using buildSpine parent recurse 0
    (transportDepth (OccurrenceId.shiftAt parent.word)) (by omega)

/-- The concrete finite raw history rooted at any surviving checkpoint. -/
noncomputable def buildCheckpoint
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) : RawHistoryTree k root parent.word :=
  BranchChild.wellFounded.fix
    (C := fun checkpoint => RawHistoryTree k root checkpoint.word)
    buildCheckpointBody parent

/-- The closed finite Phase-A history for one residue root. -/
noncomputable def buildHistory (k : ℕ) (root : ResidueSystem.State k) :
    RawHistoryTree k root [] :=
  buildCheckpoint (rootCheckpoint k root)

end ConcreteElimination

end CleanLean.KL
