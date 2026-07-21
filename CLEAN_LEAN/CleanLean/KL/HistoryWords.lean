/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteElimination
import CleanLean.KL.BranchArrivalTermination

/-!
# Occurrence words for the concrete KL expansion

An occurrence is identified by its finite edge word from a root, not by its
principal label.  This is essential: two different histories can produce the
same state and symbolic shift while only one occurrence is a forbidden higher
repeat.
-/

namespace CleanLean.KL

namespace ConcreteElimination

/-- One edge in the universal KL history tree.  Branch kinds are retained in
the word so validity is independently checkable at their source state. -/
inductive HistoryStep where
  | transport
  | retarded (lift : Fin 3)
  | advanced (lift : Fin 3)
  deriving DecidableEq, Repr

abbrev OccurrenceId := List HistoryStep

namespace HistoryStep

/-- Residue-state update encoded by one history edge. -/
def nextState (k : ℕ) (step : HistoryStep)
    (state : ResidueSystem.State k) : ResidueSystem.State k :=
  match step with
  | .transport => (ResidueSystem.system k).transport state
  | .retarded j | .advanced j =>
      (ResidueSystem.system k).fiber
        ((ResidueSystem.system k).refinementTarget state) j

/-- Exact symbolic-shift update encoded by one history edge. -/
def nextShift (step : HistoryStep) (shift : SymbolicShift) : SymbolicShift :=
  match step with
  | .transport => shift.transport
  | .retarded _ => shift.retarded
  | .advanced _ => shift.advanced

/-- Branch edges must agree with the concrete residue branch at their source.
Transport is present at every source. -/
def ValidAt (k : ℕ) (step : HistoryStep)
    (state : ResidueSystem.State k) : Prop :=
  match step with
  | .transport => True
  | .retarded _ => (ResidueSystem.system k).branch state = Branch.retarded
  | .advanced _ => (ResidueSystem.system k).branch state = Branch.advanced

@[simp] theorem nextShift_value (step : HistoryStep) (shift : SymbolicShift) :
    (step.nextShift shift).value = shift.value +
      match step with
      | .transport => -2
      | .retarded _ => alpha - 2
      | .advanced _ => alpha - 1 := by
  cases step <;> simp [nextShift, sub_eq_add_neg]

end HistoryStep

namespace OccurrenceId

/-- State reached after following an occurrence word. -/
def stateAt (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) : ResidueSystem.State k :=
  word.foldl (fun state step => step.nextState k state) root

/-- Exact symbolic shift reached after following an occurrence word. -/
def shiftAt (word : OccurrenceId) : SymbolicShift :=
  word.foldl (fun shift step => step.nextShift shift) SymbolicShift.zero

/-- Concrete real principal label at an occurrence. -/
noncomputable def labelAt (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) : PrincipalLabel (ResidueSystem.State k) :=
  symbolicLabel (stateAt k root word) (shiftAt word)

/-- Every edge of the word is legal at the state reached by its prefix. -/
def ValidFrom (k : ℕ) :
    ResidueSystem.State k → OccurrenceId → Prop
  | _, [] => True
  | state, step :: rest =>
      step.ValidAt k state ∧ ValidFrom k (step.nextState k state) rest

@[simp] theorem stateAt_nil (k : ℕ) (root : ResidueSystem.State k) :
    stateAt k root [] = root := rfl

@[simp] theorem shiftAt_nil : shiftAt [] = SymbolicShift.zero := rfl

@[simp] theorem stateAt_append_singleton
    (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) (step : HistoryStep) :
    stateAt k root (word ++ [step]) = step.nextState k (stateAt k root word) := by
  simp [stateAt, List.foldl_append]

@[simp] theorem shiftAt_append_singleton
    (word : OccurrenceId) (step : HistoryStep) :
    shiftAt (word ++ [step]) = step.nextShift (shiftAt word) := by
  simp [shiftAt, List.foldl_append]

@[simp] theorem labelAt_nil (k : ℕ) (root : ResidueSystem.State k) :
    labelAt k root [] = symbolicLabel root SymbolicShift.zero := by
  simp [labelAt]

@[simp] theorem labelAt_append_singleton
    (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) (step : HistoryStep) :
    labelAt k root (word ++ [step]) =
      symbolicLabel (step.nextState k (stateAt k root word))
        (step.nextShift (shiftAt word)) := by
  simp [labelAt]

@[simp] theorem labelAt_append_transport
    (k : ℕ) (root : ResidueSystem.State k) (word : OccurrenceId) :
    labelAt k root (word ++ [HistoryStep.transport]) =
      symbolicLabel
        ((ResidueSystem.system k).transport (stateAt k root word))
        (shiftAt word).transport := by
  simp [HistoryStep.nextState, HistoryStep.nextShift]

@[simp] theorem labelAt_append_retarded
    (k : ℕ) (root : ResidueSystem.State k) (word : OccurrenceId) (j : Fin 3) :
    labelAt k root (word ++ [HistoryStep.retarded j]) =
      symbolicLabel
        ((ResidueSystem.system k).fiber
          ((ResidueSystem.system k).refinementTarget (stateAt k root word)) j)
        (shiftAt word).retarded := by
  simp [HistoryStep.nextState, HistoryStep.nextShift]

@[simp] theorem labelAt_append_advanced
    (k : ℕ) (root : ResidueSystem.State k) (word : OccurrenceId) (j : Fin 3) :
    labelAt k root (word ++ [HistoryStep.advanced j]) =
      symbolicLabel
        ((ResidueSystem.system k).fiber
          ((ResidueSystem.system k).refinementTarget (stateAt k root word)) j)
        (shiftAt word).advanced := by
  simp [HistoryStep.nextState, HistoryStep.nextShift]

/-- A valid appended word splits into validity of its prefix, legality of the
new edge at the prefix state, and validity of its suffix. -/
theorem validFrom_append_singleton_iff
    (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) (step : HistoryStep) :
    ValidFrom k root (word ++ [step]) ↔
      ValidFrom k root word ∧ step.ValidAt k (stateAt k root word) := by
  induction word generalizing root with
  | nil => simp [ValidFrom, stateAt]
  | cons first rest ih =>
      simp only [List.cons_append, ValidFrom, stateAt, List.foldl_cons]
      rw [ih]
      tauto

/-- A transport spine is legal after every legal occurrence word. -/
theorem validFrom_append_transports
    (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) (transports : ℕ)
    (hvalid : ValidFrom k root word) :
    ValidFrom k root
      (word ++ List.replicate transports HistoryStep.transport) := by
  induction transports with
  | zero => simpa using hvalid
  | succ transports ih =>
      rw [show List.replicate (transports + 1) HistoryStep.transport =
        List.replicate transports HistoryStep.transport ++
          [HistoryStep.transport] by
        simpa using List.replicate_add transports 1 HistoryStep.transport,
        ← List.append_assoc, validFrom_append_singleton_iff]
      exact ⟨ih, trivial⟩

/-- The earlier occurrence in a repeat certificate is a concrete prefix of
the marked target word. -/
def EarlierPrefix (earlier target : OccurrenceId) : Prop :=
  earlier <+: target

end OccurrenceId

/-- Convert a compressed arrival kind and lift index to the corresponding
one-edge history symbol. -/
def arrivalHistoryStep (kind : ArrivalKind) (lift : Fin 3) : HistoryStep :=
  match kind with
  | .retarded => .retarded lift
  | .advanced => .advanced lift

namespace OccurrenceId

/-- Following a finite transport spine agrees with iterating the symbolic
transport map. -/
theorem shiftAt_append_transports
    (word : OccurrenceId) (transports : ℕ) :
    shiftAt (word ++ List.replicate transports HistoryStep.transport) =
      SymbolicShift.transport^[transports] (shiftAt word) := by
  induction transports generalizing word with
  | zero => simp
  | succ transports ih =>
      rw [List.replicate_succ]
      rw [show
        word ++ HistoryStep.transport ::
            List.replicate transports HistoryStep.transport =
          (word ++ [HistoryStep.transport]) ++
            List.replicate transports HistoryStep.transport by simp]
      rw [ih, shiftAt_append_singleton, Function.iterate_succ_apply]
      rfl

/-- A compressed transport spine followed by one branch edge has exactly the
symbolic update used by the branch-arrival compactness theorem. -/
theorem shiftAt_append_compressedArrival
    (word : OccurrenceId) (transports : ℕ)
    (kind : ArrivalKind) (lift : Fin 3) :
    shiftAt
        (word ++ List.replicate transports HistoryStep.transport ++
          [arrivalHistoryStep kind lift]) =
      kind.follow transports (shiftAt word) := by
  rw [shiftAt_append_singleton, shiftAt_append_transports]
  cases kind <;> rfl

end OccurrenceId

/-- Path-level certificate stored at one marked branch occurrence.  The
earlier word may equal the source word (a marked self-child), but is always a
prefix of it. -/
structure WordRepeatProvenance (k : ℕ) (root : ResidueSystem.State k) where
  earlier : OccurrenceId
  source : OccurrenceId
  kind : ArrivalKind
  lift : Fin 3
  earlierPrefixSource : earlier <+: source
  source_valid : OccurrenceId.ValidFrom k root source
  branch_valid : (arrivalHistoryStep kind lift).ValidAt k
    (OccurrenceId.stateAt k root source)
  same_state : OccurrenceId.stateAt k root earlier =
    OccurrenceId.stateAt k root (source ++ [arrivalHistoryStep kind lift])
  strictly_higher : (OccurrenceId.shiftAt earlier).value <
    (OccurrenceId.shiftAt (source ++ [arrivalHistoryStep kind lift])).value

namespace WordRepeatProvenance

variable {k : ℕ} {root : ResidueSystem.State k}

/-- The marked target occurrence determined by the certificate. -/
def targetWord (P : WordRepeatProvenance k root) : OccurrenceId :=
  P.source ++ [arrivalHistoryStep P.kind P.lift]

/-- The earlier occurrence is a prefix of the marked target. -/
theorem earlierPrefixTarget (P : WordRepeatProvenance k root) :
    P.earlier <+: P.targetWord := by
  exact P.earlierPrefixSource.trans
    (List.prefix_append P.source [arrivalHistoryStep P.kind P.lift])

/-- Appending the certified branch edge preserves word validity. -/
theorem target_valid (P : WordRepeatProvenance k root) :
    OccurrenceId.ValidFrom k root P.targetWord := by
  rw [targetWord, OccurrenceId.validFrom_append_singleton_iff]
  exact ⟨P.source_valid, P.branch_valid⟩

/-- The path certificate's state equality is exactly equality of the concrete
principal-label states. -/
theorem label_same_state (P : WordRepeatProvenance k root) :
    (OccurrenceId.labelAt k root P.earlier).state =
      (OccurrenceId.labelAt k root P.targetWord).state := by
  exact P.same_state

/-- The path certificate's strict height comparison is exactly the concrete
principal-label shift comparison. -/
theorem label_strictly_higher (P : WordRepeatProvenance k root) :
    (OccurrenceId.labelAt k root P.earlier).shift <
      (OccurrenceId.labelAt k root P.targetWord).shift := by
  exact P.strictly_higher

end WordRepeatProvenance

end ConcreteElimination

end CleanLean.KL
