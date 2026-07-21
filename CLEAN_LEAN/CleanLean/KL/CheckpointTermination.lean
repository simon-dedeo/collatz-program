/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.HistoryWords

/-!
# Well-founded compressed KL branch checkpoints

Transport spines are deterministic and finite once their starting shift is
fixed.  The genuinely recursive calls of the concrete builder occur only at
surviving nonnegative branch arrivals.  This file proves that relation is
well-founded by mapping any hypothetical descending chain to the already
checked irrational branch-arrival compactness theorem.
-/

namespace CleanLean.KL

namespace ConcreteElimination

/-- At a surviving checkpoint, a return to the current state is no higher
than every earlier occurrence of that state on its complete word prefix. -/
def RecordAt (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) : Prop :=
  ∀ earlier : OccurrenceId, earlier <+: word →
    OccurrenceId.stateAt k root earlier =
      OccurrenceId.stateAt k root word →
    (OccurrenceId.shiftAt word).value ≤
      (OccurrenceId.shiftAt earlier).value

/-- A nonnegative legal branch checkpoint together with the pathwise
no-higher-return invariant enforced by the repeat classifier. -/
structure BranchCheckpoint (k : ℕ) (root : ResidueSystem.State k) where
  word : OccurrenceId
  valid : OccurrenceId.ValidFrom k root word
  nonnegative : 0 ≤ (OccurrenceId.shiftAt word).value
  recordAt : RecordAt k root word

/-- The root word is the initial surviving checkpoint. -/
def rootCheckpoint (k : ℕ) (root : ResidueSystem.State k) :
    BranchCheckpoint k root where
  word := []
  valid := trivial
  nonnegative := by simp
  recordAt := by
    intro earlier hprefix hstate
    rw [List.prefix_nil] at hprefix
    subst earlier
    exact le_rfl

/-- Transport iterates eventually make every symbolic shift negative. -/
theorem exists_transport_iterate_value_neg (shift : SymbolicShift) :
    ∃ transports : ℕ,
      (SymbolicShift.transport^[transports] shift).value < 0 := by
  obtain ⟨transports, htransports⟩ := exists_nat_gt shift.value
  refine ⟨transports, ?_⟩
  rw [ArrivalKind.value_transport_iterate]
  have hnonneg : (0 : ℝ) ≤ transports := by positivity
  exact sub_neg.mpr (lt_of_lt_of_le htransports (by linarith))

/-- Least number of transports required to reach a negative shift. -/
noncomputable def transportDepth (shift : SymbolicShift) : ℕ :=
  Nat.find (exists_transport_iterate_value_neg shift)

theorem transportDepth_spec (shift : SymbolicShift) :
    (SymbolicShift.transport^[transportDepth shift] shift).value < 0 :=
  Nat.find_spec (exists_transport_iterate_value_neg shift)

theorem transportDepth_nonnegative_before (shift : SymbolicShift)
    {transports : ℕ} (htransports : transports < transportDepth shift) :
    0 ≤ (SymbolicShift.transport^[transports] shift).value := by
  exact le_of_not_gt
    (Nat.find_min (exists_transport_iterate_value_neg shift) htransports)

/-- A nonnegative checkpoint has a nonempty transport spine. -/
theorem transportDepth_pos_of_nonnegative (shift : SymbolicShift)
    (hshift : 0 ≤ shift.value) : 0 < transportDepth shift := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hneg := transportDepth_spec shift
  have : shift.value < 0 := by simpa [hzero] using hneg
  linarith

/-- The first negative transport iterate lies in the one-step band `[-2,0)`.
-/
theorem transportDepth_value_lower (shift : SymbolicShift)
    (hshift : 0 ≤ shift.value) :
    -2 ≤ (SymbolicShift.transport^[transportDepth shift] shift).value := by
  cases hdepth : transportDepth shift with
  | zero =>
      simp only [Function.iterate_zero_apply]
      linarith
  | succ depth =>
      have hbefore :
          0 ≤ (SymbolicShift.transport^[depth] shift).value := by
        apply transportDepth_nonnegative_before
        omega
      rw [Function.iterate_succ_apply', SymbolicShift.value_transport]
      linarith

/-- Every branch child of a nonnegative source has shift at least `-2`. -/
theorem branchTarget_shift_lower
    (source : OccurrenceId) (kind : ArrivalKind) (lift : Fin 3)
    (hsource : 0 ≤ (OccurrenceId.shiftAt source).value) :
    -2 ≤
      (OccurrenceId.shiftAt
        (source ++ [arrivalHistoryStep kind lift])).value := by
  rw [OccurrenceId.shiftAt_append_singleton]
  cases kind with
  | retarded =>
      simp only [arrivalHistoryStep, HistoryStep.nextShift,
        SymbolicShift.value_retarded]
      linarith [one_lt_alpha]
  | advanced =>
      simp only [arrivalHistoryStep, HistoryStep.nextShift,
        SymbolicShift.value_advanced]
      linarith [one_lt_alpha]

/-- Failure of the checkpoint record at a branch target is exactly a concrete
higher-repeat certificate.  Strictness rules out the target itself, so the
earlier word is already a prefix of the branch source (equality with the
source is allowed). -/
theorem exists_wordRepeatProvenance_of_not_recordAt
    {k : ℕ} {root : ResidueSystem.State k}
    (source : OccurrenceId) (kind : ArrivalKind) (lift : Fin 3)
    (hsource : OccurrenceId.ValidFrom k root source)
    (hbranch : (arrivalHistoryStep kind lift).ValidAt k
      (OccurrenceId.stateAt k root source))
    (hnot : ¬ RecordAt k root
      (source ++ [arrivalHistoryStep kind lift])) :
    ∃ provenance : WordRepeatProvenance k root,
      provenance.targetWord =
        source ++ [arrivalHistoryStep kind lift] := by
  rw [RecordAt] at hnot
  push Not at hnot
  obtain ⟨earlier, hprefix, hstate, hstrict⟩ := hnot
  have hearlier : earlier <+: source := by
    rcases List.prefix_concat_iff.mp hprefix with heq | hearlier
    · subst earlier
      exact False.elim (lt_irrefl _ hstrict)
    · exact hearlier
  let provenance : WordRepeatProvenance k root :=
    { earlier := earlier
      source := source
      kind := kind
      lift := lift
      earlierPrefixSource := hearlier
      source_valid := hsource
      branch_valid := hbranch
      same_state := hstate
      strictly_higher := hstrict }
  exact ⟨provenance, rfl⟩

/-- Turn a nonnegative, nonrepeating branch target on a checkpoint's
transport spine into the next recursive checkpoint. -/
def nextCheckpoint
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) (transports : ℕ)
    (kind : ArrivalKind) (lift : Fin 3)
    (hbranch : (arrivalHistoryStep kind lift).ValidAt k
      (OccurrenceId.stateAt k root
        (parent.word ++
          List.replicate transports HistoryStep.transport)))
    (hnonnegative : 0 ≤
      (OccurrenceId.shiftAt
        (parent.word ++ List.replicate transports HistoryStep.transport ++
          [arrivalHistoryStep kind lift])).value)
    (hrecord : RecordAt k root
      (parent.word ++ List.replicate transports HistoryStep.transport ++
        [arrivalHistoryStep kind lift])) :
    BranchCheckpoint k root where
  word := parent.word ++ List.replicate transports HistoryStep.transport ++
    [arrivalHistoryStep kind lift]
  valid := by
    rw [OccurrenceId.validFrom_append_singleton_iff]
    exact ⟨OccurrenceId.validFrom_append_transports
      k root parent.word transports parent.valid, hbranch⟩
  nonnegative := hnonnegative
  recordAt := hrecord

/-- Concrete witness that `child` is reached from `parent` by a deterministic
transport spine followed by one retarded or advanced branch edge. -/
structure BranchExtension {k : ℕ} {root : ResidueSystem.State k}
    (child parent : BranchCheckpoint k root) where
  transports : ℕ
  kind : ArrivalKind
  lift : Fin 3
  word_eq : child.word =
    parent.word ++ List.replicate transports HistoryStep.transport ++
      [arrivalHistoryStep kind lift]

/-- The recursive-call relation of the checkpoint builder. -/
def BranchChild {k : ℕ} {root : ResidueSystem.State k}
    (child parent : BranchCheckpoint k root) : Prop :=
  Nonempty (BranchExtension child parent)

/-- `nextCheckpoint` is definitionally a child in the well-founded compressed
branch relation. -/
theorem nextCheckpoint_branchChild
    {k : ℕ} {root : ResidueSystem.State k}
    (parent : BranchCheckpoint k root) (transports : ℕ)
    (kind : ArrivalKind) (lift : Fin 3)
    (hbranch : (arrivalHistoryStep kind lift).ValidAt k
      (OccurrenceId.stateAt k root
        (parent.word ++
          List.replicate transports HistoryStep.transport)))
    (hnonnegative : 0 ≤
      (OccurrenceId.shiftAt
        (parent.word ++ List.replicate transports HistoryStep.transport ++
          [arrivalHistoryStep kind lift])).value)
    (hrecord : RecordAt k root
      (parent.word ++ List.replicate transports HistoryStep.transport ++
        [arrivalHistoryStep kind lift])) :
    BranchChild
      (nextCheckpoint parent transports kind lift hbranch hnonnegative hrecord)
      parent := by
  exact ⟨{
    transports := transports
    kind := kind
    lift := lift
    word_eq := rfl }⟩

namespace BranchExtension

variable {k : ℕ} {root : ResidueSystem.State k}
  {child parent : BranchCheckpoint k root}

/-- Every compressed branch extension strictly extends its parent's word. -/
theorem parent_prefix (edge : BranchExtension child parent) :
    parent.word <+: child.word := by
  rw [edge.word_eq, List.append_assoc]
  exact List.prefix_append _ _

/-- The symbolic-height difference of a compressed edge is the exact
irrational drift minus its natural-valued cost. -/
theorem shift_sub (edge : BranchExtension child parent) :
    (OccurrenceId.shiftAt child.word).value -
        (OccurrenceId.shiftAt parent.word).value =
      alpha - edge.kind.cost edge.transports := by
  rw [edge.word_eq, OccurrenceId.shiftAt_append_compressedArrival]
  exact ArrivalKind.value_follow_sub edge.kind edge.transports _

end BranchExtension

namespace BranchChild

variable {k : ℕ} {root : ResidueSystem.State k}

/-- Words along a descending checkpoint chain are prefix-increasing. -/
theorem word_prefix_of_chain
    (f : ℕ → BranchCheckpoint k root)
    (hchain : ∀ n, BranchChild (f (n + 1)) (f n))
    {i j : ℕ} (hij : i ≤ j) : (f i).word <+: (f j).word := by
  classical
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
  subst j
  clear hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hedge := (Classical.choice (hchain (i + d))).parent_prefix
      simpa [Nat.add_assoc] using ih.trans hedge

/-- The surviving compressed branch relation is well-founded.  A descending
chain would have nonnegative heights, statewise antitonicity from `RecordAt`,
and exact increments `alpha - cost`, contradicting
`no_infinite_KL_branch_arrivals`. -/
theorem wellFounded :
    WellFounded (@BranchChild k root) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hchain⟩
  classical
  let edge : (n : ℕ) → BranchExtension (f (n + 1)) (f n) :=
    fun n => Classical.choice (hchain n)
  let state : ℕ → ResidueSystem.State k := fun n =>
    OccurrenceId.stateAt k root (f n).word
  let height : ℕ → ℝ := fun n =>
    (OccurrenceId.shiftAt (f n).word).value
  let cost : ℕ → ℕ := fun n =>
    (edge n).kind.cost (edge n).transports
  apply no_infinite_KL_branch_arrivals state height cost
  · intro n
    exact (f n).nonnegative
  · intro i j hij hstate
    exact (f j).recordAt (f i).word
      (word_prefix_of_chain f hchain hij) hstate
  · intro n
    exact (edge n).shift_sub

end BranchChild

end ConcreteElimination

end CleanLean.KL
