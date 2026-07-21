/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteElimination

/-!
# A finite obstruction to the printed KL termination proof

At level five there is a legal principal path which returns to its initial
residue at a strictly *larger* time shift.  The branch children before the
closing transport step are all new on their ancestor path, so the deletion
test described in Krasikov--Lagarias does not remove them.  This invalidates
the finite-step inference used to derive their printed equation (3.2), which
is itself stated under an additional infinite-path hypothesis, and directly
refutes the following history-free subtree-identification argument.  It does
not prove that the elimination procedure itself fails to terminate.
-/

namespace CleanLean.KL

open SymbolicShift

namespace TerminationObstruction

abbrev State5 := ResidueSystem.State 5

/-- The states are stored in the internal coordinate `s = (m-2)/3`; their
names record the corresponding original residues modulo `3^5`. -/
def state188 : State5 := 62
def state206 : State5 := 68
def state137 : State5 := 45
def state182 : State5 := 60
def state161 : State5 := 53
def state107 : State5 := 35
def state71 : State5 := 23
def state47 : State5 := 15

/-- Recover the original residue representative from a level-five internal
coordinate. -/
def rawResidue (state : State5) : ℕ := 2 + 3 * state.val

theorem rawResidues :
    [state188, state206, state137, state182, state161, state107, state71,
      state47].map rawResidue = [188, 206, 137, 182, 161, 107, 71, 47] := by
  decide +kernel

/-- Exact symbolic shifts at the successive destinations. -/
def shift206 : SymbolicShift := ⟨-1, 1⟩
def shift137 : SymbolicShift := ⟨-2, 2⟩
def shift182 : SymbolicShift := ⟨-4, 3⟩
def shift161 : SymbolicShift := ⟨-6, 4⟩
def shift107 : SymbolicShift := ⟨-7, 5⟩
def shift71 : SymbolicShift := ⟨-8, 6⟩
def shift47 : SymbolicShift := ⟨-9, 7⟩
def shift188Return : SymbolicShift := ⟨-11, 7⟩

/-- The path follows the splitter increments exactly. -/
theorem shift_chain :
    zero.advanced = shift206 ∧
    shift206.advanced = shift137 ∧
    shift137.retarded = shift182 ∧
    shift182.retarded = shift161 ∧
    shift161.advanced = shift107 ∧
    shift107.advanced = shift71 ∧
    shift71.advanced = shift47 ∧
    shift47.transport = shift188Return := by
  decide +kernel

/-- The state path consists of seven genuine refinement children followed by
one genuine transport child. -/
theorem state_chain :
    ResidueSystem.branch 5 state188 = .advanced ∧
      state206 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state188) 2 ∧
    ResidueSystem.branch 5 state206 = .advanced ∧
      state137 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state206) 1 ∧
    ResidueSystem.branch 5 state137 = .retarded ∧
      state182 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state137) 2 ∧
    ResidueSystem.branch 5 state182 = .retarded ∧
      state161 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state182) 1 ∧
    ResidueSystem.branch 5 state161 = .advanced ∧
      state107 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state161) 1 ∧
    ResidueSystem.branch 5 state107 = .advanced ∧
      state71 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state107) 0 ∧
    ResidueSystem.branch 5 state71 = .advanced ∧
      state47 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state71) 0 ∧
    (ResidueSystem.system 5).transport state47 = state188 := by
  have htransport : (ResidueSystem.system 5).transport state47 = state188 := by
    change ResidueSystem.transport 5 state47 = state188
    rw [ResidueSystem.transport_apply]
    norm_num [state47, state188]
  norm_num [state188, state206, state137, state182, state161, state107,
    state71, state47, ResidueSystem.system, ResidueSystem.transport_apply,
    ResidueSystem.branch, ResidueSystem.refinementTarget,
    ResidueSystem.retardedTarget, ResidueSystem.advancedTarget,
    ResidueSystem.fiber, ZMod.val_ofNat]
  exact htransport

/-- Every branch destination before the closing transport is new.  Therefore
none can satisfy an ancestor-repeat deletion test, independently of shift
comparisons. -/
theorem branch_destinations_are_new :
    state206 ∉ [state188] ∧
    state137 ∉ [state188, state206] ∧
    state182 ∉ [state188, state206, state137] ∧
    state161 ∉ [state188, state206, state137, state182] ∧
    state107 ∉ [state188, state206, state137, state182, state161] ∧
    state71 ∉ [state188, state206, state137, state182, state161, state107] ∧
    state47 ∉ [state188, state206, state137, state182, state161, state107,
      state71] := by
  decide +kernel

/-- The ancestry-dependent deletion condition used in the printed algorithm:
a newly created branch leaf is eligible if an earlier principal ancestor has
the same state and a strictly smaller shift. -/
def DeletionEligible (history : List (State5 × SymbolicShift))
    (target : State5) (targetShift : SymbolicShift) : Prop :=
  ∃ ancestor ∈ history,
    ancestor.1 = target ∧ ancestor.2.value < targetShift.value

theorem not_deletionEligible_of_new_state
    {history : List (State5 × SymbolicShift)} {target : State5}
    {targetShift : SymbolicShift}
    (hnew : target ∉ history.map Prod.fst) :
    ¬DeletionEligible history target targetShift := by
  rintro ⟨ancestor, hmem, hstate, _⟩
  apply hnew
  rw [List.mem_map]
  exact ⟨ancestor, hmem, hstate⟩

/-- Each of the seven refinement children survives the ancestor-repeat
deletion test on this first pass. -/
theorem branch_steps_survive_deletion_test :
    ¬DeletionEligible [(state188, zero)] state206 shift206 ∧
    ¬DeletionEligible [(state188, zero), (state206, shift206)] state137 shift137 ∧
    ¬DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137)]
      state182 shift182 ∧
    ¬DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182)] state161 shift161 ∧
    ¬DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182), (state161, shift161)] state107 shift107 ∧
    ¬DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182), (state161, shift161), (state107, shift107)]
      state71 shift71 ∧
    ¬DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182), (state161, shift161), (state107, shift107),
        (state71, shift71)] state47 shift47 := by
  repeat' apply And.intro
  all_goals
    apply not_deletionEligible_of_new_state
    decide +kernel

/-- The one exact logarithmic comparison needed for all shift signs. -/
theorem eleven_sevenths_lt_alpha : (11 : ℝ) / 7 < alpha := by
  apply div_lt_alpha_of_check (P := 11) (Q := 7) (by norm_num)
  norm_num [checkAlphaLower]

/-- Every destination shift on the path is nonnegative. -/
theorem shifts_nonnegative :
    0 ≤ shift206.value ∧
    0 ≤ shift137.value ∧
    0 ≤ shift182.value ∧
    0 ≤ shift161.value ∧
    0 ≤ shift107.value ∧
    0 ≤ shift71.value ∧
    0 ≤ shift47.value ∧
    0 ≤ shift188Return.value := by
  have h := eleven_sevenths_lt_alpha
  simp only [SymbolicShift.value, shift206, shift137, shift182, shift161,
    shift107, shift71, shift47, shift188Return]
  norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The closing occurrence of residue 188 has strictly larger shift than the
root.  This obstructs the finite-step decrease inference used in the printed
derivation of equation (3.2). -/
theorem returned_root_shift_increases : zero.value < shift188Return.value := by
  have h := eleven_sevenths_lt_alpha
  simp only [SymbolicShift.value, SymbolicShift.zero, shift188Return]
  norm_num
  linarith

/-- The closing transport child repeats the root in the precise
shift-increasing sense.  The printed deletion rule does not test transport
children. -/
theorem closing_transport_is_higher_repeat :
    DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182), (state161, shift161), (state107, shift107),
        (state71, shift71), (state47, shift47)]
      state188 shift188Return := by
  refine ⟨(state188, zero), by simp, rfl, ?_⟩
  exact returned_root_shift_increases

/-- Re-expanding the returned root creates the same advanced child 206, now at
shift `(-12,8)`. -/
theorem returned_advanced_child :
    shift188Return.advanced = (⟨-12, 8⟩ : SymbolicShift) ∧
      state206 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state188) 2 := by
  exact ⟨by decide +kernel, state_chain.2.1⟩

/-- The new occurrence of child 206 is strictly above its first occurrence.
It is therefore deletion-eligible against that earlier ancestor, showing
that the re-expanded subtree is history-dependent. -/
theorem returned_child_shift_increases :
    shift206.value < shift188Return.advanced.value := by
  have hreturn := returned_root_shift_increases
  simp only [SymbolicShift.value_advanced]
  simp only [SymbolicShift.value, shift206, shift188Return,
    SymbolicShift.zero] at hreturn ⊢
  norm_num at hreturn ⊢
  linarith

/-- After re-expanding the returned root, the advanced child 206 is now
deletion-eligible against its earlier occurrence. -/
theorem returned_child_is_deletionEligible :
    DeletionEligible
      [(state188, zero), (state206, shift206), (state137, shift137),
        (state182, shift182), (state161, shift161), (state107, shift107),
        (state71, shift71), (state47, shift47), (state188, shift188Return)]
      state206 shift188Return.advanced := by
  refine ⟨(state206, shift206), by simp, rfl, ?_⟩
  exact returned_child_shift_increases

/-- Compact headline: a legal first-pass path, with no repeated branch
destination, returns by transport to the same state at a larger nonnegative
shift. -/
theorem printed_equation_3_2_derivation_obstruction :
    (ResidueSystem.system 5).transport state47 = state188 ∧
      state188 ∉ [state206, state137, state182, state161, state107, state71,
        state47] ∧
      0 ≤ shift188Return.value ∧
      zero.value < shift188Return.value := by
  refine ⟨state_chain.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_,
    shifts_nonnegative.2.2.2.2.2.2.2, returned_root_shift_increases⟩
  decide +kernel

end TerminationObstruction

end CleanLean.KL
