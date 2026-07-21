/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.TerminationObstruction

/-!
# A split whose three refinement alternatives are all deletion-eligible

This is an independent kernel check of the exact level-five history found by
the external exhaustive search.  Every followed refinement child survives
the printed ancestor test, but the final advanced split at residue `242`
creates three children and all three have strictly lower same-residue
ancestors.  Thus the literal printed construction reaches the empty-minimum
case which it claims cannot occur.
-/

namespace CleanLean.KL.AllThreeDeletionObstruction

open SymbolicShift
open TerminationObstruction (DeletionEligible)

abbrev State5 := ResidueSystem.State 5

def state161 : State5 := 53
def state107 : State5 := 35
def state152 : State5 := 50
def state182 : State5 := 60
def state80 : State5 := 26
def state134 : State5 := 44
def state89 : State5 := 29
def state59 : State5 := 19
def state236 : State5 := 78
def state242 : State5 := 80

def rawResidue (state : State5) : ℕ := 2 + 3 * state.val

theorem rawResidues :
    [state161, state107, state152, state182, state80, state134, state89,
      state59, state236, state242].map rawResidue =
      [161, 107, 152, 182, 80, 134, 89, 59, 236, 242] := by
  decide +kernel

def shift107 : SymbolicShift := ⟨-1, 1⟩
def shift152a : SymbolicShift := ⟨-2, 2⟩
def shift182a : SymbolicShift := ⟨-3, 3⟩
def shift80 : SymbolicShift := ⟨-5, 4⟩
def shift134 : SymbolicShift := ⟨-6, 5⟩
def shift89 : SymbolicShift := ⟨-7, 6⟩
def shift59 : SymbolicShift := ⟨-8, 7⟩
def shift236 : SymbolicShift := ⟨-10, 7⟩
def shift152b : SymbolicShift := ⟨-12, 8⟩
def shift182b : SymbolicShift := ⟨-13, 9⟩
def shift242 : SymbolicShift := ⟨-15, 10⟩
def childShift : SymbolicShift := ⟨-16, 11⟩

theorem shift_chain :
    zero.advanced = shift107 ∧
    shift107.advanced = shift152a ∧
    shift152a.advanced = shift182a ∧
    shift182a.retarded = shift80 ∧
    shift80.advanced = shift134 ∧
    shift134.advanced = shift89 ∧
    shift89.advanced = shift59 ∧
    shift59.transport = shift236 ∧
    shift236.retarded = shift152b ∧
    shift152b.advanced = shift182b ∧
    shift182b.retarded = shift242 ∧
    shift242.advanced = childShift := by
  decide +kernel

theorem state_chain :
    ResidueSystem.branch 5 state161 = .advanced ∧
      state107 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state161) 1 ∧
    ResidueSystem.branch 5 state107 = .advanced ∧
      state152 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state107) 1 ∧
    ResidueSystem.branch 5 state152 = .advanced ∧
      state182 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state152) 2 ∧
    ResidueSystem.branch 5 state182 = .retarded ∧
      state80 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state182) 0 ∧
    ResidueSystem.branch 5 state80 = .advanced ∧
      state134 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state80) 1 ∧
    ResidueSystem.branch 5 state134 = .advanced ∧
      state89 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state134) 1 ∧
    ResidueSystem.branch 5 state89 = .advanced ∧
      state59 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state89) 0 ∧
    (ResidueSystem.system 5).transport state59 = state236 ∧
    ResidueSystem.branch 5 state236 = .retarded ∧
      state152 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state236) 1 ∧
    ResidueSystem.branch 5 state152 = .advanced ∧
      state182 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state152) 2 ∧
    ResidueSystem.branch 5 state182 = .retarded ∧
      state242 = ResidueSystem.fiber 5
        (ResidueSystem.refinementTarget 5 state182) 2 := by
  have htransport : (ResidueSystem.system 5).transport state59 = state236 := by
    change ResidueSystem.transport 5 state59 = state236
    rw [ResidueSystem.transport_apply]
    norm_num [state59, state236]
  norm_num [state161, state107, state152, state182, state80, state134,
    state89, state59, state236, state242, ResidueSystem.system,
    ResidueSystem.transport_apply, ResidueSystem.branch,
    ResidueSystem.refinementTarget, ResidueSystem.retardedTarget,
    ResidueSystem.advancedTarget, ResidueSystem.fiber, ZMod.val_ofNat]
  exact htransport

/-- The final advanced split really has the three advertised targets. -/
theorem final_targets :
    ResidueSystem.branch 5 state242 = .advanced ∧
    (∀ j : Fin 3,
      ResidueSystem.fiber 5 (ResidueSystem.refinementTarget 5 state242) j =
        ![state80, state161, state242] j) := by
  constructor
  · norm_num [state242, ResidueSystem.branch, ZMod.val_ofNat]
  · intro j
    fin_cases j <;>
      norm_num [state242, state80, state161, ResidueSystem.refinementTarget,
        ResidueSystem.branch, ResidueSystem.advancedTarget,
        ResidueSystem.fiber, ZMod.val_ofNat]

theorem three_halves_lt_alpha : (3 : ℝ) / 2 < alpha := by
  apply div_lt_alpha_of_check (P := 3) (Q := 2) (by norm_num)
  norm_num [checkAlphaLower]

theorem alpha_lt_five_thirds : alpha < (5 : ℝ) / 3 := by
  apply alpha_lt_div_of_check (P := 5) (Q := 3) (by norm_num)
  norm_num [checkAlphaUpper]

/-- Every vertex in the displayed history, and the common final child shift,
is nonnegative. -/
theorem shifts_nonnegative :
    0 ≤ shift107.value ∧ 0 ≤ shift152a.value ∧ 0 ≤ shift182a.value ∧
    0 ≤ shift80.value ∧ 0 ≤ shift134.value ∧ 0 ≤ shift89.value ∧
    0 ≤ shift59.value ∧ 0 ≤ shift236.value ∧ 0 ≤ shift152b.value ∧
    0 ≤ shift182b.value ∧ 0 ≤ shift242.value ∧ 0 ≤ childShift.value := by
  have h := three_halves_lt_alpha
  simp only [SymbolicShift.value, shift107, shift152a, shift182a, shift80,
    shift134, shift89, shift59, shift236, shift152b, shift182b, shift242,
    childShift]
  norm_num
  repeat' apply And.intro
  all_goals linarith

def history : List (State5 × SymbolicShift) :=
  [(state161, zero), (state107, shift107), (state152, shift152a),
    (state182, shift182a), (state80, shift80), (state134, shift134),
    (state89, shift89), (state59, shift59), (state236, shift236),
    (state152, shift152b), (state182, shift182b), (state242, shift242)]

def historyThrough236 : List (State5 × SymbolicShift) :=
  [(state161, zero), (state107, shift107), (state152, shift152a),
    (state182, shift182a), (state80, shift80), (state134, shift134),
    (state89, shift89), (state59, shift59), (state236, shift236)]

theorem repeated_152_survives :
    ¬DeletionEligible historyThrough236 state152 shift152b := by
  have h := alpha_lt_five_thirds
  rintro ⟨ancestor, hmem, hstate, hshift⟩
  have hfiltered :
      historyThrough236.filter (fun p => p.1 = state152) =
        [(state152, shift152a)] := by
    decide +kernel
  have hmem' : ancestor ∈
      historyThrough236.filter (fun p => p.1 = state152) :=
    List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩
  rw [hfiltered] at hmem'
  simp only [List.mem_singleton] at hmem'
  subst ancestor
  simp only [SymbolicShift.value, shift152a, shift152b] at hshift
  norm_num at hshift
  linarith

def historyThrough152b : List (State5 × SymbolicShift) :=
  historyThrough236 ++ [(state152, shift152b)]

def historyThrough182b : List (State5 × SymbolicShift) :=
  historyThrough152b ++ [(state182, shift182b)]

theorem repeated_182_survives :
    ¬DeletionEligible historyThrough152b state182 shift182b := by
  have h := alpha_lt_five_thirds
  rintro ⟨ancestor, hmem, hstate, hshift⟩
  have hfiltered :
      historyThrough152b.filter (fun p => p.1 = state182) =
        [(state182, shift182a)] := by
    decide +kernel
  have hmem' : ancestor ∈
      historyThrough152b.filter (fun p => p.1 = state182) :=
    List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩
  rw [hfiltered] at hmem'
  simp only [List.mem_singleton] at hmem'
  subst ancestor
  simp only [SymbolicShift.value, shift182a, shift182b] at hshift
  norm_num at hshift
  linarith

/-- The seven initial refinement destinations are genuinely new; the two
later repeated destinations move downward; and the last destination 242 is
new.  Thus every refinement edge followed in the certificate survives the
complete ancestor deletion test. -/
theorem all_followed_branch_steps_survive :
    ¬DeletionEligible [(state161, zero)] state107 shift107 ∧
    ¬DeletionEligible [(state161, zero), (state107, shift107)] state152 shift152a ∧
    ¬DeletionEligible
      [(state161, zero), (state107, shift107), (state152, shift152a)]
      state182 shift182a ∧
    ¬DeletionEligible
      [(state161, zero), (state107, shift107), (state152, shift152a),
        (state182, shift182a)] state80 shift80 ∧
    ¬DeletionEligible
      [(state161, zero), (state107, shift107), (state152, shift152a),
        (state182, shift182a), (state80, shift80)] state134 shift134 ∧
    ¬DeletionEligible
      [(state161, zero), (state107, shift107), (state152, shift152a),
        (state182, shift182a), (state80, shift80), (state134, shift134)]
      state89 shift89 ∧
    ¬DeletionEligible
      [(state161, zero), (state107, shift107), (state152, shift152a),
        (state182, shift182a), (state80, shift80), (state134, shift134),
        (state89, shift89)] state59 shift59 ∧
    ¬DeletionEligible historyThrough236 state152 shift152b ∧
    ¬DeletionEligible historyThrough152b state182 shift182b ∧
    ¬DeletionEligible historyThrough182b state242 shift242 := by
  repeat' apply And.intro
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel
  · exact repeated_152_survives
  · exact repeated_182_survives
  · apply TerminationObstruction.not_deletionEligible_of_new_state
    decide +kernel

/-- The two repeated refinement arrivals at 152 and 182 move downward, so
they survive the ancestor test just like the genuinely new arrivals. -/
theorem repeated_arrivals_move_down :
    shift152b.value < shift152a.value ∧
      shift182b.value < shift182a.value := by
  have h := alpha_lt_five_thirds
  simp only [SymbolicShift.value, shift152a, shift152b, shift182a, shift182b]
  norm_num
  constructor <;> linarith

/-- All three leaves of the final minimum satisfy the printed deletion test. -/
theorem all_three_final_children_deletionEligible :
    DeletionEligible history state80 childShift ∧
    DeletionEligible history state161 childShift ∧
    DeletionEligible history state242 childShift := by
  have h117 := TerminationObstruction.eleven_sevenths_lt_alpha
  have h1611 : (16 : ℝ) / 11 < alpha := by linarith
  have h1 := one_lt_alpha
  constructor
  · refine ⟨(state80, shift80), by simp [history], rfl, ?_⟩
    simp only [SymbolicShift.value, shift80, childShift]
    norm_num
    linarith
  constructor
  · refine ⟨(state161, zero), by simp [history], rfl, ?_⟩
    simp only [SymbolicShift.value, SymbolicShift.zero, childShift]
    norm_num
    linarith
  · refine ⟨(state242, shift242), by simp [history], rfl, ?_⟩
    simp only [SymbolicShift.value, shift242, childShift]
    norm_num
    linarith

/-- Kernel-checked obstruction to the claimed nonempty-minimum invariant. -/
theorem printed_nonempty_minimum_claim_fails :
    ResidueSystem.branch 5 state242 = .advanced ∧
    0 < childShift.value ∧
    (∀ j : Fin 3, DeletionEligible history
      (ResidueSystem.fiber 5 (ResidueSystem.refinementTarget 5 state242) j)
      childShift) := by
  refine ⟨final_targets.1, ?_, ?_⟩
  · have h : (16 : ℝ) / 11 < alpha := by
      linarith [TerminationObstruction.eleven_sevenths_lt_alpha]
    simp only [SymbolicShift.value, childShift]
    norm_num
    linarith
  · intro j
    rw [final_targets.2 j]
    fin_cases j
    · exact all_three_final_children_deletionEligible.1
    · exact all_three_final_children_deletionEligible.2.1
    · exact all_three_final_children_deletionEligible.2.2

end CleanLean.KL.AllThreeDeletionObstruction
