/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteSubcodeCarry

/-!
# Carry-policy potentials imply an ordinary infinite execution

This file is the exact consumer for the finite Bellman-potential CEGIS run.
The numerical worker searches for a potential `V` such that every reachable
prefix has at least one legal next word satisfying

`extensionCarry pre w + V (pre ++ [w]) <= V pre`.

If that inequality is proved for all prefixes, with a natural-valued
potential, it telescopes to a uniform bound on total extension carry.  The
existing finite-alphabet compactness theorem then supplies one coherent
ordinary execution, and the first-passage consumer refutes the Collatz
conjecture conditionally on the certificate.

The PSC fits are finite evidence only: this file does not assert that any of
their feature formulas satisfies the all-prefix premise.
-/

namespace KontoroC
namespace OutwardCarryPolicyPotential

open OutwardCodeCompactness OutwardFirstPassage
open OutwardFiniteSubcodeCarry

noncomputable section

/-- An exact policy potential: at every reachable finite-subcode prefix,
some legal extension pays its natural carry out of the potential decrease. -/
def PolicyPotential (F : Finset (List Bool))
    (V : List (List Bool) -> Nat) : Prop :=
  forall pre, WordsIn (F : Set (List Bool)) pre ->
    exists w, w ∈ F ∧
      extensionCarry pre w + V (pre ++ [w]) <= V pre

/-- A policy-potential inequality telescopes along an actual legal suffix of
every requested length. -/
theorem exists_suffix_with_carry_add_potential_le
    (F : Finset (List Bool)) (V : List (List Bool) -> Nat)
    (hV : PolicyPotential F V)
    (pre : List (List Bool))
    (hpre : WordsIn (F : Set (List Bool)) pre) (n : Nat) :
    exists suffix : List (List Bool),
      suffix.length = n ∧
      WordsIn (F : Set (List Bool)) suffix ∧
      carrySumFrom pre suffix + V (pre ++ suffix) <= V pre := by
  induction n generalizing pre with
  | zero =>
      exact ⟨[], rfl, by simp [WordsIn], by simp [carrySumFrom]⟩
  | succ n ih =>
      obtain ⟨w, hw, hstep⟩ := hV pre hpre
      have hpre' : WordsIn (F : Set (List Bool)) (pre ++ [w]) := by
        intro v hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hpre v hv
        · exact hw
      obtain ⟨suffix, hlength, hwords, htail⟩ :=
        ih (pre ++ [w]) hpre'
      refine ⟨w :: suffix, by simp [hlength], ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hw
        · exact hwords v hv
      · simp only [carrySumFrom]
        have happ : pre ++ (w :: suffix) = (pre ++ [w]) ++ suffix := by
          simp [List.append_assoc]
        rw [happ]
        omega

/-- The initial potential is a uniform bound for finite schedules of every
depth.  This is the theorem-shaped promotion gate for the B2 search. -/
theorem uniformCarryBudget_of_policyPotential
    (F : Finset (List Bool)) (V : List (List Bool) -> Nat)
    (hV : PolicyPotential F V) :
    forall n, exists u : List (List Bool),
      u.length = n ∧
      WordsIn (F : Set (List Bool)) u ∧
      carrySum u <= V [] := by
  intro n
  obtain ⟨u, hlength, hwords, hbound⟩ :=
    exists_suffix_with_carry_add_potential_le F V hV []
      (by simp [WordsIn]) n
  refine ⟨u, hlength, hwords, ?_⟩
  have : carrySum u + V u <= V [] := by
    simpa [carrySum] using hbound
  omega

/-- A global policy potential reaches the already-checked eventual-zero-carry
normal form after one finite prefix. -/
theorem exists_zeroCarryTail_of_policyPotential
    (F : Finset (List Bool)) (V : List (List Bool) -> Nat)
    (hV : PolicyPotential F V) :
    exists pre : List (List Bool),
      WordsIn (F : Set (List Bool)) pre ∧
      forall r, exists suffix : List (List Bool),
        suffix.length = r ∧
        WordsIn (F : Set (List Bool)) suffix ∧
        carrySumFrom pre suffix = 0 := by
  apply (uniformCarryBudget_iff_exists_zeroCarryTail F).1
  exact ⟨V [], uniformCarryBudget_of_policyPotential F V hV⟩

/-- For a finite first-passage subcode, an all-prefix policy potential gives
one ordinary positive infinite execution. -/
theorem exists_infiniteExecution_of_policyPotential
    (F : Finset (List Bool))
    (hfirst : forall w, w ∈ F -> FirstPassage w)
    (V : List (List Bool) -> Nat)
    (hV : PolicyPotential F V) :
    exists start, InfiniteExecution (F : Set (List Bool)) start := by
  apply (infiniteExecution_iff_uniformCarryBudget F hfirst).2
  exact ⟨V [], uniformCarryBudget_of_policyPotential F V hV⟩

/-- Fully composed conditional endpoint: proving one global B2-style policy
potential for a finite outward first-passage code refutes Collatz. -/
theorem not_conjecture_of_policyPotential
    (F : Finset (List Bool))
    (hfirst : forall w, w ∈ F -> FirstPassage w)
    (V : List (List Bool) -> Nat)
    (hV : PolicyPotential F V) :
    ¬ CleanLean.Collatz.Conjecture := by
  exact OutwardFiniteSubcodeCarry.not_conjecture_of_uniformCarryBudget
    F hfirst (uniformCarryBudget_of_policyPotential F V hV)

end

end OutwardCarryPolicyPotential
end KontoroC
