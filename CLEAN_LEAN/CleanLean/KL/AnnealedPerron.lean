/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.AnnealedIrreducible
import CleanLean.KL.KLWeights
import CleanLean.KL.TerminalPearson

/-!
# Exact low-level laws of the annealed endpoint

This file checks, inside the concrete residue model, the first two normalized
right eigenvectors of the annealed operator at `lambda = 2`, their trace
compatibility, and the first terminal-variation floor.
-/

namespace CleanLean.KL

namespace ResidueSystem

open scoped BigOperators

noncomputable section

/-- KL weights at the annealed endpoint, before the fiber average contributes
its factor `1/3`. -/
def annealedEndpointWeights : Weights ℝ where
  transport := 1 / 4
  retarded := 3 / 4
  advanced := 3 / 2

theorem klWeights_two_eq_annealedEndpointWeights :
    klWeights 2 = annealedEndpointWeights := by
  change (Weights.mk ((2 : ℝ) ^ (-2 : ℝ))
    ((2 : ℝ) ^ (alpha - 2)) ((2 : ℝ) ^ (alpha - 1))) =
      Weights.mk (1 / 4) (3 / 4) (3 / 2)
  rw [Weights.mk.injEq]
  constructor
  · change (2 : ℝ) ^ (-2 : ℝ) = 1 / 4
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [Real.rpow_natCast]
  · constructor
    · change (2 : ℝ) ^ (alpha - 2) = 3 / 4
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), two_rpow_alpha]
      norm_num only [Real.rpow_natCast]
    · change (2 : ℝ) ^ (alpha - 1) = 3 / 2
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), two_rpow_alpha,
        Real.rpow_one]

/-- Exact normalized endpoint law at level two, in coordinate order
`s = 0,1,2`, corresponding to paper residues `2,5,8`. -/
def annealedR2 (s : State 2) : ℝ :=
  match s.val with
  | 0 => 8 / 21
  | 1 => 2 / 21
  | _ => 11 / 21

/-- Numerators of the exact normalized endpoint law at level three. -/
def annealedR3Numerator (n : ℕ) : ℕ :=
  match n with
  | 0 => 9632
  | 1 => 4316
  | 2 => 5240
  | 3 => 6392
  | 4 => 2408
  | 5 => 17246
  | 6 => 17264
  | 7 => 1598
  | _ => 23285

/-- Exact normalized endpoint law at level three, in increasing residue
coordinate order. -/
def annealedR3 (s : State 3) : ℝ :=
  annealedR3Numerator s.val / 87381

private theorem transport_val (k : ℕ) (s : State k) :
    (transport k s).val = (4 * s.val + 2) % (3 ^ (k - 1)) := by
  calc
    (transport k s).val = (4 * s + 2).val :=
      congrArg ZMod.val (transport_apply k s)
    _ = (((4 * s.val + 2 : ℕ) : State k)).val := by
      congr 1
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
      norm_num
    _ = (4 * s.val + 2) % (3 ^ (k - 1)) := ZMod.val_natCast _ _

private theorem coarse_two_eq_zero (r : Coarse 2) : r = 0 :=
  by
    apply ZMod.val_injective _
    have h := ZMod.val_lt r
    have hv : r.val = 0 := by omega
    rw [hv]
    norm_num

/-- Concrete application formula, kept separate so the low-level exact checks
do not have to unfold the equivalence implementation hidden in `system`. -/
private theorem annealedOperator_apply_residue (k : ℕ) (w : Weights ℝ)
    (c : State k → ℝ) (m : State k) :
    (system k).annealedOperator w c m =
      w.transport * c (transport k m) +
        match branch k m with
        | Branch.retarded =>
            w.retarded *
              ((c (fiber k (refinementTarget k m) 0) +
                c (fiber k (refinementTarget k m) 1) +
                c (fiber k (refinementTarget k m) 2)) / 3)
        | Branch.neutral => 0
        | Branch.advanced =>
            w.advanced *
              ((c (fiber k (refinementTarget k m) 0) +
                c (fiber k (refinementTarget k m) 1) +
                c (fiber k (refinementTarget k m) 2)) / 3) :=
  rfl

/-- The displayed level-two law is fixed by the literal annealed endpoint
operator. -/
theorem annealedR2_eigen :
    (system 2).annealedOperator annealedEndpointWeights annealedR2 =
      annealedR2 := by
  change (fun s : State 2 =>
    (system 2).annealedOperator annealedEndpointWeights annealedR2 s) = annealedR2
  funext s
  have hlt := ZMod.val_lt s
  interval_cases hval : s.val <;>
    rw [← ZMod.natCast_zmod_val s, hval] <;>
    rw [annealedOperator_apply_residue] <;>
    simp only [annealedR2, transport_val] <;>
    simp [annealedEndpointWeights, branch, refinementTarget, retardedTarget,
      advancedTarget, fiber, ZMod.val_ofNat, ZMod.val_one_eq_one_mod] <;>
    norm_num

/-- The displayed level-three law is fixed by the same literal annealed
endpoint operator. -/
theorem annealedR3_eigen :
    (system 3).annealedOperator annealedEndpointWeights annealedR3 =
      annealedR3 := by
  change (fun s : State 3 =>
    (system 3).annealedOperator annealedEndpointWeights annealedR3 s) = annealedR3
  funext s
  have hlt := ZMod.val_lt s
  interval_cases hval : s.val <;>
    rw [← ZMod.natCast_zmod_val s, hval] <;>
    rw [annealedOperator_apply_residue] <;>
    simp only [annealedR3, transport_val] <;>
    simp [annealedEndpointWeights, annealedR3Numerator,
      branch, refinementTarget, retardedTarget,
      advancedTarget, fiber, ZMod.val_ofNat, ZMod.val_one_eq_one_mod] <;>
    norm_num

/-- The level-two law has total mass one. -/
theorem annealedR2_normalized : (system 2).totalMass annealedR2 = 1 := by
  change (∑ s : State 2, annealedR2 s) = 1
  rw [← (lowDigitEquiv 2 (by omega)).sum_comp annealedR2]
  change (∑ p : Coarse 2 × Fin 3, annealedR2 (lowDigit 2 p.1 p.2)) = 1
  rw [Fintype.sum_prod_type]
  have hsingle : ∀ r : Coarse 2, r = 0 := coarse_two_eq_zero
  simp_rw [hsingle]
  simp only [Fin.sum_univ_three]
  simp [annealedR2, lowDigit, ZMod.val_ofNat,
    ZMod.val_one_eq_one_mod]
  all_goals norm_num

/-- The exact level-three law projects to the exact level-two law. -/
theorem annealedR3_trace : oneStepTrace 2 annealedR3 = annealedR2 := by
  funext s
  have hlt := ZMod.val_lt s
  interval_cases hval : s.val <;>
    rw [← ZMod.natCast_zmod_val s, hval] <;>
    simp only [oneStepTrace, Fin.sum_univ_three] <;>
    simp [annealedR2, annealedR3, annealedR3Numerator,
      fiber, ZMod.val_ofNat, ZMod.val_one_eq_one_mod] <;> norm_num

/-- The level-three law has total mass one. -/
theorem annealedR3_normalized : (system 3).totalMass annealedR3 = 1 := by
  rw [← annealedR2_normalized, ← annealedR3_trace]
  exact (totalMass_oneStepTrace 2 (by omega) annealedR3).symm

/-- The first terminal `L¹` variation floor is the exact rational
`622/1533`. -/
theorem annealedR3_terminalVariation :
    (system 3).normalizedTerminalVariation annealedR3 = 622 / 1533 := by
  change (system 3).terminalVariationMass annealedR3 /
    (system 3).totalMass annealedR3 = 622 / 1533
  rw [annealedR3_normalized, div_one]
  change (∑ r : Coarse 3,
    ternaryVariation ((system 3).fiberProfile annealedR3 r)) = 622 / 1533
  rw [← (lowDigitEquiv 2 (by omega)).sum_comp (fun r : Coarse 3 =>
    ternaryVariation ((system 3).fiberProfile annealedR3 r))]
  change (∑ p : Coarse 2 × Fin 3,
    ternaryVariation ((system 3).fiberProfile annealedR3
      (lowDigit 2 p.1 p.2))) = 622 / 1533
  rw [Fintype.sum_prod_type]
  have hsingle : ∀ q : Coarse 2, q = 0 := coarse_two_eq_zero
  simp_rw [hsingle]
  simp only [Fin.sum_univ_three]
  simp [ternaryVariation, mean3, FiniteSystem.fiberProfile, system,
    annealedR3, annealedR3Numerator, fiber, lowDigit,
    ZMod.val_ofNat, ZMod.val_one_eq_one_mod]
  all_goals norm_num

/-- The exact floor already exceeds the proposed geometric envelope value. -/
theorem annealedR3_terminalVariation_gt :
    (81 / 200 : ℝ) < (system 3).normalizedTerminalVariation annealedR3 := by
  rw [annealedR3_terminalVariation]
  norm_num

/-- At the endpoint, a strictly positive normalized annealed fixed vector is
unique at every level. -/
theorem annealedEndpoint_fixedVector_unique
    (k : ℕ) (hk : 1 ≤ k) {x y : State k → ℝ}
    (hxpos : ∀ q, 0 < x q) (hypos : ∀ q, 0 < y q)
    (hxfixed : (system k).annealedOperator annealedEndpointWeights x = x)
    (hyfixed : (system k).annealedOperator annealedEndpointWeights y = y)
    (hxmass : (system k).totalMass x = 1)
    (hymass : (system k).totalMass y = 1) :
    x = y := by
  apply annealed_fixedVector_unique k hk annealedEndpointWeights
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · exact hxpos
  · exact hypos
  · exact hxfixed
  · exact hyfixed
  · exact hxmass
  · exact hymass

/-- Preferred endpoint interface: normalization and nonnegativity already
force strict positivity, hence uniqueness. -/
theorem annealedEndpoint_fixedVector_unique_nonnegative
    (k : ℕ) (hk : 1 ≤ k) {x y : State k → ℝ}
    (hx : ∀ q, 0 ≤ x q) (hy : ∀ q, 0 ≤ y q)
    (hxfixed : (system k).annealedOperator annealedEndpointWeights x = x)
    (hyfixed : (system k).annealedOperator annealedEndpointWeights y = y)
    (hxmass : (system k).totalMass x = 1)
    (hymass : (system k).totalMass y = 1) :
    x = y := by
  apply annealed_fixedVector_unique_nonnegative
    k hk annealedEndpointWeights
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · exact hx
  · exact hy
  · exact hxfixed
  · exact hyfixed
  · exact hxmass
  · exact hymass

theorem annealedR2_pos (q : State 2) : 0 < annealedR2 q := by
  have hlt := ZMod.val_lt q
  interval_cases hval : q.val <;> simp [annealedR2, hval]

theorem annealedR3_pos (q : State 3) : 0 < annealedR3 q := by
  have hlt := ZMod.val_lt q
  interval_cases hval : q.val <;>
    simp [annealedR3, annealedR3Numerator, hval]

/-- Every normalized nonnegative level-two endpoint fixed vector is the
displayed rational law. -/
theorem annealedR2_eq_of_nonnegative_fixed
    {c : State 2 → ℝ} (hc : ∀ q, 0 ≤ c q)
    (hfixed :
      (system 2).annealedOperator annealedEndpointWeights c = c)
    (hmass : (system 2).totalMass c = 1) :
    c = annealedR2 := by
  apply annealedEndpoint_fixedVector_unique_nonnegative 2 (by omega)
  · exact hc
  · exact fun q => (annealedR2_pos q).le
  · exact hfixed
  · exact annealedR2_eigen
  · exact hmass
  · exact annealedR2_normalized

/-- Every normalized nonnegative level-three endpoint fixed vector is the
displayed rational law. -/
theorem annealedR3_eq_of_nonnegative_fixed
    {c : State 3 → ℝ} (hc : ∀ q, 0 ≤ c q)
    (hfixed :
      (system 3).annealedOperator annealedEndpointWeights c = c)
    (hmass : (system 3).totalMass c = 1) :
    c = annealedR3 := by
  apply annealedEndpoint_fixedVector_unique_nonnegative 3 (by omega)
  · exact hc
  · exact fun q => (annealedR3_pos q).le
  · exact hfixed
  · exact annealedR3_eigen
  · exact hmass
  · exact annealedR3_normalized

/-- Consequently, normalized positive endpoint laws are projectively
consistent under the one-step trace. -/
theorem annealedEndpoint_oneStepTrace_fixedVector_eq
    (k : ℕ) (hk : 2 ≤ k)
    {fine : State (k + 1) → ℝ} {coarse : State k → ℝ}
    (hfinePos : ∀ q, 0 < fine q) (hcoarsePos : ∀ q, 0 < coarse q)
    (hfineFixed :
      (system (k + 1)).annealedOperator annealedEndpointWeights fine = fine)
    (hcoarseFixed :
      (system k).annealedOperator annealedEndpointWeights coarse = coarse)
    (hfineMass : (system (k + 1)).totalMass fine = 1)
    (hcoarseMass : (system k).totalMass coarse = 1) :
    oneStepTrace k fine = coarse := by
  apply oneStepTrace_fixedVector_eq k hk annealedEndpointWeights
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · norm_num [annealedEndpointWeights]
  · exact hfinePos
  · exact hcoarsePos
  · exact hfineFixed
  · exact hcoarseFixed
  · exact hfineMass
  · exact hcoarseMass

end

end ResidueSystem

end CleanLean.KL
