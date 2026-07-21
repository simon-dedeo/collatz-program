/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.LevelLift

/-!
# Ternary traces of the annealed KL operator

The one-step trace sums the three highest-digit lifts.  This file proves that
it intertwines the literal annealed operators on successive concrete residue
systems.  The proof uses the existing `ZMod` residue model throughout; no
second matrix encoding is introduced.
-/

namespace CleanLean.KL

namespace ResidueSystem

open scoped BigOperators

noncomputable section

/-- Sum the three highest-digit lifts of a fine-level vector. -/
def oneStepTrace (k : ℕ) (c : State (k + 1) → ℝ) : State k → ℝ :=
  fun r => ∑ j : Fin 3, c (fiber (k + 1) r j)

@[simp] theorem oneStepTrace_apply (k : ℕ) (c : State (k + 1) → ℝ)
    (r : State k) :
    oneStepTrace k c r = ∑ j : Fin 3, c (fiber (k + 1) r j) := rfl

/-- Tracing preserves total mass. -/
theorem totalMass_oneStepTrace (k : ℕ) (hk : 2 ≤ k)
    (c : State (k + 1) → ℝ) :
    (system k).totalMass (oneStepTrace k c) =
      (system (k + 1)).totalMass c := by
  change (∑ r : State k, ∑ j : Fin 3, c (fiber (k + 1) r j)) =
    ∑ s : State (k + 1), c s
  change (∑ r : Coarse (k + 1), ∑ j : Fin 3,
    c (fiber (k + 1) r j)) = ∑ s : State (k + 1), c s
  calc
    (∑ r : Coarse (k + 1), ∑ j : Fin 3,
        c (fiber (k + 1) r j)) =
        ∑ p : Coarse (k + 1) × Fin 3,
          c (fiber (k + 1) p.1 p.2) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ s : State (k + 1), c s :=
      (fiberEquiv (k + 1) (by omega)).sum_comp c

/-- The coarse coordinate recovered by the top-digit fiber equivalence is
exactly reduction modulo the coarser power of three. -/
theorem fiberEquiv_symm_fst_eq_parent (k : ℕ) (hk : 2 ≤ k)
    (s : State (k + 1)) :
    ((fiberEquiv (k + 1) (by omega)).symm s).1 = parent k s := by
  let p := (fiberEquiv (k + 1) (by omega)).symm s
  have hp : fiber (k + 1) p.1 p.2 = s := by
    exact (fiberEquiv (k + 1) (by omega)).apply_symm_apply s
  calc
    ((fiberEquiv (k + 1) (by omega)).symm s).1 = p.1 := rfl
    _ = parent k (fiber (k + 1) p.1 p.2) := (parent_fiber k p.1 p.2).symm
    _ = parent k s := congrArg (parent k) hp

/-- The analogous recovered coarse coordinate inside a single level. -/
theorem fiberEquiv_symm_fst_eq_coarseParent (k : ℕ) (hk : 2 ≤ k)
    (s : State k) :
    ((fiberEquiv k hk).symm s).1 = coarseParent k s := by
  let p := (fiberEquiv k hk).symm s
  have hp : fiber k p.1 p.2 = s := by
    exact (fiberEquiv k hk).apply_symm_apply s
  have hparentFiber : coarseParent k (fiber k p.1 p.2) = p.1 := by
    change ZMod.cast (fiber k p.1 p.2) = p.1
    have hd := pow_coarse_dvd k
    change ZMod.cast ((p.1.val + p.2.val * 3 ^ (k - 2) : ℕ) : State k) = p.1
    rw [ZMod.cast_natCast hd]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  calc
    ((fiberEquiv k hk).symm s).1 = p.1 := rfl
    _ = coarseParent k (fiber k p.1 p.2) := hparentFiber.symm
    _ = coarseParent k s := congrArg (coarseParent k) hp

/-- An equivalence commuting with `parent` permutes the three top-digit lifts
over every coarse state. -/
theorem sum_equiv_on_fiber
    (k : ℕ) (hk : 2 ≤ k)
    (eFine : State (k + 1) ≃ State (k + 1))
    (eCoarse : State k ≃ State k)
    (hcomm : ∀ s, parent k (eFine s) = eCoarse (parent k s))
    (c : State (k + 1) → ℝ) (r : State k) :
    ∑ j : Fin 3, c (eFine (fiber (k + 1) r j)) =
      ∑ j : Fin 3, c (fiber (k + 1) (eCoarse r) j) := by
  let digit : Fin 3 → Fin 3 := fun j =>
    ((fiberEquiv (k + 1) (by omega)).symm
      (eFine (fiber (k + 1) r j))).2
  have hreconstruct : ∀ j,
      fiber (k + 1) (eCoarse r) (digit j) =
        eFine (fiber (k + 1) r j) := by
    intro j
    have happly := (fiberEquiv (k + 1) (by omega)).apply_symm_apply
      (eFine (fiber (k + 1) r j))
    change fiber (k + 1)
      (((fiberEquiv (k + 1) (by omega)).symm
        (eFine (fiber (k + 1) r j))).1)
      (digit j) = eFine (fiber (k + 1) r j) at happly
    rw [fiberEquiv_symm_fst_eq_parent k hk] at happly
    simpa [hcomm] using happly
  have hdigitInjective : Function.Injective digit := by
    intro i j hij
    apply fiber_injective (k + 1) (by omega) r
    apply eFine.injective
    rw [← hreconstruct i, ← hreconstruct j, hij]
  let digitEquiv : Fin 3 ≃ Fin 3 :=
    Equiv.ofBijective digit
      ((Fintype.bijective_iff_injective_and_card digit).2
        ⟨hdigitInjective, rfl⟩)
  calc
    (∑ j : Fin 3, c (eFine (fiber (k + 1) r j))) =
        ∑ j : Fin 3, c (fiber (k + 1) (eCoarse r) (digitEquiv j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change c (eFine (fiber (k + 1) r j)) =
        c (fiber (k + 1) (eCoarse r) (digit j))
      exact congrArg c (hreconstruct j).symm
    _ = ∑ j : Fin 3, c (fiber (k + 1) (eCoarse r) j) :=
      digitEquiv.sum_comp (fun j => c (fiber (k + 1) (eCoarse r) j))

/-- The transport contribution commutes with the one-step trace. -/
theorem oneStepTrace_transport (k : ℕ) (hk : 2 ≤ k)
    (c : State (k + 1) → ℝ) (r : State k) :
    ∑ j : Fin 3, c (transport (k + 1) (fiber (k + 1) r j)) =
      oneStepTrace k c (transport k r) := by
  exact sum_equiv_on_fiber k hk (transport (k + 1)) (transport k)
    (parent_transport k) c r

/-- High- and low-digit decompositions commute. -/
theorem fiber_lowDigit_swap (k : ℕ) (hk : 2 ≤ k)
    (r : Coarse k) (low high : Fin 3) :
    fiber (k + 1) (lowDigit k r low) high =
      lowDigit (k + 1) (fiber k r high) low := by
  apply ZMod.val_injective _
  rw [fiber_val (k + 1) (by omega), lowDigit_val k hk,
    lowDigit_val (k + 1) (by omega), fiber_val k hk]
  have hpow : 3 ^ (k + 1 - 2) = 3 ^ (k - 1) := by congr 1
  rw [hpow, three_pow_level k hk]
  ring

/-- On a retarded output fiber, the three fine refinement targets are
distinct; multiplication by four merely permutes their middle digits. -/
theorem refinementTarget_fiber_injective_retarded
    (k : ℕ) (hk : 2 ≤ k) (m : State k)
    (hm : branch k m = Branch.retarded) :
    Function.Injective (fun e : Fin 3 =>
      refinementTarget (k + 1) (fiber (k + 1) m e)) := by
  obtain ⟨⟨r, low⟩, hr⟩ := (lowDigitEquiv k hk).surjective m
  change lowDigit k r low = m at hr
  rw [← hr] at hm ⊢
  have hlowVal : low.val = 0 := by
    rw [branch_lowDigit k hk] at hm
    generalize hq : low.val = q at hm
    have hlt : q < 3 := by omega
    interval_cases q <;> simp_all
  have hlow : low = 0 := Fin.ext hlowVal
  subst low
  intro i j hij
  change refinementTarget (k + 1) (fiber (k + 1) (lowDigit k r 0) i) =
    refinementTarget (k + 1) (fiber (k + 1) (lowDigit k r 0) j) at hij
  rw [fiber_lowDigit_swap k hk, fiber_lowDigit_swap k hk,
    refinementTarget_lowDigit_zero (k + 1) (by omega),
    refinementTarget_lowDigit_zero (k + 1) (by omega)] at hij
  have hfiber : fiber k r i = fiber k r j := (coarseMulFour (k + 1)).injective hij
  exact fiber_injective k hk r hfiber

/-- The analogous distinctness on an advanced output fiber. -/
theorem refinementTarget_fiber_injective_advanced
    (k : ℕ) (hk : 2 ≤ k) (m : State k)
    (hm : branch k m = Branch.advanced) :
    Function.Injective (fun e : Fin 3 =>
      refinementTarget (k + 1) (fiber (k + 1) m e)) := by
  obtain ⟨⟨r, low⟩, hr⟩ := (lowDigitEquiv k hk).surjective m
  change lowDigit k r low = m at hr
  rw [← hr] at hm ⊢
  have hlowVal : low.val = 2 := by
    rw [branch_lowDigit k hk] at hm
    generalize hq : low.val = q at hm
    have hlt : q < 3 := by omega
    interval_cases q <;> simp_all
  have hlow : low = 2 := Fin.ext hlowVal
  subst low
  intro i j hij
  change refinementTarget (k + 1) (fiber (k + 1) (lowDigit k r 2) i) =
    refinementTarget (k + 1) (fiber (k + 1) (lowDigit k r 2) j) at hij
  rw [fiber_lowDigit_swap k hk, fiber_lowDigit_swap k hk,
    refinementTarget_lowDigit_two (k + 1) (by omega),
    refinementTarget_lowDigit_two (k + 1) (by omega)] at hij
  have hfiber : fiber k r i = fiber k r j :=
    (coarseAffineTwo (k + 1)).injective hij
  exact fiber_injective k hk r hfiber

/-- Any injective choice of the three fine coarse states lying over one coarse
state enumerates that entire middle-digit fiber.  Averaging the top digit and
then summing this enumeration equals averaging after tracing. -/
theorem sum_fiberAverage_of_targets
    (k : ℕ) (hk : 2 ≤ k)
    (q : Fin 3 → State k) (base : Coarse k)
    (hparent : ∀ e, coarseParent k (q e) = base)
    (hqInjective : Function.Injective q)
    (c : State (k + 1) → ℝ) :
    ∑ e : Fin 3, (system (k + 1)).fiberAverage c (q e) =
      (system k).fiberAverage (oneStepTrace k c) base := by
  let digit : Fin 3 → Fin 3 := fun e =>
    ((fiberEquiv k hk).symm (q e)).2
  have hreconstruct : ∀ e, fiber k base (digit e) = q e := by
    intro e
    have happly := (fiberEquiv k hk).apply_symm_apply (q e)
    change fiber k (((fiberEquiv k hk).symm (q e)).1) (digit e) = q e at happly
    have hfirst : ((fiberEquiv k hk).symm (q e)).1 = coarseParent k (q e) :=
      fiberEquiv_symm_fst_eq_coarseParent k hk (q e)
    rw [hfirst, hparent] at happly
    exact happly
  have hdigitInjective : Function.Injective digit := by
    intro i j hij
    apply hqInjective
    rw [← hreconstruct i, ← hreconstruct j, hij]
  let digitEquiv : Fin 3 ≃ Fin 3 :=
    Equiv.ofBijective digit
      ((Fintype.bijective_iff_injective_and_card digit).2
        ⟨hdigitInjective, rfl⟩)
  change (∑ e : Fin 3,
      (c (fiber (k + 1) (q e) 0) + c (fiber (k + 1) (q e) 1) +
        c (fiber (k + 1) (q e) 2)) / 3) =
    ((oneStepTrace k c) (fiber k base 0) +
      (oneStepTrace k c) (fiber k base 1) +
      (oneStepTrace k c) (fiber k base 2)) / 3
  calc
    (∑ e : Fin 3,
      (c (fiber (k + 1) (q e) 0) + c (fiber (k + 1) (q e) 1) +
        c (fiber (k + 1) (q e) 2)) / 3) =
        ∑ e : Fin 3,
          (c (fiber (k + 1) (fiber k base (digitEquiv e)) 0) +
            c (fiber (k + 1) (fiber k base (digitEquiv e)) 1) +
            c (fiber (k + 1) (fiber k base (digitEquiv e)) 2)) / 3 := by
      apply Finset.sum_congr rfl
      intro e _
      change _ =
        (c (fiber (k + 1) (fiber k base (digit e)) 0) +
          c (fiber (k + 1) (fiber k base (digit e)) 1) +
          c (fiber (k + 1) (fiber k base (digit e)) 2)) / 3
      rw [hreconstruct]
    _ = ∑ i : Fin 3,
          (c (fiber (k + 1) (fiber k base i) 0) +
            c (fiber (k + 1) (fiber k base i) 1) +
            c (fiber (k + 1) (fiber k base i) 2)) / 3 :=
      digitEquiv.sum_comp (fun i =>
        (c (fiber (k + 1) (fiber k base i) 0) +
          c (fiber (k + 1) (fiber k base i) 1) +
          c (fiber (k + 1) (fiber k base i) 2)) / 3)
    _ = ((oneStepTrace k c) (fiber k base 0) +
          (oneStepTrace k c) (fiber k base 1) +
          (oneStepTrace k c) (fiber k base 2)) / 3 := by
      rw [Fin.sum_univ_three]
      simp only [oneStepTrace]
      simp only [Fin.sum_univ_three]
      ring

/-- Retarded branch averages commute with the one-step trace. -/
theorem oneStepTrace_retardedAverage
    (k : ℕ) (hk : 2 ≤ k) (c : State (k + 1) → ℝ) (m : State k)
    (hm : branch k m = Branch.retarded) :
    ∑ e : Fin 3, (system (k + 1)).fiberAverage c
        (refinementTarget (k + 1) (fiber (k + 1) m e)) =
      (system k).fiberAverage (oneStepTrace k c) (refinementTarget k m) := by
  apply sum_fiberAverage_of_targets k hk
  · intro e
    have hfine : branch (k + 1) (fiber (k + 1) m e) = Branch.retarded := by
      rw [← parent_branch k hk, parent_fiber]
      exact hm
    have h := coarseParent_refinementTarget_retarded k hk
      (fiber (k + 1) m e) hfine
    simpa using h
  · exact refinementTarget_fiber_injective_retarded k hk m hm

/-- Advanced branch averages commute with the one-step trace. -/
theorem oneStepTrace_advancedAverage
    (k : ℕ) (hk : 2 ≤ k) (c : State (k + 1) → ℝ) (m : State k)
    (hm : branch k m = Branch.advanced) :
    ∑ e : Fin 3, (system (k + 1)).fiberAverage c
        (refinementTarget (k + 1) (fiber (k + 1) m e)) =
      (system k).fiberAverage (oneStepTrace k c) (refinementTarget k m) := by
  apply sum_fiberAverage_of_targets k hk
  · intro e
    have hfine : branch (k + 1) (fiber (k + 1) m e) = Branch.advanced := by
      rw [← parent_branch k hk, parent_fiber]
      exact hm
    have h := coarseParent_refinementTarget_advanced k hk
      (fiber (k + 1) m e) hfine
    simpa using h
  · exact refinementTarget_fiber_injective_advanced k hk m hm

/-- All-level one-step ternary trace intertwining for the concrete annealed KL
operator. -/
theorem oneStepTrace_annealedOperator
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (c : State (k + 1) → ℝ) :
    oneStepTrace k ((system (k + 1)).annealedOperator w c) =
      (system k).annealedOperator w (oneStepTrace k c) := by
  funext m
  have hbranch : ∀ e : Fin 3,
      branch (k + 1) (fiber (k + 1) m e) = branch k m := by
    intro e
    rw [← parent_branch k hk, parent_fiber]
  have htransport :
      (∑ i : Fin 3, c (transport (k + 1) (fiber (k + 1) m i))) =
        ∑ j : Fin 3, c (fiber (k + 1) (transport k m) j) := by
    simpa [oneStepTrace] using oneStepTrace_transport k hk c m
  cases hm : branch k m with
  | retarded =>
      simp only [oneStepTrace, FiniteSystem.annealedOperator, system,
        hbranch, hm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      exact congrArg₂ (fun x y => w.transport * x + w.retarded * y)
        htransport (oneStepTrace_retardedAverage k hk c m hm)
  | neutral =>
      simp only [oneStepTrace, FiniteSystem.annealedOperator, system,
        hbranch, hm, add_zero]
      rw [← Finset.mul_sum]
      exact congrArg (fun x => w.transport * x) htransport
  | advanced =>
      simp only [oneStepTrace, FiniteSystem.annealedOperator, system,
        hbranch, hm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      exact congrArg₂ (fun x y => w.transport * x + w.advanced * y)
        htransport (oneStepTrace_advancedAverage k hk c m hm)

end

end ResidueSystem

end CleanLean.KL
