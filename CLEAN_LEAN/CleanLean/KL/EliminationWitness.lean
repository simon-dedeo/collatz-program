/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ConcreteElimination

/-!
# The exact interface required from KL advanced-term elimination

This file isolates the remaining content of Krasikov--Lagarias Theorems 3.1,
3.2, and 4.1.  A `RetardedEliminationWitness` is a finite family of labelled
trees with four properties:

* every leaf is delayed by a common positive amount and by at most two;
* the trees give valid functional difference inequalities;
* their exponential coefficient inequalities follow from finite KL
  feasibility.

Once such a witness exists, the already formalized retarded comparison
theorem gives the exact `1 / (4*C)` lower bound.  Thus termination, preservation
of the critical-path invariant under deletion, and LP bookkeeping cannot be
quietly replaced by a cleaner assumption: they must together construct this
concrete object.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree

/-- A completed, finite KL advanced-term elimination at precision `k`.

The common lag `mu` is stored explicitly.  Finiteness of the residue state
space would allow one to take the minimum of separate positive leaf lags, but
putting it in the interface makes the exact output required of a recursive
construction transparent. -/
structure RetardedEliminationWitness (k : ℕ) where
  tree : ResidueSystem.State k → EliminationTree (ResidueSystem.State k)
  mu : ℝ
  mu_pos : 0 < mu
  lag_bounds : ∀ state, (eraseToRetarded (tree state)).LagsIn mu 2
  functional_sound : ∀ (phi : ResidueSystem.State k → ℝ → ℝ),
    SatisfiesBaseSystem k phi → ∀ state y, 2 ≤ y →
      (tree state).eval phi y ≤ phi state y
  coefficient_sound : ∀ (c : ResidueSystem.State k → ℝ) (lam : ℝ),
    0 < lam →
    (ResidueSystem.system k).Feasible (klWeights lam) c → ∀ state,
      c state ≤ (eraseToRetarded (tree state)).coeffEval c lam

/-- The full KL Theorem-2.2 comparison conclusion follows from a completed
elimination witness.  This theorem composes the concrete labelled-tree
interface with the kernel-checked retarded comparison theorem; no numerical
or spectral assertion is involved. -/
theorem quarter_lower_bound_of_retardedElimination
    (W : RetardedEliminationWitness k)
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
  apply RetardedExpr.quarter_exponential_lower_bound_of_retarded
    (fun state => eraseToRetarded (W.tree state)) phi c
      lam W.mu 2 1 C hlam1 hlam2 W.mu_pos (by norm_num) (by norm_num)
      (by norm_num) hC
  · intro state
    exact zero_le_one.trans (hfeasible.1 state)
  · exact hcC
  · exact hphi0
  · exact hmono
  · exact W.lag_bounds
  · intro state y hy
    rw [eval_eraseToRetarded]
    exact W.functional_sound phi hbase state y hy
  · exact W.coefficient_sound c lam (zero_lt_one.trans hlam1) hfeasible

/-- At a non-advanced residue, the original unsplit KL right-hand side is
already fully retarded.  This confirms that the recursive construction only
has substantive work to do on the advanced (`8 mod 9`) rows. -/
theorem baseBody_allLeaves_retarded_of_not_advanced
    (k : ℕ) (state : ResidueSystem.State k)
    (hbranch : (ResidueSystem.system k).branch state ≠ Branch.advanced) :
    (baseBody k state).AllLeaves (fun label => label.shift < 0) := by
  generalize hb : (ResidueSystem.system k).branch state = branch
  cases branch with
  | retarded =>
      simp [baseBody, splitBody, transportLeaf, branchMinimum, branchLeaf,
        branchLabel, inf3, hb, EliminationTree.AllLeaves, alpha_lt_two]
  | neutral =>
      simp [baseBody, splitBody, transportLeaf, hb,
        EliminationTree.AllLeaves]
  | advanced => exact (hbranch hb).elim

end ConcreteElimination

end CleanLean.KL
