/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterStateNoRepeat

/-!
# Gluing bare three-step EC17 replays

This file isolates the construction direction of QM121d.  It has no canonical
residue or pre-existing ray in its hypotheses: compatible positive exact
three-step replays glue to one infinite positive EC17 orbit.
-/

namespace KontoroC
namespace EtherCounterBareGlue

open EtherCounterResidueBound EtherCounterStateNoRepeat

/-- Proof-carrying consecutive three-step replays on a bare branch schedule. -/
structure ThreeReplayChain where
  branch : ℕ → ℕ
  boundary : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  boundary_pos : ∀ q, 0 < boundary q
  replay : ∀ q,
    ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3
  terminal : ∀ q, (replay q).core 3 = boundary (q + 1)

namespace ThreeReplayChain

/-- Select the core in the unique three-step replay cell containing `t`. -/
def core (c : ThreeReplayChain) (t : ℕ) : ℕ :=
  (c.replay (t / 3)).core (t % 3)

theorem core_three_mul (c : ThreeReplayChain) (q : ℕ) :
    c.core (3 * q) = c.boundary q := by
  change (c.replay (3 * q / 3)).core (3 * q % 3) = c.boundary q
  have hdiv : 3 * q / 3 = q := by omega
  have hmod : 3 * q % 3 = 0 := by omega
  rw [hdiv, hmod]
  exact (c.replay q).initial

theorem core_pos (c : ThreeReplayChain) (t : ℕ) : 0 < c.core t := by
  apply (c.replay (t / 3)).core_pos (c.boundary_pos (t / 3))
  exact Nat.le_of_lt (Nat.mod_lt t (by omega))

/-- Consecutive exact cells glue at their common boundary. -/
theorem balance (c : ThreeReplayChain) (t : ℕ) :
    2 ^ binaryExponent c.branch t * c.core (t + 1) =
      3 ^ ternaryExponent c.branch t * c.core t + 17 := by
  generalize hq : t / 3 = q
  generalize hieq : t % 3 = i
  have hi0 : t % 3 < 3 := Nat.mod_lt t (by omega)
  have hi : i < 3 := by simpa only [hieq] using hi0
  have ht : 3 * q + i = t := by
    rw [← hq, ← hieq]
    exact Nat.div_add_mod t 3
  interval_cases i
  · have ht0 : t = 3 * q := by omega
    subst t
    have hdiv0 : 3 * q / 3 = q := by omega
    have hmod0 : 3 * q % 3 = 0 := by omega
    have hdiv1 : (3 * q + 1) / 3 = q := by omega
    have hmod1 : (3 * q + 1) % 3 = 1 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv0, hmod0, hdiv1, hmod1]
    simpa [binaryExponent, ternaryExponent] using
      (c.replay q).balance 0 (by omega)
  · have ht1 : t = 3 * q + 1 := by omega
    subst t
    have hdiv1 : (3 * q + 1) / 3 = q := by omega
    have hmod1 : (3 * q + 1) % 3 = 1 := by omega
    have hdiv2 : (3 * q + 1 + 1) / 3 = q := by omega
    have hmod2 : (3 * q + 1 + 1) % 3 = 2 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv1, hmod1, hdiv2, hmod2]
    simpa [binaryExponent, ternaryExponent] using
      (c.replay q).balance 1 (by omega)
  · have ht2 : t = 3 * q + 2 := by omega
    subst t
    have hlast := (c.replay q).balance 2 (by omega)
    rw [c.terminal q] at hlast
    have hdiv2 : (3 * q + 2) / 3 = q := by omega
    have hmod2 : (3 * q + 2) % 3 = 2 := by omega
    have hdiv3 : (3 * q + 2 + 1) / 3 = q + 1 := by omega
    have hmod3 : (3 * q + 2 + 1) % 3 = 0 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv2, hmod2, hdiv3, hmod3, (c.replay (q + 1)).initial]
    simpa [binaryExponent, ternaryExponent] using hlast

/-- Gluing a chain of positive exact three-step replays produces a literal
infinite positive EC17 orbit. -/
def toOrbit (c : ThreeReplayChain) : EtherCounterStateNoRepeat.Orbit where
  branch := c.branch
  branch_pos := c.branch_pos
  core := c.core
  core_pos := c.core_pos
  balance t := by
    simpa [binaryExponent, ternaryExponent] using c.balance t

end ThreeReplayChain

/-- A three-step compact factor beginning at time `3*q` decodes to a local
replay whose branch is reindexed from zero. -/
theorem exists_shiftedReplay_of_composedFactor
    (branch : ℕ → ℕ) (boundary : ℕ → ℕ) (q : ℕ)
    (hfactor : ComposedReplayFactor branch (3 * q) 3
      (boundary q) (boundary (q + 1))) :
    ∃ replay : ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3,
      replay.core 3 = boundary (q + 1) := by
  have hshift :
      ComposedReplayFactor (fun i => branch (3 * q + i)) 0 3
        (boundary q) (boundary (q + 1)) := by
    simpa [ComposedReplayFactor, replayTernaryMass_shift,
      replayOffset_shift, binaryMass_shift] using hfactor
  exact exactReplayTo_of_composedReplayFactor
    (fun i => branch (3 * q + i)) (boundary q) (boundary (q + 1)) 3 hshift

/-- Bare positive consecutive compact factors are sufficient to construct an
infinite positive EC17 orbit.  This is the gluing endpoint needed after a
zero-carry argument has supplied the factors. -/
theorem exists_orbit_of_composedReplayFactors
    (branch : ℕ → ℕ) (boundary : ℕ → ℕ)
    (hbranch : ∀ t, 0 < branch t)
    (hboundary : ∀ q, 0 < boundary q)
    (hfactor : ∀ q, ComposedReplayFactor branch (3 * q) 3
      (boundary q) (boundary (q + 1))) :
    ∃ g : EtherCounterStateNoRepeat.Orbit,
      g.branch = branch ∧ ∀ q, g.core (3 * q) = boundary q := by
  classical
  have hexists (q : ℕ) :
      ∃ replay : ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3,
        replay.core 3 = boundary (q + 1) :=
    exists_shiftedReplay_of_composedFactor branch boundary q (hfactor q)
  let replay (q : ℕ) := Classical.choose (hexists q)
  have hterminal (q : ℕ) : (replay q).core 3 = boundary (q + 1) :=
    Classical.choose_spec (hexists q)
  let chain : ThreeReplayChain := {
    branch := branch
    boundary := boundary
    branch_pos := hbranch
    boundary_pos := hboundary
    replay := replay
    terminal := hterminal
  }
  refine ⟨chain.toOrbit, rfl, ?_⟩
  intro q
  exact chain.core_three_mul q

end EtherCounterBareGlue
end KontoroC
