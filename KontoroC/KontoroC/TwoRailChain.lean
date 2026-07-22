/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.TwoRailGate

/-!
# Compositional finite two-rail certificates

This module is the finite-artifact counterpart of `InfiniteTwoRailProgram`.
A verifier checks each gate's two affine balances and the sparse endpoint
linkage, then obtains one theorem for the entire ordinary Collatz trajectory.
The represented seed and payloads may have arbitrarily many digits.
-/

namespace KontoroC

/-- Flatten a list of certified gates into its compressed valuation word. -/
def twoRailChainWord : List TwoRailGate → List ℕ
  | [] => []
  | g :: gs => g.word ++ twoRailChainWord gs

/-- The endpoint obtained by following a finite list of sparse gates. -/
def twoRailChainEndpoint : ℕ → List TwoRailGate → ℕ
  | x, [] => x
  | _, g :: gs => twoRailChainEndpoint g.endpoint gs

/-- Exact sparse linkage of a finite gate list from the supplied state. -/
def TwoRailChainLegal : ℕ → List TwoRailGate → Prop
  | _, [] => True
  | x, g :: gs => x = g.start ∧ TwoRailChainLegal g.endpoint gs

/-- Every gate in a finite chain is outward. -/
def TwoRailChainOutward (gs : List TwoRailGate) : Prop :=
  ∀ g ∈ gs, g.start < g.endpoint

/-- Composition theorem: checking each constant-size gate and each sparse
link proves all exact valuations and the endpoint of the complete chain. -/
theorem twoRailChain_legal_and_endpoint {x : ℕ} {gs : List TwoRailGate}
    (hchain : TwoRailChainLegal x gs) :
    WordLegal x (twoRailChainWord gs) ∧
      runWord x (twoRailChainWord gs) = twoRailChainEndpoint x gs := by
  induction gs generalizing x with
  | nil => simp [twoRailChainWord, twoRailChainEndpoint, WordLegal]
  | cons g gs ih =>
      have hx : x = g.start := hchain.1
      have htail : TwoRailChainLegal g.endpoint gs := hchain.2
      have hg := g.legal_and_endpoint
      have ht := ih htail
      simp only [twoRailChainWord, twoRailChainEndpoint]
      rw [wordLegal_append_iff, runWord_append, hx]
      constructor
      · exact ⟨hg.1, by simpa [hg.2] using ht.1⟩
      · rw [hg.2]
        exact ht.2

/-- The compressed finite certificate transports to the faithful ordinary
Collatz map for exactly its certified duration. -/
theorem twoRailChain_ordinary_iterate {x : ℕ} {gs : List TwoRailGate}
    (hchain : TwoRailChainLegal x gs) :
    CleanLean.Collatz.step^[ordinaryDuration (twoRailChainWord gs)] x =
      twoRailChainEndpoint x gs := by
  have h := twoRailChain_legal_and_endpoint hchain
  exact (step_iterate_ordinaryDuration h.1).trans h.2

/-- A nonempty chain of outward gates strictly increases its initial state. -/
theorem twoRailChain_strictly_grows {x : ℕ} {g : TwoRailGate}
    {gs : List TwoRailGate}
    (hchain : TwoRailChainLegal x (g :: gs))
    (hout : TwoRailChainOutward (g :: gs)) :
    x < twoRailChainEndpoint x (g :: gs) := by
  induction gs generalizing x g with
  | nil =>
      simpa [twoRailChainEndpoint, hchain.1] using hout g (by simp)
  | cons h hs ih =>
      have hx : x = g.start := hchain.1
      have hfirst : x < g.endpoint := by
        rw [hx]
        exact hout g (by simp)
      have htailChain : TwoRailChainLegal g.endpoint (h :: hs) := hchain.2
      have htailOut : TwoRailChainOutward (h :: hs) := by
        intro q hq
        exact hout q (by simp [hq])
      have htail := ih htailChain htailOut
      simp only [twoRailChainEndpoint]
      exact hfirst.trans htail

/-- If a finite gate chain closes at a positive odd seed other than `1`, its
compact certificate is a literal disproof of Collatz.  The size of the seed is
irrelevant to the theorem. -/
theorem not_conjecture_of_closed_twoRailChain {x : ℕ} {g : TwoRailGate}
    {gs : List TwoRailGate}
    (hchain : TwoRailChainLegal x (g :: gs))
    (hclose : twoRailChainEndpoint x (g :: gs) = x)
    (hne : x ≠ 1) : ¬CleanLean.Collatz.Conjecture := by
  have h := twoRailChain_legal_and_endpoint hchain
  apply not_conjecture_of_legal_cycle
    (ks := twoRailChainWord (g :: gs))
  · simp [twoRailChainWord, TwoRailGate.word]
  · exact h.1
  · exact h.2.trans hclose
  · exact hne

end KontoroC
