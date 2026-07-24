/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardIntegralPrincipality
import KontoroC.OutwardInvariantBridge
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite ranked layers with literal counter resets

A useful finite architecture separates two jobs.  Inside each finite counter
layer, a deterministic selector strictly decreases a certified rank until it
reaches a distinguished minimum.  At that minimum, one literal first-passage
macro resets into the next layer.

The first theorem below proves the sharp finite bound: every starting state
reaches the minimum in fewer than the number of states in its layer.  The
proof is a pigeonhole argument on the iterated orbit; a repeated state would
contradict strict rank descent.

The second part connects such tables to the existing invariant bridge.  It
also records an important logical simplification: once every nonminimum edge
and every minimum reset is already a literal `RechargeMacro`, closure alone
proves an infinite first-passage execution.  The rank is not needed for that
soundness implication; it is a finite search certificate explaining why a
deterministic interior policy actually consumes the layer and reaches its
reset.

All counterexample conclusions are conditional.  This file constructs no
concrete layer family, reset, or ordinary seed.
-/

namespace KontoroC
namespace OutwardRankedLayerReset

open OutwardInvariantBridge OutwardCodeCompactness OutwardFirstPassage
  OutwardCodeCounterexample
open CleanLean.Collatz

variable {State : Type*}

/-- Exact finite ranked-layer data.  The transition need only descend away
from the distinguished minimum; its value at the minimum is irrelevant. -/
def IsRankedLayer (states : Finset State) (minimum : State)
    (next : State → State) (rank : State → ℤ) : Prop :=
  minimum ∈ states ∧
    ∀ state ∈ states, state ≠ minimum →
      next state ∈ states ∧ rank (next state) < rank state

/-- Every orbit in a finite ranked layer reaches its distinguished minimum
in at most `states.card - 1` transitions, expressed without truncated
subtraction as `steps < states.card`. -/
theorem exists_iterate_eq_minimum_lt_card
    (states : Finset State) (minimum : State)
    (next : State → State) (rank : State → ℤ)
    (hlayer : IsRankedLayer states minimum next rank)
    {start : State} (hstart : start ∈ states) :
    ∃ steps < states.card, (next^[steps]) start = minimum := by
  classical
  by_contra hno
  have hnever : ∀ steps, steps < states.card →
      (next^[steps]) start ≠ minimum := by
    intro steps hsteps heq
    exact hno ⟨steps, hsteps, heq⟩
  have horbitMem : ∀ steps, steps ≤ states.card →
      (next^[steps]) start ∈ states := by
    intro steps hsteps
    induction steps with
    | zero => simpa using hstart
    | succ steps ih =>
        rw [Function.iterate_succ_apply']
        exact (hlayer.2 _ (ih (by omega)) (hnever steps (by omega))).1
  let orbit : Fin (states.card + 1) → {state // state ∈ states} :=
    fun i ↦ ⟨(next^[i.1]) start, horbitMem i.1 (by omega)⟩
  have horbitRankStrict :
      StrictAnti (fun i : Fin (states.card + 1) ↦
        rank ((next^[i.1]) start)) := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hstep := (hlayer.2 _
      (horbitMem i.1 (by omega)) (hnever i.1 (by omega))).2
    simpa [Function.iterate_succ_apply'] using hstep
  have horbitInjective : Function.Injective orbit := by
    intro i j hij
    apply horbitRankStrict.injective
    exact congrArg (fun state : {state // state ∈ states} ↦ rank state.1) hij
  have hcard := Fintype.card_le_of_injective orbit horbitInjective
  simp at hcard

/-- The union of all finite counter layers. -/
def LayerInvariant (layers : ℕ → Finset ℕ) (H : ℕ) : Prop :=
  ∃ counter, H ∈ layers counter

/-- Exact literal closure of a layer family.  Interior states take one
certified same-layer macro; each distinguished minimum takes one certified
macro into the next layer. -/
theorem layerInvariant_closed
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ)
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words) :
    ∀ H, LayerInvariant layers H →
      ∃ H' words,
        RechargeMacro H H' words ∧ LayerInvariant layers H' := by
  intro H hH
  obtain ⟨counter, hHmem⟩ := hH
  by_cases hminimum : H = minimum counter
  · subst H
    obtain ⟨H', words, hH'mem, hmacro⟩ := hreset counter
    exact ⟨H', words, hmacro, counter + 1, hH'mem⟩
  · obtain ⟨hnextMem, words, hmacro⟩ :=
      hinterior counter H hHmem hminimum
    exact ⟨next counter H, words, hmacro, counter, hnextMem⟩

/-- Every layer in a ranked family satisfies the sharp minimum-reaching
bound. -/
theorem rankedLayers_reach_minimum
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ) (rank : ℕ → ℕ → ℤ)
    (hranked : ∀ counter,
      IsRankedLayer (layers counter) (minimum counter)
        (next counter) (rank counter)) :
    ∀ counter H, H ∈ layers counter →
      ∃ steps < (layers counter).card,
        ((next counter)^[steps]) H = minimum counter := by
  intro counter H hH
  exact exists_iterate_eq_minimum_lt_card
    (layers counter) (minimum counter) (next counter) (rank counter)
    (hranked counter) hH

/-- Literal interior closure plus literal minimum resets are already enough
for an infinite first-passage execution; no rank premise is needed for this
soundness implication. -/
theorem literalLayers_give_infiniteExecution
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ)
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words)
    (counter₀ H₀ : ℕ) (hH₀pos : 0 < H₀)
    (hH₀mem : H₀ ∈ layers counter₀) :
    InfiniteExecution OutwardOddSlice.FirstPassageCode (3 * H₀ - 1) := by
  apply invariant_gives_infiniteExecution
    (LayerInvariant layers) H₀ hH₀pos
  · exact ⟨counter₀, hH₀mem⟩
  · exact layerInvariant_closed layers minimum next hinterior hreset

/-- The full ranked architecture yields both advertised facts: every finite
interior policy reaches its reset in the cardinality bound, and the literal
layer union supplies an infinite first-passage execution. -/
theorem rankedLayers_reach_minimum_and_give_infiniteExecution
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ) (rank : ℕ → ℕ → ℤ)
    (hranked : ∀ counter,
      IsRankedLayer (layers counter) (minimum counter)
        (next counter) (rank counter))
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words)
    (counter₀ H₀ : ℕ) (hH₀pos : 0 < H₀)
    (hH₀mem : H₀ ∈ layers counter₀) :
    (∀ counter H, H ∈ layers counter →
      ∃ steps < (layers counter).card,
        ((next counter)^[steps]) H = minimum counter) ∧
      InfiniteExecution OutwardOddSlice.FirstPassageCode
        (3 * H₀ - 1) := by
  exact ⟨rankedLayers_reach_minimum layers minimum next rank hranked,
    literalLayers_give_infiniteExecution layers minimum next
      hinterior hreset counter₀ H₀ hH₀pos hH₀mem⟩

/-- Projection of the preceding paired theorem to infinite execution. -/
theorem rankedLayers_give_infiniteExecution
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ) (rank : ℕ → ℕ → ℤ)
    (hranked : ∀ counter,
      IsRankedLayer (layers counter) (minimum counter)
        (next counter) (rank counter))
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words)
    (counter₀ H₀ : ℕ) (hH₀pos : 0 < H₀)
    (hH₀mem : H₀ ∈ layers counter₀) :
    InfiniteExecution OutwardOddSlice.FirstPassageCode (3 * H₀ - 1) :=
  (rankedLayers_reach_minimum_and_give_infiniteExecution
    layers minimum next rank hranked hinterior hreset
    counter₀ H₀ hH₀pos hH₀mem).2

/-- Explicit Syracuse consequence of a ranked literal layer family. -/
theorem rankedLayers_give_not_syracuseReachesOne
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ) (rank : ℕ → ℕ → ℤ)
    (hranked : ∀ counter,
      IsRankedLayer (layers counter) (minimum counter)
        (next counter) (rank counter))
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words)
    (counter₀ H₀ : ℕ) (hH₀pos : 0 < H₀)
    (hH₀mem : H₀ ∈ layers counter₀) :
    ¬ SyracuseReachesOne (3 * H₀ - 1) := by
  exact not_syracuseReachesOne_of_infiniteExecution
    (fun _ hw ↦ hw.1)
    (rankedLayers_give_infiniteExecution layers minimum next rank
      hranked hinterior hreset counter₀ H₀ hH₀pos hH₀mem)

/-- Explicit unaccelerated Collatz consequence of a ranked literal layer
family. -/
theorem rankedLayers_give_not_collatz
    (layers : ℕ → Finset ℕ) (minimum : ℕ → ℕ)
    (next : ℕ → ℕ → ℕ) (rank : ℕ → ℕ → ℤ)
    (hranked : ∀ counter,
      IsRankedLayer (layers counter) (minimum counter)
        (next counter) (rank counter))
    (hinterior : ∀ counter H, H ∈ layers counter →
      H ≠ minimum counter →
        next counter H ∈ layers counter ∧
          ∃ words, RechargeMacro H (next counter H) words)
    (hreset : ∀ counter,
      ∃ H' words, H' ∈ layers (counter + 1) ∧
        RechargeMacro (minimum counter) H' words)
    (counter₀ H₀ : ℕ) (hH₀pos : 0 < H₀)
    (hH₀mem : H₀ ∈ layers counter₀) :
    ¬ CleanLean.Collatz.Conjecture := by
  exact not_conjecture_of_infiniteExecution
    (fun _ hw ↦ hw.1)
    (rankedLayers_give_infiniteExecution layers minimum next rank
      hranked hinterior hreset counter₀ H₀ hH₀pos hH₀mem)

end OutwardRankedLayerReset
end KontoroC
