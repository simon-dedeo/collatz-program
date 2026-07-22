/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.Glider
import KontoroC.PeriodicItinerary

/-!
# Every growing Collatz macro-glider is genuinely aperiodic

A finite cycle of changing valuation words is no better than one constant
word: concatenate a whole period into a single super-block.  This file makes
that reduction at the abstract `MacroGlider` interface and also removes an
arbitrary finite transient.

The conclusion is deliberately about the *emitted valuation words*, not the
macro-states.  Thus it rules out any controller whose output schedule is
eventually periodic even when its numerical tail or payload keeps changing.
-/

namespace KontoroC

namespace MacroGlider

/-- Concatenate `n` consecutive macro-words, starting at macro-time `t`. -/
def segmentWord (g : MacroGlider) (t : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => g.word t ++ g.segmentWord (t + 1) n

@[simp] theorem segmentWord_zero (g : MacroGlider) (t : ℕ) :
    g.segmentWord t 0 = [] := rfl

@[simp] theorem segmentWord_succ (g : MacroGlider) (t n : ℕ) :
    g.segmentWord t (n + 1) =
      g.word t ++ g.segmentWord (t + 1) n := rfl

/-- A finite segment of a macro-glider is one exact legal valuation word
whose endpoint is the corresponding later macro-state. -/
theorem segment_legal_and_endpoint (g : MacroGlider) (t n : ℕ) :
    WordLegal (g.state t) (g.segmentWord t n) ∧
      runWord (g.state t) (g.segmentWord t n) = g.state (t + n) := by
  induction n generalizing t with
  | zero => simp [WordLegal]
  | succ n ih =>
      rw [segmentWord_succ, wordLegal_append_iff, runWord_append]
      have htail := ih (t + 1)
      constructor
      · refine ⟨g.legal t, ?_⟩
        rw [g.transition t]
        exact htail.1
      · rw [g.transition t, htail.2]
        congr 1
        omega

/-- Every positive-length segment word is nonempty. -/
theorem segmentWord_ne_nil (g : MacroGlider) {t n : ℕ} (hn : 0 < n) :
    g.segmentWord t n ≠ [] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [segmentWord_succ]
  exact List.append_ne_nil_of_left_ne_nil (g.word_nonempty t) _

/-- Periodicity by `p` implies invariance under every multiple of `p`. -/
theorem word_eq_of_periodic_mul (g : MacroGlider) {p : ℕ}
    (hperiod : ∀ t, g.word (t + p) = g.word t) (k t : ℕ) :
    g.word (k * p + t) = g.word t := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        g.word ((k + 1) * p + t) = g.word ((k * p + t) + p) := by
          congr 1
          simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm]
        _ = g.word (k * p + t) := hperiod _
        _ = g.word t := ih

/-- Corresponding finite segments at period-aligned starting times are the
same literal list. -/
theorem segmentWord_eq_of_periodic_mul (g : MacroGlider) {p : ℕ}
    (hperiod : ∀ t, g.word (t + p) = g.word t) (k t n : ℕ) :
    g.segmentWord (k * p + t) n = g.segmentWord t n := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [segmentWord_succ, segmentWord_succ,
        g.word_eq_of_periodic_mul hperiod k t]
      congr 1
      simpa [Nat.add_assoc] using ih (t + 1)

/-- A strictly growing macro-state sequence is strictly monotone. -/
theorem state_strictMono (g : MacroGlider) : StrictMono g.state :=
  strictMono_nat_of_lt_succ g.grows

/-- The emitted valuation-word schedule of a growing macro-glider cannot be
periodic from its start.  The proof concatenates one period into a fixed
nonempty super-block and invokes the exact periodic-block obstruction. -/
theorem not_periodic_words (g : MacroGlider) {p : ℕ} (hp : 0 < p)
    (hperiod : ∀ t, g.word (t + p) = g.word t) : False := by
  let block := g.segmentWord 0 p
  let blockState : ℕ → ℕ := fun k => g.state (k * p)
  have hblock : ∀ k, g.segmentWord (k * p) p = block := by
    intro k
    simpa [block] using g.segmentWord_eq_of_periodic_mul hperiod k 0 p
  have hblock_ne : block ≠ [] := by
    exact g.segmentWord_ne_nil hp
  have hlegal : ∀ k, WordLegal (blockState k) block := by
    intro k
    dsimp only [blockState]
    rw [← hblock k]
    exact (g.segment_legal_and_endpoint (k * p) p).1
  have htransition : ∀ k,
      runWord (blockState k) block = blockState (k + 1) := by
    intro k
    dsimp only [blockState]
    rw [← hblock k, (g.segment_legal_and_endpoint (k * p) p).2]
    congr 1
    simp [Nat.succ_mul]
  have hfixed := legal_block_chain_first_fixed blockState hblock_ne
    hlegal htransition
  have hindex : 0 * p < 1 * p := by omega
  have hgrow : blockState 0 < blockState 1 :=
    g.state_strictMono hindex
  exact (Nat.ne_of_lt hgrow) hfixed.symm

/-- Remove a finite prefix from a macro-glider while preserving every field
of its soundness interface. -/
def tail (g : MacroGlider) (t₀ : ℕ) : MacroGlider where
  state t := g.state (t₀ + t)
  word t := g.word (t₀ + t)
  start_large := lt_of_lt_of_le g.start_large (g.start_le_state t₀)
  word_nonempty t := g.word_nonempty (t₀ + t)
  legal t := g.legal (t₀ + t)
  transition t := by
    simpa [Nat.add_assoc] using g.transition (t₀ + t)
  grows t := by
    simpa [Nat.add_assoc] using g.grows (t₀ + t)

/-- Main no-go theorem: the valuation words of every growing Collatz
macro-glider fail to be eventually periodic. -/
theorem not_eventually_periodic_words (g : MacroGlider) (t₀ : ℕ)
    {p : ℕ} (hp : 0 < p)
    (hperiod : ∀ t,
      g.word (t₀ + (t + p)) = g.word (t₀ + t)) : False := by
  apply (g.tail t₀).not_periodic_words hp
  intro t
  exact hperiod t

end MacroGlider

end KontoroC
