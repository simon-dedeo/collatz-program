/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCarryThreshold
import KontoroC.OutwardOddSlice

/-!
# Invariants for the outward first-passage system

This file gives the exact conditional bridge requested by the invariant
search.  It does not construct an invariant.  Instead, it proves that any
predicate closed under positive, nonempty boundary-to-boundary recharge
macros supplies arbitrarily deep literal executions of the outward
first-passage code, and hence a counterexample to Syracuse and Collatz.

The endpoint-sensitive `ExecutesBlocksTo` relation is deliberately minimal.
It refines the existing endpoint-forgetting `ExecutesBlocks` predicate and
retains the intermediate word boundaries.
-/

namespace KontoroC
namespace OutwardInvariantBridge

open ShortcutParityPeriodicNoGo OutwardFirstPassage
  OutwardCodeCompactness OutwardBoundaryRenewal OutwardOddSlice
  OutwardCodeCounterexample
open CleanLean.Collatz

/-! ## Endpoint-sensitive block execution -/

/-- Literal execution of exactly the listed parity words, retaining the
final endpoint. -/
def ExecutesBlocksTo : List (List Bool) → ℕ → ℕ → Prop
  | [], start, finish => finish = start
  | w :: words, start, finish =>
      ∃ middle,
        Executes w start middle ∧ ExecutesBlocksTo words middle finish

@[simp] theorem executesBlocksTo_nil {start finish : ℕ} :
    ExecutesBlocksTo [] start finish ↔ finish = start := by
  rfl

@[simp] theorem executesBlocksTo_cons {w : List Bool}
    {words : List (List Bool)} {start finish : ℕ} :
    ExecutesBlocksTo (w :: words) start finish ↔
      ∃ middle, Executes w start middle ∧
        ExecutesBlocksTo words middle finish := by
  rfl

/-- Endpoint-sensitive block execution is equivalent to execution of the
flattened literal parity word. -/
theorem executesBlocksTo_iff_flatten {words : List (List Bool)}
    {start finish : ℕ} :
    ExecutesBlocksTo words start finish ↔
      Executes (flattenWords words) start finish := by
  induction words generalizing start with
  | nil => simp [ExecutesBlocksTo, flattenWords, Executes]
  | cons w words ih =>
      simp only [ExecutesBlocksTo, flattenWords]
      rw [executes_append]
      constructor
      · rintro ⟨middle, hw, hrest⟩
        exact ⟨middle, hw, ih.mp hrest⟩
      · rintro ⟨middle, hw, hrest⟩
        exact ⟨middle, hw, ih.mpr hrest⟩

/-- Forgetting the final endpoint recovers the existing block predicate. -/
theorem ExecutesBlocksTo.executesBlocks {words : List (List Bool)}
    {start finish : ℕ} (h : ExecutesBlocksTo words start finish) :
    ExecutesBlocks words start := by
  apply executesBlocks_iff_flatten.mpr
  exact ⟨finish, executesBlocksTo_iff_flatten.mp h⟩

/-- The existing block predicate is precisely existential endpoint-sensitive
execution. -/
theorem executesBlocks_iff_exists_endpoint {words : List (List Bool)}
    {start : ℕ} :
    ExecutesBlocks words start ↔
      ∃ finish, ExecutesBlocksTo words start finish := by
  rw [executesBlocks_iff_flatten]
  constructor
  · rintro ⟨finish, hfinish⟩
    exact ⟨finish, executesBlocksTo_iff_flatten.mpr hfinish⟩
  · rintro ⟨finish, hfinish⟩
    exact ⟨finish, executesBlocksTo_iff_flatten.mp hfinish⟩

/-- Concatenation exposes the unique joining boundary existentially. -/
theorem executesBlocksTo_append (left right : List (List Bool))
    {start finish : ℕ} :
    ExecutesBlocksTo (left ++ right) start finish ↔
      ∃ middle,
        ExecutesBlocksTo left start middle ∧
        ExecutesBlocksTo right middle finish := by
  induction left generalizing start with
  | nil =>
      simp [ExecutesBlocksTo]
  | cons w left ih =>
      simp only [List.cons_append, ExecutesBlocksTo]
      constructor
      · rintro ⟨next, hw, htail⟩
        obtain ⟨middle, hleft, hright⟩ := ih.mp htail
        exact ⟨middle, ⟨next, hw, hleft⟩, hright⟩
      · rintro ⟨middle, ⟨next, hw, hleft⟩, hright⟩
        exact ⟨next, hw, ih.mpr ⟨middle, hleft, hright⟩⟩

/-- Cutting a word list at any block index exposes the intermediate
endpoint.  This is the endpoint-sensitive prefix/drop compatibility. -/
theorem executesBlocksTo_take_drop_iff (n : ℕ)
    {words : List (List Bool)} {start finish : ℕ} :
    ExecutesBlocksTo words start finish ↔
      ∃ middle,
        ExecutesBlocksTo (words.take n) start middle ∧
        ExecutesBlocksTo (words.drop n) middle finish := by
  conv_lhs => rw [← List.take_append_drop n words]
  exact executesBlocksTo_append _ _

/-- In particular, every block prefix has some literal endpoint. -/
theorem ExecutesBlocksTo.exists_take_endpoint {n : ℕ}
    {words : List (List Bool)} {start finish : ℕ}
    (h : ExecutesBlocksTo words start finish) :
    ∃ middle, ExecutesBlocksTo (words.take n) start middle := by
  obtain ⟨middle, htake, _⟩ :=
    (executesBlocksTo_take_drop_iff n).mp h
  exact ⟨middle, htake⟩

/-! ## Exact boundary macros -/

/-- A positive, nonempty boundary-to-boundary execution through exactly the
listed first-passage words. -/
def RechargeMacro (H H' : ℕ) (words : List (List Bool)) : Prop :=
  0 < H ∧
  0 < H' ∧
  words ≠ [] ∧
  WordsIn FirstPassageCode words ∧
  ExecutesBlocksTo words (3 * H - 1) (3 * H' - 1)

theorem RechargeMacro.source_pos {H H' : ℕ} {words : List (List Bool)}
    (h : RechargeMacro H H' words) : 0 < H := h.1

theorem RechargeMacro.target_pos {H H' : ℕ} {words : List (List Bool)}
    (h : RechargeMacro H H' words) : 0 < H' := h.2.1

theorem RechargeMacro.words_ne_nil {H H' : ℕ}
    {words : List (List Bool)} (h : RechargeMacro H H' words) :
    words ≠ [] := h.2.2.1

theorem RechargeMacro.wordsIn {H H' : ℕ} {words : List (List Bool)}
    (h : RechargeMacro H H' words) :
    WordsIn FirstPassageCode words := h.2.2.2.1

theorem RechargeMacro.executesTo {H H' : ℕ}
    {words : List (List Bool)} (h : RechargeMacro H H' words) :
    ExecutesBlocksTo words (3 * H - 1) (3 * H' - 1) :=
  h.2.2.2.2

theorem wordsIn_append {C : Set (List Bool)}
    {left right : List (List Bool)}
    (hleft : WordsIn C left) (hright : WordsIn C right) :
    WordsIn C (left ++ right) := by
  intro w hw
  rw [List.mem_append] at hw
  exact hw.elim (hleft w) (hright w)

/-- Boundary macros compose by literal word-list concatenation. -/
theorem RechargeMacro.append {H K L : ℕ}
    {left right : List (List Bool)}
    (hleft : RechargeMacro H K left)
    (hright : RechargeMacro K L right) :
    RechargeMacro H L (left ++ right) := by
  refine ⟨hleft.source_pos, hright.target_pos, ?_,
    wordsIn_append hleft.wordsIn hright.wordsIn, ?_⟩
  · simp [hleft.words_ne_nil]
  · exact (executesBlocksTo_append left right).mpr
      ⟨3 * K - 1, hleft.executesTo, hright.executesTo⟩

/-! ## The invariant bridge -/

/-- `n` applications of relational invariant closure produce at least `n`
first-passage blocks.  Macro lengths may vary and no infinite choice
sequence is assumed. -/
theorem invariant_gives_finiteMacroChain
    (I : ℕ → Prop)
    (hclosed :
      ∀ H, I H →
        ∃ H' words, RechargeMacro H H' words ∧ I H')
    (n H : ℕ) (hHpos : 0 < H) (hH : I H) :
    ∃ H' words,
      0 < H' ∧
      I H' ∧
      n ≤ words.length ∧
      WordsIn FirstPassageCode words ∧
      ExecutesBlocksTo words (3 * H - 1) (3 * H' - 1) := by
  induction n generalizing H with
  | zero =>
      exact ⟨H, [], hHpos, hH, by simp, by simp [WordsIn],
        by simp [ExecutesBlocksTo]⟩
  | succ n ih =>
      obtain ⟨K, head, hmacro, hK⟩ := hclosed H hH
      obtain ⟨L, tail, hLpos, hL, htailLen, htailWords, htailExec⟩ :=
        ih K hmacro.target_pos hK
      refine ⟨L, head ++ tail, hLpos, hL, ?_,
        wordsIn_append hmacro.wordsIn htailWords, ?_⟩
      · have hheadLen : 0 < head.length :=
          List.length_pos_iff.mpr hmacro.words_ne_nil
        simp only [List.length_append]
        omega
      · exact (executesBlocksTo_append head tail).mpr
          ⟨3 * K - 1, hmacro.executesTo, htailExec⟩

/-- A positive invariant closed under nonempty recharge macros supplies an
ordinary infinite execution of the exact first-passage code. -/
theorem invariant_gives_infiniteExecution
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hclosed :
      ∀ H, I H →
        ∃ H' words,
          RechargeMacro H H' words ∧ I H') :
    InfiniteExecution FirstPassageCode (3 * H₀ - 1) := by
  intro n
  obtain ⟨H', words, _, _, hlen, hwords, hexec⟩ :=
    invariant_gives_finiteMacroChain I hclosed n H₀ h₀pos h₀
  have hstart : 0 < 3 * H₀ - 1 := by omega
  refine ⟨hstart, words.take n, List.length_take_of_le hlen,
    wordsIn_take hwords, ?_⟩
  exact executesBlocks_take hexec.executesBlocks

/-- The invariant bridge, stated at the Syracuse endpoint. -/
theorem invariant_gives_not_syracuseReachesOne
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hclosed :
      ∀ H, I H →
        ∃ H' words,
          RechargeMacro H H' words ∧ I H') :
    ¬ SyracuseReachesOne (3 * H₀ - 1) := by
  apply not_syracuseReachesOne_of_infiniteExecution
    (C := FirstPassageCode)
  · intro w hw
    exact hw.1
  · exact invariant_gives_infiniteExecution I H₀ h₀pos h₀ hclosed

/-- The invariant bridge, stated as a refutation of the standard
unaccelerated Collatz conjecture. -/
theorem invariant_gives_not_collatz
    (I : ℕ → Prop) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hclosed :
      ∀ H, I H →
        ∃ H' words,
          RechargeMacro H H' words ∧ I H') :
    ¬ CleanLean.Collatz.Conjecture := by
  apply not_conjecture_of_infiniteExecution
    (C := FirstPassageCode)
  · intro w hw
    exact hw.1
  · exact invariant_gives_infiniteExecution I H₀ h₀pos h₀ hclosed

/-! ## Partial functional recharge maps -/

/-- A partial function version.  Closure of `I` under the returned boundary
is not enough by itself: `hsound` is the necessary semantic hypothesis that
the returned edge is realized by a literal nonempty recharge macro. -/
theorem partialMap_invariant_gives_infiniteExecution
    (I : ℕ → Prop) (R : ℕ → Option ℕ) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hstep : ∀ H, I H → ∃ H', R H = some H' ∧ I H')
    (hsound : ∀ H H', I H → R H = some H' →
      ∃ words, RechargeMacro H H' words) :
    InfiniteExecution FirstPassageCode (3 * H₀ - 1) := by
  apply invariant_gives_infiniteExecution I H₀ h₀pos h₀
  intro H hH
  obtain ⟨H', hR, hH'⟩ := hstep H hH
  obtain ⟨words, hmacro⟩ := hsound H H' hH hR
  exact ⟨H', words, hmacro, hH'⟩

theorem partialMap_invariant_gives_not_syracuseReachesOne
    (I : ℕ → Prop) (R : ℕ → Option ℕ) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hstep : ∀ H, I H → ∃ H', R H = some H' ∧ I H')
    (hsound : ∀ H H', I H → R H = some H' →
      ∃ words, RechargeMacro H H' words) :
    ¬ SyracuseReachesOne (3 * H₀ - 1) := by
  exact not_syracuseReachesOne_of_infiniteExecution
    (fun _ hw => hw.1)
    (partialMap_invariant_gives_infiniteExecution
      I R H₀ h₀pos h₀ hstep hsound)

theorem partialMap_invariant_gives_not_collatz
    (I : ℕ → Prop) (R : ℕ → Option ℕ) (H₀ : ℕ)
    (h₀pos : 0 < H₀)
    (h₀ : I H₀)
    (hstep : ∀ H, I H → ∃ H', R H = some H' ∧ I H')
    (hsound : ∀ H H', I H → R H = some H' →
      ∃ words, RechargeMacro H H' words) :
    ¬ CleanLean.Collatz.Conjecture := by
  exact not_conjecture_of_infiniteExecution
    (fun _ hw => hw.1)
    (partialMap_invariant_gives_infiniteExecution
      I R H₀ h₀pos h₀ hstep hsound)

end OutwardInvariantBridge
end KontoroC
