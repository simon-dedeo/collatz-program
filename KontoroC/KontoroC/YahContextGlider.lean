/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate

/-!
# Generic context-loop gliders for string rewriting

This file formalizes the relation-theoretic part of the YAH certificate
checker.  It is independent of the eleven concrete rules.  Any nonempty
derivation which reproduces its source inside an outer context yields
nonempty derivations at every scale.
-/

namespace KontoroC
namespace YahContextGlider

/-- A word relation is closed under arbitrary left and right contexts. -/
def ContextClosed {α : Type*} (Step : List α → List α → Prop) : Prop :=
  ∀ left right {u v}, Step u v →
    Step (left ++ u ++ right) (left ++ v ++ right)

/-- Context closure lifts from one rewrite to every nonempty finite
derivation. -/
theorem transGen_context {α : Type*} {Step : List α → List α → Prop}
    (hclosed : ContextClosed Step) {u v : List α}
    (h : Relation.TransGen Step u v) (left right : List α) :
    Relation.TransGen Step (left ++ u ++ right) (left ++ v ++ right) := by
  induction h with
  | single huv => exact .single (hclosed left right huv)
  | tail hab hbc ih => exact ih.tail (hclosed left right hbc)

/-- One outer-context inflation. -/
def inflate {α : Type*} (left right word : List α) : List α :=
  left ++ word ++ right

/-- A chunked infinite derivation records a nonempty finite rewrite segment
between every two successive scales.  Concatenating the chunks gives an
ordinary infinite rewrite sequence. -/
structure ChunkedInfiniteDerivation {α : Type*}
    (Step : List α → List α → Prop) where
  state : ℕ → List α
  chunk : ∀ n, Relation.TransGen Step (state n) (state (n + 1))

theorem iterate_inflate_chunk {α : Type*} {Step : List α → List α → Prop}
    (hclosed : ContextClosed Step) {u : List α} (left right : List α)
    (hseed : Relation.TransGen Step u (inflate left right u)) (n : ℕ) :
    Relation.TransGen Step
      (((inflate left right)^[n]) u) (((inflate left right)^[n + 1]) u) := by
  induction n with
  | zero => simpa [inflate] using hseed
  | succ n ih =>
      have hctx := transGen_context hclosed ih left right
      simpa [Function.iterate_succ_apply', inflate] using hctx

/-- Y1: a literal context loop is a finite proof object for a chunked
infinite derivation. -/
def of_context_loop {α : Type*} {Step : List α → List α → Prop}
    (hclosed : ContextClosed Step) (u left right : List α)
    (hseed : Relation.TransGen Step u (left ++ u ++ right)) :
    ChunkedInfiniteDerivation Step where
  state n := ((inflate left right)^[n]) u
  chunk n := iterate_inflate_chunk hclosed left right
    (by simpa [inflate] using hseed) n

/-- A word morphism induced by images of individual letters. -/
def wordMap {α : Type*} (sigma : α → List α) (word : List α) : List α :=
  word.flatMap sigma

@[simp] theorem wordMap_nil {α : Type*} (sigma : α → List α) :
    wordMap sigma [] = [] := rfl

theorem wordMap_append {α : Type*} (sigma : α → List α)
    (u v : List α) :
    wordMap sigma (u ++ v) = wordMap sigma u ++ wordMap sigma v := by
  simp [wordMap]

/-- Y2 at the generating-rewrite level. -/
def RuleSimulation {α : Type*} (Step : List α → List α → Prop)
    (sigma : α → List α) : Prop :=
  ∀ {u v}, Step u v →
    Relation.TransGen Step (wordMap sigma u) (wordMap sigma v)

/-- Simulations of the generating rules simulate every nonempty finite
derivation. -/
theorem transGen_wordMap {α : Type*} {Step : List α → List α → Prop}
    {sigma : α → List α} (hsim : RuleSimulation Step sigma)
    {u v : List α} (h : Relation.TransGen Step u v) :
    Relation.TransGen Step (wordMap sigma u) (wordMap sigma v) := by
  induction h with
  | single huv => exact hsim huv
  | tail hab hbc ih => exact ih.trans (hsim hbc)

/-- Iterating a rule-simulating morphism simulates the same derivation at
every scale. -/
theorem transGen_wordMap_iterate {α : Type*}
    {Step : List α → List α → Prop} {sigma : α → List α}
    (hsim : RuleSimulation Step sigma) {u v : List α}
    (h : Relation.TransGen Step u v) (n : ℕ) :
    Relation.TransGen Step
      (((wordMap sigma)^[n]) u) (((wordMap sigma)^[n]) v) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using transGen_wordMap hsim ih

/-- The `n`-fold word morphism. -/
def morphIter {α : Type*} (sigma : α → List α) (n : ℕ)
    (word : List α) : List α :=
  ((wordMap sigma)^[n]) word

theorem morphIter_append {α : Type*} (sigma : α → List α) (n : ℕ)
    (u v : List α) :
    morphIter sigma n (u ++ v) =
      morphIter sigma n u ++ morphIter sigma n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [morphIter, Function.iterate_succ_apply']
      change wordMap sigma (morphIter sigma n (u ++ v)) =
        wordMap sigma (morphIter sigma n u) ++
          wordMap sigma (morphIter sigma n v)
      rw [ih, wordMap_append]

theorem morphIter_wordMap {α : Type*} (sigma : α → List α) (n : ℕ)
    (u : List α) :
    morphIter sigma n (wordMap sigma u) = morphIter sigma (n + 1) u := by
  simp [morphIter, Function.iterate_succ_apply]

/-- Left contexts accumulated by successive morphic reproductions. -/
def morphLeft {α : Type*} (sigma : α → List α) (left : List α) : ℕ → List α
  | 0 => []
  | n + 1 => morphLeft sigma left n ++ morphIter sigma n left

/-- Right contexts accumulated in the opposite nesting order. -/
def morphRight {α : Type*} (sigma : α → List α) (right : List α) : ℕ → List α
  | 0 => []
  | n + 1 => morphIter sigma n right ++ morphRight sigma right n

/-- Scale-`n` word generated by a morphic context loop. -/
def morphState {α : Type*} (sigma : α → List α)
    (u left right : List α) (n : ℕ) : List α :=
  morphLeft sigma left n ++ morphIter sigma n u ++ morphRight sigma right n

theorem morphic_context_chunk {α : Type*}
    {Step : List α → List α → Prop} (hclosed : ContextClosed Step)
    {sigma : α → List α} (hsim : RuleSimulation Step sigma)
    (u left right : List α)
    (hseed : Relation.TransGen Step u
      (left ++ wordMap sigma u ++ right)) (n : ℕ) :
    Relation.TransGen Step
      (morphState sigma u left right n)
      (morphState sigma u left right (n + 1)) := by
  have hn := transGen_wordMap_iterate hsim hseed n
  have hctx := transGen_context hclosed hn
    (morphLeft sigma left n) (morphRight sigma right n)
  change Relation.TransGen Step
    (morphLeft sigma left n ++ morphIter sigma n u ++ morphRight sigma right n)
    (morphLeft sigma left n ++
      morphIter sigma n (left ++ wordMap sigma u ++ right) ++
        morphRight sigma right n) at hctx
  rw [morphIter_append sigma n (left ++ wordMap sigma u) right,
    morphIter_append sigma n left (wordMap sigma u),
    morphIter_wordMap] at hctx
  simpa [morphState, morphLeft, morphRight, List.append_assoc] using hctx

/-- Y2--Y3: a rule-simulating morphism and one morphic reproduction seed
produce a nonempty derivation chunk at every scale. -/
def of_morphic_context_loop {α : Type*}
    {Step : List α → List α → Prop} (hclosed : ContextClosed Step)
    (sigma : α → List α) (hsim : RuleSimulation Step sigma)
    (u left right : List α)
    (hseed : Relation.TransGen Step u
      (left ++ wordMap sigma u ++ right)) :
    ChunkedInfiniteDerivation Step where
  state := morphState sigma u left right
  chunk := morphic_context_chunk hclosed hsim u left right hseed

end YahContextGlider
end KontoroC
