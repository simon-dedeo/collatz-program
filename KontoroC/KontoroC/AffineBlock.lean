/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ValuationWord

/-!
# Compressed affine blocks

This is the exact algebra used by the bounded morphic search.  A block stores
the number of accelerated steps, total removed power of two, and affine
constant without expanding its valuation word.
-/

namespace KontoroC

@[ext] structure AffineBlock where
  steps : ℕ
  halvings : ℕ
  constant : ℕ
deriving Repr, DecidableEq

namespace AffineBlock

def identity : AffineBlock := ⟨0, 0, 0⟩

def letter (k : ℕ) : AffineBlock := ⟨1, k, 1⟩

/-- Execute `left` and then `right`. -/
def concat (left right : AffineBlock) : AffineBlock where
  steps := left.steps + right.steps
  halvings := left.halvings + right.halvings
  constant :=
    3 ^ right.steps * left.constant +
      2 ^ left.halvings * right.constant

def ofWord (ks : List ℕ) : AffineBlock where
  steps := ks.length
  halvings := totalValuation ks
  constant := affineOffset ks

@[simp] theorem ofWord_nil : ofWord [] = identity := rfl

@[simp] theorem ofWord_singleton (k : ℕ) : ofWord [k] = letter k := by
  ext <;> simp [ofWord, letter]

theorem ofWord_append (u v : List ℕ) :
    ofWord (u ++ v) = (ofWord u).concat (ofWord v) := by
  ext
  · simp [ofWord, concat]
  · simp [ofWord, concat, totalValuation_append]
  · simp [ofWord, concat, affineOffset_append]

theorem concat_assoc (a b c : AffineBlock) :
    (a.concat b).concat c = a.concat (b.concat c) := by
  ext <;> simp [concat, Nat.pow_add] <;> ring

@[simp] theorem identity_concat (a : AffineBlock) : identity.concat a = a := by
  ext <;> simp [identity, concat]

@[simp] theorem concat_identity (a : AffineBlock) : a.concat identity = a := by
  ext <;> simp [identity, concat]

end AffineBlock

end KontoroC
