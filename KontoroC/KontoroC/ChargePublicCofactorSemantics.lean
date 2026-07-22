/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePublicCofactor
import KontoroC.Glider

/-!
# The missing semantic endpoint for public-cofactor chains

`ChargePublicCofactor.Step` is an exact arithmetic presentation of the
charge-bouncer equations in the normalized coordinate `y`.  That coordinate
is not silently identified with the underlying odd Collatz integer.  This file
records the honest remaining interface: a public chain becomes a
`MacroGlider` once it supplies an ordinary-state encoding and every edge
supplies its nonempty legal word and endpoint theorem.

No construction of those words is assumed or hidden here.  A future generic
charge-to-unit compiler should discharge the final two fields of
`SemanticChain` from the public balance equations.
-/

namespace KontoroC

namespace ChargePublicCofactor

/-- Infinite public PC3 data together with the still-required literal
accelerated-Collatz semantics of each edge. -/
structure SemanticChain where
  boundary : ℕ → Boundary
  recharge : ℕ → ℕ
  recharge_pos : ∀ t, 0 < recharge t
  balance : ∀ t,
    publicA ^ recharge t *
        (publicC ^ (boundary t).opcode * (boundary t).cofactor - 1) =
      publicB ^ recharge t * (boundary (t + 1)).value
  /-- Decode a normalized public boundary to the literal odd Collatz state. -/
  encode : Boundary → ℕ
  /-- The encoded states lie above the small `1-2-4` cycle. -/
  encode_large : ∀ b, 4 < encode b
  /-- Actual outwardness is required only on the edges used by this chain.
  The final router decoding need not be globally monotone in normalized `y`. -/
  encoded_grows : ∀ t, encode (boundary t) < encode (boundary (t + 1))
  word : ℕ → List ℕ
  word_nonempty : ∀ t, word t ≠ []
  word_legal : ∀ t, WordLegal (encode (boundary t)) (word t)
  word_endpoint : ∀ t,
    runWord (encode (boundary t)) (word t) = encode (boundary (t + 1))

namespace SemanticChain

def arithmeticStep (g : SemanticChain) (t : ℕ) : Step where
  source := g.boundary t
  target := g.boundary (t + 1)
  recharge := g.recharge t
  recharge_pos := g.recharge_pos t
  balance := g.balance t

theorem value_grows (g : SemanticChain) (t : ℕ) :
    (g.boundary t).value < (g.boundary (t + 1)).value := by
  exact (g.arithmeticStep t).toChargeBouncerStep.strictly_outward

/-- This is the precise end-to-end theorem that a symbolic charge/unit
compiler must target.  The public equations provide growth; the explicit
legal words provide actual Collatz semantics. -/
def toMacroGlider (g : SemanticChain) : MacroGlider where
  state t := g.encode (g.boundary t)
  word := g.word
  start_large := g.encode_large (g.boundary 0)
  word_nonempty := g.word_nonempty
  legal := g.word_legal
  transition := g.word_endpoint
  grows := g.encoded_grows

theorem not_conjecture (g : SemanticChain) : ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end SemanticChain

end ChargePublicCofactor

end KontoroC
