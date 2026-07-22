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
charge-bouncer equations.  Those equations alone are not a Lean proof that an
underlying accelerated Collatz valuation word is legal.  This file records the
honest remaining interface: a public chain becomes a `MacroGlider` once every
edge additionally supplies its nonempty legal word and endpoint theorem.

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
  word : ℕ → List ℕ
  word_nonempty : ∀ t, word t ≠ []
  word_legal : ∀ t, WordLegal (boundary t).value (word t)
  word_endpoint : ∀ t,
    runWord (boundary t).value (word t) = (boundary (t + 1)).value

namespace SemanticChain

def arithmeticStep (g : SemanticChain) (t : ℕ) : Step where
  source := g.boundary t
  target := g.boundary (t + 1)
  recharge := g.recharge t
  recharge_pos := g.recharge_pos t
  balance := g.balance t

theorem grows (g : SemanticChain) (t : ℕ) :
    (g.boundary t).value < (g.boundary (t + 1)).value := by
  exact (g.arithmeticStep t).toChargeBouncerStep.strictly_outward

theorem start_large (g : SemanticChain) : 4 < (g.boundary 0).value := by
  have hle : chargeRegisterModulus ≤ (g.boundary 0).value :=
    Nat.le_of_dvd (g.boundary 0).value_pos (g.boundary 0).register
  have hlarge : 4 < chargeRegisterModulus := by
    norm_num [chargeRegisterModulus, chargeDifference]
  exact hlarge.trans_le hle

/-- This is the precise end-to-end theorem that a symbolic charge/unit
compiler must target.  The public equations provide growth; the explicit
legal words provide actual Collatz semantics. -/
def toMacroGlider (g : SemanticChain) : MacroGlider where
  state t := (g.boundary t).value
  word := g.word
  start_large := g.start_large
  word_nonempty := g.word_nonempty
  legal := g.word_legal
  transition := g.word_endpoint
  grows := g.grows

theorem not_conjecture (g : SemanticChain) : ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end SemanticChain

end ChargePublicCofactor

end KontoroC
