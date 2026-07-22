/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SaturatedBridge

/-!
# Variable saturated-bridge chains

This is the all-level endpoint for a changing sequence of rational-base
compiler blocks.  Gate families, address lengths, and residual-tail
coordinates may all vary with time.  The only global obligations are exact
index renewal, one large start, and outwardness of every selected source gate.

Unlike a fixed affine return circuit, such a chain can emit a genuinely
aperiodic valuation-word stream.
-/

namespace KontoroC

/-- A composable sequence of saturated affine bridges. -/
structure SaturatedBridgeChain where
  family : ℕ → AffineTwoRailFamily
  bridge : ∀ t, SaturatedAffineBridge (family t) (family (t + 1))
  tail : ℕ → ℕ
  start_large :
    4 < ((family 0).member
      ((bridge 0).link.sourceIndex (tail 0))).start
  index_link : ∀ t,
    (bridge t).link.targetIndex (tail t) =
      (bridge (t + 1)).link.sourceIndex (tail (t + 1))
  outward : ∀ t,
    ((family t).member
      ((bridge t).link.sourceIndex (tail t))).start <
    ((family t).member
      ((bridge t).link.sourceIndex (tail t))).endpoint

namespace SaturatedBridgeChain

/-- Source index selected at bridge time `t`. -/
def sourceIndex (g : SaturatedBridgeChain) (t : ℕ) : ℕ :=
  (g.bridge t).link.sourceIndex (g.tail t)

/-- Exact two-rail gate selected at bridge time `t`. -/
def gate (g : SaturatedBridgeChain) (t : ℕ) : TwoRailGate :=
  (g.family t).member (g.sourceIndex t)

/-- The selected source indices follow the variable-length saturated map
block by block. -/
theorem sourceIndex_succ (g : SaturatedBridgeChain) (t : ℕ) :
    g.sourceIndex (t + 1) =
      saturatedStep^[(g.bridge t).addressBits] (g.sourceIndex t) := by
  calc
    g.sourceIndex (t + 1) =
        (g.bridge t).link.targetIndex (g.tail t) :=
      (g.index_link t).symm
    _ = saturatedStep^[(g.bridge t).addressBits]
          ((g.bridge t).link.sourceIndex (g.tail t)) :=
      (g.bridge t).targetIndex_eq_iterate (g.tail t)
    _ = saturatedStep^[(g.bridge t).addressBits] (g.sourceIndex t) := rfl

/-- Each compiled endpoint is exactly the next selected gate start. -/
theorem gate_linked (g : SaturatedBridgeChain) (t : ℕ) :
    (g.gate t).endpoint = (g.gate (t + 1)).start := by
  calc
    (g.gate t).endpoint =
        ((g.family (t + 1)).member
          ((g.bridge t).link.targetIndex (g.tail t))).start :=
      (g.bridge t).link.endpoint_link (g.tail t)
    _ = (g.gate (t + 1)).start := by
      rw [g.index_link t]
      rfl

/-- A renewing outward bridge chain is an ordinary infinite two-rail
program. -/
def toInfiniteTwoRailProgram (g : SaturatedBridgeChain) :
    InfiniteTwoRailProgram where
  gate := g.gate
  start_large := g.start_large
  linked := g.gate_linked
  outward := g.outward

/-- Sound endpoint for the variable-block rational-base compiler. -/
theorem not_conjecture (g : SaturatedBridgeChain) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toInfiniteTwoRailProgram.not_conjecture

end SaturatedBridgeChain

end KontoroC
