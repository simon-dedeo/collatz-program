/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ResidueSystem
import CleanLean.KL.PressureCertificate

/-!
# The level-six ball pressure automaton

This file gives an executable, independently specified version of the
243-state automaton used by the portable Lemma-5 pressure certificate.  A
state is the coordinate `s` in the residue `2 + 3*s (mod 3^6)`.  The graph is
defined from the concrete KL transport and refinement formulas rather than
from the imported certificate edge table.
-/

namespace CleanLean.KL

/-- The low-window state space in the `s = (q-2)/3` coordinate. -/
abbrev BallStateJ6 := Fin 243

/-- One digit is lost by a refinement edge. -/
abbrev BallCoarseJ6 := Fin 81

/-- Exact rational one-edge bounds before the exceptional-set tilt.  The two
branch fields already contain the factor `1/3` from `min ≤ mean`. -/
structure BallEdgeWeights where
  transport : ℚ
  retarded : ℚ
  advanced : ℚ
  deriving DecidableEq, Repr

private def finMod (n : ℕ) (hn : 0 < n) (x : ℕ) : Fin n :=
  ⟨x % n, Nat.mod_lt _ hn⟩

/-- The certificate's transport edge, in internal KL coordinates. -/
def ballTransportJ6 (q : BallStateJ6) : BallStateJ6 :=
  finMod 243 (by norm_num) (4 * q.val + 2)

/-- Coarse target of the retarded (`2 mod 9`) branch. -/
def ballRetardedTargetJ6 (q : BallStateJ6) : BallCoarseJ6 :=
  finMod 81 (by norm_num) (4 * (q.val / 3))

/-- Coarse target of the advanced (`8 mod 9`) branch. -/
def ballAdvancedTargetJ6 (q : BallStateJ6) : BallCoarseJ6 :=
  finMod 81 (by norm_num) (1 + 2 * (q.val / 3))

/-- The three fine balls above one coarse target. -/
def ballFiberJ6 (r : BallCoarseJ6) (j : Fin 3) : BallStateJ6 :=
  ⟨r.val + j.val * 81, by omega⟩

/-- Branch classification inherited from the low base-three digit. -/
def ballBranchJ6 (q : BallStateJ6) : Branch :=
  match q.val % 3 with
  | 0 => .retarded
  | 1 => .neutral
  | _ => .advanced

/-- The first six points `-4^{-t}`, `0 ≤ t < 6`, written in internal
coordinates modulo `3^5`. -/
def exceptionalOrbitJ6 : List BallStateJ6 := [242, 60, 136, 155, 99, 85]

/-- An edge is charged exactly when its target lies in the truncated backward
orbit of `-1`. -/
def exceptionalJ6 (q : BallStateJ6) : Bool := q ∈ exceptionalOrbitJ6

/-- Apply the target charge to an un-tilted edge weight. -/
def tiltedBallWeightJ6 (z w : ℚ) (target : BallStateJ6) : ℚ :=
  if exceptionalJ6 target then w * z else w

/-- The complete outgoing adjacency list used by the pressure certificate.
The transport edge comes first, followed (when present) by the three
refinement edges in increasing lift order. -/
def ballEdgesJ6 (w : BallEdgeWeights) (z : ℚ)
    (q : BallStateJ6) : List (BallStateJ6 × ℚ) :=
  let transport :=
    (ballTransportJ6 q, tiltedBallWeightJ6 z w.transport (ballTransportJ6 q))
  let branchEdges :=
    match ballBranchJ6 q with
    | .retarded =>
        [0, 1, 2].map fun j =>
          let target := ballFiberJ6 (ballRetardedTargetJ6 q) j
          (target, tiltedBallWeightJ6 z w.retarded target)
    | .neutral => []
    | .advanced =>
        [0, 1, 2].map fun j =>
          let target := ballFiberJ6 (ballAdvancedTargetJ6 q) j
          (target, tiltedBallWeightJ6 z w.advanced target)
  transport :: branchEdges

/-- Convert an automaton state to the concrete level-six KL state. -/
def ballStateToResidueSystem (q : BallStateJ6) : ResidueSystem.State 6 := q.val

/-- Convert a coarse automaton state to the concrete level-six coarse state. -/
def ballCoarseToResidueSystem (q : BallCoarseJ6) : ResidueSystem.Coarse 6 := q.val

@[simp] theorem ballStateToResidueSystem_val (q : BallStateJ6) :
    (ballStateToResidueSystem q).val = q.val := by
  simp [ballStateToResidueSystem]

@[simp] theorem ballCoarseToResidueSystem_val (q : BallCoarseJ6) :
    (ballCoarseToResidueSystem q).val = q.val := by
  simp [ballCoarseToResidueSystem]

/-- The independently defined transport edge is exactly the concrete KL
transport at precision six. -/
theorem ballTransportJ6_semantics (q : BallStateJ6) :
    ballStateToResidueSystem (ballTransportJ6 q) =
      ResidueSystem.transport 6 (ballStateToResidueSystem q) := by
  apply ZMod.val_injective
  simp [ballTransportJ6, finMod, ResidueSystem.transport_apply,
    ballStateToResidueSystem]

/-- The executable branch label agrees with the concrete KL branch label. -/
theorem ballBranchJ6_semantics (q : BallStateJ6) :
    ballBranchJ6 q = ResidueSystem.branch 6 (ballStateToResidueSystem q) := by
  generalize hdigit : q.val % 3 = digit
  have hdigit_lt : digit < 3 := by
    rw [← hdigit]
    omega
  interval_cases digit <;>
    simp [ballBranchJ6, ResidueSystem.branch, ballStateToResidueSystem_val,
      hdigit]

/-- The retarded target formula agrees with the concrete KL target formula. -/
theorem ballRetardedTargetJ6_semantics (q : BallStateJ6) :
    ballCoarseToResidueSystem (ballRetardedTargetJ6 q) =
      ResidueSystem.retardedTarget 6 (ballStateToResidueSystem q) := by
  apply ZMod.val_injective
  simp only [ballCoarseToResidueSystem_val, ballRetardedTargetJ6, finMod,
    ResidueSystem.retardedTarget, ballStateToResidueSystem_val]
  change (4 * (q.val / 3)) % 81 =
    ((4 * (q.val / 3) : ℕ) : ZMod 81).val
  rw [ZMod.val_natCast]

/-- The advanced target formula agrees with the concrete KL target formula. -/
theorem ballAdvancedTargetJ6_semantics (q : BallStateJ6) :
    ballCoarseToResidueSystem (ballAdvancedTargetJ6 q) =
      ResidueSystem.advancedTarget 6 (ballStateToResidueSystem q) := by
  apply ZMod.val_injective
  simp only [ballCoarseToResidueSystem_val, ballAdvancedTargetJ6, finMod,
    ResidueSystem.advancedTarget, ballStateToResidueSystem_val]
  change (1 + 2 * (q.val / 3)) % 81 =
    ((1 + 2 * (q.val / 3) : ℕ) : ZMod 81).val
  rw [ZMod.val_natCast]

/-- The fine target list is exactly the concrete three-point KL fiber. -/
theorem ballFiberJ6_semantics (r : BallCoarseJ6) (j : Fin 3) :
    ballStateToResidueSystem (ballFiberJ6 r j) =
      ResidueSystem.fiber 6 (ballCoarseToResidueSystem r) j := by
  apply ZMod.val_injective
  simp only [ballStateToResidueSystem_val, ballFiberJ6,
    ResidueSystem.fiber, ballCoarseToResidueSystem_val]
  change r.val + j.val * 81 =
    ((r.val + j.val * 81 : ℕ) : ZMod 243).val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  omega

/-- Recover the original residue representative `q = 2 + 3*s`. -/
def ballRawResidueJ6 (q : BallStateJ6) : ℕ := 2 + 3 * q.val

/-- The stored exceptional coordinates really are the first six points of the
backward-four orbit, beginning at `-1 mod 3^6`. -/
theorem exceptionalOrbitJ6_raw :
    exceptionalOrbitJ6.map ballRawResidueJ6 =
      [728, 182, 410, 467, 299, 257] := by
  decide +kernel

/-- Consecutive entries of the stored list satisfy `4*y = x (mod 3^6)`. -/
theorem exceptionalOrbitJ6_backward_chain :
    (4 * 182) % 729 = 728 ∧
    (4 * 410) % 729 = 182 ∧
    (4 * 467) % 729 = 410 ∧
    (4 * 299) % 729 = 467 ∧
    (4 * 257) % 729 = 299 := by
  norm_num

end CleanLean.KL
