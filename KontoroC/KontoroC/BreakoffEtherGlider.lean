/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.BreakoffFiniteSemantics
import KontoroC.AffineBreakoffDelay

/-!
# The exact ether--defect--ether break-off macro

This file independently checks the two concrete affine delay-gate families
used by the experimental `E,H,E^N` substitution.  It proves the universal
`E -> H -> E` prefix linkage; no bounded replay or imported JSON artifact is
used.
-/

namespace KontoroC
namespace BreakoffEtherGlider

/-- The one-delay, opcode-two ether family `E`. -/
def ether : AffineBreakoffDelayGate where
  delay := 1
  collisionOpcode := 2
  nextDelay := 1
  coefficientBase := 13
  coefficientStride := 512
  collisionPayloadBase := 263
  collisionPayloadStride := 10368
  outputCoefficientBase := 37
  outputCoefficientStride := 1458
  coefficientBase_pos := by norm_num
  collisionPayloadBase_odd := by norm_num [Nat.odd_iff]
  collisionPayloadStride_even := by norm_num
  outputCoefficientBase_pos := by norm_num
  collision_base := by norm_num
  collision_stride := by norm_num
  renewal_base := by norm_num
  renewal_stride := by norm_num

/-- The one-delay, opcode-one defect family `H`. -/
def defect : AffineBreakoffDelayGate where
  delay := 1
  collisionOpcode := 1
  nextDelay := 1
  coefficientBase := 187
  coefficientStride := 256
  collisionPayloadBase := 7573
  collisionPayloadStride := 10368
  outputCoefficientBase := 355
  outputCoefficientStride := 486
  coefficientBase_pos := by norm_num
  collisionPayloadBase_odd := by norm_num [Nat.odd_iff]
  collisionPayloadStride_even := by norm_num
  outputCoefficientBase_pos := by norm_num
  collision_base := by norm_num
  collision_stride := by norm_num
  renewal_base := by norm_num
  renewal_stride := by norm_num

/-- Universal affine tail link from ether to defect. -/
def etherToDefect : AffineBreakoffDelayLink where
  first := ether
  second := defect
  firstTailBase := 67
  firstTailStride := 128
  secondTailBase := 381
  secondTailStride := 729
  shared_delay := rfl
  coefficient_base_link := by norm_num [ether, defect,
    AffineBreakoffDelayGate.outputCoefficient,
    AffineBreakoffDelayGate.coefficient]
  coefficient_stride_link := by norm_num [ether, defect]

/-- Universal affine tail link from defect back to ether. -/
def defectToEther : AffineBreakoffDelayLink where
  first := defect
  second := ether
  firstTailBase := 151
  firstTailStride := 256
  secondTailBase := 144
  secondTailStride := 243
  shared_delay := rfl
  coefficient_base_link := by norm_num [ether, defect,
    AffineBreakoffDelayGate.outputCoefficient,
    AffineBreakoffDelayGate.coefficient]
  coefficient_stride_link := by norm_num [ether, defect]

/-- Universal ether self-link used to append further ether cells. -/
def etherToEther : AffineBreakoffDelayLink where
  first := ether
  second := ether
  firstTailBase := 20
  firstTailStride := 256
  secondTailBase := 57
  secondTailStride := 729
  shared_delay := rfl
  coefficient_base_link := by norm_num [ether,
    AffineBreakoffDelayGate.outputCoefficient,
    AffineBreakoffDelayGate.coefficient]
  coefficient_stride_link := by norm_num [ether]

/-- The two independently generated affine links meet on the defect family
for every common upper tail. -/
theorem defect_bridge_tail (u : ℕ) :
    etherToDefect.secondTail (170 + 256 * u) =
      defectToEther.firstTail (485 + 729 * u) := by
  simp [AffineBreakoffDelayLink.secondTail,
    AffineBreakoffDelayLink.firstTail, etherToDefect, defectToEther]
  ring

/-- The three distinct gates executed by a one-cell glider. -/
def oneCellGates (u : ℕ) : List BreakoffDelayGate :=
  let v := 170 + 256 * u
  let w := 485 + 729 * u
  [etherToDefect.firstGate v, etherToDefect.secondGate v,
    defectToEther.secondGate w]

/-- The universal `E -> H -> E` execution links at both intermediate
break-off coordinates. -/
theorem oneCellGates_linked (u : ℕ) :
    BreakoffGateChainLinked (etherToDefect.firstGate (170 + 256 * u)).start
      (oneCellGates u) := by
  let v := 170 + 256 * u
  let w := 485 + 729 * u
  have hfirst := etherToDefect.endpoint_eq_start v
  have hbridge : etherToDefect.secondGate v = defectToEther.firstGate w := by
    change defect.member (etherToDefect.secondTail v) =
      defect.member (defectToEther.firstTail w)
    exact congrArg defect.member (defect_bridge_tail u)
  have hsecond := defectToEther.endpoint_eq_start w
  dsimp [oneCellGates, v, w, BreakoffGateChainLinked]
  constructor
  · rfl
  constructor
  · exact hfirst
  constructor
  · rw [hbridge]
    exact hsecond
  trivial

/-- Consequently, any honest incoming ternary factorization at the first
ether boundary gives a kernel-checked literal Collatz word for the complete
one-cell `E,H,E` macro. -/
noncomputable def oneCell_literal_semantics (u : ℕ) {r H : ℕ}
    (hstart : 0 < (etherToDefect.firstGate (170 + 256 * u)).start)
    (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor :
      8 * (etherToDefect.firstGate (170 + 256 * u)).start =
        3 ^ (r + 2) * H + 1) :
    BreakoffRunSemantics (breakoffGateChainDuration (oneCellGates u))
      (etherToDefect.firstGate (170 + 256 * u)).start
      (breakoffGateChainEndpoint
        (etherToDefect.firstGate (170 + 256 * u)).start (oneCellGates u))
      r H :=
  breakoffGateChain_literal_semantics (oneCellGates u) hstart hHpos hHodd
    hfactor (oneCellGates_linked u)

end BreakoffEtherGlider
end KontoroC
