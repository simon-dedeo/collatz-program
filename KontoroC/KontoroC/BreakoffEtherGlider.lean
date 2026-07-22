/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.BreakoffFiniteSemantics
import KontoroC.AffineBreakoffDelay
import KontoroC.AffineQuotientNoGo

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

/-! ## The ether self-link cannot persist forever -/

/-- Eliminating the shared affine tail from one `E -> E` link gives its
small public recurrence. -/
theorem ether_tail_balance (z : ℕ) :
    256 * etherToEther.secondTail z =
      729 * etherToEther.firstTail z + 12 := by
  simp [AffineBreakoffDelayLink.firstTail,
    AffineBreakoffDelayLink.secondTail, etherToEther]
  ring

/-- An attempted infinite execution which remains in the ether self-link. -/
structure InfiniteEtherTailPath where
  tail : ℕ → ℕ
  tail_pos : ∀ t, 0 < tail t
  balance : ∀ t, 256 * tail (t + 1) = 729 * tail t + 12

namespace InfiniteEtherTailPath

def toPositiveAffineGainOrbit (g : InfiniteEtherTailPath) :
    PositiveAffineGainOrbit 729 256 12 where
  value := g.tail
  value_pos := g.tail_pos
  balance := g.balance

/-- No ordinary natural tail can execute `E -> E` forever.  Finite ether
runs therefore require ever deeper congruence restrictions; they do not
define a hidden constant-ray counterexample. -/
theorem impossible (g : InfiniteEtherTailPath) : False := by
  exact g.toPositiveAffineGainOrbit.impossible (by norm_num) (by norm_num)
    (by norm_num)

end InfiniteEtherTailPath

/-! ## Arbitrary finite ether strings -/

/-- Two consecutive ether tails are one certified `E -> E` affine link. -/
def EtherTailStep (t t' : ℕ) : Prop :=
  ∃ z, t = etherToEther.firstTail z ∧ t' = etherToEther.secondTail z

/-- Proof-carrying adjacency for a finite list of ether tails. -/
def EtherTailChain : List ℕ → Prop
  | [] => True
  | [_] => True
  | t :: t' :: ts => EtherTailStep t t' ∧ EtherTailChain (t' :: ts)

def etherGates (ts : List ℕ) : List BreakoffDelayGate :=
  ts.map ether.member

/-- Every finite proof-carrying ether-tail string becomes a linked gate
program. -/
theorem etherGates_linked (t : ℕ) (ts : List ℕ)
    (hchain : EtherTailChain (t :: ts)) :
    BreakoffGateChainLinked (ether.member t).start
      (etherGates (t :: ts)) := by
  induction ts generalizing t with
  | nil => simp [etherGates, BreakoffGateChainLinked]
  | cons t' ts ih =>
      have hstep : EtherTailStep t t' := hchain.1
      obtain ⟨z, ht, ht'⟩ := hstep
      have hlink := etherToEther.endpoint_eq_start z
      have hlinked : (ether.member t).endpoint = (ether.member t').start := by
        rw [ht, ht']
        exact hlink
      change (ether.member t).start = (ether.member t).start ∧
        BreakoffGateChainLinked (ether.member t).endpoint
          (etherGates (t' :: ts))
      refine ⟨rfl, ?_⟩
      change (ether.member t).endpoint = (ether.member t').start ∧
        BreakoffGateChainLinked (ether.member t').endpoint (etherGates ts)
      exact ⟨hlinked, (ih t' hchain.2).2⟩

def returnedEtherTail (u : ℕ) : ℕ :=
  defectToEther.secondTail (485 + 729 * u)

/-- The complete gate list of a finite glider: its defect prefix followed by
one or more ether gates. -/
def gliderGates (u : ℕ) (moreEtherTails : List ℕ) :
    List BreakoffDelayGate :=
  let v := 170 + 256 * u
  [etherToDefect.firstGate v, etherToDefect.secondGate v] ++
    etherGates (returnedEtherTail u :: moreEtherTails)

/-- The `E,H` prefix and any finite certified `E` tail string compose to one
linked break-off gate program. -/
theorem gliderGates_linked (u : ℕ) (moreEtherTails : List ℕ)
    (hchain : EtherTailChain (returnedEtherTail u :: moreEtherTails)) :
    BreakoffGateChainLinked (etherToDefect.firstGate (170 + 256 * u)).start
      (gliderGates u moreEtherTails) := by
  let v := 170 + 256 * u
  let w := 485 + 729 * u
  have hfirst := etherToDefect.endpoint_eq_start v
  have hbridge : etherToDefect.secondGate v = defectToEther.firstGate w := by
    change defect.member (etherToDefect.secondTail v) =
      defect.member (defectToEther.firstTail w)
    exact congrArg defect.member (defect_bridge_tail u)
  have hsecond := defectToEther.endpoint_eq_start w
  have hether := etherGates_linked (returnedEtherTail u) moreEtherTails hchain
  dsimp [gliderGates, v, w, BreakoffGateChainLinked]
  refine ⟨rfl, hfirst, ?_⟩
  constructor
  · rw [hbridge]
    exact hsecond
  exact hether.2

/-- Literal semantics for any finite glider once its finite ether tail list
and the honest incoming chart are supplied. -/
noncomputable def glider_literal_semantics (u : ℕ)
    (moreEtherTails : List ℕ)
    (hchain : EtherTailChain (returnedEtherTail u :: moreEtherTails))
    {r H : ℕ}
    (hstart : 0 < (etherToDefect.firstGate (170 + 256 * u)).start)
    (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor :
      8 * (etherToDefect.firstGate (170 + 256 * u)).start =
        3 ^ (r + 2) * H + 1) :
    BreakoffRunSemantics
      (breakoffGateChainDuration (gliderGates u moreEtherTails))
      (etherToDefect.firstGate (170 + 256 * u)).start
      (breakoffGateChainEndpoint
        (etherToDefect.firstGate (170 + 256 * u)).start
        (gliderGates u moreEtherTails)) r H :=
  breakoffGateChain_literal_semantics (gliderGates u moreEtherTails)
    hstart hHpos hHodd hfactor (gliderGates_linked u moreEtherTails hchain)

end BreakoffEtherGlider
end KontoroC
