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

/-- The existential self-link address is equivalent to its small public
affine balance. -/
theorem etherTailStep_iff_balance (t t' : ℕ) :
    EtherTailStep t t' ↔ 256 * t' = 729 * t + 12 := by
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ether_tail_balance z
  · intro hbalance
    have hmod := congrArg (fun n : ℕ => n % 256) hbalance
    have htmod_lt : t % 256 < 256 := Nat.mod_lt _ (by omega)
    have htmod : t % 256 = 20 := by
      norm_num [Nat.add_mod, Nat.mul_mod] at hmod
      omega
    let z := t / 256
    have ht : t = 20 + 256 * z := by
      have hdiv := Nat.mod_add_div t 256
      dsimp [z]
      omega
    have ht' : t' = 57 + 729 * z := by
      rw [ht] at hbalance
      omega
    refine ⟨z, ?_, ?_⟩
    · simp [AffineBreakoffDelayLink.firstTail, etherToEther, ht]
    · simp [AffineBreakoffDelayLink.secondTail, etherToEther, ht']

/-- Proof-carrying adjacency for a finite list of ether tails. -/
def EtherTailChain : List ℕ → Prop
  | [] => True
  | [_] => True
  | t :: t' :: ts => EtherTailStep t t' ∧ EtherTailChain (t' :: ts)

/-- The same finite chain stated only with the public affine balance. -/
def EtherBalanceChain : List ℕ → Prop
  | [] => True
  | [_] => True
  | t :: t' :: ts =>
      256 * t' = 729 * t + 12 ∧ EtherBalanceChain (t' :: ts)

theorem etherTailChain_iff_balanceChain (ts : List ℕ) :
    EtherTailChain ts ↔ EtherBalanceChain ts := by
  induction ts with
  | nil => simp [EtherTailChain, EtherBalanceChain]
  | cons t ts ih =>
      cases ts with
      | nil => simp [EtherTailChain, EtherBalanceChain]
      | cons t' ts =>
          simp only [EtherTailChain, EtherBalanceChain]
          rw [etherTailStep_iff_balance, ih]

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

/-! ## Exact public packet endpoints for the one-cell glider -/

def levelOneBoundaryTail (K : ℕ) : ℕ := 2 ^ 20 * K - 10941

def oneCellInputPacket (q : ℕ) : ℕ := 3520715 + 2 ^ 23 * q
def oneCellOutputPacket (q : ℕ) : ℕ := 54200376 + 3 ^ 17 * q

def oneCellBridgeResidual (q : ℕ) : ℕ :=
  32 * oneCellInputPacket q - 1

@[simp] theorem etherToDefect_firstTail (z : ℕ) :
    etherToDefect.firstTail z = 67 + 128 * z := rfl

@[simp] theorem defectToEther_secondTail (z : ℕ) :
    defectToEther.secondTail z = 144 + 243 * z := rfl

theorem oneCellBridgeResidual_normal_form (q : ℕ) :
    oneCellBridgeResidual q = 112662879 + 268435456 * q := by
  dsimp [oneCellBridgeResidual, oneCellInputPacket]
  rw [Nat.mul_add]
  have hsmall : 1 ≤ 32 * 3520715 := by norm_num
  rw [Nat.add_comm (32 * 3520715) (32 * (8388608 * q)),
    Nat.add_sub_assoc hsmall]
  norm_num
  ring

theorem oneCellInputBoundary_normal_form (q : ℕ) :
    levelOneBoundaryTail (oneCellInputPacket q) =
      3691737240899 + 8796093022208 * q := by
  dsimp [levelOneBoundaryTail, oneCellInputPacket]
  rw [Nat.mul_add]
  have hsmall : 10941 ≤ 1048576 * 3520715 := by norm_num
  rw [Nat.add_comm (1048576 * 3520715) (1048576 * (8388608 * q)),
    Nat.add_sub_assoc hsmall]
  norm_num
  ring

theorem oneCellOutputBoundary_normal_form (q : ℕ) :
    levelOneBoundaryTail (oneCellOutputPacket q) =
      56833213453635 + 135413275557888 * q := by
  dsimp [levelOneBoundaryTail, oneCellOutputPacket]
  rw [Nat.mul_add]
  have hsmall : 10941 ≤ 1048576 * 54200376 := by norm_num
  rw [Nat.add_comm (1048576 * 54200376) (1048576 * (129140163 * q)),
    Nat.add_sub_assoc hsmall]
  norm_num
  ring

theorem returnedEtherTail_oneCell_normal_form (q : ℕ) :
    returnedEtherTail (oneCellBridgeResidual q) =
      19957891144212 + 47552535724032 * q := by
  rw [show returnedEtherTail (oneCellBridgeResidual q) =
    144 + 243 * (485 + 729 * oneCellBridgeResidual q) by rfl,
    oneCellBridgeResidual_normal_form]
  ring

/-- The affine `E -> H` input generated by the packet compiler is exactly the
global level-one break-off tail. -/
theorem oneCell_firstTail_eq_boundary (q : ℕ) :
    etherToDefect.firstTail (170 + 256 * oneCellBridgeResidual q) =
      levelOneBoundaryTail (oneCellInputPacket q) := by
  rw [etherToDefect_firstTail]
  rw [oneCellBridgeResidual_normal_form, oneCellInputBoundary_normal_form]
  ring

/-- One-cell packet congruence supplies the final self-link which exposes the
next global level-one packet boundary. -/
theorem oneCell_return_step (q : ℕ) :
    EtherTailStep (returnedEtherTail (oneCellBridgeResidual q))
      (levelOneBoundaryTail (oneCellOutputPacket q)) := by
  rw [etherTailStep_iff_balance]
  rw [returnedEtherTail_oneCell_normal_form,
    oneCellOutputBoundary_normal_form]
  ring

/-- The executable endpoint of `[E,H,E]` is the break-off start encoded by
the advertised output packet, universally in the free tail `q`. -/
theorem oneCell_endpoint_eq_output_boundary (q : ℕ) :
    breakoffGateChainEndpoint
        (etherToDefect.firstGate
          (170 + 256 * oneCellBridgeResidual q)).start
        (oneCellGates (oneCellBridgeResidual q)) =
      (ether.member (levelOneBoundaryTail (oneCellOutputPacket q))).start := by
  obtain ⟨z, ht, ht'⟩ := oneCell_return_step q
  have hlink := etherToEther.endpoint_eq_start z
  dsimp [oneCellGates, breakoffGateChainEndpoint]
  change (ether.member (returnedEtherTail (oneCellBridgeResidual q))).endpoint =
    (ether.member (levelOneBoundaryTail (oneCellOutputPacket q))).start
  rw [ht, ht']
  exact hlink

end BreakoffEtherGlider
end KontoroC
