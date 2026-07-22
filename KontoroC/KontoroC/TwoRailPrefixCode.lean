/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineTwoRail

/-!
# The two-rail LSB-first prefix decoder

For a fixed amplifier length, the low bits of the odd input payload determine
the complete two-rail gate shape.  This file proves uniqueness directly from
the exact gate balances and packages every gate as its full dyadic cylinder.

The point is architectural: an unbounded payload can select a changing gate
word even though an autonomous finite-state selector cannot.
-/

namespace KontoroC

/-- Uniqueness of the factorization of a positive natural as a power of two
times an odd natural. -/
theorem twoPow_mul_odd_unique {a b x y : ℕ}
    (hx : Odd x) (hy : Odd y)
    (heq : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have hxpos : 0 < x := by
    have := Nat.odd_iff.mp hx
    omega
  have hN : 2 ^ a * x ≠ 0 := by positivity
  have hleft := Nat.maxPowDvdDiv_of_pow_mul_eq hN rfl hx.not_two_dvd_nat
  have hright := Nat.maxPowDvdDiv_of_pow_mul_eq hN heq.symm
    hy.not_two_dvd_nat
  exact Prod.mk.inj (hleft.symm.trans hright)

/-- The four parameters that determine a two-rail valuation word once the
amplifier length is fixed. -/
structure TwoRailShape where
  cleanTicks : ℕ
  toPlusExtra : ℕ
  toMinusExtra : ℕ
  outputGap : ℕ
deriving DecidableEq

namespace TwoRailGate

def shape (g : TwoRailGate) : TwoRailShape :=
  ⟨g.cleanTicks, g.toPlusExtra, g.toMinusExtra, g.outputGap⟩

/-- The first exact balance uniquely recovers the collision valuation and
the complete positive-rail state. -/
theorem first_collision_unique (g h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) :
    g.toPlusExtra = h.toPlusExtra ∧ g.plusState = h.plusState := by
  apply twoPow_mul_odd_unique
  · exact delayState_odd (by omega)
  · exact delayState_odd (by omega)
  · calc
      2 ^ g.toPlusExtra * g.plusState =
          3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := by
        exact g.toPlus_balance
      _ = 3 ^ (h.ampTicks + 1) * h.inputPayload - 1 := by rw [hr, hP]
      _ = 2 ^ h.toPlusExtra * h.plusState := h.toPlus_balance.symm

/-- A positive separated state uniquely recovers its gap and odd payload. -/
theorem delayState_unique {q q' J J' : ℕ}
    (hq : Odd q) (hq' : Odd q')
    (heq : delayState q J = delayState q' J') :
    J = J' ∧ q = q' := by
  apply twoPow_mul_odd_unique hq hq'
  simpa [delayState, Nat.mul_comm] using heq

/-- The decoded positive-rail state uniquely recovers the cleanup length and
its odd payload. -/
theorem cleanup_unique (g h : TwoRailGate)
    (hplus : g.plusState = h.plusState) :
    g.cleanTicks = h.cleanTicks ∧ g.plusPayload = h.plusPayload := by
  have hfactor := delayState_unique g.plusPayload_odd h.plusPayload_odd hplus
  constructor
  · omega
  · exact hfactor.2

/-- Once the positive rail agrees, the second balance uniquely recovers the
cleanup collision valuation and complete output state. -/
theorem second_collision_unique (g h : TwoRailGate)
    (hs : g.cleanTicks = h.cleanTicks)
    (hQ : g.plusPayload = h.plusPayload) :
    g.toMinusExtra = h.toMinusExtra ∧ g.endpoint = h.endpoint := by
  apply twoPow_mul_odd_unique
  · exact (minusOneState_pos_odd g.outputPayload_pos g.outputGap_pos).2
  · exact (minusOneState_pos_odd h.outputPayload_pos h.outputGap_pos).2
  · calc
      2 ^ g.toMinusExtra * g.endpoint =
          1 + 3 ^ (g.cleanTicks + 1) * g.plusPayload := by
        exact g.toMinus_balance
      _ = 1 + 3 ^ (h.cleanTicks + 1) * h.plusPayload := by rw [hs, hQ]
      _ = 2 ^ h.toMinusExtra * h.endpoint := h.toMinus_balance.symm

/-- A positive `-1`-rail state uniquely recovers its gap and odd payload. -/
theorem minusOneState_unique {p p' L L' : ℕ}
    (hp : 0 < p) (hp' : 0 < p') (_hL : 0 < L) (_hL' : 0 < L')
    (hpodd : Odd p) (hpodd' : Odd p')
    (heq : minusOneState p L = minusOneState p' L') :
    L = L' ∧ p = p' := by
  apply twoPow_mul_odd_unique hpodd hpodd'
  have hleft : 0 < 2 ^ L * p := by positivity
  have hright : 0 < 2 ^ L' * p' := by positivity
  simp only [minusOneState] at heq
  omega

/-- Literal decoder theorem: for fixed amplifier length and input payload,
all four shape parameters and both hidden/output payloads are unique. -/
theorem decoded_parameters_unique (g h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) :
    g.shape = h.shape ∧
      g.plusPayload = h.plusPayload ∧
      g.outputPayload = h.outputPayload := by
  have hfirst := g.first_collision_unique h hr hP
  have hcleanup := g.cleanup_unique h hfirst.2
  have hsecond := g.second_collision_unique h hcleanup.1 hcleanup.2
  have hout := minusOneState_unique g.outputPayload_pos h.outputPayload_pos
    g.outputGap_pos h.outputGap_pos g.outputPayload_odd h.outputPayload_odd
    hsecond.2
  constructor
  · change TwoRailShape.mk g.cleanTicks g.toPlusExtra
        g.toMinusExtra g.outputGap =
      TwoRailShape.mk h.cleanTicks h.toPlusExtra
        h.toMinusExtra h.outputGap
    rw [hcleanup.1, hfirst.1, hsecond.1, hout.1]
  · exact ⟨hcleanup.2, hout.2⟩

/-- Strong form: the fixed rail length and literal input payload determine
the entire proof-carrying gate, not only its shape. -/
theorem eq_of_ampTicks_inputPayload (g h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) : g = h := by
  have hd := g.decoded_parameters_unique h hr hP
  cases g
  cases h
  simp only [shape, TwoRailShape.mk.injEq] at hd
  simp_all

/-- Type of exact gates decoded by one rail length and one literal payload. -/
def GateAt (r P : ℕ) :=
  {g : TwoRailGate // g.ampTicks = r ∧ g.inputPayload = P}

instance gateAt_subsingleton (r P : ℕ) : Subsingleton (GateAt r P) where
  allEq g h := by
    apply Subtype.ext
    exact g.1.eq_of_ampTicks_inputPayload h.1
      (g.2.1.trans h.2.1.symm) (g.2.2.trans h.2.2.symm)

/-- Existence predicate for the partial LSB decoder.  Uniqueness is supplied
globally by `gateAt_subsingleton`. -/
def Decodable (r P : ℕ) : Prop := Nonempty (GateAt r P)

/-- The exact gate selected by a decodable unbounded payload. -/
noncomputable def decodedGate {r P : ℕ} (h : Decodable r P) : TwoRailGate :=
  (Classical.choice h).1

@[simp] theorem decodedGate_ampTicks {r P : ℕ} (h : Decodable r P) :
    (decodedGate h).ampTicks = r := (Classical.choice h).2.1

@[simp] theorem decodedGate_inputPayload {r P : ℕ} (h : Decodable r P) :
    (decodedGate h).inputPayload = P := (Classical.choice h).2.2

/-- Any independently supplied gate at `(r,P)` is definitionally the same
mathematical gate as the decoder's choice. -/
theorem eq_decodedGate {r P : ℕ} (h : Decodable r P) (g : TwoRailGate)
    (hr : g.ampTicks = r) (hP : g.inputPayload = P) :
    g = decodedGate h :=
  g.eq_of_ampTicks_inputPayload (decodedGate h)
    (hr.trans (decodedGate_ampTicks h).symm)
    (hP.trans (decodedGate_inputPayload h).symm)

/-- Number of low payload bits fixed by a complete gate shape. -/
def codeExponent (g : TwoRailGate) : ℕ :=
  g.toPlusExtra + g.toMinusExtra + 2 * g.cleanTicks + g.outputGap + 3

/-- Dyadic stride of the input-payload cylinder. -/
def prefixInputStride (g : TwoRailGate) : ℕ := 2 ^ g.codeExponent

/-- Induced stride of the hidden positive-rail payload. -/
def prefixPlusStride (g : TwoRailGate) : ℕ :=
  3 ^ (g.ampTicks + 1) * 2 ^ (g.toMinusExtra + g.outputGap + 1)

/-- Induced stride of the output payload. -/
def prefixOutputStride (g : TwoRailGate) : ℕ :=
  2 * 3 ^ (g.ampTicks + g.cleanTicks + 2)

/-- Every exact gate extends to the complete affine cylinder with input
stride `2^E`, where `E` is its code exponent. -/
def prefixFamily (g : TwoRailGate) : AffineTwoRailFamily where
  base := g
  inputStride := g.prefixInputStride
  plusStride := g.prefixPlusStride
  outputStride := g.prefixOutputStride
  inputStride_even := by
    apply even_two.pow_of_ne_zero
    simp [codeExponent]
  plusStride_even := by
    apply Even.mul_left
    apply even_two.pow_of_ne_zero
    omega
  outputStride_even := even_two.mul_right _
  toPlus_stride_balance := by
    simp only [prefixPlusStride, prefixInputStride, codeExponent]
    rw [show g.toPlusExtra + g.toMinusExtra + 2 * g.cleanTicks +
          g.outputGap + 3 =
        g.toPlusExtra + (g.toMinusExtra + g.outputGap + 1) +
          (2 * g.cleanTicks + 2) by omega]
    simp only [pow_add]
    ring
  toMinus_stride_balance := by
    simp only [prefixOutputStride, prefixPlusStride]
    rw [show g.toMinusExtra + g.outputGap + 1 =
        g.toMinusExtra + g.outputGap + 1 by rfl,
      show g.ampTicks + g.cleanTicks + 2 =
        (g.cleanTicks + 1) + (g.ampTicks + 1) by omega]
    simp only [pow_add]
    norm_num
    ring

@[simp] theorem prefixFamily_inputStride (g : TwoRailGate) :
    g.prefixFamily.inputStride = 2 ^ g.codeExponent := rfl

@[simp] theorem prefixFamily_member_ampTicks (g : TwoRailGate) (z : ℕ) :
    (g.prefixFamily.member z).ampTicks = g.ampTicks := rfl

@[simp] theorem prefixFamily_member_shape (g : TwoRailGate) (z : ℕ) :
    (g.prefixFamily.member z).shape = g.shape := rfl

@[simp] theorem prefixFamily_member_inputPayload (g : TwoRailGate) (z : ℕ) :
    (g.prefixFamily.member z).inputPayload =
      g.inputPayload + 2 ^ g.codeExponent * z := rfl

/-- The natural-number part of the LSB-first dyadic cylinder selected by a
gate shape. -/
def prefixCylinder (g : TwoRailGate) : Set ℕ :=
  Set.range fun z => (g.prefixFamily.member z).inputPayload

/-- If two fixed-rail cylinders overlap, literal decoding forces their four
shape parameters to agree. -/
theorem shape_eq_of_prefixCylinder_overlap (g h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks) {P : ℕ}
    (hg : P ∈ g.prefixCylinder) (hh : P ∈ h.prefixCylinder) :
    g.shape = h.shape := by
  obtain ⟨z, hz⟩ := hg
  obtain ⟨w, hw⟩ := hh
  have hamp : (g.prefixFamily.member z).ampTicks =
      (h.prefixFamily.member w).ampTicks := by
    change g.ampTicks = h.ampTicks
    exact hr
  have hinput : (g.prefixFamily.member z).inputPayload =
      (h.prefixFamily.member w).inputPayload := hz.trans hw.symm
  have hdecoded := (g.prefixFamily.member z).decoded_parameters_unique
    (h.prefixFamily.member w) hamp hinput
  simpa using hdecoded.1

/-- Prefix-free form: distinct shapes at one amplifier length have disjoint
dyadic payload cylinders. -/
theorem prefixCylinder_disjoint (g h : TwoRailGate)
    (hr : g.ampTicks = h.ampTicks) (hshape : g.shape ≠ h.shape) :
    Disjoint g.prefixCylinder h.prefixCylinder := by
  rw [Set.disjoint_left]
  intro P hg hh
  exact hshape (shape_eq_of_prefixCylinder_overlap g h hr hg hh)

end TwoRailGate

/-- A controller specified only by its changing rail lengths and unbounded
input payloads.  `decodable` lets the prefix decoder select the unique gate;
linkage and outwardness remain the substantive all-level obligations. -/
structure PayloadDecodedTwoRailProgram where
  railLength : ℕ → ℕ
  payload : ℕ → ℕ
  decodable : ∀ t, TwoRailGate.Decodable (railLength t) (payload t)
  start_large :
    4 < (TwoRailGate.decodedGate (decodable 0)).start
  linked : ∀ t,
    (TwoRailGate.decodedGate (decodable t)).endpoint =
      (TwoRailGate.decodedGate (decodable (t + 1))).start
  outward : ∀ t,
    (TwoRailGate.decodedGate (decodable t)).start <
      (TwoRailGate.decodedGate (decodable t)).endpoint

namespace PayloadDecodedTwoRailProgram

/-- The unique decoded gate at macro-time `t`. -/
noncomputable def gate (g : PayloadDecodedTwoRailProgram) (t : ℕ) :
    TwoRailGate :=
  TwoRailGate.decodedGate (g.decodable t)

@[simp] theorem gate_ampTicks (g : PayloadDecodedTwoRailProgram) (t : ℕ) :
    (g.gate t).ampTicks = g.railLength t :=
  TwoRailGate.decodedGate_ampTicks _

@[simp] theorem gate_inputPayload (g : PayloadDecodedTwoRailProgram) (t : ℕ) :
    (g.gate t).inputPayload = g.payload t :=
  TwoRailGate.decodedGate_inputPayload _

/-- The payload-decoded interface compiles directly to the existing sound
infinite-program endpoint. -/
noncomputable def toInfiniteTwoRailProgram
    (g : PayloadDecodedTwoRailProgram) : InfiniteTwoRailProgram where
  gate := g.gate
  start_large := g.start_large
  linked := g.linked
  outward := g.outward

theorem not_conjecture (g : PayloadDecodedTwoRailProgram) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toInfiniteTwoRailProgram.not_conjecture

end PayloadDecodedTwoRailProgram

end KontoroC
