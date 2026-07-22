/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ExecutableBreakoff

/-!
# Affine families of regenerative break-off delay gates

The exact search constructs delay gates in affine families and links two such
families coefficientwise.  This file makes those universal claims small Lean
certificates: one base equation and one stride equation replace bounded tail
replay.

Pairwise linkability is not an infinite orbit, and no such orbit is supplied.
-/

namespace KontoroC

/-- An affine family of proof-carrying regenerative delay gates. -/
structure AffineBreakoffDelayGate where
  delay : ℕ
  collisionOpcode : ℕ
  nextDelay : ℕ
  coefficientBase : ℕ
  coefficientStride : ℕ
  collisionPayloadBase : ℕ
  collisionPayloadStride : ℕ
  outputCoefficientBase : ℕ
  outputCoefficientStride : ℕ
  coefficientBase_pos : 0 < coefficientBase
  collisionPayloadBase_odd : Odd collisionPayloadBase
  collisionPayloadStride_even : Even collisionPayloadStride
  outputCoefficientBase_pos : 0 < outputCoefficientBase
  collision_base :
    3 ^ (2 * delay + 2) * coefficientBase =
      2 ^ collisionOpcode * collisionPayloadBase + 1
  collision_stride :
    3 ^ (2 * delay + 2) * coefficientStride =
      2 ^ collisionOpcode * collisionPayloadStride
  renewal_base :
    3 ^ collisionOpcode * collisionPayloadBase + 1 =
      2 ^ (3 * (nextDelay + 1)) * outputCoefficientBase
  renewal_stride :
    3 ^ collisionOpcode * collisionPayloadStride =
      2 ^ (3 * (nextDelay + 1)) * outputCoefficientStride

namespace AffineBreakoffDelayGate

def coefficient (f : AffineBreakoffDelayGate) (t : ℕ) : ℕ :=
  f.coefficientBase + f.coefficientStride * t

def collisionPayload (f : AffineBreakoffDelayGate) (t : ℕ) : ℕ :=
  f.collisionPayloadBase + f.collisionPayloadStride * t

def outputCoefficient (f : AffineBreakoffDelayGate) (t : ℕ) : ℕ :=
  f.outputCoefficientBase + f.outputCoefficientStride * t

theorem coefficient_pos (f : AffineBreakoffDelayGate) (t : ℕ) :
    0 < f.coefficient t := by
  dsimp [coefficient]
  exact lt_of_lt_of_le f.coefficientBase_pos (Nat.le_add_right _ _)

theorem collisionPayload_odd (f : AffineBreakoffDelayGate) (t : ℕ) :
    Odd (f.collisionPayload t) := by
  obtain ⟨b, hb⟩ := f.collisionPayloadBase_odd
  obtain ⟨s, hs⟩ := f.collisionPayloadStride_even
  refine ⟨b + s * t, ?_⟩
  dsimp [collisionPayload]
  rw [hb, hs]
  ring

theorem outputCoefficient_pos (f : AffineBreakoffDelayGate) (t : ℕ) :
    0 < f.outputCoefficient t := by
  dsimp [outputCoefficient]
  exact lt_of_lt_of_le f.outputCoefficientBase_pos (Nat.le_add_right _ _)

/-- Every natural tail is an exact regenerative gate. -/
def member (f : AffineBreakoffDelayGate) (t : ℕ) : BreakoffDelayGate where
  delay := f.delay
  collisionOpcode := f.collisionOpcode
  nextDelay := f.nextDelay
  coefficient := f.coefficient t
  collisionPayload := f.collisionPayload t
  outputCoefficient := f.outputCoefficient t
  coefficient_pos := f.coefficient_pos t
  collisionPayload_odd := f.collisionPayload_odd t
  outputCoefficient_pos := f.outputCoefficient_pos t
  collision_factor := by
    have hfull :
        3 ^ (2 * f.delay + 2) * f.coefficient t =
          2 ^ f.collisionOpcode * f.collisionPayload t + 1 := by
      dsimp [coefficient, collisionPayload]
      calc
        3 ^ (2 * f.delay + 2) *
            (f.coefficientBase + f.coefficientStride * t) =
          3 ^ (2 * f.delay + 2) * f.coefficientBase +
            (3 ^ (2 * f.delay + 2) * f.coefficientStride) * t := by ring
        _ = (2 ^ f.collisionOpcode * f.collisionPayloadBase + 1) +
            (2 ^ f.collisionOpcode * f.collisionPayloadStride) * t := by
              rw [f.collision_base, f.collision_stride]
        _ = 2 ^ f.collisionOpcode *
            (f.collisionPayloadBase + f.collisionPayloadStride * t) + 1 := by
              ring
    omega
  renewal_factor := by
    dsimp [collisionPayload, outputCoefficient]
    calc
      3 ^ f.collisionOpcode *
            (f.collisionPayloadBase + f.collisionPayloadStride * t) + 1 =
          (3 ^ f.collisionOpcode * f.collisionPayloadBase + 1) +
            (3 ^ f.collisionOpcode * f.collisionPayloadStride) * t := by ring
      _ = 2 ^ (3 * (f.nextDelay + 1)) * f.outputCoefficientBase +
            (2 ^ (3 * (f.nextDelay + 1)) *
              f.outputCoefficientStride) * t := by
            rw [f.renewal_base, f.renewal_stride]
      _ = 2 ^ (3 * (f.nextDelay + 1)) *
            (f.outputCoefficientBase + f.outputCoefficientStride * t) := by ring

@[simp] theorem member_delay (f : AffineBreakoffDelayGate) (t : ℕ) :
    (f.member t).delay = f.delay := rfl

@[simp] theorem member_nextDelay (f : AffineBreakoffDelayGate) (t : ℕ) :
    (f.member t).nextDelay = f.nextDelay := rfl

@[simp] theorem member_coefficient (f : AffineBreakoffDelayGate) (t : ℕ) :
    (f.member t).coefficient = f.coefficient t := rfl

@[simp] theorem member_outputCoefficient (f : AffineBreakoffDelayGate)
    (t : ℕ) :
    (f.member t).outputCoefficient = f.outputCoefficient t := rfl

end AffineBreakoffDelayGate

/-- A coefficientwise link between two affine gate families.  The two tail
parameters may themselves evolve affinely with a common free tail. -/
structure AffineBreakoffDelayLink where
  first : AffineBreakoffDelayGate
  second : AffineBreakoffDelayGate
  firstTailBase : ℕ
  firstTailStride : ℕ
  secondTailBase : ℕ
  secondTailStride : ℕ
  shared_delay : first.nextDelay = second.delay
  coefficient_base_link :
    first.outputCoefficient firstTailBase =
      second.coefficient secondTailBase
  coefficient_stride_link :
    first.outputCoefficientStride * firstTailStride =
      second.coefficientStride * secondTailStride

namespace AffineBreakoffDelayLink

def firstTail (L : AffineBreakoffDelayLink) (t : ℕ) : ℕ :=
  L.firstTailBase + L.firstTailStride * t

def secondTail (L : AffineBreakoffDelayLink) (t : ℕ) : ℕ :=
  L.secondTailBase + L.secondTailStride * t

def firstGate (L : AffineBreakoffDelayLink) (t : ℕ) : BreakoffDelayGate :=
  L.first.member (L.firstTail t)

def secondGate (L : AffineBreakoffDelayLink) (t : ℕ) : BreakoffDelayGate :=
  L.second.member (L.secondTail t)

/-- The outgoing coefficient of the first family equals the incoming
coefficient of the second for every common tail. -/
theorem coefficient_link (L : AffineBreakoffDelayLink) (t : ℕ) :
    L.first.outputCoefficient (L.firstTail t) =
      L.second.coefficient (L.secondTail t) := by
  dsimp [AffineBreakoffDelayGate.outputCoefficient,
    AffineBreakoffDelayGate.coefficient, firstTail, secondTail]
  have hbase := L.coefficient_base_link
  dsimp [AffineBreakoffDelayGate.outputCoefficient,
    AffineBreakoffDelayGate.coefficient] at hbase
  calc
    L.first.outputCoefficientBase +
        L.first.outputCoefficientStride *
          (L.firstTailBase + L.firstTailStride * t) =
      (L.first.outputCoefficientBase +
        L.first.outputCoefficientStride * L.firstTailBase) +
        (L.first.outputCoefficientStride * L.firstTailStride) * t := by ring
    _ = (L.second.coefficientBase +
        L.second.coefficientStride * L.secondTailBase) +
        (L.second.coefficientStride * L.secondTailStride) * t := by
          rw [hbase, L.coefficient_stride_link]
    _ = L.second.coefficientBase +
        L.second.coefficientStride *
          (L.secondTailBase + L.secondTailStride * t) := by ring

/-- The two ordinary one-register states link exactly. -/
theorem endpoint_eq_start (L : AffineBreakoffDelayLink) (t : ℕ) :
    (L.firstGate t).endpoint = (L.secondGate t).start := by
  dsimp [firstGate, secondGate, BreakoffDelayGate.endpoint,
    BreakoffDelayGate.start]
  rw [L.shared_delay, L.coefficient_link t]

/-- Two linked affine gate members compose into one universally checked
finite run. -/
theorem two_gate_run (L : AffineBreakoffDelayLink) (t : ℕ) :
    breakoffRun
        ((L.firstGate t).delay + 1 + ((L.secondGate t).delay + 1))
        (L.firstGate t).start =
      some (L.secondGate t).endpoint := by
  rw [breakoffRun_add, (L.firstGate t).run]
  rw [L.endpoint_eq_start t]
  exact (L.secondGate t).run

/-- The linked two-gate macro is strictly outward. -/
theorem outward (L : AffineBreakoffDelayLink) (t : ℕ) :
    (L.firstGate t).start < (L.secondGate t).endpoint := by
  exact lt_trans (L.firstGate t).outward
    (by rw [L.endpoint_eq_start t]; exact (L.secondGate t).outward)

end AffineBreakoffDelayLink

end KontoroC
