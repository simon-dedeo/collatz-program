/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnSuccessorBouncer
import KontoroC.KLDyadicReset

/-!
# Rigidity of the successor six-cell bouncer

The six splits `k+n+1=6` have equal source width and output stride, but this
does not make them six control instructions.  Their complete ordinary return
is the same affine map, and that map has a unique output from a fixed source.
Thus phase switching can recognize different internal exact valuations, but
cannot choose or write the next ordinary boundary source.

After erasing the internal phase, a putative successor ray is one fixed
nonautonomous dyadic reset program

`2^S F_(t+1) = 3^R F_t - defect`.

The generic inverse-limit theory in `KLDyadicReset` then gives the exact
ordinary-root gate: its canonical carry digits must eventually be identically
zero.  Positive bit production does not evade this gate.  It only acts on the
current quotient after the initial dyadic address has been selected.

This file constructs no ray and no Collatz counterexample.
-/

namespace KontoroC
namespace LongReturnSuccessorRigidity

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open LongReturnTwoRail
open LongReturnSuccessorBouncer
open KLDyadicReset

/-- A complete return has at most one ordinary output from a fixed source. -/
theorem returnBalance_output_unique
    {k g F X Y : ℕ}
    (hX : ReturnBalance k g F X) (hY : ReturnBalance k g F Y) :
    X = Y := by
  have hsum : defect k g + 2 ^ S k g * X =
      defect k g + 2 ^ S k g * Y := hX.symm.trans hY
  have hmul : 2 ^ S k g * X = 2 ^ S k g * Y :=
    Nat.add_left_cancel hsum
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-- The proposed six-letter phase alphabet is observational, not
controlling.  Any two enabled phase splits from the same source have the same
next ordinary boundary source. -/
theorem sixPhase_nextSource_unique
    {k n k' n' g F u u' knext gnext nnext Fnext unext
      knext' gnext' nnext' Fnext' unext' : ℕ}
    (hg : 1 < g) (hphase : k + n + 1 = 6)
    (hphase' : k' + n' + 1 = 6)
    (hstep : TwoRailStepAt k g n F u
      knext gnext nnext Fnext unext)
    (hstep' : TwoRailStepAt k' g n' F u'
      knext' gnext' nnext' Fnext' unext') :
    Fnext = Fnext' := by
  have hreturn := (twoRailStepAt_realizes_boundary_return hg hstep).2
  have hreturn' := (twoRailStepAt_realizes_boundary_return hg hstep').2
  rw [hphase] at hreturn
  rw [hphase'] at hreturn'
  exact returnBalance_output_unique hreturn hreturn'

/-- Phase-erased arithmetic target: one ordinary natural sequence obeying
the complete six-cell return at the successor opcode schedule. -/
structure SuccessorSixBalanceRay (g0 : ℕ) where
  source : ℕ → ℕ
  balance : ∀ t : ℕ,
    ReturnBalance 6 (g0 + t) (source t) (source (t + 1))

/-- The internal two-rail ray necessarily erases to the scalar full-return
ray. -/
def SuccessorSixRay.toBalanceRay {g0 : ℕ} (ray : SuccessorSixRay g0)
    (hg0 : 1 < g0) : SuccessorSixBalanceRay g0 where
  source := ray.source
  balance := ray.returnBalance hg0

/-- The fixed signed reset instruction at successor time `t`.  Its negative
affine digit is the long-return defect. -/
def successorSixReset (g0 t : ℕ) : ResetStep where
  N := S 6 (g0 + t)
  O := R 6 (g0 + t)
  delta := -((defect 6 (g0 + t) : ℕ) : ℤ)

/-- A scalar successor balance ray is literally an integer path following
the fixed signed reset program. -/
theorem SuccessorSixBalanceRay.follows
    {g0 : ℕ} (ray : SuccessorSixBalanceRay g0) :
    Follows (successorSixReset g0) (fun t => (ray.source t : ℤ)) := by
  intro t
  have h := ray.balance t
  simp only [ReturnBalance] at h
  have hz := congrArg (fun x : ℕ => (x : ℤ)) h
  push_cast at hz
  simp only [successorSixReset]
  rw [hz]
  ring

/-- Conversely, a pointwise nonnegative integer path of the fixed reset
program is exactly a natural full-return ray.  This isolates the arithmetic
construction problem without any internal phase coordinates. -/
theorem nonempty_successorSixBalanceRay_iff_nonnegative_follows (g0 : ℕ) :
    Nonempty (SuccessorSixBalanceRay g0) ↔
      ∃ m : ℕ → ℤ,
        Follows (successorSixReset g0) m ∧ ∀ t, 0 ≤ m t := by
  constructor
  · rintro ⟨ray⟩
    exact ⟨fun t => (ray.source t : ℤ), ray.follows,
      fun t => Int.natCast_nonneg (ray.source t)⟩
  · rintro ⟨m, hm, hnonneg⟩
    refine ⟨{ source := fun t => (m t).toNat, balance := ?_ }⟩
    intro t
    simp only [ReturnBalance]
    have hs := hm t
    simp only [successorSixReset] at hs
    have hs' :
        (3 : ℤ) ^ R 6 (g0 + t) * m t -
            (defect 6 (g0 + t) : ℤ) =
          (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) := by
      calc
        (3 : ℤ) ^ R 6 (g0 + t) * m t -
            (defect 6 (g0 + t) : ℤ) =
          (3 : ℤ) ^ R 6 (g0 + t) * m t +
            -((defect 6 (g0 + t) : ℕ) : ℤ) := by ring
        _ = (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) := hs.symm
    have hi :
        (3 : ℤ) ^ R 6 (g0 + t) * m t =
          (defect 6 (g0 + t) : ℤ) +
            (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) := by
      calc
        (3 : ℤ) ^ R 6 (g0 + t) * m t =
            ((3 : ℤ) ^ R 6 (g0 + t) * m t -
              (defect 6 (g0 + t) : ℤ)) +
                (defect 6 (g0 + t) : ℤ) := by ring
        _ = (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) +
              (defect 6 (g0 + t) : ℤ) := by rw [hs']
        _ = (defect 6 (g0 + t) : ℤ) +
              (2 : ℤ) ^ S 6 (g0 + t) * m (t + 1) := by ring
    have hi' :
        ((3 ^ R 6 (g0 + t) * (m t).toNat : ℕ) : ℤ) =
          ((defect 6 (g0 + t) +
            2 ^ S 6 (g0 + t) * (m (t + 1)).toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (hnonneg t),
        Int.toNat_of_nonneg (hnonneg (t + 1))]
      exact hi
    exact_mod_cast hi'

/-- Every reset writes at least one new binary bit. -/
theorem successorSixReset_N_pos (g0 t : ℕ) :
    0 < (successorSixReset g0 t).N := by
  change 0 < LongDoublingQuineThreshold.S 6 (g0 + t)
  simp only [LongDoublingQuineThreshold.S]
  omega

/-- Cumulative source precision dominates elapsed successor time. -/
theorem successorSixReset_cumulativeS_ge (g0 J : ℕ) :
    J ≤ (cumulative (successorSixReset g0) J).S := by
  induction J with
  | zero => simp [cumulative, initialData]
  | succ J ih =>
      rw [cumulative_succ_S]
      have hpos := successorSixReset_N_pos g0 J
      omega

/-- The fixed successor program has unbounded accumulated dyadic precision. -/
theorem successorSixReset_precision_unbounded (g0 : ℕ) :
    ∀ L, ∃ J, L ≤ (cumulative (successorSixReset g0) J).S := by
  intro L
  exact ⟨L, successorSixReset_cumulativeS_ge g0 L⟩

/-- Exact ordinary-root gate.  Any natural successor balance ray forces the
canonical inverse-limit carry digits of its fixed reset program eventually to
vanish identically. -/
theorem SuccessorSixBalanceRay.eventuallyZeroCarry
    {g0 : ℕ} (ray : SuccessorSixBalanceRay g0) :
    EventuallyZeroCarry (successorSixReset g0) := by
  apply eventuallyZeroCarry_of_follows
      (successorSixReset g0) (fun t => (ray.source t : ℤ)) ray.follows
  exact_mod_cast (Nat.zero_le (ray.source 0))

/-- The same zero-carry obligation applies to the richer two-rail target. -/
theorem SuccessorSixRay.eventuallyZeroCarry
    {g0 : ℕ} (ray : SuccessorSixRay g0) (hg0 : 1 < g0) :
    EventuallyZeroCarry (successorSixReset g0) :=
  (LongReturnSuccessorRigidity.SuccessorSixRay.toBalanceRay ray hg0).eventuallyZeroCarry

/-- Perpetually writing fresh canonical address digits would refute this
counterexample architecture rather than realize it. -/
theorem no_successorSixBalanceRay_of_nonzeroCarries
    (g0 : ℕ)
    (hcarry : NonzeroCarriesArbitrarilyLate (successorSixReset g0)) :
    ¬ Nonempty (SuccessorSixBalanceRay g0) := by
  rintro ⟨ray⟩
  obtain ⟨J, hzero⟩ := ray.eventuallyZeroCarry
  obtain ⟨K, hJK, hne⟩ := hcarry J
  exact hne (hzero K hJK)

/-- Difference-map rigidity: unbounded accumulated precision leaves at most
one ordinary initial source for the full successor program. -/
theorem SuccessorSixBalanceRay.initial_unique
    {g0 : ℕ} (ray ray' : SuccessorSixBalanceRay g0) :
    ray.source 0 = ray'.source 0 := by
  have h := initial_eq_of_unbounded_cumulative_precision
    (successorSixReset g0)
    (fun t => (ray.source t : ℤ))
    (fun t => (ray'.source t : ℤ))
    ray.follows ray'.follows (successorSixReset_precision_unbounded g0)
  exact_mod_cast h

/-- Determinism propagates the difference-map equality: if two full rays
exist, their entire ordinary source sequences coincide. -/
theorem SuccessorSixBalanceRay.source_unique
    {g0 : ℕ} (ray ray' : SuccessorSixBalanceRay g0) (t : ℕ) :
    ray.source t = ray'.source t := by
  induction t with
  | zero => exact ray.initial_unique ray'
  | succ t ih =>
      exact returnBalance_output_unique
        (show ReturnBalance 6 (g0 + t) (ray.source t) (ray.source (t + 1))
          from ray.balance t)
        (show ReturnBalance 6 (g0 + t) (ray.source t) (ray'.source (t + 1))
          by simpa [ih] using ray'.balance t)

end LongReturnSuccessorRigidity
end KontoroC
