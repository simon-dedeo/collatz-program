/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.BreakoffCounter

/-!
# Executable one-register break-off counter

This file turns the proof-carrying break-off equations into a computable
partial map on one natural number.  It is designed as the trusted seam for a
very large proposed witness: Lean need only evaluate exact powers, products,
remainders, and quotients for each macro-step.

No infinite orbit is constructed here.
-/

namespace KontoroC

/-- Binary exponent selected by the one-register counter. -/
def breakoffOpcode (k : ℕ) : ℕ := padicValNat 2 k

/-- Odd binary payload selected by the one-register counter. -/
def breakoffPayload (k : ℕ) : ℕ := k.divMaxPow 2

/-- The numerator whose divisibility by eight decides whether the next
break-off macro-step exists. -/
def breakoffNumerator (k : ℕ) : ℕ :=
  3 ^ (breakoffOpcode k + 2) * breakoffPayload k + 1

/-- Executable one-register partial transition

`B(k) = (3^(v₂(k)+2) * oddPart(k) + 1) / 8`.

The `Option` rejects exactly those inputs for which the displayed numerator
is not divisible by eight. -/
def breakoffNext (k : ℕ) : Option ℕ :=
  if 8 ∣ breakoffNumerator k then some (breakoffNumerator k / 8) else none

theorem breakoff_binary_factor (k : ℕ) :
    k = 2 ^ breakoffOpcode k * breakoffPayload k := by
  simpa [breakoffOpcode, breakoffPayload] using
    (Nat.pow_padicValNat_mul_divMaxPow 2 k).symm

theorem breakoffPayload_pos {k : ℕ} (hk : 0 < k) :
    0 < breakoffPayload k := by
  have hprod := Nat.pow_padicValNat_mul_divMaxPow 2 k
  have hpow : 0 < 2 ^ padicValNat 2 k := Nat.pow_pos (by omega)
  dsimp [breakoffPayload]
  nlinarith

theorem breakoffPayload_odd {k : ℕ} (hk : 0 < k) :
    Odd (breakoffPayload k) := by
  rw [Nat.odd_iff]
  have hlt : breakoffPayload k % 2 < 2 := Nat.mod_lt _ (by omega)
  have hne : breakoffPayload k % 2 ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_divMaxPow (p := 2) (n := k) (by omega)
      (Nat.ne_of_gt hk) ((Nat.dvd_iff_mod_eq_zero).2 hzero)
  omega

/-- Successful executable evaluation is precisely the exact break-off
equation. -/
theorem breakoffNext_eq_some_iff (k k' : ℕ) :
    breakoffNext k = some k' ↔ 8 * k' = breakoffNumerator k := by
  unfold breakoffNext
  split_ifs with hdiv
  · simp only [Option.some.injEq]
    constructor
    · intro h
      rw [← h]
      exact Nat.mul_div_cancel' hdiv
    · intro h
      rw [← h]
      simp
  · constructor
    · simp
    · intro heq
      exfalso
      apply hdiv
      exact ⟨k', heq.symm⟩

theorem breakoffNext_eq_some_iff_equation (k k' : ℕ) :
    breakoffNext k = some k' ↔
      8 * k' = 3 ^ (breakoffOpcode k + 2) * breakoffPayload k + 1 := by
  simpa [breakoffNumerator] using breakoffNext_eq_some_iff k k'

/-- A successful step lands automatically in the invariant residue class
`8 mod 9`. -/
theorem breakoffNext_mod_nine {k k' : ℕ}
    (hstep : breakoffNext k = some k') : k' % 9 = 8 := by
  have heq := (breakoffNext_eq_some_iff_equation k k').mp hstep
  have hdiv : 9 ∣ 3 ^ (breakoffOpcode k + 2) * breakoffPayload k := by
    refine ⟨3 ^ breakoffOpcode k * breakoffPayload k, ?_⟩
    rw [show breakoffOpcode k + 2 = 2 + breakoffOpcode k by omega, pow_add]
    norm_num
    ring
  obtain ⟨q, hq⟩ := hdiv
  have hmod : (8 * k') % 9 = 1 := by
    rw [heq, hq]
    simp [Nat.add_mod]
  rw [Nat.mul_mod] at hmod
  norm_num at hmod
  have hkmod := Nat.mod_lt k' (by omega : 0 < 9)
  omega

/-- Every successful positive step is strictly outward. -/
theorem breakoffNext_strictly_grows {k k' : ℕ} (hk : 0 < k)
    (hstep : breakoffNext k = some k') : k < k' := by
  have hcoeff := twoPow_add_three_lt_threePow_add_two (breakoffOpcode k)
  have hpayload := breakoffPayload_pos hk
  have hmul : 2 ^ (breakoffOpcode k + 3) * breakoffPayload k <
      3 ^ (breakoffOpcode k + 2) * breakoffPayload k :=
    (Nat.mul_lt_mul_right hpayload).2 hcoeff
  have hleft : 8 * k =
      2 ^ (breakoffOpcode k + 3) * breakoffPayload k := by
    conv_lhs => rw [breakoff_binary_factor k]
    rw [show breakoffOpcode k + 3 = 3 + breakoffOpcode k by omega, pow_add]
    norm_num
    ring
  have hright := (breakoffNext_eq_some_iff_equation k k').mp hstep
  omega

/-- An infinite orbit of the executable one-register transition.  Only the
initial ternary factorization is supplied; every later one is reconstructed
from executable evaluation of `breakoffNext`. -/
structure ExecutableBreakoffOrbit where
  k : ℕ → ℕ
  k_pos : ∀ t, 0 < k t
  step : ∀ t, breakoffNext (k t) = some (k (t + 1))
  initialRail : ℕ
  initialPayload : ℕ
  initialPayload_pos : 0 < initialPayload
  initialPayload_odd : Odd initialPayload
  initial_factor : 8 * k 0 = 3 ^ (initialRail + 2) * initialPayload + 1
  start_large : 4 < minusOneState (3 * initialPayload) (initialRail + 1)

namespace ExecutableBreakoffOrbit

/-- Register sequence reconstructed from the preceding executable opcode. -/
def rail (g : ExecutableBreakoffOrbit) : ℕ → ℕ
  | 0 => g.initialRail
  | t + 1 => breakoffOpcode (g.k t)

/-- Ternary payload sequence reconstructed from the preceding binary odd
part. -/
def ternaryPayload (g : ExecutableBreakoffOrbit) : ℕ → ℕ
  | 0 => g.initialPayload
  | t + 1 => breakoffPayload (g.k t)

@[simp] theorem rail_zero (g : ExecutableBreakoffOrbit) :
    g.rail 0 = g.initialRail := rfl

@[simp] theorem rail_succ (g : ExecutableBreakoffOrbit) (t : ℕ) :
    g.rail (t + 1) = breakoffOpcode (g.k t) := rfl

@[simp] theorem ternaryPayload_zero (g : ExecutableBreakoffOrbit) :
    g.ternaryPayload 0 = g.initialPayload := rfl

@[simp] theorem ternaryPayload_succ (g : ExecutableBreakoffOrbit) (t : ℕ) :
    g.ternaryPayload (t + 1) = breakoffPayload (g.k t) := rfl

/-- Compile the executable orbit into the previously audited proof-carrying
break-off interface. -/
def toBreakoffCounterOrbit (g : ExecutableBreakoffOrbit) :
    BreakoffCounterOrbit where
  k := g.k
  j t := breakoffOpcode (g.k t)
  u t := breakoffPayload (g.k t)
  r := g.rail
  H := g.ternaryPayload
  k_pos := g.k_pos
  u_pos t := breakoffPayload_pos (g.k_pos t)
  H_pos
    | 0 => g.initialPayload_pos
    | t + 1 => breakoffPayload_pos (g.k_pos t)
  u_odd t := breakoffPayload_odd (g.k_pos t)
  H_odd
    | 0 => g.initialPayload_odd
    | t + 1 => breakoffPayload_odd (g.k_pos t)
  binary_factor t := breakoff_binary_factor (g.k t)
  ternary_factor
    | 0 => g.initial_factor
    | t + 1 => by
        simpa using
          (breakoffNext_eq_some_iff_equation (g.k t) (g.k (t + 1))).mp
            (g.step t)
  next_r t := rfl
  next_H t := rfl
  start_large := g.start_large

theorem k_strictly_grows (g : ExecutableBreakoffOrbit) (t : ℕ) :
    g.k t < g.k (t + 1) :=
  breakoffNext_strictly_grows (g.k_pos t) (g.step t)

theorem k_mod_nine (g : ExecutableBreakoffOrbit) (t : ℕ) :
    g.k (t + 1) % 9 = 8 :=
  breakoffNext_mod_nine (g.step t)

/-- Main executable endpoint: an infinite positive orbit accepted by the
one-register checker refutes the literal standard Collatz conjecture. -/
theorem not_conjecture (g : ExecutableBreakoffOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toBreakoffCounterOrbit.not_conjecture

end ExecutableBreakoffOrbit

end KontoroC
