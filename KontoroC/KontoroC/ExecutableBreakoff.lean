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

/-- An exact power-of-two/odd factorization recovers the executable opcode
and payload.  This is the certificate seam: no valuation computation has to
be trusted separately. -/
theorem breakoff_registers_of_factor {k j u : ℕ} (hu : Odd u)
    (hfactor : k = 2 ^ j * u) :
    breakoffOpcode k = j ∧ breakoffPayload k = u := by
  have hu_pos : 0 < u := by
    have := Nat.odd_iff.mp hu
    omega
  have hk_ne : k ≠ 0 := by
    rw [hfactor]
    positivity
  have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq hk_ne hfactor.symm
    hu.not_two_dvd_nat
  exact ⟨congrArg Prod.fst hspec, congrArg Prod.snd hspec⟩

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

/-- Execute finitely many break-off macro-steps, stopping at the first
illegal transition. -/
def breakoffRun : ℕ → ℕ → Option ℕ
  | 0, k => some k
  | n + 1, k => breakoffNext k >>= breakoffRun n

@[simp] theorem breakoffRun_zero (k : ℕ) : breakoffRun 0 k = some k := rfl

theorem breakoffRun_succ_of_step {k k' : ℕ}
    (hstep : breakoffNext k = some k') (n : ℕ) :
    breakoffRun (n + 1) k = breakoffRun n k' := by
  simp [breakoffRun, hstep]

theorem breakoffRun_add (m n k : ℕ) :
    breakoffRun (m + n) k = breakoffRun m k >>= breakoffRun n := by
  induction m generalizing k with
  | zero => simp [breakoffRun]
  | succ m ih =>
      simp only [Nat.succ_add, breakoffRun]
      cases h : breakoffNext k with
      | none => simp [h]
      | some k' => simp [h, ih]

/-- Any successful finite run of positive length is strictly outward. -/
theorem breakoffRun_strictly_grows {n k k' : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hrun : breakoffRun n k = some k') : k < k' := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      simp only [breakoffRun] at hrun
      cases hstep : breakoffNext k with
      | none => simp [hstep] at hrun
      | some y =>
          rw [hstep] at hrun
          have hky : k < y := breakoffNext_strictly_grows hk hstep
          cases n with
          | zero =>
              have hy_eq : y = k' := by simpa [breakoffRun] using hrun
              simpa [hy_eq] using hky
          | succ n =>
              have hy : 0 < y := lt_trans hk hky
              exact lt_trans hky (ih (by omega) hy hrun)

/-- One clean delay cell consumes three powers of two and multiplies its
coefficient by nine. -/
theorem breakoffNext_delay_cell (q c : ℕ) (hc : 0 < c) :
    breakoffNext (9 * 2 ^ (3 * (q + 1)) * c - 1) =
      some (9 * 2 ^ (3 * q) * (9 * c) - 1) := by
  let k := 9 * 2 ^ (3 * (q + 1)) * c - 1
  let k' := 9 * 2 ^ (3 * q) * (9 * c) - 1
  have htail_pos : 0 < 2 ^ (3 * (q + 1)) * c := by positivity
  have hbase_large : 1 < 9 * 2 ^ (3 * (q + 1)) * c := by nlinarith
  have hk_pos : 0 < k := by dsimp [k]; omega
  have hk_odd : Odd k := by
    rw [Nat.odd_iff]
    have hpow : 2 ∣ 2 ^ (3 * (q + 1)) := by
      exact dvd_pow_self 2 (by omega)
    obtain ⟨d, hd⟩ := hpow
    have hk_eq : k + 1 = 9 * 2 ^ (3 * (q + 1)) * c := by
      dsimp [k]
      omega
    have hbase_mod : (9 * 2 ^ (3 * (q + 1)) * c) % 2 = 0 := by
      rw [hd]
      rw [show 9 * (2 * d) * c = 2 * (9 * d * c) by ring]
      simp
    have hsum_mod : (k + 1) % 2 = 0 := by rw [hk_eq, hbase_mod]
    have hkmod_lt := Nat.mod_lt k (by omega : 0 < 2)
    omega
  have hregisters : breakoffOpcode k = 0 ∧ breakoffPayload k = k := by
    apply breakoff_registers_of_factor hk_odd
    simp
  apply (breakoffNext_eq_some_iff_equation k k').2
  rw [hregisters.1, hregisters.2]
  norm_num
  have hk_eq : k + 1 = 9 * 2 ^ (3 * (q + 1)) * c := by
    dsimp [k]
    omega
  have hk'_pos : 0 < 9 * 2 ^ (3 * q) * (9 * c) := by positivity
  have hk'_eq : k' + 1 = 9 * 2 ^ (3 * q) * (9 * c) := by
    dsimp [k']
    omega
  have hscale : 8 * (k' + 1) = 9 * (k + 1) := by
    rw [hk_eq, hk'_eq]
    rw [show 3 * (q + 1) = 3 * q + 3 by omega, pow_add]
    norm_num
    ring
  omega

/-- A delay line of length `q` is a universally verified compressed run: it
reaches the collision state without replaying its `q` cells individually. -/
theorem breakoffRun_delay (q c : ℕ) (hc : 0 < c) :
    breakoffRun q (9 * 2 ^ (3 * q) * c - 1) =
      some (3 ^ (2 * q + 2) * c - 1) := by
  induction q generalizing c with
  | zero => norm_num [breakoffRun]
  | succ q ih =>
      rw [breakoffRun_succ_of_step (breakoffNext_delay_cell q c hc)]
      rw [ih (9 * c) (by positivity)]
      congr 2
      rw [show 2 * (q + 1) + 2 = (2 * q + 2) + 2 by omega, pow_add]
      norm_num
      ring

/-- A proof-carrying regenerative delay/collision gate.  The equations are
the exact two valuation factorizations found by the symbolic constructor. -/
structure BreakoffDelayGate where
  delay : ℕ
  collisionOpcode : ℕ
  nextDelay : ℕ
  coefficient : ℕ
  collisionPayload : ℕ
  outputCoefficient : ℕ
  coefficient_pos : 0 < coefficient
  collisionPayload_odd : Odd collisionPayload
  outputCoefficient_pos : 0 < outputCoefficient
  collision_factor :
    3 ^ (2 * delay + 2) * coefficient - 1 =
      2 ^ collisionOpcode * collisionPayload
  renewal_factor :
    3 ^ collisionOpcode * collisionPayload + 1 =
      2 ^ (3 * (nextDelay + 1)) * outputCoefficient

namespace BreakoffDelayGate

def start (g : BreakoffDelayGate) : ℕ :=
  9 * 2 ^ (3 * g.delay) * g.coefficient - 1

def collision (g : BreakoffDelayGate) : ℕ :=
  3 ^ (2 * g.delay + 2) * g.coefficient - 1

def endpoint (g : BreakoffDelayGate) : ℕ :=
  9 * 2 ^ (3 * g.nextDelay) * g.outputCoefficient - 1

/-- The two exact factorization certificates eliminate the collision payload
to the single affine balance used by the symbolic gate search.  The
subtraction-free form is preferable over naturals. -/
theorem eliminated_balance (g : BreakoffDelayGate) :
    2 ^ (g.collisionOpcode + 3 * (g.nextDelay + 1)) *
        g.outputCoefficient + 3 ^ g.collisionOpcode =
      3 ^ (g.collisionOpcode + 2 * g.delay + 2) * g.coefficient +
        2 ^ g.collisionOpcode := by
  have hcollision_pos :
      0 < 3 ^ (2 * g.delay + 2) * g.coefficient :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.coefficient_pos
  have hcollision :
      3 ^ (2 * g.delay + 2) * g.coefficient =
        2 ^ g.collisionOpcode * g.collisionPayload + 1 := by
    have := g.collision_factor
    omega
  calc
    2 ^ (g.collisionOpcode + 3 * (g.nextDelay + 1)) *
          g.outputCoefficient + 3 ^ g.collisionOpcode =
        2 ^ g.collisionOpcode *
          (2 ^ (3 * (g.nextDelay + 1)) * g.outputCoefficient) +
            3 ^ g.collisionOpcode := by rw [pow_add]; ring
    _ = 2 ^ g.collisionOpcode *
          (3 ^ g.collisionOpcode * g.collisionPayload + 1) +
            3 ^ g.collisionOpcode := by rw [g.renewal_factor]
    _ = 3 ^ g.collisionOpcode *
          (2 ^ g.collisionOpcode * g.collisionPayload + 1) +
            2 ^ g.collisionOpcode := by ring
    _ = 3 ^ g.collisionOpcode *
          (3 ^ (2 * g.delay + 2) * g.coefficient) +
            2 ^ g.collisionOpcode := by rw [← hcollision]
    _ = 3 ^ (g.collisionOpcode + 2 * g.delay + 2) * g.coefficient +
          2 ^ g.collisionOpcode := by
        rw [show g.collisionOpcode + 2 * g.delay + 2 =
          g.collisionOpcode + (2 * g.delay + 2) by omega, pow_add]
        ring

/-- Conversely, once the collision factorization is known, the eliminated
affine balance recovers the renewal factorization exactly. -/
theorem renewal_factor_of_eliminated_balance
    (delay collisionOpcode nextDelay coefficient collisionPayload
      outputCoefficient : ℕ)
    (hcoefficient_pos : 0 < coefficient)
    (hcollision :
      3 ^ (2 * delay + 2) * coefficient - 1 =
        2 ^ collisionOpcode * collisionPayload)
    (hbalance :
      2 ^ (collisionOpcode + 3 * (nextDelay + 1)) * outputCoefficient +
          3 ^ collisionOpcode =
        3 ^ (collisionOpcode + 2 * delay + 2) * coefficient +
          2 ^ collisionOpcode) :
    3 ^ collisionOpcode * collisionPayload + 1 =
      2 ^ (3 * (nextDelay + 1)) * outputCoefficient := by
  have hcollision_pos : 0 < 3 ^ (2 * delay + 2) * coefficient := by
    exact Nat.mul_pos (Nat.pow_pos (by omega)) hcoefficient_pos
  have hcollision' :
      3 ^ (2 * delay + 2) * coefficient =
        2 ^ collisionOpcode * collisionPayload + 1 := by
    omega
  have hnormalized :
      2 ^ collisionOpcode *
          (2 ^ (3 * (nextDelay + 1)) * outputCoefficient) +
          3 ^ collisionOpcode =
        2 ^ collisionOpcode *
          (3 ^ collisionOpcode * collisionPayload + 1) +
          3 ^ collisionOpcode := by
    calc
      2 ^ collisionOpcode *
            (2 ^ (3 * (nextDelay + 1)) * outputCoefficient) +
            3 ^ collisionOpcode =
          2 ^ (collisionOpcode + 3 * (nextDelay + 1)) *
            outputCoefficient + 3 ^ collisionOpcode := by rw [pow_add]; ring
      _ = 3 ^ (collisionOpcode + 2 * delay + 2) * coefficient +
            2 ^ collisionOpcode := hbalance
      _ = 3 ^ collisionOpcode *
            (3 ^ (2 * delay + 2) * coefficient) +
            2 ^ collisionOpcode := by
          rw [show collisionOpcode + 2 * delay + 2 =
            collisionOpcode + (2 * delay + 2) by omega, pow_add]
          ring
      _ = 3 ^ collisionOpcode *
            (2 ^ collisionOpcode * collisionPayload + 1) +
            2 ^ collisionOpcode := by rw [hcollision']
      _ = 2 ^ collisionOpcode *
            (3 ^ collisionOpcode * collisionPayload + 1) +
            3 ^ collisionOpcode := by ring
  have hmul :
      2 ^ collisionOpcode *
          (2 ^ (3 * (nextDelay + 1)) * outputCoefficient) =
        2 ^ collisionOpcode *
          (3 ^ collisionOpcode * collisionPayload + 1) :=
    Nat.add_right_cancel hnormalized
  exact (Nat.mul_left_cancel (Nat.pow_pos (by omega) : 0 < 2 ^ collisionOpcode))
    hmul |>.symm

/-- The collision factorization determines the executable registers. -/
theorem collision_registers (g : BreakoffDelayGate) :
    breakoffOpcode g.collision = g.collisionOpcode ∧
      breakoffPayload g.collision = g.collisionPayload := by
  apply breakoff_registers_of_factor g.collisionPayload_odd
  exact g.collision_factor

/-- The collision step regenerates the requested clean delay. -/
theorem collision_step (g : BreakoffDelayGate) :
    breakoffNext g.collision = some g.endpoint := by
  apply (breakoffNext_eq_some_iff_equation g.collision g.endpoint).2
  rw [g.collision_registers.1, g.collision_registers.2]
  have hend_pos : 0 < 9 * 2 ^ (3 * g.nextDelay) * g.outputCoefficient := by
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
      g.outputCoefficient_pos
  have hend : g.endpoint + 1 =
      9 * 2 ^ (3 * g.nextDelay) * g.outputCoefficient := by
    dsimp [endpoint]
    omega
  have hrenew := g.renewal_factor
  rw [show 3 * (g.nextDelay + 1) = 3 * g.nextDelay + 3 by omega,
    pow_add] at hrenew
  norm_num at hrenew
  have hscale : 8 * (g.endpoint + 1) =
      9 * (3 ^ g.collisionOpcode * g.collisionPayload + 1) := by
    rw [hend, hrenew]
    ring
  let A := 3 ^ g.collisionOpcode * g.collisionPayload
  have hscale' : 8 * (g.endpoint + 1) = 9 * (A + 1) := hscale
  have hpow : 3 ^ (g.collisionOpcode + 2) * g.collisionPayload = 9 * A := by
    dsimp [A]
    rw [pow_add]
    norm_num
    ring
  rw [hpow]
  omega

/-- A whole regenerative gate is one compressed exact execution: `delay`
opcode-zero cells followed by the prescribed collision. -/
theorem run (g : BreakoffDelayGate) :
    breakoffRun (g.delay + 1) g.start = some g.endpoint := by
  rw [breakoffRun_add]
  rw [show breakoffRun g.delay g.start = some g.collision by
    simpa [start, collision] using
      breakoffRun_delay g.delay g.coefficient g.coefficient_pos]
  simp [breakoffRun, g.collision_step]

/-- Every regenerative delay gate is genuinely outward, independent of its
size or how its coefficients were generated. -/
theorem outward (g : BreakoffDelayGate) : g.start < g.endpoint := by
  have hstart_base : 1 < 9 * 2 ^ (3 * g.delay) * g.coefficient := by
    have htail : 0 < 2 ^ (3 * g.delay) * g.coefficient :=
      Nat.mul_pos (Nat.pow_pos (by omega)) g.coefficient_pos
    nlinarith
  have hstart : 0 < g.start := by
    dsimp [start]
    omega
  exact breakoffRun_strictly_grows (by omega) hstart g.run

end BreakoffDelayGate

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
