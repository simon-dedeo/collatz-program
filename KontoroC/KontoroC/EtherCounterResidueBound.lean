/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodicTheta
import Mathlib.Data.ZMod.Units

/-!
# Finite EC17 residue certificates

For a prescribed finite list of one-based branches, backward EC17
substitution modulo `2^P` determines the initial core once the accumulated
binary exponent is at least `P`.  This file proves that bridge symbolically.
Large residue rows remain data: a checker only has to establish that the
least representative does not realize the prescribed natural prefix.
-/

namespace KontoroC
namespace EtherCounterResidueBound

variable {branch : ℕ → ℕ} {length : ℕ}

def binaryExponent (branch : ℕ → ℕ) (t : ℕ) : ℕ :=
  8 * branch (t + 1) + 15

def ternaryExponent (branch : ℕ → ℕ) (t : ℕ) : ℕ :=
  6 * branch t + 11

def binaryMass (branch : ℕ → ℕ) (start length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, binaryExponent branch (start + i)

theorem binaryMass_zero (branch : ℕ → ℕ) (start : ℕ) :
    binaryMass branch start 0 = 0 := by simp [binaryMass]

theorem binaryMass_succ (branch : ℕ → ℕ) (start length : ℕ) :
    binaryMass branch start (length + 1) =
      binaryExponent branch start + binaryMass branch (start + 1) length := by
  rw [binaryMass, Finset.sum_range_succ']
  simp only [binaryMass]
  have hsum :
      (∑ i ∈ Finset.range length,
        binaryExponent branch (start + (i + 1))) =
      ∑ i ∈ Finset.range length,
        binaryExponent branch (start + 1 + i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hsum]
  ac_rfl

/-- One exact backward EC17 step modulo `2^P`.  The inverse exists because
every power of three is a unit modulo every power of two. -/
def backStep (branch : ℕ → ℕ) (P t : ℕ) (x : ZMod (2 ^ P)) :
    ZMod (2 ^ P) :=
  ((2 : ZMod (2 ^ P)) ^ binaryExponent branch t * x - 17) *
    ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹

/-- Apply `length` backward steps beginning at time `start`. -/
def backwardEval (branch : ℕ → ℕ) (P : ℕ) :
    ℕ → ℕ → ZMod (2 ^ P) → ZMod (2 ^ P)
  | 0, _, x => x
  | length + 1, start, x =>
      backStep branch P start (backwardEval branch P length (start + 1) x)

/-- The certified residue obtained by putting zero at the terminal end. -/
def initialResidue (branch : ℕ → ℕ) (P length : ℕ) : ZMod (2 ^ P) :=
  backwardEval branch P length 0 0

theorem ternary_isUnit (branch : ℕ → ℕ) (P t : ℕ) :
    IsUnit ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) := by
  have hthree : IsUnit (3 : ZMod (2 ^ P)) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ P)).2
      ((by norm_num : Nat.Coprime 3 2).pow_right P)
  exact hthree.pow _

/-- A literal natural EC17 prefix on a prescribed branch schedule. -/
structure NaturalPrefix (branch : ℕ → ℕ) (length : ℕ) where
  branch_pos : ∀ t ≤ length, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t ≤ length, 0 < core t
  balance : ∀ t < length,
    2 ^ binaryExponent branch t * core (t + 1) =
      3 ^ ternaryExponent branch t * core t + 17

theorem backStep_core (g : NaturalPrefix branch length) (P t : ℕ)
    (ht : t < length) :
    backStep branch P t (g.core (t + 1) : ZMod (2 ^ P)) =
      (g.core t : ZMod (2 ^ P)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ P))) (g.balance t ht)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [backStep]
  have hu := ternary_isUnit branch P t
  calc
    ((2 : ZMod (2 ^ P)) ^ binaryExponent branch t * g.core (t + 1) - 17) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹ =
        ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t * g.core t) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹ := by
      rw [h]
      ring
    _ = g.core t *
        (((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹) := by ring
    _ = g.core t := by
      rw [ZMod.mul_inv_of_unit
        ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) hu, mul_one]

/-- Backward evaluation with the actual terminal core exactly recovers the
actual core at the beginning of the interval. -/
theorem backwardEval_core (g : NaturalPrefix branch length) (P start n : ℕ)
    (hbound : start + n ≤ length) :
    backwardEval branch P n start (g.core (start + n) : ZMod (2 ^ P)) =
      (g.core start : ZMod (2 ^ P)) := by
  induction n generalizing start with
  | zero => simp [backwardEval]
  | succ n ih =>
      rw [backwardEval]
      have htail := ih (start := start + 1) (by omega)
      rw [show start + (n + 1) = (start + 1) + n by omega, htail]
      exact backStep_core g P start (by omega)

/-- Exact dependence on the terminal residue: the difference has a factor
`2^binaryMass`.  The remaining factor is deliberately left existential,
because only its integrality matters for the residue certificate. -/
theorem backwardEval_sub_factor (branch : ℕ → ℕ) (P start length : ℕ)
    (x y : ZMod (2 ^ P)) :
    ∃ u : ZMod (2 ^ P),
      backwardEval branch P length start x -
          backwardEval branch P length start y =
        (2 : ZMod (2 ^ P)) ^ binaryMass branch start length * u * (x - y) := by
  induction length generalizing start with
  | zero =>
      refine ⟨1, ?_⟩
      simp [backwardEval, binaryMass]
  | succ length ih =>
      obtain ⟨u, hu⟩ := ih (start := start + 1)
      refine ⟨u * ((3 : ZMod (2 ^ P)) ^
        ternaryExponent branch start)⁻¹, ?_⟩
      rw [backwardEval, backwardEval, binaryMass_succ, pow_add]
      simp only [backStep]
      calc
        (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) x - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ -
            (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) y - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ =
            2 ^ binaryExponent branch start *
              (backwardEval branch P length (start + 1) x -
                backwardEval branch P length (start + 1) y) *
              (3 ^ ternaryExponent branch start)⁻¹ := by ring
        _ = 2 ^ binaryExponent branch start *
              2 ^ binaryMass branch (start + 1) length *
              (u * (3 ^ ternaryExponent branch start)⁻¹) * (x - y) := by
          rw [hu]
          ring

theorem two_pow_binaryMass_eq_zero (branch : ℕ → ℕ) (P start length : ℕ)
    (hprecision : P ≤ binaryMass branch start length) :
    (2 : ZMod (2 ^ P)) ^ binaryMass branch start length = 0 := by
  have hcast :
      ((2 ^ binaryMass branch start length : ℕ) : ZMod (2 ^ P)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.pow_dvd_pow 2 hprecision)
  simpa using hcast

/-- Once the accumulated binary exponent reaches the requested precision,
the backward result is independent of the arbitrary terminal residue. -/
theorem backwardEval_eq_zero_terminal (branch : ℕ → ℕ)
    (P start length : ℕ) (x : ZMod (2 ^ P))
    (hprecision : P ≤ binaryMass branch start length) :
    backwardEval branch P length start x =
      backwardEval branch P length start 0 := by
  obtain ⟨u, hu⟩ := backwardEval_sub_factor branch P start length x 0
  apply sub_eq_zero.mp
  rw [hu, two_pow_binaryMass_eq_zero branch P start length hprecision]
  simp

/-- QM58: every natural EC17 prefix on the schedule has the unique initial
residue computed by the zero-terminal backward recurrence. -/
theorem initial_core_cast_eq_residue (g : NaturalPrefix branch length) (P : ℕ)
    (hprecision : P ≤ binaryMass branch 0 length) :
    (g.core 0 : ZMod (2 ^ P)) = initialResidue branch P length := by
  rw [initialResidue]
  calc
    (g.core 0 : ZMod (2 ^ P)) =
        backwardEval branch P length 0 (g.core length : ZMod (2 ^ P)) := by
      symm
      simpa using backwardEval_core g P 0 length (by omega)
    _ = backwardEval branch P length 0 0 :=
      backwardEval_eq_zero_terminal branch P 0 length _ hprecision

/-- Abstract finite-certificate consumer (QM59).  If exact execution proves
that the least representative is not the initial core of any natural prefix,
then every natural prefix begins at least at the modulus. -/
theorem initial_core_ge_modulus_of_least_residue_fails
    (P : ℕ) (hprecision : P ≤ binaryMass branch 0 length)
    (hfail : ∀ g : NaturalPrefix branch length,
      g.core 0 ≠ (initialResidue branch P length).val)
    (g : NaturalPrefix branch length) :
    2 ^ P ≤ g.core 0 := by
  by_contra hlt
  push Not at hlt
  apply hfail g
  have hcast := initial_core_cast_eq_residue g P hprecision
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hlt] at hval
  exact hval

end EtherCounterResidueBound
end KontoroC
