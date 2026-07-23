/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PeriodicAffineChartNoGo

/-!
# The autonomous ether counter cannot have a periodic branch tail

The zero-tail escape left by `AffineSuccessorCylinder` is an infinite orbit
of the autonomous public register.  In zero-based branch coordinates its
exact recurrence has the form

`2^(8*n+23) Y' = 3^(6*n+17) Y + 51*2^(8*n+3)`.

This file proves an adversarial restriction on such an orbit: its branch
sequence cannot be eventually periodic.  A finite controller, a fixed cycle
of ether lengths, or a periodic zero-tail dispatcher therefore cannot supply
the missing ordinary ray.  Any surviving candidate must choose genuinely
aperiodic, unbounded-context branch lengths.
-/

namespace KontoroC
namespace EtherCounterAperiodic

open ChargeBouncerPeriodicNoGo
open PeriodicAffineChartNoGo

/-- Binary denominator exponent for zero-based ether level `n`.  The research
branch numbered `n+1` has input valuation `8*n+3`, followed by the fixed
division by `2^20`. -/
def binaryExponent (n : ℕ) : ℕ := 8 * n + 23

/-- Ternary numerator exponent for zero-based ether level `n`. -/
def ternaryExponent (n : ℕ) : ℕ := 6 * n + 17

/-- Positive affine gain after eliminating the odd part of the register. -/
def edgeGain (n : ℕ) : ℕ := 51 * 2 ^ (8 * n + 3)

def edgeA (n : ℕ) : ℕ := 3 ^ ternaryExponent n
def edgeB (n : ℕ) : ℕ := 2 ^ binaryExponent n

/-- Every ether branch is strictly expanding before its integrality
condition is imposed. -/
theorem edge_expanding (n : ℕ) : edgeB n < edgeA n := by
  have hbase : 2 ^ 23 < 3 ^ 17 := by norm_num
  have hscale : (2 ^ 8) ^ n ≤ (3 ^ 6) ^ n :=
    Nat.pow_le_pow_left (by norm_num) n
  have hscale_pos : 0 < (2 ^ 8) ^ n := by positivity
  calc
    edgeB n = 2 ^ 23 * (2 ^ 8) ^ n := by
      simp [edgeB, binaryExponent, pow_add, pow_mul]
      ring
    _ < 3 ^ 17 * (2 ^ 8) ^ n :=
      (Nat.mul_lt_mul_right hscale_pos).2 hbase
    _ ≤ 3 ^ 17 * (3 ^ 6) ^ n := Nat.mul_le_mul_left _ hscale
    _ = edgeA n := by
      simp [edgeA, ternaryExponent, pow_add, pow_mul]
      ring

/-- Abstract infinite execution of the exact autonomous ether recurrence.
No Collatz semantics are hidden here: a concrete counterexample compiler must
construct this public arithmetic object and then connect it to its macro
semantics. -/
structure Orbit where
  level : ℕ → ℕ
  value : ℕ → ℕ
  value_pos : ∀ t, 0 < value t
  balance : ∀ t,
    edgeB (level t) * value (t + 1) =
      edgeA (level t) * value t + edgeGain (level t)

/-- The normalized public form used by the executable research worker.  At
zero-based level `n`, the register is `2^(8*n+3) * oddPart`; a successful
step divides `3^(6*n+17)*oddPart+51` by `2^20`. -/
structure NormalizedOrbit where
  level : ℕ → ℕ
  value : ℕ → ℕ
  oddPart : ℕ → ℕ
  value_pos : ∀ t, 0 < value t
  factor : ∀ t,
    value t = 2 ^ (8 * level t + 3) * oddPart t
  transition : ∀ t,
    2 ^ 20 * value (t + 1) =
      3 ^ (6 * level t + 17) * oddPart t + 51

/-- Eliminating the odd part gives the affine recurrence used by the
periodic-chart obstruction. -/
def NormalizedOrbit.toOrbit (o : NormalizedOrbit) : Orbit where
  level := o.level
  value := o.value
  value_pos := o.value_pos
  balance t := by
    have hstep := o.transition t
    have hfactor := o.factor t
    calc
      edgeB (o.level t) * o.value (t + 1) =
          2 ^ (8 * o.level t + 3) *
            (2 ^ 20 * o.value (t + 1)) := by
        simp [edgeB, binaryExponent, pow_add]
        ring
      _ = 2 ^ (8 * o.level t + 3) *
            (3 ^ (6 * o.level t + 17) * o.oddPart t + 51) := by
        rw [hstep]
      _ = edgeA (o.level t) * o.value t + edgeGain (o.level t) := by
        rw [hfactor]
        simp [edgeA, edgeGain, ternaryExponent]
        ring

/-- Standard eventual periodicity after time `K`, with nonzero period `p`
supplied separately where needed. -/
def EventuallyPeriodicFrom (f : ℕ → ℕ) (K p : ℕ) : Prop :=
  ∀ k, f (K + k + p) = f (K + k)

private theorem periodic_schedule {f : ℕ → ℕ} {K p : ℕ}
    (hperiodic : EventuallyPeriodicFrom f K p) :
    ∀ t i, f (K + (p * t + i)) = f (K + i) := by
  intro t
  induction t with
  | zero =>
      intro i
      simp
  | succ t ih =>
      intro i
      calc
        f (K + (p * (t + 1) + i)) =
            f (K + (p * t + i) + p) := by
          congr 1
          ring
        _ = f (K + (p * t + i)) := hperiodic (p * t + i)
        _ = f (K + i) := ih i

/-- A periodic branch tail becomes a periodic affine chart orbit after the
finite transient is discarded. -/
def periodicChartOrbit (o : Orbit) (K p : ℕ)
    (hperiodic : EventuallyPeriodicFrom o.level K p) :
    PeriodicAffineChartOrbit p
      (fun i => edgeA (o.level (K + i)))
      (fun i => edgeB (o.level (K + i)))
      (fun i => edgeGain (o.level (K + i))) where
  value s := o.value (K + s)
  value_pos s := o.value_pos (K + s)
  balance t i hi := by
    have hschedule := periodic_schedule hperiodic t i
    have h := o.balance (K + (p * t + i))
    rw [hschedule] at h
    simpa [Nat.add_assoc] using h

private def exponentSum (e : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => exponentSum e n + e n

private theorem prefixProduct_pow (base : ℕ) (e : ℕ → ℕ) (n : ℕ) :
    prefixProduct (fun i => base ^ e i) n = base ^ exponentSum e n := by
  induction n with
  | zero => simp [prefixProduct, exponentSum]
  | succ n ih =>
      simp only [prefixProduct, exponentSum]
      rw [ih, ← pow_add]

/-- No positive exact ether-counter orbit has an eventually periodic branch
tail.  This rejects the entire finite-period zero-tail search space, not only
the observed `115 -> 59 -> 9 -> 1` finite path. -/
theorem branch_not_eventually_periodic (o : Orbit) (K p : ℕ)
    (hp : 0 < p) : ¬ EventuallyPeriodicFrom o.level K p := by
  intro hperiodic
  let chart := periodicChartOrbit o K p hperiodic
  apply chart.impossible_of_termwise_expanding
  · exact hp
  · intro i
    simp [edgeB]
  · intro i hi
    exact edge_expanding (o.level (K + i))
  · change
      (prefixProduct
        (fun i => 3 ^ ternaryExponent (o.level (K + i))) p).Coprime
      (prefixProduct
        (fun i => 2 ^ binaryExponent (o.level (K + i))) p)
    rw [prefixProduct_pow, prefixProduct_pow]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  · cases p with
    | zero => omega
    | succ p =>
        simp only [prefixProduct]
        have hprefix : 0 < prefixProduct
            (fun i => edgeB (o.level (K + i))) p :=
          prefixProduct_pos _ (fun i => by simp [edgeB]) p
        have hlast : 1 < edgeB (o.level (K + p)) := by
          rw [edgeB]
          exact Nat.one_lt_pow (by simp [binaryExponent]) (by omega)
        exact hlast.trans_le (Nat.le_mul_of_pos_left _ hprefix)

theorem NormalizedOrbit.branch_not_eventually_periodic
    (o : NormalizedOrbit) (K p : ℕ) (hp : 0 < p) :
    ¬ EventuallyPeriodicFrom o.level K p :=
  EtherCounterAperiodic.branch_not_eventually_periodic o.toOrbit K p hp

/-- Times at which a proposed branch period fails. -/
def periodBreaks (o : Orbit) (p : ℕ) : Set ℕ :=
  {t | o.level (t + p) ≠ o.level t}

/-- Every positive proposed period is broken infinitely often. -/
theorem periodBreaks_infinite (o : Orbit) {p : ℕ} (hp : 0 < p) :
    (periodBreaks o p).Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  apply branch_not_eventually_periodic o (M + 1) p hp
  intro t
  by_contra hne
  have hmem : M + 1 + t ∈ periodBreaks o p := by
    change o.level ((M + 1 + t) + p) ≠ o.level (M + 1 + t)
    exact hne
  have := hM (M + 1 + t) hmem
  omega

/-! ## Finite autonomous dispatchers -/

/-- A factorization of the ether-level sequence through an autonomous finite
state machine.  Reading the unbounded numerical register is deliberately not
allowed: if a controller reads it, that register is part of its effective
state. -/
structure AutonomousFiniteBranchController (o : Orbit)
    (σ : Type*) [Finite σ] where
  phase : ℕ → σ
  next : σ → σ
  emit : σ → ℕ
  phase_succ : ∀ t, phase (t + 1) = next (phase t)
  level_eq : ∀ t, o.level t = emit (phase t)

namespace AutonomousFiniteBranchController

variable {o : Orbit} {σ : Type*} [Finite σ]

private theorem phase_future_eq
    (c : AutonomousFiniteBranchController o σ)
    {i j : ℕ} (hij : c.phase i = c.phase j) (t : ℕ) :
    c.phase (i + t) = c.phase (j + t) := by
  induction t with
  | zero => simpa using hij
  | succ t ih =>
      calc
        c.phase (i + (t + 1)) = c.next (c.phase (i + t)) := by
          simpa [Nat.add_assoc] using c.phase_succ (i + t)
        _ = c.next (c.phase (j + t)) := congrArg c.next ih
        _ = c.phase (j + (t + 1)) := by
          simpa [Nat.add_assoc] using (c.phase_succ (j + t)).symm

/-- No autonomous finite-state machine can choose the branch levels of an
infinite exact ether-counter orbit. -/
theorem impossible (c : AutonomousFiniteBranchController o σ) : False := by
  obtain ⟨i, j, hne, hij⟩ :=
    Finite.exists_ne_map_eq_of_infinite c.phase
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply branch_not_eventually_periodic o i (j - i) (by omega)
    intro t
    rw [c.level_eq, c.level_eq]
    apply congrArg c.emit
    have hji : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
    calc
      c.phase (i + t + (j - i)) = c.phase (i + (t + (j - i))) := by
        congr 1
        omega
      _ = c.phase ((i + (j - i)) + t) := by
        congr 1
        ac_rfl
      _ = c.phase (j + t) := by rw [hji]
      _ = c.phase (i + t) := (phase_future_eq c hij t).symm
  · apply branch_not_eventually_periodic o j (i - j) (by omega)
    intro t
    rw [c.level_eq, c.level_eq]
    apply congrArg c.emit
    have hij' : j + (i - j) = i := Nat.add_sub_of_le (Nat.le_of_lt hgt)
    calc
      c.phase (j + t + (i - j)) = c.phase (j + (t + (i - j))) := by
        congr 1
        omega
      _ = c.phase ((j + (i - j)) + t) := by
        congr 1
        ac_rfl
      _ = c.phase (i + t) := by rw [hij']
      _ = c.phase (j + t) := (phase_future_eq c hij.symm t).symm

theorem no_controller :
    ¬ Nonempty (AutonomousFiniteBranchController o σ) := by
  rintro ⟨c⟩
  exact c.impossible

end AutonomousFiniteBranchController

end EtherCounterAperiodic
end KontoroC
