/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DispatcherBoundary

/-!
# Aperiodicity is compatible with an ordinary stabilized address

Address stabilization alone does not imply periodic output when a dispatcher
retains unbounded arithmetic memory.  This file gives a concrete two-symbol
counterexample: a natural clock emits a marker exactly at powers of two, while
all nested dyadic addresses are the residues of the ordinary natural zero.

This is a statement about symbolic dispatchers, not a construction of a
Collatz macro-glider.  Together with `DispatcherBoundary`, it identifies the
sharp abstract boundary: finite post-stabilization memory is impossible for a
growing macro-glider, whereas unbounded injective memory can remain genuinely
aperiodic.
-/

namespace KontoroC

/-- A symbolic controller with a natural-valued internal phase and nested
dyadic addresses belonging to one ordinary natural. -/
structure OrdinaryAddressSymbolicDispatcher (α : Type*) where
  phase : ℕ → ℕ
  next : ℕ → ℕ
  emit : ℕ → α
  phase_succ : ∀ t, phase (t + 1) = next (phase t)
  ordinaryAddress : ℕ
  nestedAddress : ℕ → ℕ
  nestedAddress_eq_residue :
    ∀ k, nestedAddress k = ordinaryAddress % 2 ^ k

namespace OrdinaryAddressSymbolicDispatcher

variable {α : Type*}

def symbol (d : OrdinaryAddressSymbolicDispatcher α) (t : ℕ) : α :=
  d.emit (d.phase t)

/-- Every positive proposed period must fail after every finite prefix. -/
def GenuinelyAperiodic (d : OrdinaryAddressSymbolicDispatcher α) : Prop :=
  ∀ K p, 0 < p →
    ∃ t, d.symbol (K + (t + p)) ≠ d.symbol (K + t)

end OrdinaryAddressSymbolicDispatcher

/-- The first of two symbols: a marker occurs exactly at powers of two.  We
use `Prop` as the alphabet; by propositional extensionality it has exactly two
elements. -/
def powerMarker (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

@[simp] theorem powerMarker_pow (k : ℕ) : powerMarker (2 ^ k) :=
  ⟨k, rfl⟩

theorem not_powerMarker_of_between {k n : ℕ}
    (hl : 2 ^ k < n) (hu : n < 2 ^ (k + 1)) :
    ¬ powerMarker n := by
  rintro ⟨j, rfl⟩
  have hkj : k < j := (Nat.pow_lt_pow_iff_right (by omega)).mp hl
  have hj : j < k + 1 := (Nat.pow_lt_pow_iff_right (by omega)).mp hu
  omega

/-- Powers of two have unbounded gaps, so their marker sequence is not
eventually periodic. -/
theorem powerMarker_not_eventually_periodic (K p : ℕ) (hp : 0 < p) :
    ∃ t, powerMarker (K + (t + p)) ≠ powerMarker (K + t) := by
  let k := K + p + 1
  have hKpow : K ≤ 2 ^ k := by
    have hK : K < 2 ^ K := Nat.lt_pow_self (by omega)
    have hpow : 2 ^ K ≤ 2 ^ k :=
      (Nat.pow_le_pow_iff_right (by omega)).2 (by dsimp [k]; omega)
    omega
  let t := 2 ^ k - K
  refine ⟨t, ?_⟩
  have hKt : K + t = 2 ^ k := Nat.add_sub_of_le hKpow
  have hppow : p < 2 ^ k := by
    have hp0 : p < 2 ^ p := Nat.lt_pow_self (by omega)
    have hpow : 2 ^ p ≤ 2 ^ k :=
      (Nat.pow_le_pow_iff_right (by omega)).2 (by dsimp [k]; omega)
    omega
  have hl : 2 ^ k < 2 ^ k + p := by omega
  have hu : 2 ^ k + p < 2 ^ (k + 1) := by
    calc
      2 ^ k + p < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hppow _
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hleft : K + (t + p) = 2 ^ k + p := by
    calc
      K + (t + p) = (K + t) + p := by omega
      _ = 2 ^ k + p := by rw [hKt]
  rw [hleft, hKt]
  intro heq
  exact (not_powerMarker_of_between hl hu)
    ((Iff.of_eq heq).mpr (powerMarker_pow k))

/-- Concrete two-symbol dispatcher: the phase is an unbounded natural clock,
while every nested address is the ordinary address zero. -/
def powerMarkerDispatcher : OrdinaryAddressSymbolicDispatcher Prop where
  phase t := t
  next t := t + 1
  emit := powerMarker
  phase_succ _ := rfl
  ordinaryAddress := 0
  nestedAddress _ := 0
  nestedAddress_eq_residue k := by simp

theorem powerMarkerDispatcher_two_symbols : Fintype.card Prop = 2 := by
  decide

theorem powerMarkerDispatcher_address_stable (k : ℕ) :
    powerMarkerDispatcher.nestedAddress k = 0 := rfl

/-- Absolute symbolic possibility result: a genuinely aperiodic dispatcher
can have nested addresses stabilizing to an ordinary natural. -/
theorem powerMarkerDispatcher_genuinelyAperiodic :
    powerMarkerDispatcher.GenuinelyAperiodic := by
  intro K p hp
  simpa [OrdinaryAddressSymbolicDispatcher.symbol, powerMarkerDispatcher]
    using powerMarker_not_eventually_periodic K p hp

theorem exists_genuinelyAperiodic_ordinaryAddress_dispatcher :
    ∃ d : OrdinaryAddressSymbolicDispatcher Prop,
      d.GenuinelyAperiodic ∧
        d.ordinaryAddress = 0 ∧
          ∀ k, d.nestedAddress k = 0 := by
  exact ⟨powerMarkerDispatcher, powerMarkerDispatcher_genuinelyAperiodic,
    rfl, powerMarkerDispatcher_address_stable⟩

end KontoroC
