/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, Claude
-/
import Mathlib

/-!
# The Collatz (3x+1) conjecture: definitions and first lemmas

Trust note: `reachesOne_of_le_10000` uses `native_decide`, which trusts the
Lean compiler in addition to the kernel. Everything else is kernel-checked.

We use the unaccelerated Collatz step `T(n) = n/2` (n even), `3n+1` (n odd),
iterated with `Function.iterate`. Everything here is sorry-free.

Main contents:
* `Collatz.step`, `Collatz.ReachesOne`, `Collatz.Conjecture` — the statement.
* `Collatz.conjecture_of_descent` — the strong-induction reduction: if every
  `n ≥ 2` eventually maps strictly below itself, the conjecture holds.
* `Collatz.reachesOne_of_within` — soundness of a fueled Boolean checker,
  giving `native_decide`-powered verification on ranges.
* `Collatz.cycle_mem_trivial` — any cycle through a verified number is the
  trivial cycle {1, 4, 2}.
* `Collatz.counterexample_shape` — the only two disproof shapes: a divergent
  orbit, or an orbit falling into a cycle that avoids 1.
-/

set_option linter.style.nativeDecide false

namespace Collatz

/-- The Collatz step: halve if even, else `3n + 1`. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The orbit of `n` eventually hits 1. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, step^[k] n = 1

/-- The Collatz conjecture. -/
def Conjecture : Prop := ∀ n, 0 < n → ReachesOne n

/-! ## Basic facts about the step -/

theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step; split <;> omega

theorem iterate_pos (k : ℕ) {n : ℕ} (hn : 0 < n) : 0 < step^[k] n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (step_pos hn)

theorem iterate_zero_orbit (k : ℕ) : step^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; simpa [step] using ih

theorem not_reachesOne_zero : ¬ ReachesOne 0 := by
  rintro ⟨k, hk⟩
  simp [iterate_zero_orbit] at hk

/-- Powers of two reach 1 (in exactly `i` steps). -/
theorem pow_two_reachesOne (i : ℕ) : step^[i] (2 ^ i) = 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h : step (2 ^ (i + 1)) = 2 ^ i := by
      have h2 : (2 : ℕ) ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
      unfold step
      split <;> omega
    rw [Function.iterate_succ_apply, h, ih]

/-- Reaching 1 propagates backwards along the orbit. -/
theorem reachesOne_of_iterate {n k : ℕ} (h : ReachesOne (step^[k] n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [Function.iterate_add_apply]; exact hj⟩

/-! ## The descent reduction

The standard skeleton: to prove the conjecture it suffices to show every
`n ≥ 2` eventually drops strictly below its starting value. Any future
drift/density argument plugs in here. -/

theorem conjecture_of_descent (h : ∀ n, 2 ≤ n → ∃ k, step^[k] n < n) :
    Conjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h2 : n < 2
    · have : n = 1 := by omega
      exact ⟨0, this⟩
    · obtain ⟨k, hk⟩ := h n (by omega)
      have hm : 0 < step^[k] n := iterate_pos k hn
      exact reachesOne_of_iterate (ih (step^[k] n) hk hm)

/-! ## A fueled checker and verified ranges -/

/-- `reachesOneWithin f n = true` iff the orbit of `n` hits 1 within `f` steps. -/
def reachesOneWithin : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reachesOneWithin f (step n)

/-- Soundness of the checker. -/
theorem reachesOne_of_within {f n : ℕ} (h : reachesOneWithin f n = true) :
    ReachesOne n := by
  induction f generalizing n with
  | zero =>
    simp only [reachesOneWithin, beq_iff_eq] at h
    exact ⟨0, h⟩
  | succ f ih =>
    simp only [reachesOneWithin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- Every `1 ≤ n ≤ 10000` reaches 1. (Max total stopping time in range: 261, at n = 6171.) -/
theorem reachesOne_of_le_10000 {n : ℕ} (hn : 0 < n) (hle : n ≤ 10000) :
    ReachesOne n := by
  have h : ∀ m, m < 10000 → reachesOneWithin 300 (m + 1) = true := by native_decide
  have h' := h (n - 1) (by omega)
  rw [Nat.sub_add_cancel hn] at h'
  exact reachesOne_of_within h'

/-! ## The trivial cycle is the only cycle through verified numbers -/

/-- The forward orbit of 1 is the trivial cycle {1, 4, 2}. -/
theorem orbit_one (i : ℕ) : step^[i] 1 = 1 ∨ step^[i] 1 = 4 ∨ step^[i] 1 = 2 := by
  induction i with
  | zero => left; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> simp [step]

/-- A periodic point's orbit returns to it at every multiple of the period. -/
theorem iterate_mul_period {n k : ℕ} (hcyc : step^[k] n = n) (m : ℕ) :
    step^[k * m] n = n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.mul_succ, Function.iterate_add_apply, hcyc, ih]

/-- A periodic point that reaches 1 lies on the trivial cycle. -/
theorem cycle_mem_of_reachesOne {n k : ℕ} (hr : ReachesOne n) (hk : 0 < k)
    (hcyc : step^[k] n = n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨j, hj⟩ := hr
  have h1 : step^[k * j] n = n := iterate_mul_period hcyc j
  have hjle : j ≤ k * j := Nat.le_mul_of_pos_left j hk
  have h2 : k * j = (k * j - j) + j := by omega
  rw [h2, Function.iterate_add_apply, hj] at h1
  rcases orbit_one (k * j - j) with h | h | h <;> rw [h1] at h <;> tauto

/-- Any cycle through a number in the verified range is the trivial cycle. -/
theorem cycle_mem_trivial {n k : ℕ} (hn : 0 < n) (hle : n ≤ 10000) (hk : 0 < k)
    (hcyc : step^[k] n = n) : n = 1 ∨ n = 2 ∨ n = 4 :=
  cycle_mem_of_reachesOne (reachesOne_of_le_10000 hn hle) hk hcyc

/-- If the conjecture holds, the trivial cycle is the only cycle on positive integers. -/
theorem cycle_trivial_of_conjecture (hC : Conjecture) {n k : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hcyc : step^[k] n = n) : n = 1 ∨ n = 2 ∨ n = 4 :=
  cycle_mem_of_reachesOne (hC n hn) hk hcyc

/-! ## Shapes of a counterexample

A bounded orbit is eventually periodic (pigeonhole), so any counterexample to
the conjecture is either a divergent orbit or falls into a cycle avoiding 1.
These are the only two disproof shapes. -/

/-- A bounded orbit is eventually periodic. -/
theorem eventually_periodic_of_bounded {n B : ℕ} (hB : ∀ k, step^[k] n ≤ B) :
    ∃ i p, 0 < p ∧ step^[p] (step^[i] n) = step^[i] n := by
  obtain ⟨x, y, hxy, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨step^[k] n, Nat.lt_succ_of_le (hB k)⟩ : Fin (B + 1)))
  have hv : step^[x] n = step^[y] n := by simpa using congrArg Fin.val hfeq
  rcases Nat.lt_trichotomy x y with h | h | h
  · refine ⟨x, y - x, by omega, ?_⟩
    rw [← Function.iterate_add_apply]
    have hyx : y - x + x = y := by omega
    rw [hyx, ← hv]
  · exact absurd h hxy
  · refine ⟨y, x - y, by omega, ?_⟩
    rw [← Function.iterate_add_apply]
    have hxy' : x - y + y = x := by omega
    rw [hxy', hv]

/-- The certificate principle: a nonempty set of positive integers, closed under
the step and avoiding 1, refutes the conjecture. A machine-found certificate
(e.g. a regular language with verified closure) plugs in here. -/
theorem not_conjecture_of_invariant_set (L : Set ℕ)
    (hne : L.Nonempty) (hpos : ∀ n ∈ L, 0 < n) (hone : 1 ∉ L)
    (hclosed : ∀ n ∈ L, step n ∈ L) : ¬ Conjecture := by
  obtain ⟨n, hn⟩ := hne
  intro hC
  have hiter : ∀ k, step^[k] n ∈ L := by
    intro k
    induction k with
    | zero => simpa using hn
    | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  obtain ⟨k, hk⟩ := hC n (hpos n hn)
  exact hone (hk ▸ hiter k)

/-- Every counterexample is divergent or eventually periodic with 1 never visited. -/
theorem counterexample_shape {n : ℕ} (h : ¬ ReachesOne n) :
    (∀ B, ∃ k, B < step^[k] n) ∨
    (∃ i p, 0 < p ∧ step^[p] (step^[i] n) = step^[i] n ∧ ∀ j, step^[j] n ≠ 1) := by
  have hne : ∀ j, step^[j] n ≠ 1 := fun j hj => h ⟨j, hj⟩
  by_cases hb : ∀ B, ∃ k, B < step^[k] n
  · exact Or.inl hb
  · simp only [not_forall, not_exists, not_lt] at hb
    obtain ⟨B, hB⟩ := hb
    obtain ⟨i, p, hp, hcyc⟩ := eventually_periodic_of_bounded hB
    exact Or.inr ⟨i, p, hp, hcyc, hne⟩

end Collatz
