/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ComponentDescentAtlas

/-!
# Cyclic tail certificates for Syracuse termination

A finite proof graph need not list an infinite descent atlas.  A state can
instead denote an affine family `base + step*k`.  Its base parameter is
checked directly.  For a positive parameter, a rule reads finitely many low
binary digits, transports the corresponding subfamily through an exact
Syracuse-component collision, and recurses on the remaining tail.  The state
graph may have cycles because the tail parameter strictly decreases.

This file gives the kernel-checked soundness theorem for the one-bit form.
It is the semantic target of the cyclic-descent CHC miner.  Existence of a
finite certificate rooted at `1+k` is an open problem; no Collatz proof is
claimed here.
-/

namespace KontoroC
namespace ComponentCyclicTail

open CleanLean.Collatz
open CollatzComponentHolonomy
open ComponentDescentAtlas

/-- A possibly cyclic system of component transports indexed by one binary
tail digit.  Each recursive call replaces `2*k+d` by `k`. -/
structure BinaryTailSystem (ι : Type) where
  base : ι → ℕ
  step : ι → ℕ
  nextEven : ι → ι
  nextOdd : ι → ι
  base_pos : ∀ i, 0 < base i
  step_pos : ∀ i, 0 < step i
  base_merge_one : ∀ i, Merge (base i) 1
  even_merge : ∀ i k,
    Merge (base i + step i * (2 * k))
      (base (nextEven i) + step (nextEven i) * k)
  odd_merge : ∀ i k,
    Merge (base i + step i * (2 * k + 1))
      (base (nextOdd i) + step (nextOdd i) * k)

namespace BinaryTailSystem

def source (sys : BinaryTailSystem ι) (i : ι) (k : ℕ) : ℕ :=
  sys.base i + sys.step i * k

theorem source_pos (sys : BinaryTailSystem ι) (i : ι) (k : ℕ) :
    0 < sys.source i k := by
  exact Nat.add_pos_left (sys.base_pos i) _

/-- The cyclic graph is sound because every edge deletes one low binary
digit from the ordinary tail parameter. -/
theorem merge_one (sys : BinaryTailSystem ι) :
    ∀ k : ℕ, ∀ i : ι, Merge (sys.source i k) 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro i
      by_cases hk : k = 0
      · subst k
        simpa [source] using sys.base_merge_one i
      · let tail := k / 2
        have htail : tail < k := by
          apply Nat.div_lt_self
          · omega
          · omega
        have hdecomp := Nat.mod_add_div k 2
        rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
        · have hkEven : k = 2 * tail := by
            dsimp [tail]
            omega
          have hedge := sys.even_merge i tail
          rw [← hkEven] at hedge
          exact merge_trans hedge (ih tail htail (sys.nextEven i))
        · have hkOdd : k = 2 * tail + 1 := by
            dsimp [tail]
            omega
          have hedge := sys.odd_merge i tail
          rw [← hkOdd] at hedge
          exact merge_trans hedge (ih tail htail (sys.nextOdd i))

/-- A root state literally parametrizing `1+k` proves Syracuse. -/
theorem syracuseConjecture_of_root (sys : BinaryTailSystem ι) (root : ι)
    (hbase : sys.base root = 1) (hstep : sys.step root = 1) :
    SyracuseConjecture := by
  intro n hn
  let k := n - 1
  have hsource : sys.source root k = n := by
    simp [source, hbase, hstep, k]
    omega
  exact syracuseReachesOne_of_merge_one
    (hsource ▸ sys.merge_one k root)

end BinaryTailSystem

/-- The variable-radix certificate language used by the miner.  A state may
read several binary tail digits at once by taking `radix = 2^p`. -/
structure RadixTailSystem (ι : Type) where
  base : ι → ℕ
  step : ι → ℕ
  radix : ι → ℕ
  next : ι → ℕ → ι
  base_pos : ∀ i, 0 < base i
  step_pos : ∀ i, 0 < step i
  radix_ge_two : ∀ i, 2 ≤ radix i
  base_merge_one : ∀ i, Merge (base i) 1
  branch_merge : ∀ i digit tail, digit < radix i →
    Merge (base i + step i * (radix i * tail + digit))
      (base (next i digit) + step (next i digit) * tail)

namespace RadixTailSystem

def source (sys : RadixTailSystem ι) (i : ι) (k : ℕ) : ℕ :=
  sys.base i + sys.step i * k

theorem merge_one (sys : RadixTailSystem ι) :
    ∀ k : ℕ, ∀ i : ι, Merge (sys.source i k) 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro i
      by_cases hk : k = 0
      · subst k
        simpa [source] using sys.base_merge_one i
      · let q := sys.radix i
        let tail := k / q
        let digit := k % q
        have hq : 1 < q := by
          have htwo := sys.radix_ge_two i
          dsimp [q]
          omega
        have htail : tail < k := by
          dsimp [tail]
          exact Nat.div_lt_self (by omega) hq
        have hdigit : digit < q := by
          dsimp [digit]
          exact Nat.mod_lt _ (by omega)
        have hdecomp : k = q * tail + digit := by
          have h := Nat.mod_add_div k q
          dsimp [tail, digit]
          omega
        have hedge := sys.branch_merge i digit tail (by simpa [q] using hdigit)
        rw [← hdecomp] at hedge
        exact merge_trans hedge (ih tail htail (sys.next i digit))

theorem syracuseConjecture_of_root (sys : RadixTailSystem ι) (root : ι)
    (hbase : sys.base root = 1) (hstep : sys.step root = 1) :
    SyracuseConjecture := by
  intro n hn
  let k := n - 1
  have hsource : sys.source root k = n := by
    simp [source, hbase, hstep, k]
    omega
  exact syracuseReachesOne_of_merge_one
    (hsource ▸ sys.merge_one k root)

end RadixTailSystem

/-- A general size-change certificate. Recursive rules may rewrite the tail
parameter arbitrarily; a supplied natural-valued rank must strictly decrease.
The miner specializes `targetParam` and `rank` to affine functions and asks an
SMT solver for their coefficients. -/
structure RankedTailSystem (ι : Type) where
  base : ι → ℕ
  step : ι → ℕ
  radix : ι → ℕ
  next : ι → ℕ → ι
  targetParam : ι → ℕ → ℕ → ℕ
  rank : ι → ℕ → ℕ
  base_pos : ∀ i, 0 < base i
  step_pos : ∀ i, 0 < step i
  radix_ge_two : ∀ i, 2 ≤ radix i
  base_merge_one : ∀ i, Merge (base i) 1
  branch_merge : ∀ i digit tail, digit < radix i →
    Merge (base i + step i * (radix i * tail + digit))
      (base (next i digit) +
        step (next i digit) * targetParam i digit tail)
  rank_decrease : ∀ i digit tail, digit < radix i →
    0 < radix i * tail + digit →
    rank (next i digit) (targetParam i digit tail) <
      rank i (radix i * tail + digit)

namespace RankedTailSystem

def source (sys : RankedTailSystem ι) (i : ι) (k : ℕ) : ℕ :=
  sys.base i + sys.step i * k

/-- Soundness of an arbitrary finite or infinite cyclic proof graph equipped
with a decreasing size-change rank. -/
theorem merge_one (sys : RankedTailSystem ι) :
    ∀ i : ι, ∀ k : ℕ, Merge (sys.source i k) 1 := by
  intro i k
  induction hrank : sys.rank i k using Nat.strong_induction_on generalizing i k with
  | h rank ih =>
      by_cases hk : k = 0
      · subst k
        simpa [source] using sys.base_merge_one i
      · let q := sys.radix i
        let tail := k / q
        let digit := k % q
        have hq : 0 < q := by
          have htwo := sys.radix_ge_two i
          dsimp [q]
          omega
        have hdigit : digit < q := by
          dsimp [digit]
          exact Nat.mod_lt _ hq
        have hdecomp : k = q * tail + digit := by
          have h := Nat.mod_add_div k q
          dsimp [tail, digit]
          omega
        have hedge := sys.branch_merge i digit tail (by simpa [q] using hdigit)
        rw [← hdecomp] at hedge
        have hrankLt := sys.rank_decrease i digit tail
          (by simpa [q] using hdigit) (by rw [← hdecomp]; omega)
        have hrankTarget :
            sys.rank (sys.next i digit) (sys.targetParam i digit tail) < rank := by
          calc
            sys.rank (sys.next i digit) (sys.targetParam i digit tail) <
                sys.rank i k := by simpa [hdecomp] using hrankLt
            _ = rank := hrank
        have htarget := ih
          (sys.rank (sys.next i digit) (sys.targetParam i digit tail))
          hrankTarget
          (sys.next i digit) (sys.targetParam i digit tail) rfl
        exact merge_trans hedge htarget

theorem syracuseConjecture_of_root (sys : RankedTailSystem ι) (root : ι)
    (hbase : sys.base root = 1) (hstep : sys.step root = 1) :
    SyracuseConjecture := by
  intro n hn
  let k := n - 1
  have hsource : sys.source root k = n := by
    simp [source, hbase, hstep, k]
    omega
  exact syracuseReachesOne_of_merge_one
    (hsource ▸ sys.merge_one root k)

end RankedTailSystem

end ComponentCyclicTail
end KontoroC
