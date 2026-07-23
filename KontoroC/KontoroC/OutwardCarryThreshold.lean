/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCodeCounterexample

/-!
# Dyadic carry threshold for nested outward addresses

This file isolates QM157a--b from the particular first-passage language.  A
nested parity path has a cumulative bit length `length n`, canonical source
residue `residue n`, and nonnegative cylinder lift `carry n`.  The exact
extension law is

`residue (n+1) = residue n + 2^(length n) * carry n`.

Nonempty blocks give `n ≤ length n`.  Consequently every nonzero carry is
already visible above the dyadic threshold `2^n`.
-/

namespace KontoroC
namespace OutwardCarryThreshold

open Filter

structure CarryPath where
  length : ℕ → ℕ
  residue : ℕ → ℕ
  carry : ℕ → ℕ
  length_ge_depth : ∀ n, n ≤ length n
  extension : ∀ n,
    residue (n + 1) = residue n + 2 ^ length n * carry n

/-- QM157b, pointwise form: a positive lift at depth `n` forces the next
canonical residue above `2^n`. -/
theorem carry_pos_forces_dyadic (P : CarryPath) {n : ℕ}
    (hcarry : 0 < P.carry n) :
    2 ^ n ≤ P.residue (n + 1) := by
  have hpow : 2 ^ n ≤ 2 ^ P.length n :=
    Nat.pow_le_pow_right (by omega) (P.length_ge_depth n)
  rw [P.extension n]
  have hone : 2 ^ P.length n ≤ 2 ^ P.length n * P.carry n := by
    nlinarith [show 0 < 2 ^ P.length n by positivity]
  omega

/-- Eventual filter form of QM157b. -/
theorem eventually_carry_eq_zero_of_eventually_below_dyadic
    (P : CarryPath)
    (hsmall : ∀ᶠ n in atTop, P.residue (n + 1) < 2 ^ n) :
    ∀ᶠ n in atTop, P.carry n = 0 := by
  filter_upwards [hsmall] with n hn
  by_contra hne
  have hpos : 0 < P.carry n := Nat.pos_of_ne_zero hne
  exact (not_le_of_gt hn) (carry_pos_forces_dyadic P hpos)

/-- Quantified-natural form, convenient for construction workers which do
not use filters. -/
theorem exists_eventually_carry_eq_zero_of_below_dyadic
    (P : CarryPath)
    (hsmall : ∃ N, ∀ n, N ≤ n → P.residue (n + 1) < 2 ^ n) :
    ∃ N, ∀ n, N ≤ n → P.carry n = 0 := by
  obtain ⟨N, hN⟩ := hsmall
  refine ⟨N, fun n hn => ?_⟩
  by_contra hne
  have hpos : 0 < P.carry n := Nat.pos_of_ne_zero hne
  exact (not_le_of_gt (hN n hn)) (carry_pos_forces_dyadic P hpos)

/-- Contrapositive diagnostic: infinitely many positive carries force
infinitely many dyadic-threshold crossings. -/
theorem frequently_dyadic_le_of_frequently_carry_pos
    (P : CarryPath)
    (hcarry : ∀ N, ∃ n, N ≤ n ∧ 0 < P.carry n) :
    ∀ N, ∃ n, N ≤ n ∧ 2 ^ n ≤ P.residue (n + 1) := by
  intro N
  obtain ⟨n, hn, hpos⟩ := hcarry N
  exact ⟨n, hn, carry_pos_forces_dyadic P hpos⟩

end OutwardCarryThreshold
end KontoroC
