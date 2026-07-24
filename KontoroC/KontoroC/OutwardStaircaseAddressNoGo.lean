/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCircuitValuationNoGo

/-!
# A second-order staircase cannot itself be the ordinary root address

An exact recurrence `A(n+2) + A(n) = K*A(n+1)` with `K >= 3` and increasing
initial data grows at least geometrically.  Such a recurrence may still be a
compact description of growing counter or payload parameters.  It cannot be
the canonical dyadic initial-residue sequence of one ordinary seed.
-/

namespace KontoroC
namespace OutwardStaircaseAddressNoGo

open KLDyadicReset OutwardCoerciveConverse

/-- A subtraction-free natural form of the proposed second-order staircase
recurrence. -/
structure SecondOrderStaircase where
  multiplier : ℕ
  value : ℕ → ℕ
  multiplier_ge : 3 ≤ multiplier
  seed_lt : value 0 < value 1
  recurrence : ∀ n,
    value (n + 2) + value n = multiplier * value (n + 1)

namespace SecondOrderStaircase

/-- Every step after the initial pair more than doubles its predecessor. -/
theorem two_mul_lt_next (s : SecondOrderStaircase) (n : ℕ) :
    2 * s.value (n + 1) < s.value (n + 2) := by
  induction n with
  | zero =>
      change 2 * s.value 1 < s.value 2
      have hseed := s.seed_lt
      have hscale : 3 * s.value 1 ≤ s.multiplier * s.value 1 :=
        Nat.mul_le_mul_right (s.value 1) s.multiplier_ge
      have hrec :
          s.value 2 + s.value 0 = s.multiplier * s.value 1 := by
        simpa using s.recurrence 0
      omega
  | succ n ih =>
      change 2 * s.value (n + 2) < s.value (n + 3)
      have hprev : s.value (n + 1) < s.value (n + 2) := by omega
      have hscale :
          3 * s.value (n + 2) ≤ s.multiplier * s.value (n + 2) :=
        Nat.mul_le_mul_right (s.value (n + 2)) s.multiplier_ge
      have hrec :
          s.value (n + 3) + s.value (n + 1) =
            s.multiplier * s.value (n + 2) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using s.recurrence (n + 1)
      omega

/-- In particular the staircase is strictly increasing. -/
theorem strictMono (s : SecondOrderStaircase) : StrictMono s.value := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => exact s.seed_lt
  | succ n =>
      have h := s.two_mul_lt_next n
      have hlt : s.value (n + 1) < s.value (n + 2) := by omega
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hlt

/-- Explicit geometric lower bound from the second entry onward. -/
theorem twoPow_mul_seed_le (s : SecondOrderStaircase) (n : ℕ) :
    2 ^ n * s.value 1 ≤ s.value (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdouble := s.two_mul_lt_next n
      calc
        2 ^ (n + 1) * s.value 1 =
            2 * (2 ^ n * s.value 1) := by rw [pow_succ]; ring
        _ ≤ 2 * s.value (n + 1) := Nat.mul_le_mul_left 2 ih
        _ ≤ s.value (n + 2) := Nat.le_of_lt hdouble

/-- The staircase values are unbounded in ordinary height. -/
theorem values_unbounded (s : SecondOrderStaircase) :
    ∀ B, ∃ n, B < s.value n := by
  intro B
  have hseed := s.seed_lt
  have hseedPos : 0 < s.value 1 := by omega
  have hpow : 2 ^ B ≤ 2 ^ B * s.value 1 :=
    Nat.le_mul_of_pos_right _ hseedPos
  refine ⟨B + 1, ?_⟩
  exact B.lt_two_pow_self.trans_le
    (hpow.trans (s.twoPow_mul_seed_le B))

/-- If canonical reset residues are a staircase, they are unbounded and
therefore cannot come from an ordinary nonnegative initial integer. -/
theorem no_nonnegative_follows_of_initialResidue_staircase
    (s : SecondOrderStaircase) (e : ℕ → ResetStep)
    (haddress : ∀ n, initialResidue e n = s.value n) :
    ¬ ∃ m : ℕ → ℤ, Follows e m ∧ 0 ≤ m 0 := by
  apply no_nonnegative_follows_of_unbounded_residues e
  intro B
  obtain ⟨n, hn⟩ := s.values_unbounded B
  exact ⟨n, by simpa [haddress n] using hn⟩

/-- The same address identification rules out every coercive sublevel
certificate, regardless of its chosen symbolic state space or potential. -/
theorem no_coerciveSublevelCertificate_of_initialResidue_staircase
    (s : SecondOrderStaircase) (e : ℕ → ResetStep)
    (haddress : ∀ n, initialResidue e n = s.value n)
    (State : Type*) :
    ¬ Nonempty (CoerciveSublevelCertificate e State) := by
  rintro ⟨cert⟩
  apply cert.false_of_residuesUnbounded
  intro B
  obtain ⟨n, hn⟩ := s.values_unbounded B
  exact ⟨n, by simpa [haddress n] using hn⟩

end SecondOrderStaircase

end OutwardStaircaseAddressNoGo
end KontoroC
