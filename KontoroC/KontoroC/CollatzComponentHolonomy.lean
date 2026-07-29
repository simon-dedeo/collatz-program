/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Syracuse

/-!
# Affine holonomy inside Collatz components

Two positive integers are in the same Syracuse component when their forward
orbits merge.  Different legal inverse words can have the same linear part
but offsets differing by a power of three.  After division, this produces
consecutive integers in one component.

The first collision is the familiar pair `8k+4, 8k+5`.  The next two are

* `32k+4, 32k+5, 32k+6`, merging to `9k+2` in five Syracuse steps;
* `256k+98, ..., 256k+102`, merging to `27k+11` in eight steps.

Since multiplication by two is a backward Syracuse move, every component
which contains a number prime to three contains a representative `11 mod 27`.
Every positive component contains such a number.  Consequently every positive
Collatz component contains five consecutive positive integers.

This is a structural theorem, not the Collatz conjecture: two disjoint subsets
of the naturals can both contain arbitrarily placed finite intervals.  Its use
is as a new component-minimum descent interface.
-/

namespace KontoroC
namespace CollatzComponentHolonomy

open CleanLean.Collatz

/-- Two points lie in the same functional-graph component when their forward
Syracuse orbits have a common point. -/
def Merge (x y : ℕ) : Prop :=
  ∃ i j : ℕ, syracuseStep^[i] x = syracuseStep^[j] y

theorem merge_refl (x : ℕ) : Merge x x := by
  exact ⟨0, 0, rfl⟩

theorem merge_symm {x y : ℕ} (h : Merge x y) : Merge y x := by
  obtain ⟨i, j, hij⟩ := h
  exact ⟨j, i, hij.symm⟩

theorem merge_trans {x y z : ℕ} (hxy : Merge x y) (hyz : Merge y z) :
    Merge x z := by
  obtain ⟨i, j, hxy⟩ := hxy
  obtain ⟨k, l, hyz⟩ := hyz
  have hcomm (a b t : ℕ) :
      syracuseStep^[a] (syracuseStep^[b] t) =
        syracuseStep^[b] (syracuseStep^[a] t) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.add_comm]
  refine ⟨i + k, j + l, ?_⟩
  calc
    syracuseStep^[i + k] x = syracuseStep^[k] (syracuseStep^[i] x) := by
      rw [Function.iterate_add_apply, hcomm]
    _ = syracuseStep^[k] (syracuseStep^[j] y) := by rw [hxy]
    _ = syracuseStep^[j + k] y := by
      rw [Function.iterate_add_apply, hcomm]
    _ = syracuseStep^[j] (syracuseStep^[k] y) := by
      rw [Function.iterate_add_apply]
    _ = syracuseStep^[j] (syracuseStep^[l] z) := by rw [hyz]
    _ = syracuseStep^[j + l] z := by rw [Function.iterate_add_apply]

theorem merge_next (n : ℕ) : Merge (syracuseStep n) n := by
  exact ⟨0, 1, by simp⟩

theorem merge_of_common_target {x y t i j : ℕ}
    (hx : syracuseStep^[i] x = t) (hy : syracuseStep^[j] y = t) :
    Merge x y := by
  exact ⟨i, j, hx.trans hy.symm⟩

@[simp] theorem syracuseStep_two_mul (n : ℕ) :
    syracuseStep (2 * n) = n := by
  simp [syracuseStep]

@[simp] theorem syracuseStep_two_mul_add_one (n : ℕ) :
    syracuseStep (2 * n + 1) = 3 * n + 2 := by
  have hodd : (2 * n + 1) % 2 ≠ 0 := by omega
  rw [syracuseStep, if_neg hodd]
  omega

theorem affine_step_even {x y : ℕ} (h : x = 2 * y) :
    syracuseStep x = y := by
  rw [h, syracuseStep_two_mul]

theorem affine_step_odd {x y : ℕ} (h : x = 2 * y + 1) :
    syracuseStep x = 3 * y + 2 := by
  rw [h, syracuseStep_two_mul_add_one]

/-- A target-oriented form of the odd branch, convenient when the affine
output rather than the half-input is syntactically visible. -/
theorem affine_step_odd_to {x z : ℕ} (hodd : x % 2 ≠ 0)
    (hvalue : (3 * x + 1) / 2 = z) : syracuseStep x = z := by
  simp [syracuseStep, hodd, hvalue]

/-- The first affine-holonomy diamond. -/
theorem adjacent_pair_hits_mod_three_two (k : ℕ) :
    syracuseStep^[3] (8 * k + 4) = 3 * k + 2 ∧
      syracuseStep^[3] (8 * k + 5) = 3 * k + 2 := by
  constructor
  · change syracuseStep (syracuseStep (syracuseStep (8 * k + 4))) = 3 * k + 2
    rw [show syracuseStep (8 * k + 4) = 4 * k + 2 by
          apply affine_step_even <;> omega,
      show syracuseStep (4 * k + 2) = 2 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (2 * k + 1) = 3 * k + 2 by
          apply affine_step_odd_to <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (8 * k + 5))) = 3 * k + 2
    rw [show syracuseStep (8 * k + 5) = 12 * k + 8 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (12 * k + 8) = 6 * k + 4 by
          apply affine_step_even <;> omega,
      show syracuseStep (6 * k + 4) = 3 * k + 2 by
          apply affine_step_even <;> omega]

/-- The other unit residue has the same unit holonomy one step later. -/
theorem adjacent_pair_hits_mod_three_one (k : ℕ) :
    syracuseStep^[4] (16 * k + 4) = 3 * k + 1 ∧
      syracuseStep^[4] (16 * k + 5) = 3 * k + 1 := by
  constructor
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (16 * k + 4)))) = 3 * k + 1
    rw [show syracuseStep (16 * k + 4) = 8 * k + 2 by
          apply affine_step_even <;> omega,
      show syracuseStep (8 * k + 2) = 4 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (4 * k + 1) = 6 * k + 2 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (6 * k + 2) = 3 * k + 1 by
          apply affine_step_even <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (16 * k + 5)))) = 3 * k + 1
    rw [show syracuseStep (16 * k + 5) = 24 * k + 8 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (24 * k + 8) = 12 * k + 4 by
          apply affine_step_even <;> omega,
      show syracuseStep (12 * k + 4) = 6 * k + 2 by
          apply affine_step_even <;> omega,
      show syracuseStep (6 * k + 2) = 3 * k + 1 by
          apply affine_step_even <;> omega]

/-- Three distinct inverse words with the same linear part and consecutive
offsets modulo `3^2`. -/
theorem three_run_hits (k j : ℕ) (hj : j < 3) :
    syracuseStep^[5] (32 * k + 4 + j) = 9 * k + 2 := by
  interval_cases j
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (32 * k + 4))))) = 9 * k + 2
    rw [show syracuseStep (32 * k + 4) = 16 * k + 2 by
          apply affine_step_even <;> omega,
      show syracuseStep (16 * k + 2) = 8 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (8 * k + 1) = 12 * k + 2 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (12 * k + 2) = 6 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (6 * k + 1) = 9 * k + 2 by
          apply affine_step_odd_to <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (32 * k + 5))))) = 9 * k + 2
    rw [show syracuseStep (32 * k + 5) = 48 * k + 8 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (48 * k + 8) = 24 * k + 4 by
          apply affine_step_even <;> omega,
      show syracuseStep (24 * k + 4) = 12 * k + 2 by
          apply affine_step_even <;> omega,
      show syracuseStep (12 * k + 2) = 6 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (6 * k + 1) = 9 * k + 2 by
          apply affine_step_odd_to <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (32 * k + 6))))) = 9 * k + 2
    rw [show syracuseStep (32 * k + 6) = 16 * k + 3 by
          apply affine_step_even <;> omega,
      show syracuseStep (16 * k + 3) = 24 * k + 5 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (24 * k + 5) = 36 * k + 8 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (36 * k + 8) = 18 * k + 4 by
          apply affine_step_even <;> omega,
      show syracuseStep (18 * k + 4) = 9 * k + 2 by
          apply affine_step_even <;> omega]

set_option maxHeartbeats 1000000 in
-- Five symbolic eight-step branches make `interval_cases` exceed the default.
/-- Five distinct inverse words with the same linear part and consecutive
offsets modulo `3^3`. -/
theorem five_run_hits (k j : ℕ) (hj : j < 5) :
    syracuseStep^[8] (256 * k + 98 + j) = 27 * k + 11 := by
  interval_cases j
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (syracuseStep (syracuseStep (syracuseStep
        (256 * k + 98)))))))) = 27 * k + 11
    rw [show syracuseStep (256 * k + 98) = 128 * k + 49 by apply affine_step_even <;> omega,
      show syracuseStep (128 * k + 49) = 192 * k + 74 by apply affine_step_odd_to <;> omega,
      show syracuseStep (192 * k + 74) = 96 * k + 37 by apply affine_step_even <;> omega,
      show syracuseStep (96 * k + 37) = 144 * k + 56 by apply affine_step_odd_to <;> omega,
      show syracuseStep (144 * k + 56) = 72 * k + 28 by apply affine_step_even <;> omega,
      show syracuseStep (72 * k + 28) = 36 * k + 14 by apply affine_step_even <;> omega,
      show syracuseStep (36 * k + 14) = 18 * k + 7 by apply affine_step_even <;> omega,
      show syracuseStep (18 * k + 7) = 27 * k + 11 by apply affine_step_odd_to <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (syracuseStep (syracuseStep (syracuseStep
        (256 * k + 99)))))))) = 27 * k + 11
    rw [show syracuseStep (256 * k + 99) = 384 * k + 149 by apply affine_step_odd_to <;> omega,
      show syracuseStep (384 * k + 149) = 576 * k + 224 by apply affine_step_odd_to <;> omega,
      show syracuseStep (576 * k + 224) = 288 * k + 112 by apply affine_step_even <;> omega,
      show syracuseStep (288 * k + 112) = 144 * k + 56 by apply affine_step_even <;> omega,
      show syracuseStep (144 * k + 56) = 72 * k + 28 by apply affine_step_even <;> omega,
      show syracuseStep (72 * k + 28) = 36 * k + 14 by apply affine_step_even <;> omega,
      show syracuseStep (36 * k + 14) = 18 * k + 7 by apply affine_step_even <;> omega,
      show syracuseStep (18 * k + 7) = 27 * k + 11 by apply affine_step_odd_to <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (syracuseStep (syracuseStep (syracuseStep
        (256 * k + 100)))))))) = 27 * k + 11
    rw [show syracuseStep (256 * k + 100) = 128 * k + 50 by apply affine_step_even <;> omega,
      show syracuseStep (128 * k + 50) = 64 * k + 25 by apply affine_step_even <;> omega,
      show syracuseStep (64 * k + 25) = 96 * k + 38 by apply affine_step_odd_to <;> omega,
      show syracuseStep (96 * k + 38) = 48 * k + 19 by apply affine_step_even <;> omega,
      show syracuseStep (48 * k + 19) = 72 * k + 29 by apply affine_step_odd_to <;> omega,
      show syracuseStep (72 * k + 29) = 108 * k + 44 by apply affine_step_odd_to <;> omega,
      show syracuseStep (108 * k + 44) = 54 * k + 22 by apply affine_step_even <;> omega,
      show syracuseStep (54 * k + 22) = 27 * k + 11 by apply affine_step_even <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (syracuseStep (syracuseStep (syracuseStep
        (256 * k + 101)))))))) = 27 * k + 11
    rw [show syracuseStep (256 * k + 101) = 384 * k + 152 by apply affine_step_odd_to <;> omega,
      show syracuseStep (384 * k + 152) = 192 * k + 76 by apply affine_step_even <;> omega,
      show syracuseStep (192 * k + 76) = 96 * k + 38 by apply affine_step_even <;> omega,
      show syracuseStep (96 * k + 38) = 48 * k + 19 by apply affine_step_even <;> omega,
      show syracuseStep (48 * k + 19) = 72 * k + 29 by apply affine_step_odd_to <;> omega,
      show syracuseStep (72 * k + 29) = 108 * k + 44 by apply affine_step_odd_to <;> omega,
      show syracuseStep (108 * k + 44) = 54 * k + 22 by apply affine_step_even <;> omega,
      show syracuseStep (54 * k + 22) = 27 * k + 11 by apply affine_step_even <;> omega]
  · change syracuseStep (syracuseStep (syracuseStep (syracuseStep
      (syracuseStep (syracuseStep (syracuseStep (syracuseStep
        (256 * k + 102)))))))) = 27 * k + 11
    rw [show syracuseStep (256 * k + 102) = 128 * k + 51 by apply affine_step_even <;> omega,
      show syracuseStep (128 * k + 51) = 192 * k + 77 by apply affine_step_odd_to <;> omega,
      show syracuseStep (192 * k + 77) = 288 * k + 116 by apply affine_step_odd_to <;> omega,
      show syracuseStep (288 * k + 116) = 144 * k + 58 by apply affine_step_even <;> omega,
      show syracuseStep (144 * k + 58) = 72 * k + 29 by apply affine_step_even <;> omega,
      show syracuseStep (72 * k + 29) = 108 * k + 44 by apply affine_step_odd_to <;> omega,
      show syracuseStep (108 * k + 44) = 54 * k + 22 by apply affine_step_even <;> omega,
      show syracuseStep (54 * k + 22) = 27 * k + 11 by apply affine_step_even <;> omega]

/-- The `2 mod 9` collision is already order-sensitive: it exposes a smaller
point in the same component and contracts the shifted height by more than
`8/9`. -/
theorem mod_nine_two_portal_descent (k : ℕ) :
    Merge (8 * k + 1) (9 * k + 2) ∧
      8 * k + 1 < 9 * k + 2 ∧
      9 * ((8 * k + 1) + 1) < 8 * ((9 * k + 2) + 1) := by
  constructor
  · refine ⟨3, 0, ?_⟩
    change syracuseStep (syracuseStep (syracuseStep (8 * k + 1))) = 9 * k + 2
    rw [show syracuseStep (8 * k + 1) = 12 * k + 2 by
          apply affine_step_odd_to <;> omega,
      show syracuseStep (12 * k + 2) = 6 * k + 1 by
          apply affine_step_even <;> omega,
      show syracuseStep (6 * k + 1) = 9 * k + 2 by
          apply affine_step_odd_to <;> omega]
  · omega

theorem three_run_merge (k : ℕ) :
    ∀ j < 3, Merge (32 * k + 4 + j) (9 * k + 2) := by
  intro j hj
  exact ⟨5, 0, by simpa using three_run_hits k j hj⟩

theorem five_run_merge (k : ℕ) :
    ∀ j < 5, Merge (256 * k + 98 + j) (27 * k + 11) := by
  intro j hj
  exact ⟨8, 0, by simpa using five_run_hits k j hj⟩

/-- Iterating the even Syracuse branch removes a prescribed power of two. -/
theorem iterate_pow_two_mul (a n : ℕ) :
    syracuseStep^[a] (2 ^ a * n) = n := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      have hform : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by
        rw [pow_succ]
        ring
      rw [hform, syracuseStep_two_mul, ih]

theorem pow_two_mul_merge (a n : ℕ) : Merge (2 ^ a * n) n := by
  exact ⟨a, 0, by simpa using iterate_pow_two_mul a n⟩

/-- Finite arithmetic core: two generates every unit class modulo `27`, so
every unit can be doubled into the class `11 mod 27`.  `decide` kernel-reduces
the complete `27 x 18` statement. -/
theorem unit_residue_pow_two_to_eleven :
    ∀ r : Fin 27, r.val % 3 ≠ 0 →
      ∃ a : Fin 18, (2 ^ a.val * r.val) % 27 = 11 := by
  decide

theorem exists_doubling_to_eleven {n : ℕ} (hunit : n % 3 ≠ 0) :
    ∃ a : ℕ, (2 ^ a * n) % 27 = 11 := by
  let r : Fin 27 := ⟨n % 27, Nat.mod_lt _ (by omega)⟩
  have hthree : r.val % 3 = n % 3 := by
    dsimp [r]
    omega
  obtain ⟨a, ha⟩ := unit_residue_pow_two_to_eleven r (by simpa [hthree] using hunit)
  refine ⟨a.val, ?_⟩
  calc
    (2 ^ a.val * n) % 27 = (2 ^ a.val * (n % 27)) % 27 := by
      simp [Nat.mul_mod]
    _ = 11 := ha

/-- Every positive Syracuse component contains a positive number prime to
three.  If the starting point is an even multiple of three, repeatedly halve;
if it is odd, its next Syracuse value is already a unit modulo three. -/
theorem exists_unit_merge : ∀ n : ℕ, 0 < n →
    ∃ u : ℕ, 0 < u ∧ u % 3 ≠ 0 ∧ Merge u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hunit : n % 3 ≠ 0
      · exact ⟨n, hn, hunit, merge_refl n⟩
      · have hthree : n % 3 = 0 := by omega
        by_cases heven : n % 2 = 0
        · have hhalfPos : 0 < n / 2 := by omega
          have hhalfLt : n / 2 < n := by omega
          obtain ⟨u, hu, huunit, humerge⟩ := ih (n / 2) hhalfLt hhalfPos
          have hstep : syracuseStep n = n / 2 := by simp [syracuseStep, heven]
          refine ⟨u, hu, huunit, merge_trans humerge ?_⟩
          rw [← hstep]
          exact merge_next n
        · let u := syracuseStep n
          have huform : u = (3 * n + 1) / 2 := by simp [u, syracuseStep, heven]
          have huPos : 0 < u := by
            dsimp [u]
            simp only [syracuseStep, if_neg heven]
            omega
          have huunit : u % 3 ≠ 0 := by
            rw [huform]
            have hodd : n % 2 = 1 := by omega
            omega
          exact ⟨u, huPos, huunit, merge_next n⟩

/-- Every positive Collatz component contains five consecutive integers.
All five displayed points merge to one `11 mod 27` representative in exactly
eight Syracuse steps. -/
theorem every_positive_component_contains_five_run {n : ℕ} (hn : 0 < n) :
    ∃ base : ℕ, 0 < base ∧ ∀ j < 5, Merge (base + j) n := by
  obtain ⟨u, hu, huunit, hun⟩ := exists_unit_merge n hn
  obtain ⟨a, ha⟩ := exists_doubling_to_eleven huunit
  let target := 2 ^ a * u
  have htargetPos : 0 < target := by
    exact Nat.mul_pos (by positivity) hu
  have htargetMod : target % 27 = 11 := by simpa [target] using ha
  let k := target / 27
  have htarget : target = 27 * k + 11 := by
    dsimp [k]
    omega
  let base := 256 * k + 98
  refine ⟨base, by dsimp [base]; omega, ?_⟩
  intro j hj
  have hjtarget : Merge (base + j) target := by
    apply merge_of_common_target (t := target) (i := 8) (j := 0)
    · simpa [base, htarget] using five_run_hits k j hj
    · simp
  have htargetu : Merge target u := by
    simpa [target] using pow_two_mul_merge a u
  exact merge_trans hjtarget (merge_trans htargetu hun)

end CollatzComponentHolonomy
end KontoroC
