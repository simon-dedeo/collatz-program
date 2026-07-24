/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ValuationWord

/-!
# Pointwise nonempty valuation cylinders need not have a shared root

At odd depth `H`, take the exact accelerated valuation word consisting of
`H` copies of `1`; at even depth take `H` copies of `2`.  Every cylinder has
a positive odd ordinary realization.  The odd-depth all-one word is realized
by `2^(H+1)-1`, while the all-two word is realized by the fixed point `1`.

Nevertheless no ordinary seed lies in all cylinders.  Already the first
letter at depth one forces the seed to be `3 mod 4`, while the first letter at
depth two forces it to be `1 mod 4`.

This is an exact finite-family coherence counterexample.  It does not concern
a nested family: that failure is the point.  Any set-valued search must carry
restriction maps or a literal shared-root certificate rather than use
pointwise nonemptiness alone.
-/

namespace KontoroC
namespace OutwardAlternatingCylinderNoRoot

theorem even_positive_sub_one_mod_two
    {a : ℕ} (ha : 0 < a) (heven : 2 ∣ a) :
    (a - 1) % 2 = 1 := by
  obtain ⟨q, rfl⟩ := heven
  have hq : 0 < q := by nlinarith
  omega

/-- A general all-valuation-one cylinder realization.  The extra leading
power of two ensures that all requested accelerated valuations are exactly
one, including the last. -/
theorem wordLegal_replicate_one
    {H t : ℕ} (ht : 0 < t) (htodd : t % 2 = 1) :
    WordLegal (2 ^ (H + 1) * t - 1) (List.replicate H 1) := by
  induction H generalizing t with
  | zero => simp [WordLegal]
  | succ H ih =>
      rw [List.replicate_succ]
      simp only [WordLegal]
      let source := 2 ^ (H + 2) * t - 1
      let target := 2 ^ (H + 1) * (3 * t) - 1
      have htOne : 1 ≤ t := by omega
      have hsourceProduct : 2 ≤ 2 ^ (H + 2) * t := by
        have hpow : 2 ≤ 2 ^ (H + 2) := by
          have := Nat.pow_le_pow_right (n := 2) (by omega)
            (show 1 ≤ H + 2 by omega)
          norm_num at this ⊢
          exact this
        have hmul := Nat.mul_le_mul hpow htOne
        norm_num at hmul ⊢
        exact hmul
      have hsourcePos : 0 < source := by
        dsimp [source]
        omega
      have hsourceOdd : source % 2 = 1 := by
        have hpowDvd : 2 ∣ 2 ^ (H + 2) :=
          dvd_pow_self 2 (by omega : H + 2 ≠ 0)
        dsimp [source]
        exact even_positive_sub_one_mod_two
          (by omega) (dvd_mul_of_dvd_left hpowDvd t)
      have htargetProduct : 0 < 2 ^ (H + 1) * (3 * t) := by
        exact Nat.mul_pos (by positivity) (by nlinarith)
      have htargetOdd : target % 2 = 1 := by
        have hpowDvd : 2 ∣ 2 ^ (H + 1) :=
          dvd_pow_self 2 (by omega : H + 1 ≠ 0)
        dsimp [target]
        exact even_positive_sub_one_mod_two htargetProduct
          (dvd_mul_of_dvd_left hpowDvd (3 * t))
      have hequation : 2 ^ 1 * target = 3 * source + 1 := by
        have hscale :
            2 * (2 ^ (H + 1) * (3 * t)) =
              3 * (2 ^ (H + 2) * t) := by
          rw [show H + 2 = (H + 1) + 1 by omega, pow_succ]
          ring
        dsimp [source, target]
        omega
      have hstep := legalInstruction_of_step_equation
        hsourcePos hsourceOdd htargetOdd hequation
      have htail :
          WordLegal target (List.replicate H 1) := by
        have ht3odd : (3 * t) % 2 = 1 := by omega
        simpa [target] using ih (t := 3 * t) (by nlinarith) ht3odd
      simpa [source, hstep.2] using And.intro hstep.1 htail

/-- The accelerated fixed point `1` realizes every all-two valuation word. -/
theorem wordLegal_one_replicate_two (H : ℕ) :
    WordLegal 1 (List.replicate H 2) := by
  have hone : LegalInstruction 1 2 ∧ oddStep 1 = 1 := by
    apply legalInstruction_of_step_equation
    · omega
    · norm_num
    · norm_num
    · norm_num
  induction H with
  | zero => simp [WordLegal]
  | succ H ih =>
      rw [List.replicate_succ]
      simpa only [WordLegal, hone.2] using And.intro hone.1 ih

/-- The alternating family: odd indices request valuation one throughout;
even indices request valuation two throughout. -/
def alternatingCylinderWord (H : ℕ) : List ℕ :=
  if Odd H then List.replicate H 1 else List.replicate H 2

/-- Every member of the alternating family is a nonempty exact cylinder over
positive odd ordinary seeds. -/
theorem alternatingCylinder_pointwise_nonempty (H : ℕ) :
    ∃ n, 0 < n ∧ n % 2 = 1 ∧
      WordLegal n (alternatingCylinderWord H) := by
  by_cases hodd : Odd H
  · let n := 2 ^ (H + 1) - 1
    have hnpos : 0 < n := by
      dsimp [n]
      have : 1 < 2 ^ (H + 1) :=
        Nat.one_lt_pow (by omega) (by omega)
      omega
    have hnodd : n % 2 = 1 := by
      have hpow : 2 ^ (H + 1) % 2 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
      dsimp [n]
      omega
    refine ⟨n, hnpos, hnodd, ?_⟩
    simp only [alternatingCylinderWord, if_pos hodd]
    simpa [n] using wordLegal_replicate_one (H := H) (t := 1)
      (by omega) (by norm_num)
  · refine ⟨1, by omega, by norm_num, ?_⟩
    simp only [alternatingCylinderWord, if_neg hodd]
    exact wordLegal_one_replicate_two H

/-- Exact valuation one at a positive odd source forces residue `3 mod 4`. -/
theorem mod_four_eq_three_of_legal_one
    {n : ℕ} (h : LegalInstruction n 1) :
    n % 4 = 3 := by
  have heq := legalInstruction_step_equation h
  have hyodd := oddStep_mod_two n
  obtain ⟨q, hq⟩ : ∃ q, oddStep n = 2 * q + 1 := by
    exact ⟨oddStep n / 2, by omega⟩
  have hdecomp := Nat.mod_add_div n 4
  have hmodlt := Nat.mod_lt n (by omega : 0 < 4)
  norm_num at heq
  omega

/-- Exact valuation two at a positive odd source forces residue `1 mod 4`. -/
theorem mod_four_eq_one_of_legal_two
    {n : ℕ} (h : LegalInstruction n 2) :
    n % 4 = 1 := by
  have heq := legalInstruction_step_equation h
  have hdecomp := Nat.mod_add_div n 4
  have hmodlt := Nat.mod_lt n (by omega : 0 < 4)
  norm_num at heq
  omega

/-- Despite pointwise nonemptiness at every depth, no ordinary natural lies
in the entire alternating cylinder family.  Depths one and two already
contradict each other modulo four. -/
theorem no_shared_ordinary_root :
    ¬ ∃ n : ℕ, ∀ H : ℕ,
      WordLegal n (alternatingCylinderWord H) := by
  rintro ⟨n, hall⟩
  have hone := hall 1
  have htwo := hall 2
  have hoddOne : Odd 1 := by norm_num
  have hnotOddTwo : ¬ Odd 2 := by norm_num
  have honeWord : WordLegal n [1] := by
    simpa [alternatingCylinderWord, hoddOne] using hone
  have htwoWord : WordLegal n [2, 2] := by
    simpa [alternatingCylinderWord, hnotOddTwo] using htwo
  have hn3 := mod_four_eq_three_of_legal_one honeWord.1
  have hn1 := mod_four_eq_one_of_legal_two htwoWord.1
  omega

/-- Packaged coherence counterexample: all finite cylinders are literally
inhabited, but the family has no shared ordinary root. -/
theorem pointwise_nonempty_does_not_give_shared_root :
    (∀ H, ∃ n, 0 < n ∧ n % 2 = 1 ∧
      WordLegal n (alternatingCylinderWord H)) ∧
    ¬ ∃ n : ℕ, ∀ H : ℕ,
      WordLegal n (alternatingCylinderWord H) := by
  exact ⟨alternatingCylinder_pointwise_nonempty, no_shared_ordinary_root⟩

end OutwardAlternatingCylinderNoRoot
end KontoroC
