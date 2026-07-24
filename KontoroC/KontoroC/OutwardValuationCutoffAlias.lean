/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.Defs

/-!
# Finite valuation cutoffs alias arbitrarily different exact successors

For every positive dyadic cutoff `K`, there are positive odd seeds agreeing
modulo `2^K` whose exact two-adic valuations both clip to `K`, while their
fully accelerated successors are arbitrarily far apart.

The construction is elementary.  At an even exponent `2t`, put

`x = (2^(2t) - 1) / 3` and `y = x + 2^K`.

Then `3x+1 = 2^(2t)`, whereas

`3y+1 = 2^K * (2^(2t-K) + 3)`.

The second factor is odd when `K < 2t`.  Thus the exact valuations are `2t`
and `K`, but a cutoff at `K` identifies them.  This is an exact semantic
counterexample to replacing all large carries by one clipped symbol; it says
nothing against a finite model equipped with a separately verified exact
large-carry correction.
-/

namespace KontoroC
namespace OutwardValuationCutoffAlias

/-- The seed whose exact accelerated numerator is the even power `2^(2t)`. -/
def cutoffAliasSeed (t : ℕ) : ℕ :=
  (2 ^ (2 * t) - 1) / 3

/-- Divisibility making `cutoffAliasSeed` an exact natural, not a rational
surrogate. -/
theorem three_dvd_twoPow_even_sub_one (t : ℕ) :
    3 ∣ 2 ^ (2 * t) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 t
  norm_num only [Nat.reduceSubDiff, one_pow] at h
  convert h using 1
  rw [show 4 = 2 ^ 2 by norm_num, pow_mul]

/-- Exact numerator identity for the base seed. -/
theorem three_mul_cutoffAliasSeed_add_one (t : ℕ) :
    3 * cutoffAliasSeed t + 1 = 2 ^ (2 * t) := by
  rw [cutoffAliasSeed, Nat.mul_div_cancel'
    (three_dvd_twoPow_even_sub_one t)]
  exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))

theorem cutoffAliasSeed_pos {t : ℕ} (ht : 0 < t) :
    0 < cutoffAliasSeed t := by
  have heq := three_mul_cutoffAliasSeed_add_one t
  have hexponent : 2 ≤ 2 * t := by omega
  have hpow : 4 ≤ 2 ^ (2 * t) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hexponent
    norm_num at this ⊢
    exact this
  omega

theorem cutoffAliasSeed_odd {t : ℕ} (ht : 0 < t) :
    cutoffAliasSeed t % 2 = 1 := by
  have heq := three_mul_cutoffAliasSeed_add_one t
  have hexponent : 0 < 2 * t := by omega
  have heven : 2 ^ (2 * t) % 2 = 0 := by
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hexponent.ne')
  have hmod := congrArg (fun z : ℕ => z % 2) heq
  norm_num [heven] at hmod
  have hlt := Nat.mod_lt (cutoffAliasSeed t) (by omega : 0 < 2)
  omega

/-- Literal exact accelerated instruction for the base seed. -/
theorem cutoffAliasSeed_instruction {t : ℕ} (ht : 0 < t) :
    LegalInstruction (cutoffAliasSeed t) (2 * t) ∧
      oddStep (cutoffAliasSeed t) = 1 := by
  apply legalInstruction_of_step_equation
  · exact cutoffAliasSeed_pos ht
  · exact cutoffAliasSeed_odd ht
  · norm_num
  · simpa using (three_mul_cutoffAliasSeed_add_one t).symm

/-- Perturbation invisible modulo the chosen cutoff. -/
def cutoffAliasPerturbation (t K : ℕ) : ℕ :=
  cutoffAliasSeed t + 2 ^ K

theorem cutoffAliasPerturbation_modEq (t K : ℕ) :
    cutoffAliasSeed t ≡ cutoffAliasPerturbation t K [MOD 2 ^ K] := by
  rw [Nat.ModEq]
  simp [cutoffAliasPerturbation]

theorem cutoffAliasPerturbation_pos {t K : ℕ} (ht : 0 < t) :
    0 < cutoffAliasPerturbation t K := by
  dsimp [cutoffAliasPerturbation]
  exact Nat.add_pos_left (cutoffAliasSeed_pos ht) _

theorem cutoffAliasPerturbation_odd
    {t K : ℕ} (ht : 0 < t) (hK : 0 < K) :
    cutoffAliasPerturbation t K % 2 = 1 := by
  have hpow : 2 ^ K % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hK.ne')
  rw [cutoffAliasPerturbation, Nat.add_mod, cutoffAliasSeed_odd ht, hpow]

/-- Exact numerator factorization for the perturbed seed. -/
theorem cutoffAliasPerturbation_equation
    {t K : ℕ} (hKt : K ≤ 2 * t) :
    2 ^ K * (2 ^ (2 * t - K) + 3) =
      3 * cutoffAliasPerturbation t K + 1 := by
  have hsplit : 2 ^ K * 2 ^ (2 * t - K) = 2 ^ (2 * t) := by
    rw [← pow_add, Nat.add_sub_of_le hKt]
  calc
    2 ^ K * (2 ^ (2 * t - K) + 3) =
        2 ^ K * 2 ^ (2 * t - K) + 3 * 2 ^ K := by ring
    _ = 2 ^ (2 * t) + 3 * 2 ^ K := by rw [hsplit]
    _ = (3 * cutoffAliasSeed t + 1) + 3 * 2 ^ K := by
      rw [three_mul_cutoffAliasSeed_add_one]
    _ = 3 * cutoffAliasPerturbation t K + 1 := by
      simp only [cutoffAliasPerturbation]
      ring

theorem cutoffAliasPerturbation_quotient_odd
    {t K : ℕ} (hKt : K < 2 * t) :
    (2 ^ (2 * t - K) + 3) % 2 = 1 := by
  have hexponent : 0 < 2 * t - K := Nat.sub_pos_of_lt hKt
  have hpow : 2 ^ (2 * t - K) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hexponent.ne')
  rw [Nat.add_mod, hpow]

/-- Literal exact accelerated instruction for the perturbed seed. -/
theorem cutoffAliasPerturbation_instruction
    {t K : ℕ} (ht : 0 < t) (hK : 0 < K) (hKt : K < 2 * t) :
    LegalInstruction (cutoffAliasPerturbation t K) K ∧
      oddStep (cutoffAliasPerturbation t K) =
        2 ^ (2 * t - K) + 3 := by
  apply legalInstruction_of_step_equation
  · exact cutoffAliasPerturbation_pos ht
  · exact cutoffAliasPerturbation_odd ht hK
  · exact cutoffAliasPerturbation_quotient_odd hKt
  · exact cutoffAliasPerturbation_equation hKt.le

/-- The exact finite alias package at parameters `t,K`.  The seeds agree at
cutoff precision and have the same clipped valuation, but their literal
accelerated endpoints retain the discarded carry. -/
theorem cutoffAlias_exact
    {t K : ℕ} (ht : 0 < t) (hK : 0 < K) (hKt : K < 2 * t) :
    cutoffAliasSeed t ≡ cutoffAliasPerturbation t K [MOD 2 ^ K] ∧
    min K (oddValuation (cutoffAliasSeed t)) = K ∧
    min K (oddValuation (cutoffAliasPerturbation t K)) = K ∧
    oddStep (cutoffAliasSeed t) = 1 ∧
    oddStep (cutoffAliasPerturbation t K) =
      2 ^ (2 * t - K) + 3 := by
  have hx := cutoffAliasSeed_instruction ht
  have hy := cutoffAliasPerturbation_instruction ht hK hKt
  refine ⟨cutoffAliasPerturbation_modEq t K, ?_, ?_, hx.2, hy.2⟩
  · rw [← hx.1.2.2]
    exact Nat.min_eq_left hKt.le
  · rw [← hy.1.2.2]
    exact Nat.min_self K

/-- Main no-go theorem: at every positive finite valuation cutoff, aliases
with the same visible residue and clipped valuation have exact accelerated
successors exceeding any prescribed bound. -/
theorem exists_cutoff_alias_with_arbitrarily_large_successor
    (K B : ℕ) (hK : 0 < K) :
    ∃ x y,
      0 < x ∧ 0 < y ∧ x % 2 = 1 ∧ y % 2 = 1 ∧
      x ≡ y [MOD 2 ^ K] ∧
      min K (oddValuation x) = min K (oddValuation y) ∧
      oddStep x = 1 ∧ B < oddStep y := by
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B (by norm_num : 1 < (2 : ℕ))
  let t := K + e + 1
  let x := cutoffAliasSeed t
  let y := cutoffAliasPerturbation t K
  have ht : 0 < t := by dsimp [t]; omega
  have hKt : K < 2 * t := by dsimp [t]; omega
  have halias := cutoffAlias_exact ht hK hKt
  have hexponent : e ≤ 2 * t - K := by
    dsimp [t]
    omega
  have hpow : 2 ^ e ≤ 2 ^ (2 * t - K) :=
    Nat.pow_le_pow_right (by omega) hexponent
  refine ⟨x, y, cutoffAliasSeed_pos ht,
    cutoffAliasPerturbation_pos ht, cutoffAliasSeed_odd ht,
    cutoffAliasPerturbation_odd ht hK, halias.1, ?_, halias.2.2.2.1, ?_⟩
  · exact halias.2.1.trans halias.2.2.1.symm
  · rw [halias.2.2.2.2]
    omega

/-- No function which is constant on the visible cutoff features can
approximate the exact accelerated successor with a uniform additive error.
The predictor is otherwise completely arbitrary; finiteness or computability
is not assumed. -/
theorem no_uniformly_bounded_cutoff_predictor
    (K : ℕ) (hK : 0 < K) (predict : ℕ → ℕ) (error : ℕ)
    (hfeature : ∀ x y,
      x ≡ y [MOD 2 ^ K] →
      min K (oddValuation x) = min K (oddValuation y) →
      predict x = predict y)
    (haccurate : ∀ n, 0 < n → n % 2 = 1 →
      oddStep n ≤ predict n + error ∧
      predict n ≤ oddStep n + error) :
    False := by
  obtain ⟨x, y, hxpos, hypos, hxodd, hyodd, hmod, hclip,
      hxstep, hystep⟩ :=
    exists_cutoff_alias_with_arbitrarily_large_successor
      K (2 * error + 1) hK
  have hpredict : predict x = predict y :=
    hfeature x y hmod hclip
  have hxupper := (haccurate x hxpos hxodd).2
  have hylower := (haccurate y hypos hyodd).1
  rw [hxstep] at hxupper
  rw [← hpredict] at hylower
  omega

/-- In particular, the cutoff features do not determine the exact successor.
This is the zero-error specialization of the stronger bounded-approximation
obstruction. -/
theorem no_exact_cutoff_predictor
    (K : ℕ) (hK : 0 < K) (predict : ℕ → ℕ)
    (hfeature : ∀ x y,
      x ≡ y [MOD 2 ^ K] →
      min K (oddValuation x) = min K (oddValuation y) →
      predict x = predict y)
    (hexact : ∀ n, 0 < n → n % 2 = 1 → predict n = oddStep n) :
    False := by
  apply no_uniformly_bounded_cutoff_predictor K hK predict 0 hfeature
  intro n hn hodd
  rw [hexact n hn hodd]
  omega

end OutwardValuationCutoffAlias
end KontoroC
