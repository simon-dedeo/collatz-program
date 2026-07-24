/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCoerciveConverse

/-!
# Exact S-arithmetic stabilization gates

Congruence alone permits an arbitrary extension carry.  Congruence together
with a strict Archimedean difference bound smaller than the modulus forces
the carry to vanish.  The first theorem records this for the mixed modulus
`2^A * 3^B`; the second section specializes it to the canonical residue
increments of `KLDyadicReset`.
-/

namespace KontoroC
namespace OutwardSArithmeticStabilization

open KLDyadicReset

/-- Exact mixed-place gate: congruent naturals whose ordinary difference is
strictly smaller than the full dyadic--triadic modulus are equal. -/
theorem eq_of_sArithmetic_modEq_of_abs_lt
    {current next A B : ℕ}
    (hmod : next ≡ current [MOD 2 ^ A * 3 ^ B])
    (hsmall : |(next : ℤ) - current| < (2 ^ A * 3 ^ B : ℕ)) :
    next = current := by
  apply hmod.eq_of_abs_lt
  simpa [abs_sub_comm] using hsmall

/-- Eventual mixed-place smallness makes a compatible representative
sequence eventually literally constant, not merely convergent in a product
of local topologies. -/
theorem eventuallyConstant_of_sArithmetic_extension_bounds
    (N A B : ℕ → ℕ)
    (hmod : ∀ k, N (k + 1) ≡ N k [MOD 2 ^ A k * 3 ^ B k])
    (hsmall : ∃ K, ∀ k, K ≤ k →
      |(N (k + 1) : ℤ) - N k| < (2 ^ A k * 3 ^ B k : ℕ)) :
    ∃ K, ∀ k, K ≤ k → N k = N K := by
  obtain ⟨K, hK⟩ := hsmall
  have hstep : ∀ k, K ≤ k → N (k + 1) = N k := by
    intro k hk
    exact eq_of_sArithmetic_modEq_of_abs_lt (hmod k) (hK k hk)
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Nat.add_succ]
      exact (hstep (K + d) (Nat.le_add_right K d)).trans
        (ih (Nat.le_add_right K d))

/-- In the canonical reset cylinder, an increment smaller than the old
dyadic width forces the extension carry digit to be zero. -/
theorem carryDigit_eq_zero_of_residue_increment_lt
    (e : ℕ → ResetStep) (J : ℕ)
    (hsmall :
      initialResidue e (J + 1) - initialResidue e J <
        2 ^ (cumulative e J).S) :
    carryDigit e J = 0 := by
  have hdecomp := initialResidue_succ_eq_add_carry e J
  have hproduct :
      2 ^ (cumulative e J).S * carryDigit e J <
        2 ^ (cumulative e J).S := by
    omega
  by_contra hne
  have hpositive : 0 < carryDigit e J := Nat.pos_of_ne_zero hne
  have hwidth :
      2 ^ (cumulative e J).S ≤
        2 ^ (cumulative e J).S * carryDigit e J :=
    Nat.le_mul_of_pos_right _ hpositive
  omega

/-- Eventual strict increment control gives the operational zero-carry
condition required for ordinary-integer promotion. -/
theorem eventuallyZeroCarry_of_residue_increment_eventually_lt
    (e : ℕ → ResetStep)
    (hsmall : ∃ J, ∀ K, J ≤ K →
      initialResidue e (K + 1) - initialResidue e K <
        2 ^ (cumulative e K).S) :
    EventuallyZeroCarry e := by
  obtain ⟨J, hJ⟩ := hsmall
  exact ⟨J, fun K hK =>
    carryDigit_eq_zero_of_residue_increment_lt e K (hJ K hK)⟩

/-- Consequently the same strict increment estimate reconstructs an
ordinary nonnegative initial reset chain.  Positivity of later entries and
literal first-passage semantics remain separate obligations. -/
theorem exists_nonnegative_follows_of_residue_increment_eventually_lt
    (e : ℕ → ResetStep)
    (hsmall : ∃ J, ∀ K, J ≤ K →
      initialResidue e (K + 1) - initialResidue e K <
        2 ^ (cumulative e K).S) :
    ∃ m : ℕ → ℤ, Follows e m ∧ 0 ≤ m 0 := by
  apply (eventuallyZeroCarry_iff_exists_nonnegative_follows e).mp
  exact eventuallyZeroCarry_of_residue_increment_eventually_lt e hsmall

end OutwardSArithmeticStabilization
end KontoroC
