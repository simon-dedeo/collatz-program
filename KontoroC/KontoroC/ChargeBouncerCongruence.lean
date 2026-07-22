/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerDecoder

/-!
# Congruence preservation is not a local ray obstruction

The fixed-form charge bouncer uses two public congruences.  This file proves
that both are automatically preserved by the accepted arithmetic equations.
Consequently they cannot, by themselves, rule out a one-sided ray; any no-ray
proof must use the global address tower or a stronger Diophantine invariant.
-/

namespace KontoroC

/-- Odd fixed-form divisor `(3^114 - 2^154)/5`. -/
def chargeFixedDivisor : ℕ :=
  493006936424420884140154671288273660376560866054730997

/-- Difference factor `3^17 - 2^23`. -/
def chargeDifference : ℕ := 120751555

def chargeRegisterModulus : ℕ := 3 ^ 33 * chargeDifference

theorem chargeFixedDivisor_spec :
    3 ^ 114 - 2 ^ 154 = 5 * chargeFixedDivisor := by
  norm_num [chargeFixedDivisor]

theorem chargeDifference_spec :
    3 ^ 17 - 2 ^ 23 = chargeDifference := by
  norm_num [chargeDifference]

/-- Generic fixed-form principle: a congruence modulo a divisor of `A-B` is
preserved when `B^h*q` is replaced by `A^h*q`. -/
theorem fixedFormCongruence_preserved {A B F q h : ℕ}
    (hBA : B ≤ A) (hF : F ∣ A - B)
    (hin : F ∣ B ^ h * q + 1) :
    F ∣ A ^ h * q + 1 := by
  have hAB : A ≡ B [MOD F] :=
    ((Nat.modEq_iff_dvd' hBA).2 hF).symm
  have hpows : A ^ h ≡ B ^ h [MOD F] := hAB.pow h
  have hproducts : A ^ h * q ≡ B ^ h * q [MOD F] :=
    hpows.mul (Nat.ModEq.refl q)
  have hsums : A ^ h * q + 1 ≡ B ^ h * q + 1 [MOD F] :=
    hproducts.add (Nat.ModEq.refl 1)
  exact Nat.modEq_zero_iff_dvd.mp
    (hsums.trans (Nat.modEq_zero_iff_dvd.mpr hin))

/-- Concrete preservation of the `y=-1 (mod F)` register condition. -/
theorem chargeFixedCongruence_preserved (h q : ℕ)
    (hin : chargeFixedDivisor ∣ 2 ^ (154 * h) * q + 1) :
    chargeFixedDivisor ∣ 3 ^ (114 * h) * q + 1 := by
  rw [pow_mul] at hin
  have hBA : 2 ^ 154 ≤ 3 ^ 114 := by norm_num
  have hF : chargeFixedDivisor ∣ 3 ^ 114 - 2 ^ 154 := by
    refine ⟨5, ?_⟩
    rw [chargeFixedDivisor_spec]
    ring
  have h := fixedFormCongruence_preserved hBA hF hin
  simpa [pow_mul] using h

/-- The `3^33*(3^17-2^23)` register modulus is also automatic at every
positive recharge: the output contributes `3^(114h)` and the odd quotient
already contributes the difference factor. -/
theorem chargeRegisterModulus_dvd_output {h q : ℕ} (hh : 0 < h)
    (hq : chargeDifference ∣ q) :
    chargeRegisterModulus ∣ 3 ^ (114 * h) * q := by
  have hexp : 33 ≤ 114 * h := by omega
  have hpow : 3 ^ 33 ∣ 3 ^ (114 * h) := Nat.pow_dvd_pow 3 hexp
  obtain ⟨u, hu⟩ := hpow
  obtain ⟨v, rfl⟩ := hq
  refine ⟨u * v, ?_⟩
  simp only [chargeRegisterModulus]
  rw [hu]
  ring

end KontoroC
