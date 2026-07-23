/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRestorativeDecoderArithmetic

/-!
# The returned-chart burst sources form a nonordinary two-adic tower

The first returned-chart searches find parameters whose returned registers
are divisible by `2^3` and `2^6`.  The exact register isometry proves the
right general statement without extrapolating the observed residue digits:

* at each depth there is at most one source residue class;
* source classes at larger depths are compatible with shallower ones;
* a choice of sources with unbounded depth cannot eventually stabilize to an
  ordinary natural parameter.

This does not rule out an autonomous dispatcher which changes its ordinary
register after every burst.  It does rule out interpreting successively
deeper returned-chart congruence searches as one fixed ordinary source.
-/

namespace KontoroC
namespace YahReturnedBurstAddressNoGo

open YahRestorativeDecoderArithmetic

/-- The returned-register map preserves and reflects every power-of-two
congruence, not merely congruence to zero. -/
theorem returnedRegister_modEq_iff (u v k : ℕ) :
    returnedRegister u ≡ returnedRegister v [MOD 2 ^ k] ↔
      u ≡ v [MOD 2 ^ k] := by
  wlog huv : u ≤ v generalizing u v
  · have h := this v u (by omega)
    simpa only [Nat.ModEq.comm] using h
  by_cases heq : u = v
  · subst v
    constructor <;> intro _
    · exact Nat.ModEq.refl u
    · exact Nat.ModEq.refl (returnedRegister u)
  · have huvlt : u < v := lt_of_le_of_ne huv heq
    have hvalueLt := returnedRegister_strictMono huvlt
    have hvalueDiff : returnedRegister v - returnedRegister u ≠ 0 :=
      Nat.sub_ne_zero_of_lt hvalueLt
    have hparamDiff : v - u ≠ 0 := Nat.sub_ne_zero_of_lt huvlt
    have hisometry := returnedRegister_sub_val u v huvlt
    rw [Nat.modEq_iff_dvd' hvalueLt.le, Nat.modEq_iff_dvd' huv]
    constructor
    · intro hdvd
      have hk : k ≤ padicValNat 2
          (returnedRegister v - returnedRegister u) :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hvalueDiff).1 hdvd
      apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hparamDiff).2
      rwa [hisometry] at hk
    · intro hdvd
      have hk : k ≤ padicValNat 2 (v - u) :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hparamDiff).1 hdvd
      apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hvalueDiff).2
      rwa [hisometry]

/-- Two parameters whose returned registers vanish to depth `k` have the
same parameter residue modulo `2^k`. -/
theorem returnedRoot_unique_mod (u v k : ℕ)
    (hu : 2 ^ k ∣ returnedRegister u)
    (hv : 2 ^ k ∣ returnedRegister v) :
    u ≡ v [MOD 2 ^ k] := by
  wlog huv : u ≤ v generalizing u v
  · exact (this v u hv hu (by omega)).symm
  by_cases heq : u = v
  · subst v
    exact Nat.ModEq.refl u
  · have huvlt : u < v := lt_of_le_of_ne huv heq
    have hvalueLt := returnedRegister_strictMono huvlt
    have hdiff : returnedRegister v - returnedRegister u ≠ 0 :=
      Nat.sub_ne_zero_of_lt hvalueLt
    have hvalueDvd : 2 ^ k ∣ returnedRegister v - returnedRegister u :=
      Nat.dvd_sub hv hu
    have hk : k ≤ padicValNat 2
        (returnedRegister v - returnedRegister u) :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiff).1 hvalueDvd
    have hisometry := returnedRegister_sub_val u v huvlt
    have hparamDvd : 2 ^ k ∣ v - u := by
      apply (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.sub_ne_zero_of_lt huvlt)).2
      rwa [hisometry] at hk
    exact (Nat.modEq_iff_dvd' huv).2 hparamDvd

/-- The finite residue permutation induced by the returned-register
isometry. -/
def returnedResidueMap (k : ℕ) : Fin (2 ^ k) → Fin (2 ^ k) := fun u =>
  ⟨returnedRegister u.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩

theorem returnedResidueMap_injective (k : ℕ) :
    Function.Injective (returnedResidueMap k) := by
  intro u v huv
  have hvalue : returnedRegister u.val % 2 ^ k =
      returnedRegister v.val % 2 ^ k := congrArg Fin.val huv
  have hmodValue : returnedRegister u.val ≡ returnedRegister v.val
      [MOD 2 ^ k] := hvalue
  have hmodParam := (returnedRegister_modEq_iff u.val v.val k).1 hmodValue
  apply Fin.ext
  exact hmodParam.eq_of_lt_of_lt u.isLt v.isLt

theorem returnedResidueMap_surjective (k : ℕ) :
    Function.Surjective (returnedResidueMap k) :=
  Finite.injective_iff_surjective.mp (returnedResidueMap_injective k)

/-- Every dyadic depth has one returned-register root representative below
the modulus.  This is arithmetic existence, not yet a word-level burst
certificate. -/
theorem exists_unique_returnedRoot (k : ℕ) :
    ∃! u : Fin (2 ^ k), 2 ^ k ∣ returnedRegister u.val := by
  let zero : Fin (2 ^ k) := ⟨0, by positivity⟩
  obtain ⟨u, hu⟩ := returnedResidueMap_surjective k zero
  have hmod : returnedRegister u.val % 2 ^ k = 0 := congrArg Fin.val hu
  refine ⟨u, (Nat.dvd_iff_mod_eq_zero).2 hmod, ?_⟩
  intro v hv
  have hroot := returnedRoot_unique_mod v.val u.val k hv
    ((Nat.dvd_iff_mod_eq_zero).2 hmod)
  apply Fin.ext
  exact hroot.eq_of_lt_of_lt v.isLt u.isLt

/-- There is therefore a canonical arithmetic root choice at every
depth `3g`. -/
theorem exists_returnedBurstAddress :
    ∃ address : ℕ → ℕ,
      ∀ g, address g < 2 ^ (3 * g) ∧
        2 ^ (3 * g) ∣ returnedRegister (address g) := by
  choose root hroot using fun g => exists_unique_returnedRoot (3 * g)
  refine ⟨fun g => (root g).val, ?_⟩
  intro g
  exact ⟨(root g).isLt, (hroot g).1⟩

/-- Any supplied family of depth-`3g` burst sources is automatically a
coherent tower of residue classes. -/
theorem returnedBurstAddress_coherent (address : ℕ → ℕ)
    (hdeep : ∀ g, 2 ^ (3 * g) ∣ returnedRegister (address g))
    {g h : ℕ} (hgh : g ≤ h) :
    address g ≡ address h [MOD 2 ^ (3 * g)] := by
  apply returnedRoot_unique_mod
  · exact hdeep g
  · have hpow : 2 ^ (3 * g) ∣ 2 ^ (3 * h) :=
      Nat.pow_dvd_pow 2 (by omega)
    exact hpow.trans (hdeep h)

/-- Unbounded nested burst-source searches cannot eventually name one fixed
ordinary natural parameter. -/
theorem no_eventually_constant_returnedBurstAddress
    (address : ℕ → ℕ)
    (hdeep : ∀ g, 2 ^ (3 * g) ∣ returnedRegister (address g)) :
    ¬ ∃ u g₀ : ℕ, ∀ g, g₀ ≤ g → address g = u := by
  rintro ⟨u, g₀, hstable⟩
  let X := returnedRegister u
  let g := g₀ + X
  have hX : 0 < X := returnedRegister_pos u
  have haddress : address g = u := hstable g (by simp [g])
  have hdeep' : 2 ^ (3 * g) ∣ X := by
    simpa [X, haddress] using hdeep g
  have hsmallPow : 2 ^ X ∣ 2 ^ (3 * g) :=
    Nat.pow_dvd_pow 2 (by dsimp [g]; omega)
  have hdvd : 2 ^ X ∣ X := hsmallPow.trans hdeep'
  have hle : 2 ^ X ≤ X := Nat.le_of_dvd hX hdvd
  exact (not_lt_of_ge hle) X.lt_two_pow_self

/-- In particular, no single ordinary parameter can fund burst depths
`3g` for every `g`. -/
theorem no_ordinary_unbounded_returnedBurstSource :
    ¬ ∃ u : ℕ, ∀ g, 2 ^ (3 * g) ∣ returnedRegister u := by
  rintro ⟨u, hu⟩
  let address : ℕ → ℕ := fun _ => u
  apply no_eventually_constant_returnedBurstAddress address
    (by intro g; exact hu g)
  exact ⟨u, 0, by intro g hg; rfl⟩

end YahReturnedBurstAddressNoGo
end KontoroC
