/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Tactic.ReduceModChar
import KontoroC.YahSecondRestorativeArithmetic

/-!
# Arithmetic of the third YAH restorative edge

The abstract chart-clock worker proposes a third edge on the cylinder
`w=249+256z`.  This file checks its complete all-parameter register layer:

`256 * U(z) = 3^7 * T(249+256z) + 1`.

It also proves that `U` is another two-adic isometry and that its low bit is
the free source bit.  The five-macro word itinerary and the bridge from the
abstract scale clock to the exact finite word remain separate obligations.
-/

namespace KontoroC
namespace YahThirdRestorativeArithmetic

open YahSecondRestorativeArithmetic

def thirdSourceParameter (z : ℕ) : ℕ := 249 + 256 * z

def thirdIncomingRegister (z : ℕ) : ℕ :=
  secondReturnedRegister (thirdSourceParameter z)

def thirdReturnedRegister (z : ℕ) : ℕ :=
  (3 ^ 7 * thirdIncomingRegister z + 1) / 2 ^ 8

private theorem huge_pow_mod_38 :
    (9 ^ 16711265681 : ℕ) % 274877906944 = 94991470217 := by
  have hz : (9 : ZMod 274877906944) ^ 16711265681 = 94991470217 := by
    reduce_mod_char
  have hz' : ((9 ^ 16711265681 : ℕ) : ZMod 274877906944) =
      (94991470217 : ℕ) := by
    rw [Nat.cast_pow]
    exact hz
  have hm := (ZMod.natCast_eq_natCast_iff'
    (9 ^ 16711265681) 94991470217 274877906944).mp hz'
  have hr : 94991470217 % 274877906944 = 94991470217 := by norm_num
  rw [hr] at hm
  exact hm

private theorem third_base_rhs_mod_38 :
    (588305187 * 9 ^ 16711265681 + 277796933) % 274877906944 =
      118648471552 := by
  rw [Nat.add_mod, Nat.mul_mod, huge_pow_mod_38]

private theorem thirdIncoming_base_mod_512 :
    thirdIncomingRegister 0 % 512 = 221 := by
  have hvalue := secondReturnedRegister_value 249
  have hexp : 11665 + 32768 * secondSourceParameter 249 = 16711265681 := by
    norm_num [secondSourceParameter]
  rw [hexp] at hvalue
  have hsource : thirdIncomingRegister 0 = secondReturnedRegister 249 := by rfl
  rw [hsource]
  have hmod := congrArg (fun n : ℕ => n % 274877906944) hvalue
  have hpow : 2 ^ 29 = 536870912 := by norm_num
  rw [hpow, third_base_rhs_mod_38] at hmod
  clear hvalue
  have hfactor := Nat.mul_mod_mul_left 536870912
    (secondReturnedRegister 249) 512
  have hmodulus : 536870912 * 512 = 274877906944 := by norm_num
  rw [hmodulus] at hfactor
  rw [hfactor] at hmod
  omega

theorem thirdIncomingRegister_strictMono : StrictMono thirdIncomingRegister := by
  intro u v huv
  apply secondReturnedRegister_strictMono
  simp only [thirdSourceParameter]
  omega

theorem thirdIncomingRegister_sub_val (u v : ℕ) (huv : u < v) :
    padicValNat 2 (thirdIncomingRegister v - thirdIncomingRegister u) =
      8 + padicValNat 2 (v - u) := by
  have hindex : thirdSourceParameter u < thirdSourceParameter v := by
    simp only [thirdSourceParameter]
    omega
  have hv := secondReturnedRegister_sub_val
    (thirdSourceParameter u) (thirdSourceParameter v) hindex
  have hsub : thirdSourceParameter v - thirdSourceParameter u =
      256 * (v - u) := by
    simp only [thirdSourceParameter]
    omega
  rw [hsub, show 256 = 2 ^ 8 by norm_num,
    padicValNat.mul (by positivity) (Nat.sub_ne_zero_of_lt huv),
    padicValNat.prime_pow] at hv
  simpa only [thirdIncomingRegister] using hv

/-- The proposed third source residue, valid on the complete cylinder. -/
theorem thirdIncomingRegister_mod (z : ℕ) :
    thirdIncomingRegister z % 256 = 221 := by
  by_cases hz : z = 0
  · subst z
    have h := thirdIncoming_base_mod_512
    omega
  · have hzpos : 0 < z := Nat.pos_of_ne_zero hz
    have hmono := thirdIncomingRegister_strictMono hzpos
    have hdiff : thirdIncomingRegister z - thirdIncomingRegister 0 ≠ 0 :=
      Nat.sub_ne_zero_of_lt hmono
    have hval := thirdIncomingRegister_sub_val 0 z hzpos
    have hdvd : 2 ^ 8 ∣ thirdIncomingRegister z - thirdIncomingRegister 0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiff).2 (by omega)
    have hmodzero := Nat.dvd_iff_mod_eq_zero.mp hdvd
    norm_num only [Nat.reducePow] at hmodzero
    have hbase := thirdIncoming_base_mod_512
    have hsplit := Nat.sub_add_cancel hmono.le
    rw [← hsplit, Nat.add_mod, hmodzero]
    omega

/-- The third restorative numerator is divisible by its exact denominator. -/
theorem third_numerator_dvd (z : ℕ) :
    2 ^ 8 ∣ 3 ^ 7 * thirdIncomingRegister z + 1 := by
  let q := thirdIncomingRegister z / 256
  have hsplit := Nat.mod_add_div (thirdIncomingRegister z) 256
  rw [thirdIncomingRegister_mod] at hsplit
  refine ⟨1888 + 2187 * q, ?_⟩
  dsimp [q]
  omega

/-- The all-parameter register equation asserted for the third edge. -/
theorem thirdReturnedRegister_balance (z : ℕ) :
    2 ^ 8 * thirdReturnedRegister z =
      3 ^ 7 * thirdIncomingRegister z + 1 := by
  exact Nat.mul_div_cancel' (third_numerator_dvd z)

theorem thirdReturnedRegister_pos (z : ℕ) :
    0 < thirdReturnedRegister z := by
  have h := thirdReturnedRegister_balance z
  norm_num only [Nat.reducePow] at h
  omega

theorem thirdReturnedRegister_strictMono : StrictMono thirdReturnedRegister := by
  intro u v huv
  have hin := thirdIncomingRegister_strictMono huv
  have hu := thirdReturnedRegister_balance u
  have hv := thirdReturnedRegister_balance v
  norm_num only [Nat.reducePow] at hu hv
  omega

theorem thirdReturnedRegister_sub_balance (u v : ℕ) (huv : u < v) :
    2 ^ 8 * (thirdReturnedRegister v - thirdReturnedRegister u) =
      3 ^ 7 * (thirdIncomingRegister v - thirdIncomingRegister u) := by
  have hout := thirdReturnedRegister_strictMono huv
  have hin := thirdIncomingRegister_strictMono huv
  have hu := thirdReturnedRegister_balance u
  have hv := thirdReturnedRegister_balance v
  norm_num only [Nat.reducePow] at hu hv ⊢
  omega

theorem thirdReturnedRegister_sub_val (u v : ℕ) (huv : u < v) :
    padicValNat 2 (thirdReturnedRegister v - thirdReturnedRegister u) =
      padicValNat 2 (v - u) := by
  have hout := thirdReturnedRegister_strictMono huv
  have hin := thirdIncomingRegister_strictMono huv
  have hv := YahBattery.padicVal_of_twoPow_balance
    (k := 8)
    (E := thirdReturnedRegister v - thirdReturnedRegister u)
    (A := 3 ^ 7)
    (X := thirdIncomingRegister v - thirdIncomingRegister u)
    (Nat.sub_pos_of_lt hout) (by positivity) (Nat.sub_pos_of_lt hin)
    (by norm_num) (thirdReturnedRegister_sub_balance u v huv)
  have hsource := thirdIncomingRegister_sub_val u v huv
  omega

private theorem thirdReturnedRegister_base_parity :
    thirdReturnedRegister 0 % 2 = 0 := by
  have hin := thirdIncoming_base_mod_512
  have hout := thirdReturnedRegister_balance 0
  have hsplit := Nat.mod_add_div (thirdIncomingRegister 0) 512
  rw [hin] at hsplit
  norm_num only [Nat.reducePow] at hout
  have houtput := Nat.mod_add_div (thirdReturnedRegister 0) 2
  omega

private theorem thirdReturnedRegister_step_odd (z : ℕ) :
    (thirdReturnedRegister (z + 1) - thirdReturnedRegister z) % 2 = 1 := by
  have hv := thirdReturnedRegister_sub_val z (z + 1) (by omega)
  have hmono := thirdReturnedRegister_strictMono (show z < z + 1 by omega)
  have hdiff : thirdReturnedRegister (z + 1) - thirdReturnedRegister z ≠ 0 :=
    Nat.sub_ne_zero_of_lt hmono
  have hvalzero : padicValNat 2
      (thirdReturnedRegister (z + 1) - thirdReturnedRegister z) = 0 := by
    simpa using hv
  have hnotdvd : ¬2 ∣
      thirdReturnedRegister (z + 1) - thirdReturnedRegister z := by
    rcases padicValNat.eq_zero_iff.mp hvalzero with h | h | h
    · norm_num at h
    · exact (hdiff h).elim
    · exact h
  rw [Nat.dvd_iff_mod_eq_zero] at hnotdvd
  have hlt := Nat.mod_lt
    (thirdReturnedRegister (z + 1) - thirdReturnedRegister z) (by omega : 0 < 2)
  omega

/-- The third returned register exposes exactly the remaining source bit. -/
theorem thirdReturnedRegister_parity (z : ℕ) :
    thirdReturnedRegister z % 2 = z % 2 := by
  induction z with
  | zero => exact thirdReturnedRegister_base_parity
  | succ z ih =>
      have hlt := thirdReturnedRegister_strictMono (show z < z + 1 by omega)
      have hsplit := Nat.sub_add_cancel hlt.le
      have hodd := thirdReturnedRegister_step_odd z
      omega

end YahThirdRestorativeArithmetic
end KontoroC
