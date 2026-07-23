/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRestorativeDecoderArithmetic
import KontoroC.YahTwoRestorativeCycleNoGo

/-!
# Arithmetic of the second YAH restorative edge

On the returned-chart cylinder `u=35+2048w`, the incoming register is
`824 mod 2048`.  Dividing the depth-one burst charge by eight leaves a
residual register `103 mod 256`, which funds the next restorative update.
This file proves the all-parameter arithmetic equations QM31 and QM33.

The word-level seven-macro lasso identity QM32 remains a separate certificate.
-/

namespace KontoroC
namespace YahSecondRestorativeArithmetic

open YahLiftDecoderArithmetic YahRestorativeDecoderArithmetic

def secondSourceParameter (w : ℕ) : ℕ := 35 + 2048 * w

def secondIncomingRegister (w : ℕ) : ℕ :=
  returnedRegister (secondSourceParameter w)

def burstResidual (w : ℕ) : ℕ := secondIncomingRegister w / 2 ^ 3

def secondReturnedRegister (w : ℕ) : ℕ :=
  (3 ^ 10 * burstResidual w + 1) / 2 ^ 8

set_option maxRecDepth 2000000 in
set_option exponentiation.threshold 2000000 in
private theorem second_base_rhs_mod :
    (9963 * 9 ^ (11665 + 32768 * 35) + 4669) % 536870912 =
      216006656 := by
  decide

set_option maxRecDepth 200000 in
private theorem secondIncoming_base_mod :
    secondIncomingRegister 0 % 2048 = 824 := by
  have hvalue := returnedRegister_value 35
  have hsource : secondIncomingRegister 0 = returnedRegister 35 := by rfl
  rw [hsource]
  have hmod := congrArg (fun n : ℕ => n % 536870912) hvalue
  have hpow : 2 ^ 18 = 262144 := by norm_num
  rw [hpow] at hmod
  rw [second_base_rhs_mod] at hmod
  clear hvalue
  have hfactor := Nat.mul_mod_mul_left 262144 (returnedRegister 35) 2048
  have hmodulus : 262144 * 2048 = 536870912 := by norm_num
  rw [hmodulus] at hfactor
  rw [hfactor] at hmod
  omega

theorem secondIncomingRegister_strictMono : StrictMono secondIncomingRegister := by
  intro u v huv
  apply returnedRegister_strictMono
  simp only [secondSourceParameter]
  omega

theorem secondIncomingRegister_sub_val (u v : ℕ) (huv : u < v) :
    padicValNat 2 (secondIncomingRegister v - secondIncomingRegister u) =
      11 + padicValNat 2 (v - u) := by
  have hindex : secondSourceParameter u < secondSourceParameter v := by
    simp only [secondSourceParameter]
    omega
  have hv := returnedRegister_sub_val
    (secondSourceParameter u) (secondSourceParameter v) hindex
  have hsub : secondSourceParameter v - secondSourceParameter u =
      2048 * (v - u) := by
    simp only [secondSourceParameter]
    omega
  rw [hsub, show 2048 = 2 ^ 11 by norm_num,
    padicValNat.mul (by positivity) (Nat.sub_ne_zero_of_lt huv),
    padicValNat.prime_pow] at hv
  simpa only [secondIncomingRegister] using hv

/-- The QM31 source residue, propagated to the complete cylinder by the
two-adic isometry. -/
theorem secondIncomingRegister_mod (w : ℕ) :
    secondIncomingRegister w % 2048 = 824 := by
  by_cases hw : w = 0
  · simpa [hw] using secondIncoming_base_mod
  · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
    have hmono := secondIncomingRegister_strictMono hwpos
    have hdiff : secondIncomingRegister w - secondIncomingRegister 0 ≠ 0 :=
      Nat.sub_ne_zero_of_lt hmono
    have hval := secondIncomingRegister_sub_val 0 w hwpos
    have hdvd : 2 ^ 11 ∣
        secondIncomingRegister w - secondIncomingRegister 0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiff).2 (by omega)
    have hmodzero := Nat.dvd_iff_mod_eq_zero.mp hdvd
    norm_num only [Nat.reducePow] at hmodzero
    have hsplit := Nat.sub_add_cancel hmono.le
    rw [← hsplit, Nat.add_mod, hmodzero, secondIncoming_base_mod]

theorem burstResidual_balance (w : ℕ) :
    2 ^ 3 * burstResidual w = secondIncomingRegister w := by
  apply Nat.mul_div_cancel'
  rw [show 2 ^ 3 = 8 by norm_num, Nat.dvd_iff_mod_eq_zero]
  have hmod := secondIncomingRegister_mod w
  omega

theorem burstResidual_mod (w : ℕ) : burstResidual w % 256 = 103 := by
  have hRsplit := Nat.mod_add_div (secondIncomingRegister w) 2048
  rw [secondIncomingRegister_mod] at hRsplit
  have hbalance := burstResidual_balance w
  have hSsplit := Nat.mod_add_div (burstResidual w) 256
  norm_num only [Nat.reducePow] at hbalance
  omega

/-- QM31. -/
theorem second_numerator_dvd (w : ℕ) :
    2 ^ 8 ∣ 3 ^ 10 * burstResidual w + 1 := by
  let q := burstResidual w / 256
  have hsplit := Nat.mod_add_div (burstResidual w) 256
  rw [burstResidual_mod] at hsplit
  refine ⟨23758 + 59049 * q, ?_⟩
  dsimp [q]
  omega

theorem secondReturned_small_balance (w : ℕ) :
    2 ^ 8 * secondReturnedRegister w = 3 ^ 10 * burstResidual w + 1 := by
  exact Nat.mul_div_cancel' (second_numerator_dvd w)

/-- QM33, with no division in the statement. -/
theorem secondReturnedRegister_balance (w : ℕ) :
    2 ^ 11 * secondReturnedRegister w =
      3 ^ 10 * secondIncomingRegister w + 8 := by
  have hsmall := secondReturned_small_balance w
  have hresidual := burstResidual_balance w
  norm_num only [Nat.reducePow] at hsmall hresidual ⊢
  omega

theorem secondReturnedRegister_pos (w : ℕ) :
    0 < secondReturnedRegister w := by
  have h := secondReturnedRegister_balance w
  norm_num only [Nat.reducePow] at h
  omega

theorem secondReturnedRegister_strictMono : StrictMono secondReturnedRegister := by
  intro u v huv
  have hin := secondIncomingRegister_strictMono huv
  have hu := secondReturnedRegister_balance u
  have hv := secondReturnedRegister_balance v
  norm_num only [Nat.reducePow] at hu hv
  omega

theorem secondReturnedRegister_sub_balance (u v : ℕ) (huv : u < v) :
    2 ^ 11 * (secondReturnedRegister v - secondReturnedRegister u) =
      3 ^ 10 * (secondIncomingRegister v - secondIncomingRegister u) := by
  have hout := secondReturnedRegister_strictMono huv
  have hin := secondIncomingRegister_strictMono huv
  have hu := secondReturnedRegister_balance u
  have hv := secondReturnedRegister_balance v
  norm_num only [Nat.reducePow] at hu hv ⊢
  omega

/-- The second returned register is again a two-adic isometry in its free
parameter. -/
theorem secondReturnedRegister_sub_val (u v : ℕ) (huv : u < v) :
    padicValNat 2 (secondReturnedRegister v - secondReturnedRegister u) =
      padicValNat 2 (v - u) := by
  have hout := secondReturnedRegister_strictMono huv
  have hin := secondIncomingRegister_strictMono huv
  have hv := YahBattery.padicVal_of_twoPow_balance
    (k := 11)
    (E := secondReturnedRegister v - secondReturnedRegister u)
    (A := 3 ^ 10)
    (X := secondIncomingRegister v - secondIncomingRegister u)
    (Nat.sub_pos_of_lt hout) (by positivity) (Nat.sub_pos_of_lt hin)
    (by norm_num) (secondReturnedRegister_sub_balance u v huv)
  have hsource := secondIncomingRegister_sub_val u v huv
  omega

/-- Closed value formula for the second returned chart. -/
theorem secondReturnedRegister_value (w : ℕ) :
    2 ^ 29 * secondReturnedRegister w =
      588305187 * 9 ^ (11665 + 32768 * secondSourceParameter w) +
        277796933 := by
  let p : ℕ := 9 ^ (11665 + 32768 * secondSourceParameter w)
  have hin := returnedRegister_value (secondSourceParameter w)
  have hout := secondReturnedRegister_balance w
  change 262144 * secondIncomingRegister w = 9963 * p + 4669 at hin
  change 2048 * secondReturnedRegister w =
    59049 * secondIncomingRegister w + 8 at hout
  change 536870912 * secondReturnedRegister w =
    588305187 * p + 277796933
  calc
    536870912 * secondReturnedRegister w =
        262144 * (2048 * secondReturnedRegister w) := by ring
    _ = 262144 * (59049 * secondIncomingRegister w + 8) := by rw [hout]
    _ = 59049 * (262144 * secondIncomingRegister w) + 2097152 := by ring
    _ = 59049 * (9963 * p + 4669) + 2097152 := by rw [hin]
    _ = 588305187 * p + 277796933 := by ring

/-- The original decoder parameter with exactly the same leading
`9`-exponent as the second restorative source. -/
def decoderBracketParameter (w : ℕ) : ℕ := 9051 + 524288 * w

theorem decoderBracketExponent (w : ℕ) :
    decoderExponent (decoderBracketParameter w) =
      11665 + 32768 * secondSourceParameter w := by
  simp only [decoderExponent, decoderBracketParameter, secondSourceParameter]
  ring

theorem decoderRegister_lt_secondReturnedRegister (w : ℕ) :
    decoderRegister (decoderBracketParameter w) < secondReturnedRegister w := by
  have hd := decoderRegister_value (decoderBracketParameter w)
  rw [decoderBracketExponent] at hd
  have ht := secondReturnedRegister_value w
  generalize hpdef : 9 ^ (11665 + 32768 * secondSourceParameter w) = p at hd ht
  change 3072 * decoderRegister (decoderBracketParameter w) = 41 * p + 15 at hd
  change 536870912 * secondReturnedRegister w =
    588305187 * p + 277796933 at ht
  have hp : 0 < p := by rw [← hpdef]; positivity
  have hcross :
      536870912 * (41 * p + 15) <
        3072 * (588305187 * p + 277796933) := by nlinarith
  have hscaled :
      (536870912 * 3072) * decoderRegister (decoderBracketParameter w) <
        (536870912 * 3072) * secondReturnedRegister w := by
    calc
      (536870912 * 3072) * decoderRegister (decoderBracketParameter w) =
          536870912 * (3072 * decoderRegister (decoderBracketParameter w)) := by ring
      _ = 536870912 * (41 * p + 15) := by rw [hd]
      _ < 3072 * (588305187 * p + 277796933) := hcross
      _ = 3072 * (536870912 * secondReturnedRegister w) := by rw [ht]
      _ = (536870912 * 3072) * secondReturnedRegister w := by ring
  exact Nat.lt_of_mul_lt_mul_left hscaled

private theorem seven_twenty_nine_le_decoder_step : 729 ≤ 9 ^ 128 := by
  calc
    729 = 9 ^ 3 := by norm_num
    _ ≤ 9 ^ 128 := pow_le_pow_right' (by norm_num) (by norm_num)

theorem secondReturnedRegister_lt_decoder_next (w : ℕ) :
    secondReturnedRegister w < decoderRegister (decoderBracketParameter w + 1) := by
  have ht := secondReturnedRegister_value w
  have hd := decoderRegister_value (decoderBracketParameter w + 1)
  have hexp : decoderExponent (decoderBracketParameter w + 1) =
      (11665 + 32768 * secondSourceParameter w) + 128 := by
    simp only [decoderExponent, decoderBracketParameter, secondSourceParameter]
    ring
  rw [hexp, pow_add] at hd
  generalize hpdef : 9 ^ (11665 + 32768 * secondSourceParameter w) = p at ht hd
  generalize hqdef : 9 ^ 128 = q at hd
  change 536870912 * secondReturnedRegister w =
    588305187 * p + 277796933 at ht
  change 3072 * decoderRegister (decoderBracketParameter w + 1) =
    41 * (p * q) + 15 at hd
  have hq : 729 ≤ q := by
    rw [← hqdef]
    exact seven_twenty_nine_le_decoder_step
  have hpq : 729 * p ≤ p * q := by
    rw [Nat.mul_comm 729 p]
    exact Nat.mul_le_mul_left p hq
  have hp : 0 < p := by rw [← hpdef]; positivity
  have hcross :
      3072 * (588305187 * p + 277796933) <
        536870912 * (41 * (p * q) + 15) := by nlinarith
  have hscaled :
      (536870912 * 3072) * secondReturnedRegister w <
        (536870912 * 3072) * decoderRegister (decoderBracketParameter w + 1) := by
    calc
      (536870912 * 3072) * secondReturnedRegister w =
          3072 * (536870912 * secondReturnedRegister w) := by ring
      _ = 3072 * (588305187 * p + 277796933) := by rw [ht]
      _ < 536870912 * (41 * (p * q) + 15) := hcross
      _ = 536870912 *
          (3072 * decoderRegister (decoderBracketParameter w + 1)) := by rw [hd]
      _ = (536870912 * 3072) *
          decoderRegister (decoderBracketParameter w + 1) := by ring
  exact Nat.lt_of_mul_lt_mul_left hscaled

/-- The proposed endpoint is disjoint from the original decoder chart as
well as from the first returned chart. -/
theorem secondReturnedRegister_ne_decoderRegister (w s : ℕ) :
    secondReturnedRegister w ≠ decoderRegister s := by
  have hlower := decoderRegister_lt_secondReturnedRegister w
  have hupper := secondReturnedRegister_lt_decoder_next w
  by_cases hs : s ≤ decoderBracketParameter w
  · have hmono := decoderRegister_strictMono.monotone hs
    omega
  · have hsnext : decoderBracketParameter w + 1 ≤ s := by omega
    have hmono := decoderRegister_strictMono.monotone hsnext
    omega

/-- The second restorative update expands the returned register at its source
parameter. -/
theorem secondIncomingRegister_lt_secondReturnedRegister (w : ℕ) :
    secondIncomingRegister w < secondReturnedRegister w := by
  have h := secondReturnedRegister_balance w
  norm_num only [Nat.reducePow] at h
  omega

private theorem eighty_one_le_large_step : 81 ≤ 9 ^ 32768 := by
  calc
    81 = 9 ^ 2 := by norm_num
    _ ≤ 9 ^ 32768 := pow_le_pow_right' (by norm_num) (by norm_num)

/-- A single step in the old returned-register chart is much larger than the
second restorative update.  The deliberately coarse factor `30` is already
enough: `3^10 / 2^11 < 30`, whereas one chart step multiplies the leading
power by `9^32768`. -/
theorem thirty_mul_secondIncoming_le_next (w : ℕ) :
    30 * secondIncomingRegister w ≤
      returnedRegister (secondSourceParameter w + 1) := by
  let u := secondSourceParameter w
  have hexp : 11665 + 32768 * (u + 1) =
      (11665 + 32768 * u) + 32768 := by omega
  let p : ℕ := 9 ^ (11665 + 32768 * u)
  let q : ℕ := 9 ^ 32768
  have hcur := returnedRegister_value u
  have hnext := returnedRegister_value (u + 1)
  rw [hexp, pow_add] at hnext
  change 262144 * returnedRegister u = 9963 * p + 4669 at hcur
  change 262144 * returnedRegister (u + 1) = 9963 * (p * q) + 4669 at hnext
  have hpq : 81 * p ≤ p * q := by
    rw [Nat.mul_comm 81 p]
    exact Nat.mul_le_mul_left p eighty_one_le_large_step
  change 30 * returnedRegister u ≤ returnedRegister (u + 1)
  omega

theorem secondReturnedRegister_lt_next (w : ℕ) :
    secondReturnedRegister w <
      returnedRegister (secondSourceParameter w + 1) := by
  have hbalance := secondReturnedRegister_balance w
  have hstep := thirty_mul_secondIncoming_le_next w
  norm_num only [Nat.reducePow] at hbalance
  omega

/-- The second restorative output is not a point of the existing returned
chart.  Hence the proposed second edge does not close the two known charts:
if its word-level endpoint is valid, it necessarily creates a third chart. -/
theorem secondReturnedRegister_ne_returnedRegister (w s : ℕ) :
    secondReturnedRegister w ≠ returnedRegister s := by
  have hlower := secondIncomingRegister_lt_secondReturnedRegister w
  have hupper := secondReturnedRegister_lt_next w
  by_cases hs : s ≤ secondSourceParameter w
  · have hmono := returnedRegister_strictMono.monotone hs
    change returnedRegister (secondSourceParameter w) <
      secondReturnedRegister w at hlower
    omega
  · have hsnext : secondSourceParameter w + 1 ≤ s := by omega
    have hmono := returnedRegister_strictMono.monotone hsnext
    omega

end YahSecondRestorativeArithmetic
end KontoroC
