/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahBattery

/-!
# Exact arithmetic of the first YAH recharge packet

This file kernel-checks the division-free content of QM11 for

`P(s,q) = 2 (0012)^s (01)^q`.

The displayed quotient formula is equivalent to the exact natural-number
identity

`16 * N(P(s,q)) + 2 = 9^q * (81^(s+1) + 1)`.

Keeping the theorem division-free avoids silently assuming divisibility and
is the more useful interface for later valuation arguments.  It still does
not provide an orbit: `YahPacketFamilyNoGo` proves that one queue macro never
returns to this packet family.
-/

namespace KontoroC
namespace YahPacketRecharge

open YahQueueMacro
open YahPacketFamilyNoGo
open YahPerpetualGrowthNoGo

private theorem eval_repeat_0012 (x s : ℕ) :
    16 * tritEvalFrom x
        (repeatBlock [Trit.zero, Trit.zero, Trit.one, Trit.two] s) + 1 =
      81 ^ s * (16 * x + 1) := by
  induction s generalizing x with
  | zero => simp [repeatBlock, tritEvalFrom]
  | succ s ih =>
      rw [repeatBlock, tritEvalFrom_append]
      simp only [tritEvalFrom, tritDigit]
      rw [ih]
      ring

private theorem eval_repeat_01 (x q : ℕ) :
    8 * tritEvalFrom x (repeatBlock [Trit.zero, Trit.one] q) + 1 =
      9 ^ q * (8 * x + 1) := by
  induction q generalizing x with
  | zero => simp [repeatBlock, tritEvalFrom]
  | succ q ih =>
      rw [repeatBlock, tritEvalFrom_append]
      simp only [tritEvalFrom, tritDigit]
      rw [ih]
      ring

/-- Division-free QM11.  This is exactly the proposed packet-value formula,
but stated so that all divisibility obligations remain visible. -/
theorem packet_value_balance (s q : ℕ) :
    16 * tritEvalFrom 1 (packet s q) + 2 =
      9 ^ q * (81 ^ (s + 1) + 1) := by
  let y := tritEvalFrom 5
    (repeatBlock [Trit.zero, Trit.zero, Trit.one, Trit.two] s)
  have hs := eval_repeat_0012 5 s
  have hq := eval_repeat_01 y q
  have hy : 16 * y + 1 = 81 ^ (s + 1) := by
    dsimp [y]
    rw [hs]
    ring
  simp only [packet, packetTail, tritEvalFrom, tritDigit,
    tritEvalFrom_append]
  change 16 * tritEvalFrom y
      (repeatBlock [Trit.zero, Trit.one] q) + 2 = _
  nlinarith

/-- The packet scale occurring in QM11 is always congruent to one modulo
eight.  The theorem is again written without division:
`81^(s+1)+1 = 2*C` with `C % 8 = 1`. -/
theorem exists_packetScale_mod_eight (s : ℕ) :
    ∃ C : ℕ, 81 ^ (s + 1) + 1 = 2 * C ∧ C % 8 = 1 := by
  refine ⟨(81 ^ (s + 1) + 1) / 2, ?_, ?_⟩
  · have heven : 2 ∣ 81 ^ (s + 1) + 1 := by
      have hodd : 81 ^ (s + 1) % 2 = 1 := by
        norm_num [Nat.pow_mod]
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    exact (Nat.mul_div_cancel' heven).symm
  · have hmod : (81 ^ (s + 1) + 1) % 16 = 2 := by
      have hpow : 81 ^ (s + 1) % 16 = 1 := by
        norm_num [Nat.pow_mod]
      omega
    omega

def packetScale (s : ℕ) : ℕ := (81 ^ (s + 1) + 1) / 2

theorem two_mul_packetScale (s : ℕ) :
    2 * packetScale s = 81 ^ (s + 1) + 1 := by
  obtain ⟨C, hC, _⟩ := exists_packetScale_mod_eight s
  simp [packetScale, hC]

theorem packetScale_mod_eight (s : ℕ) : packetScale s % 8 = 1 := by
  obtain ⟨C, hC, hmod⟩ := exists_packetScale_mod_eight s
  have hpos : 0 < 2 := by omega
  have hcancel : packetScale s = C := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    simpa [two_mul_packetScale] using hC
  simpa [hcancel] using hmod

/-- The quotient presentation of QM11, still expressed as an exact
multiplicative balance. -/
theorem packet_value_scale_balance (s q : ℕ) :
    8 * tritEvalFrom 1 (packet s q) + 1 = 9 ^ q * packetScale s := by
  have hvalue := packet_value_balance s q
  have hscale := two_mul_packetScale s
  have hprod : 2 * (9 ^ q * packetScale s) =
      9 ^ q * (81 ^ (s + 1) + 1) := by
    rw [← hscale]
    ring
  omega

private theorem eval_repeat_0012_mod_four (x s : ℕ) :
    tritEvalFrom x
        (repeatBlock [Trit.zero, Trit.zero, Trit.one, Trit.two] s) % 4 =
      (x + s) % 4 := by
  induction s generalizing x with
  | zero => simp [repeatBlock, tritEvalFrom]
  | succ s ih =>
      rw [repeatBlock, tritEvalFrom_append]
      simp only [tritEvalFrom, tritDigit]
      rw [ih]
      omega

private theorem eval_repeat_01_mod_four (x q : ℕ) :
    tritEvalFrom x (repeatBlock [Trit.zero, Trit.one] q) % 4 =
      (x + q) % 4 := by
  induction q generalizing x with
  | zero => simp [repeatBlock, tritEvalFrom]
  | succ q ih =>
      rw [repeatBlock, tritEvalFrom_append]
      simp only [tritEvalFrom, tritDigit]
      rw [ih]
      omega

/-- The packet phase is its canonical residue, shifted by one.  This is the
exact checksum conversion used in QM12. -/
theorem packet_mod_four (s q : ℕ) :
    tritEvalFrom 1 (packet s q) % 4 = (s + q + 1) % 4 := by
  simp only [packet, packetTail, tritEvalFrom, tritDigit,
    tritEvalFrom_append]
  rw [eval_repeat_01_mod_four, Nat.add_mod, eval_repeat_0012_mod_four]
  omega

private theorem packet_endpoint (s q : ℕ) :
    queueMacro (packet s q) =
      YahBattery.twoHeadEndpoint Carry.one (packetTail s q) := by
  rfl

private theorem packet_source (s q : ℕ) :
    YahBattery.twoHeadWord Carry.one (packetTail s q) = packet s q := by
  rfl

/-- QM12, phase zero, without natural subtraction. -/
theorem packet_phase_zero_battery (s q : ℕ) (hphase : (s + q) % 4 = 0) :
    YahBattery.battery (queueMacro (packet s q)) + 6 =
      YahBattery.battery (packet s q) +
        padicValNat 2 (3 * (9 ^ q * packetScale s) + 37) := by
  have hmod : tritEvalFrom 1 (packet s q) % 4 = 1 := by
    rw [packet_mod_four]
    omega
  have hbase := YahBattery.twoHead_mod_one_battery Carry.one (packetTail s q)
    (by simpa [packet_source] using hmod)
  have hscale := packet_value_scale_balance s q
  have hdefect : 8 * (3 * YahBattery.defect (packet s q) + 2) =
      3 * (9 ^ q * packetScale s) + 37 := by
    simp only [YahBattery.defect]
    nlinarith
  have hval := YahBattery.padicVal_of_twoPow_balance
    (k := 3) (E := 3 * YahBattery.defect (packet s q) + 2) (A := 1)
    (X := 3 * (9 ^ q * packetScale s) + 37)
    (by have := YahBattery.defect_pos (packet s q); omega)
    (by omega) (by positivity) (by norm_num) (by simpa using hdefect)
  rw [packet_endpoint]
  rw [packet_source] at hbase
  omega

/-- QM12, phase one. -/
theorem packet_phase_one_battery (s q : ℕ) (hphase : (s + q) % 4 = 1) :
    YahBattery.battery (queueMacro (packet s q)) + 5 =
      YahBattery.battery (packet s q) +
        padicValNat 2 (9 ^ q * packetScale s + 15) := by
  have hmod : tritEvalFrom 1 (packet s q) % 4 = 2 := by
    rw [packet_mod_four]
    omega
  have hbase := YahBattery.twoHead_mod_two_battery Carry.one (packetTail s q)
    (by simpa [packet_source] using hmod)
  have hscale := packet_value_scale_balance s q
  have hdefect : 8 * (YahBattery.defect (packet s q) + 1) =
      9 ^ q * packetScale s + 15 := by
    simp only [YahBattery.defect]
    nlinarith
  have hval := YahBattery.padicVal_of_twoPow_balance
    (k := 3) (E := YahBattery.defect (packet s q) + 1) (A := 1)
    (X := 9 ^ q * packetScale s + 15)
    (by have := YahBattery.defect_pos (packet s q); omega)
    (by omega) (by positivity) (by norm_num) (by simpa using hdefect)
  rw [packet_endpoint]
  rw [packet_source] at hbase
  omega

/-- QM12, phase two: this is the reproducing residue and conserves battery. -/
theorem packet_phase_two_battery (s q : ℕ) (hphase : (s + q) % 4 = 2) :
    YahBattery.battery (queueMacro (packet s q)) =
      YahBattery.battery (packet s q) := by
  have hmod : tritEvalFrom 1 (packet s q) % 4 = 3 := by
    rw [packet_mod_four]
    omega
  have hbase := YahBattery.twoHead_mod_three_battery Carry.one (packetTail s q)
    (by simpa [packet_source] using hmod)
  simpa [packet_endpoint, packet_source] using hbase

/-- QM12, phase three. -/
theorem packet_phase_three_battery (s q : ℕ) (hphase : (s + q) % 4 = 3) :
    YahBattery.battery (queueMacro (packet s q)) + 7 =
      YahBattery.battery (packet s q) +
        padicValNat 2 (9 ^ q * packetScale s + 31) := by
  have hmod : tritEvalFrom 1 (packet s q) % 4 = 0 := by
    rw [packet_mod_four]
    omega
  have hbase := YahBattery.twoHead_mod_zero_battery Carry.one (packetTail s q)
    (by simpa [packet_source] using hmod)
  have hscale := packet_value_scale_balance s q
  have hdefect : 8 * (YahBattery.defect (packet s q) + 3) =
      9 ^ q * packetScale s + 31 := by
    simp only [YahBattery.defect]
    nlinarith
  have hval := YahBattery.padicVal_of_twoPow_balance
    (k := 3) (E := YahBattery.defect (packet s q) + 3) (A := 1)
    (X := 9 ^ q * packetScale s + 31)
    (by have := YahBattery.defect_pos (packet s q); omega)
    (by omega) (by positivity) (by norm_num) (by simpa using hdefect)
  rw [packet_endpoint]
  rw [packet_source] at hbase
  omega

end YahPacketRecharge
end KontoroC
