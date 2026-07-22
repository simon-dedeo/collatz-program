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

end YahPacketRecharge
end KontoroC
