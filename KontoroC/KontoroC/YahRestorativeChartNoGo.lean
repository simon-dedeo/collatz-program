/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahLiftDecoderStep

/-!
# The first restorative output is not in the original decoder chart

The proposed bit-one restoration sends an incoming stripped register `R` to

`R' = (3^6 R + 1) / 2^8`.

Even when this quotient is integral and its word again has head zero and a
seven-trit reservoir, it is not a return to the original family
`decoderRegister(s)`.  For every original index `t`, the putative output lies
strictly between two consecutive members of that discrete family.

This does not rule out a genuine multi-chart cycle.  It does rule out
silently identifying the restorative head-zero shape with the original
recharge chart.
-/

namespace KontoroC
namespace YahRestorativeChartNoGo

open YahLiftDecoderArithmetic

def restoredRegister (t : ℕ) : ℕ :=
  (3 ^ 6 * decoderRegister t + 1) / 2 ^ 8

theorem decoderRegister_lt_restoredRegister (t : ℕ) :
    decoderRegister t < restoredRegister t := by
  have hpos := decoderRegister_pos t
  simp only [restoredRegister]
  norm_num only [Nat.reducePow]
  omega

theorem scaled_register_lt_next (t : ℕ) :
    3 ^ 6 * decoderRegister t + 1 < decoderRegister (t + 1) := by
  have ht := decoderRegister_value t
  have hs := decoderRegister_value (t + 1)
  have hexp : decoderExponent (t + 1) = decoderExponent t + 128 := by
    simp only [decoderExponent]
    omega
  rw [hexp, pow_add] at hs
  have hx : 0 < 9 ^ decoderExponent t := by positivity
  norm_num only [Nat.reducePow] at ht hs ⊢
  omega

theorem restoredRegister_lt_next (t : ℕ) :
    restoredRegister t < decoderRegister (t + 1) := by
  have hscaled := scaled_register_lt_next t
  have hdiv : restoredRegister t ≤ 3 ^ 6 * decoderRegister t + 1 := by
    dsimp [restoredRegister]
    exact Nat.div_le_self _ _
  omega

/-- The restorative output misses every point of the original decoder
register chart, not merely the point at the same parameter. -/
theorem restoredRegister_ne_decoderRegister (t s : ℕ) :
    restoredRegister t ≠ decoderRegister s := by
  have hlower := decoderRegister_lt_restoredRegister t
  have hupper := restoredRegister_lt_next t
  by_cases hst : s ≤ t
  · have hmono := decoderRegister_strictMono.monotone hst
    omega
  · have hts : t + 1 ≤ s := by omega
    have hmono := decoderRegister_strictMono.monotone hts
    omega

end YahRestorativeChartNoGo
end KontoroC
