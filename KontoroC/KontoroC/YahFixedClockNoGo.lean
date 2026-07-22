/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahQueueMacro

/-!
# No fixed-time ternary-shift clock

A fixed shortcut word with `L` total steps and `O` odd steps has leading
multiplier `3^O / 2^L`.  If it returned a family with leading term `A*3^n`
to the same family at exponent `n+d`, coefficient comparison would require
`2^L * 3^d = 3^O`.  Positive elapsed time makes the left side even while the
right side is odd.

Thus a live YAH compiler cannot reproduce a pure ternary-run scale on one
fixed positive-time clock.  It must vary elapsed time, change scale, or use a
genuinely mixed leading family.
-/

namespace KontoroC
namespace YahFixedClockNoGo

/-- QM8 in its irreducible arithmetic form. -/
theorem twoPow_mul_threePow_ne_threePow {L d O : ℕ} (hL : 0 < L) :
    2 ^ L * 3 ^ d ≠ 3 ^ O := by
  intro heq
  have htwoDvd : 2 ∣ 2 ^ L * 3 ^ d :=
    dvd_mul_of_dvd_left (dvd_pow_self 2 hL.ne') _
  rw [heq] at htwoDvd
  exact ((by norm_num : Odd 3).pow).not_two_dvd_nat htwoDvd

/-- The advertised version keeps the positive scale shift explicit. -/
theorem no_fixed_clock_equation {L d O : ℕ} (hL : 0 < L) (_hd : 0 < d) :
    ¬ (2 ^ L * 3 ^ d = 3 ^ O) := by
  exact twoPow_mul_threePow_ne_threePow hL

/-- Coefficient wrapper: a positive leading coefficient cannot be returned
to itself with a positive ternary exponent shift by one fixed positive-time
shortcut word. -/
theorem no_fixed_leading_coefficient_return
    {A n L d O : ℕ} (hA : 0 < A) (hL : 0 < L) (hd : 0 < d) :
    2 ^ L * (A * 3 ^ (n + d)) ≠ 3 ^ O * (A * 3 ^ n) := by
  intro heq
  have hfactor :
      (2 ^ L * 3 ^ d) * (A * 3 ^ n) =
        3 ^ O * (A * 3 ^ n) := by
    calc
      (2 ^ L * 3 ^ d) * (A * 3 ^ n) =
          2 ^ L * (A * 3 ^ (n + d)) := by
            rw [pow_add]
            ring
      _ = 3 ^ O * (A * 3 ^ n) := heq
  have hcommon : 0 < A * 3 ^ n := Nat.mul_pos hA (by positivity)
  have hcoeff : 2 ^ L * 3 ^ d = 3 ^ O :=
    Nat.mul_right_cancel hcommon hfactor
  exact no_fixed_clock_equation hL hd hcoeff

end YahFixedClockNoGo
end KontoroC
