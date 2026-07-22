/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRechargeAddressNoGo

/-!
# Arithmetic core of the finite YAH space amplifier

This file formalizes the scale comparison behind the new finite-amplifier
artifact.  It deliberately assumes the exact all-odd defect balance and
proves what that balance implies for ternary word lengths.  The separate
dynamical obligation is to produce such a whole-macro prefix from a recharge
packet.
-/

namespace KontoroC
namespace YahFiniteAmplifier

open YahQueueMacro
open YahBattery

/-- Positional lower bound for canonical ternary evaluation. -/
theorem threePow_mul_le_tritEvalFrom (x : ℕ) (w : List Trit) :
    3 ^ w.length * x ≤ tritEvalFrom x w := by
  induction w generalizing x with
  | nil => simp [tritEvalFrom]
  | cons t w ih =>
      rw [tritEvalFrom]
      calc
        3 ^ (t :: w).length * x = 3 ^ w.length * (3 * x) := by
          simp only [List.length_cons, pow_succ]
          ring
        _ ≤ 3 ^ w.length * (3 * x + tritDigit t) := by
          exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ ≤ tritEvalFrom (3 * x + tritDigit t) w := ih _

/-- Exact strict upper endpoint of the canonical ternary interval. -/
theorem tritEvalFrom_lt_threePow_mul (x : ℕ) (w : List Trit) :
    tritEvalFrom x w < 3 ^ w.length * (x + 1) := by
  induction w generalizing x with
  | nil => simp [tritEvalFrom]
  | cons t w ih =>
      rw [tritEvalFrom]
      calc
        tritEvalFrom (3 * x + tritDigit t) w <
            3 ^ w.length * (3 * x + tritDigit t + 1) := ih _
        _ ≤ 3 ^ w.length * (3 * x + 3) := by
          apply Nat.mul_le_mul_left
          cases t <;> simp [tritDigit]
        _ = 3 ^ (t :: w).length * (x + 1) := by
          simp only [List.length_cons, pow_succ]
          ring

theorem threePow_length_lt_defect (w : List Trit) :
    3 ^ w.length < defect w := by
  have h := threePow_mul_le_tritEvalFrom 1 w
  simp only [mul_one] at h
  simp [defect]
  omega

theorem defect_le_two_mul_threePow_length (w : List Trit) :
    defect w ≤ 2 * 3 ^ w.length := by
  have h := tritEvalFrom_lt_threePow_mul 1 w
  simp only [Nat.reduceAdd, mul_comm (3 ^ w.length) 2] at h
  simp [defect]
  omega

/-- The numerical inequality used by the amplifier at the threshold
`J=4G`. -/
theorem amplifier_scale_base {G : ℕ} (hG : 1 ≤ G) :
    2 ^ (4 * G + 1) * 3 ^ (G - 1) < 3 ^ (4 * G) := by
  induction G, hG using Nat.le_induction with
  | base => norm_num
  | succ G hG ih =>
      have hpow3 : 0 < 3 ^ (4 * G) := by positivity
      have hl : 2 ^ (4 * (G + 1) + 1) * 3 ^ (G + 1 - 1) =
          48 * (2 ^ (4 * G + 1) * 3 ^ (G - 1)) := by
        rw [show 4 * (G + 1) + 1 = (4 * G + 1) + 4 by omega,
            show G + 1 - 1 = (G - 1) + 1 by omega,
            pow_add, pow_succ]
        norm_num
        ring
      have hr : 3 ^ (4 * (G + 1)) = 81 * 3 ^ (4 * G) := by
        rw [show 4 * (G + 1) = 4 * G + 4 by omega, pow_add]
        norm_num
        ring
      rw [hl, hr]
      nlinarith

/-- Once `J≥4G`, every additional odd step only strengthens the scale
separation because its numerator factor is three and denominator factor is
two. -/
theorem amplifier_scale {G J : ℕ} (hG : 1 ≤ G) (hJ : 4 * G ≤ J) :
    2 ^ (J + 1) * 3 ^ (G - 1) < 3 ^ J := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hJ
  induction r with
  | zero =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        amplifier_scale_base hG
  | succ r ih =>
      have ihr := ih (by omega)
      have hpow3 : 0 < 3 ^ (4 * G + r) := by positivity
      have hl : 2 ^ (4 * G + (r + 1) + 1) * 3 ^ (G - 1) =
          2 * (2 ^ (4 * G + r + 1) * 3 ^ (G - 1)) := by
        rw [show 4 * G + (r + 1) + 1 = (4 * G + r + 1) + 1 by omega,
            pow_succ]
        ring
      have hr : 3 ^ (4 * G + (r + 1)) =
          3 * 3 ^ (4 * G + r) := by
        rw [show 4 * G + (r + 1) = (4 * G + r) + 1 by omega, pow_succ]
        ring
      rw [hl, hr]
      nlinarith

/-- Arithmetic amplifier theorem.  An all-odd defect balance of at least
`4G` steps forces a gain of at least `G` canonical ternary cells. -/
theorem length_gain_of_allOdd_balance (start finish : List Trit) (J G : ℕ)
    (hG : 1 ≤ G) (hJ : 4 * G ≤ J)
    (hbalance : 2 ^ J * defect finish = 3 ^ J * defect start) :
    start.length + G ≤ finish.length := by
  by_contra hnot
  have hlen : finish.length ≤ start.length + (G - 1) := by omega
  have hpowLen : 3 ^ finish.length ≤
      3 ^ (start.length + (G - 1)) :=
    Nat.pow_le_pow_right (by omega) hlen
  have hfinish := defect_le_two_mul_threePow_length finish
  have hstart := threePow_length_lt_defect start
  have hscale := amplifier_scale hG hJ
  have hleft : 2 ^ J * defect finish ≤
      2 ^ (J + 1) * 3 ^ (start.length + (G - 1)) := by
    calc
      2 ^ J * defect finish ≤ 2 ^ J * (2 * 3 ^ finish.length) := by
        exact Nat.mul_le_mul_left _ hfinish
      _ ≤ 2 ^ J * (2 * 3 ^ (start.length + (G - 1))) := by
        gcongr
      _ = 2 ^ (J + 1) * 3 ^ (start.length + (G - 1)) := by
        rw [pow_succ]
        ring
  have hscale' : 2 ^ (J + 1) * 3 ^ (start.length + (G - 1)) <
      3 ^ (J + start.length) := by
    calc
      2 ^ (J + 1) * 3 ^ (start.length + (G - 1)) =
          (2 ^ (J + 1) * 3 ^ (G - 1)) * 3 ^ start.length := by
            rw [pow_add]
            ring
      _ < 3 ^ J * 3 ^ start.length :=
        Nat.mul_lt_mul_of_pos_right hscale (by positivity)
      _ = 3 ^ (J + start.length) := by rw [pow_add]
  have hright : 3 ^ (J + start.length) < 3 ^ J * defect start := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left hstart (by positivity)
  rw [hbalance] at hleft
  omega

end YahFiniteAmplifier
end KontoroC
