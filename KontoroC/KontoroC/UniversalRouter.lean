/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OddCatcherPrefix

/-!
# Universal outward odd-catcher routers

The shape `(r,0,1,L)` is an outward router for every amplifier length `r` and
every positive output gap `L`.  The proof is symbolic in all payloads and
parameters; it does not enumerate the finite shapes used by a search.
-/

namespace KontoroC

theorem twoPow_add_three_lt_threePow_add_two (r : ℕ) :
    2 ^ (r + 3) < 3 ^ (r + 2) := by
  have hpow : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by omega) r
  have hthree : 0 < 3 ^ r := Nat.pow_pos (by omega)
  rw [show r + 3 = 3 + r by omega, show r + 2 = 2 + r by omega,
    pow_add, pow_add]
  norm_num
  nlinarith

theorem three_mul_twoPow_succ_lt_threePow_add_two (r : ℕ) :
    3 * 2 ^ (r + 1) < 3 ^ (r + 2) := by
  have hpow : 2 ^ (r + 1) < 3 ^ (r + 1) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hmul : 3 * 2 ^ (r + 1) < 3 * 3 ^ (r + 1) := by
    nlinarith
  calc
    3 * 2 ^ (r + 1) < 3 * 3 ^ (r + 1) := hmul
    _ = 3 ^ (r + 2) := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      ring

namespace OddCatcherGate

/-- Literal valuation word emitted by the universal router shape. -/
theorem router_word_eq (g : OddCatcherGate)
    (hclean : g.cleanTicks = 0) (hextra : g.toPlusExtra = 1) :
    g.word = List.replicate g.ampTicks 1 ++ [2, 1] := by
  rw [OddCatcherGate.word, hclean, hextra]
  simp [mersenneMacroWord_eq]

theorem router_word_length (g : OddCatcherGate)
    (hclean : g.cleanTicks = 0) (hextra : g.toPlusExtra = 1) :
    g.word.length = g.ampTicks + 2 := by
  rw [g.router_word_eq hclean hextra]
  simp

theorem router_word_totalValuation (g : OddCatcherGate)
    (hclean : g.cleanTicks = 0) (hextra : g.toPlusExtra = 1) :
    totalValuation g.word = g.ampTicks + 3 := by
  rw [g.router_word_eq hclean hextra]
  simp [totalValuation]

/-- Every exact odd catcher of shape `(r,0,1,L)` is outward, independently of
the payloads and of the positive output gap `L`. -/
theorem outward_of_router_shape (g : OddCatcherGate)
    (hclean : g.cleanTicks = 0) (hextra : g.toPlusExtra = 1) :
    g.start < g.endpoint := by
  have hfirst := g.toPlus_balance
  rw [hclean, hextra] at hfirst
  norm_num [plusState, delayState] at hfirst
  have hinput :
      3 ^ (g.ampTicks + 1) * g.inputPayload =
        3 + 4 * g.plusPayload := by
    omega
  have hsecond := g.catcher_balance
  rw [hclean] at hsecond
  norm_num at hsecond
  have houtput :
      2 ^ g.outputGap * g.outputPayload = 3 + 3 * g.plusPayload := by
    have hprod : 0 < 2 ^ g.outputGap * g.outputPayload :=
      Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
    simp only [minusOneState] at hsecond
    omega
  rw [outward_iff]
  rw [← Nat.mul_lt_mul_left (Nat.pow_pos (by omega) :
    0 < 3 ^ (g.ampTicks + 1))]
  calc
    3 ^ (g.ampTicks + 1) *
          (2 ^ (g.ampTicks + 1) * g.inputPayload) =
        2 ^ (g.ampTicks + 1) * (3 + 4 * g.plusPayload) := by
      rw [← hinput]
      ring
    _ < 3 ^ (g.ampTicks + 2) * (1 + g.plusPayload) := by
      have hconstant :=
        three_mul_twoPow_succ_lt_threePow_add_two g.ampTicks
      have hpayload :=
        twoPow_add_three_lt_threePow_add_two g.ampTicks
      have hfour : 4 * 2 ^ (g.ampTicks + 1) =
          2 ^ (g.ampTicks + 3) := by
        rw [show g.ampTicks + 3 = (g.ampTicks + 1) + 2 by omega,
          pow_add]
        norm_num
        ring
      have hpayload' : 4 * 2 ^ (g.ampTicks + 1) <
          3 ^ (g.ampTicks + 2) := by rw [hfour]; exact hpayload
      have hvariable :
          (4 * 2 ^ (g.ampTicks + 1)) * g.plusPayload <
            3 ^ (g.ampTicks + 2) * g.plusPayload :=
        (Nat.mul_lt_mul_right g.plusPayload_pos).2 hpayload'
      calc
        2 ^ (g.ampTicks + 1) * (3 + 4 * g.plusPayload) =
            3 * 2 ^ (g.ampTicks + 1) +
              (4 * 2 ^ (g.ampTicks + 1)) * g.plusPayload := by ring
        _ < 3 ^ (g.ampTicks + 2) +
              3 ^ (g.ampTicks + 2) * g.plusPayload :=
          Nat.add_lt_add hconstant hvariable
        _ = 3 ^ (g.ampTicks + 2) * (1 + g.plusPayload) := by ring
    _ = 3 ^ (g.ampTicks + 1) *
          (2 ^ g.outputGap * g.outputPayload) := by
      rw [houtput, show g.ampTicks + 2 =
        (g.ampTicks + 1) + 1 by omega, pow_succ]
      ring

end OddCatcherGate

end KontoroC
