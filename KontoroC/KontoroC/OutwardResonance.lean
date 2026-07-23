/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardOddSlice

/-!
# A resonant first-passage recharge family

This file kernel-checks QM159b as an all-parameter execution theorem.  It is
a regression and a no-go example for scalar valuation Lyapunov functions;
it does not assert an infinite orbit.
-/

namespace KontoroC
namespace OutwardResonance

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardBoundaryRenewal

def resonantWord : List Bool :=
  [false, false, false, false, false, false,
    true, true, true, true, true, true, true, true, true, true, true]

theorem resonantWord_length : resonantWord.length = 17 := by
  rfl

theorem resonantWord_oddCount : resonantWord.count true = 11 := by
  rfl

/-- The literal canonical execution used to generate the whole resonant
family.  The witnesses expose every shortcut state, so this theorem uses no
search oracle. -/
theorem resonant_base_executes :
    Executes resonantWord 131008 (3 ^ 11 - 1) := by
  simp only [resonantWord, Executes]
  exact ⟨65504, by norm_num,
    ⟨32752, by norm_num,
    ⟨16376, by norm_num,
    ⟨8188, by norm_num,
    ⟨4094, by norm_num,
    ⟨2047, by norm_num,
    ⟨3071, by norm_num,
    ⟨4607, by norm_num,
    ⟨6911, by norm_num,
    ⟨10367, by norm_num,
    ⟨15551, by norm_num,
    ⟨23327, by norm_num,
    ⟨34991, by norm_num,
    ⟨52487, by norm_num,
    ⟨78731, by norm_num,
    ⟨118097, by norm_num,
    ⟨177146, by norm_num, by norm_num⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem resonantWord_boundaryError :
    boundaryError resonantWord = 7 * 3 ^ 12 := by
  norm_num [resonantWord, boundaryError, rawDefect, programData,
    accumulate, initialData, ParityData.step]

/-- QM159b: one fixed word maps the whole displayed unbounded family to
pure powers of three. -/
theorem resonant_family_executes (L : ℕ) :
    let H := 3 * (2 ^ 17 * 3 ^ L - 7)
    Executes resonantWord (3 * H - 1) (3 * 3 ^ (12 + L) - 1) := by
  let t := 9 * 3 ^ L - 1
  have ht : 0 < 9 * 3 ^ L := by positivity
  have hs := executes_shift resonantWord resonant_base_executes t
  rw [resonantWord_length, resonantWord_oddCount] at hs
  dsimp only
  convert hs using 1 <;> dsimp [t]
  · have hpow : 2 ^ 17 * (9 * 3 ^ L - 1) + 2 ^ 17 =
        2 ^ 17 * (9 * 3 ^ L) := by
      calc
        2 ^ 17 * (9 * 3 ^ L - 1) + 2 ^ 17 =
            2 ^ 17 * ((9 * 3 ^ L - 1) + 1) := by ring
        _ = 2 ^ 17 * (9 * 3 ^ L) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ 9 * 3 ^ L)]
    omega
  · rw [show 12 + L = 11 + (L + 1) by omega, pow_add]
    norm_num
    have hsub : 9 * 3 ^ L - 1 + 1 = 9 * 3 ^ L :=
      Nat.sub_add_cancel (by omega)
    have hprod : 3 * (177147 * 3 ^ (L + 1)) =
        177147 * (9 * 3 ^ L) := by
      rw [pow_succ]
      ring
    have hright : 177146 + 177147 * (9 * 3 ^ L - 1) + 1 =
        177147 * (9 * 3 ^ L) := by
      calc
        177146 + 177147 * (9 * 3 ^ L - 1) + 1 =
            177147 * ((9 * 3 ^ L - 1) + 1) := by ring
        _ = 177147 * (9 * 3 ^ L) := by rw [hsub]
    omega

end OutwardResonance
end KontoroC
