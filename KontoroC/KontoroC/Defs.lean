/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Defs
import Mathlib.Data.Nat.MaxPowDiv

/-!
# The fully accelerated odd Collatz map

This file fixes the definition used by the Kontorovich challenge.  Unlike the
one-halving Syracuse map, `oddStep` removes the *maximal* power of two from
`3n+1`.  The intended state space is the positive odd natural numbers.
-/

namespace KontoroC

/-- The exact exponent of two removed by the fully accelerated odd map. -/
def oddValuation (n : ℕ) : ℕ :=
  padicValNat 2 (3 * n + 1)

/-- The fully accelerated odd Collatz map.  It is total on `ℕ`; the challenge
uses it only on positive odd inputs. -/
def oddStep (n : ℕ) : ℕ :=
  (3 * n + 1).divMaxPow 2

/-- One exact accelerated instruction. -/
def LegalInstruction (n k : ℕ) : Prop :=
  0 < n ∧ n % 2 = 1 ∧ k = oddValuation n

instance (n k : ℕ) : Decidable (LegalInstruction n k) := by
  unfold LegalInstruction
  infer_instance

theorem pow_oddValuation_mul_oddStep (n : ℕ) :
    2 ^ oddValuation n * oddStep n = 3 * n + 1 := by
  simpa [oddValuation, oddStep] using
    (Nat.pow_padicValNat_mul_divMaxPow 2 (3 * n + 1))

theorem oddStep_pos (n : ℕ) : 0 < oddStep n := by
  have hsource : 3 * n + 1 ≠ 0 := by omega
  have hpow : 0 < 2 ^ oddValuation n := Nat.pow_pos (by omega)
  have hprod := pow_oddValuation_mul_oddStep n
  nlinarith

theorem oddValuation_pos_of_odd {n : ℕ} (hodd : n % 2 = 1) :
    0 < oddValuation n := by
  have hdvd : 2 ∣ 3 * n + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hne : 3 * n + 1 ≠ 0 := by omega
  have hle : 1 ≤ padicValNat 2 (3 * n + 1) :=
    (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 1) (n := 3 * n + 1)
      (by omega) hne).mp (by simpa using hdvd)
  exact lt_of_lt_of_le Nat.zero_lt_one (by simpa [oddValuation] using hle)

theorem oddStep_not_even (n : ℕ) : ¬2 ∣ oddStep n := by
  exact Nat.not_dvd_divMaxPow (p := 2) (n := 3 * n + 1) (by omega) (by omega)

theorem oddStep_mod_two (n : ℕ) : oddStep n % 2 = 1 := by
  have hlt : oddStep n % 2 < 2 := Nat.mod_lt _ (by omega)
  have hne : oddStep n % 2 ≠ 0 := by
    intro hzero
    exact oddStep_not_even n ((Nat.dvd_iff_mod_eq_zero).2 hzero)
  omega

theorem legalInstruction_step_equation {n k : ℕ}
    (h : LegalInstruction n k) :
    2 ^ k * oddStep n = 3 * n + 1 := by
  rw [h.2.2]
  exact pow_oddValuation_mul_oddStep n

end KontoroC
