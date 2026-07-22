/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahRestorativeChartNoGo

/-!
# The same YAH restorative chart cannot recur forever

Suppose a proposed recurrent chart used the first restorative arithmetic
instruction at every generation:

`256 * R(n+1) = 729 * R(n) + 1`.

After translating by its negative rational fixed point, put
`C(n)=473*R(n)+1`.  Then `256*C(n+1)=729*C(n)`.  Coprimality forces every
power `256^n` to divide the one fixed positive natural `C(0)`, an
impossibility.

Thus a successful finite chart cycle would need other arithmetic edges; it
cannot become eventually trapped in repeated applications of this
restorative opcode.
-/

namespace KontoroC
namespace YahRestorativeLoopNoGo

def shiftedRegister (register : ℕ → ℕ) (n : ℕ) : ℕ :=
  473 * register n + 1

theorem shifted_step (register : ℕ → ℕ)
    (hstep : ∀ n, 256 * register (n + 1) = 729 * register n + 1)
    (n : ℕ) :
    256 * shiftedRegister register (n + 1) =
      729 * shiftedRegister register n := by
  have h := hstep n
  simp only [shiftedRegister]
  omega

theorem shifted_balance (register : ℕ → ℕ)
    (hstep : ∀ n, 256 * register (n + 1) = 729 * register n + 1)
    (n : ℕ) :
    256 ^ n * shiftedRegister register n =
      729 ^ n * shiftedRegister register 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      have hs := shifted_step register hstep n
      calc
        256 ^ n * 256 * shiftedRegister register (n + 1) =
            256 ^ n * (256 * shiftedRegister register (n + 1)) := by ring
        _ = 256 ^ n * (729 * shiftedRegister register n) := by rw [hs]
        _ = 729 * (256 ^ n * shiftedRegister register n) := by ring
        _ = 729 * (729 ^ n * shiftedRegister register 0) := by rw [ih]
        _ = 729 ^ n * 729 * shiftedRegister register 0 := by ring

theorem restorative_power_dvd_initial (register : ℕ → ℕ)
    (hstep : ∀ n, 256 * register (n + 1) = 729 * register n + 1)
    (n : ℕ) :
    256 ^ n ∣ shiftedRegister register 0 := by
  have hbalance := shifted_balance register hstep n
  have hdvd : 256 ^ n ∣ 729 ^ n * shiftedRegister register 0 :=
    ⟨shiftedRegister register n, hbalance.symm⟩
  have hcopBase : Nat.Coprime 256 729 := by norm_num
  have hcop := Nat.Coprime.pow n n hcopBase
  exact hcop.dvd_mul_left.mp hdvd

theorem no_perpetual_restorative_chart (register : ℕ → ℕ)
    (hstep : ∀ n, 256 * register (n + 1) = 729 * register n + 1) : False := by
  let C := shiftedRegister register 0
  have hCpos : 0 < C := by dsimp [C, shiftedRegister]; omega
  have hdvd : 256 ^ C ∣ C := by
    simpa [C] using restorative_power_dvd_initial register hstep C
  have hle : 256 ^ C ≤ C := Nat.le_of_dvd hCpos hdvd
  have hlt : C < 256 ^ C := C.lt_pow_self (by norm_num)
  omega

theorem no_eventually_only_restorative_chart (register : ℕ → ℕ) :
    ¬ ∃ start, ∀ n, start ≤ n →
      256 * register (n + 1) = 729 * register n + 1 := by
  rintro ⟨start, htail⟩
  let shifted : ℕ → ℕ := fun n => register (start + n)
  apply no_perpetual_restorative_chart shifted
  intro n
  dsimp [shifted]
  simpa only [Nat.add_assoc] using
    htail (start + n) (Nat.le_add_right start n)

end YahRestorativeLoopNoGo
end KontoroC
