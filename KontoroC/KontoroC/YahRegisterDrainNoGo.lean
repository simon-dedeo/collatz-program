/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahQueueCausalityNoGo

/-!
# A finite YAH lift register cannot be popped forever

The first lift-register decoder has a zero-bit instruction whose arithmetic
effect is `R ↦ R / 2`.  This is a genuine instruction, but by itself it cannot
close an infinite ordinary-natural execution.  Repeated exact pops force
arbitrarily large powers of two to divide one fixed positive register.

The result below is deliberately independent of the proposed word grammar.
Any future closure proof must use a restorative/chart-changing instruction
infinitely often; it cannot have an eventual tail consisting only of bit
pops.
-/

namespace KontoroC
namespace YahRegisterDrainNoGo

/-- Exact balance after `n` consecutive register-pop instructions. -/
theorem pop_balance (register : ℕ → ℕ)
    (hpop : ∀ n, 2 * register (n + 1) = register n) (n : ℕ) :
    2 ^ n * register n = register 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        2 ^ n * 2 * register (n + 1) =
            2 ^ n * (2 * register (n + 1)) := by ring
        _ = 2 ^ n * register n := by rw [hpop n]
        _ = register 0 := ih

theorem pop_power_dvd (register : ℕ → ℕ)
    (hpop : ∀ n, 2 * register (n + 1) = register n) (n : ℕ) :
    2 ^ n ∣ register 0 := by
  exact ⟨register n, (pop_balance register hpop n).symm⟩

/-- No positive ordinary-natural register supports an infinite tail of exact
binary right shifts. -/
theorem no_perpetual_bit_pop (register : ℕ → ℕ)
    (hpositive : 0 < register 0)
    (hpop : ∀ n, 2 * register (n + 1) = register n) : False := by
  have hdvd : 2 ^ register 0 ∣ register 0 :=
    pop_power_dvd register hpop (register 0)
  have hle : 2 ^ register 0 ≤ register 0 := Nat.le_of_dvd hpositive hdvd
  exact (not_le_of_gt (register 0).lt_two_pow_self) hle

/-- Hence an infinite positive register execution cannot become permanently
confined to the zero-bit/pop chart. -/
theorem no_eventually_only_bit_pop (register : ℕ → ℕ)
    (hpositive : ∀ n, 0 < register n) :
    ¬ ∃ start, ∀ n, start ≤ n → 2 * register (n + 1) = register n := by
  rintro ⟨start, htail⟩
  let shifted : ℕ → ℕ := fun n => register (start + n)
  apply no_perpetual_bit_pop shifted (by
    simpa [shifted] using hpositive start)
  intro n
  dsimp [shifted]
  simpa only [Nat.add_assoc] using
    htail (start + n) (Nat.le_add_right start n)

end YahRegisterDrainNoGo
end KontoroC
