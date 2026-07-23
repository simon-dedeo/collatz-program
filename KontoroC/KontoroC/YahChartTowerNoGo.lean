/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahThirdRestorativeArithmetic

/-!
# A lasso-restriction chart tower exhausts every ordinary parameter

If each chart change merely restricts the current repetition parameter to a
proper dyadic cylinder

`t(n) = address(n) + 2^(bits(n)) * t(n+1)`, with `bits(n)>0`,

then the remaining quotient strictly decreases whenever it is positive.  An
ordinary natural parameter therefore reaches zero after finitely many chart
changes, and every later address and quotient is zero.  This rules out an
infinite restorative tower powered only by reading more preloaded source
digits.  It does not rule out an opcode which writes or reindexes the counter.
-/

namespace KontoroC
namespace YahChartTowerNoGo

variable (parameter address bits : ℕ → ℕ)

def ProperDyadicRestriction : Prop :=
  (∀ n, 0 < bits n) ∧
  (∀ n, parameter n = address n + 2 ^ bits n * parameter (n + 1))

private theorem next_lt_of_ne_zero
    (hbits : ∀ n, 0 < bits n)
    (hdecomp : ∀ n,
      parameter n = address n + 2 ^ bits n * parameter (n + 1))
    (hnext : parameter (n + 1) ≠ 0) :
    parameter (n + 1) < parameter n := by
  have hpow : 1 < 2 ^ bits n := Nat.one_lt_two_pow (Nat.ne_of_gt (hbits n))
  have hnextpos : 0 < parameter (n + 1) := Nat.pos_of_ne_zero hnext
  have h := hdecomp n
  nlinarith

/-- An ordinary parameter cannot survive infinitely many positive-width
dyadic restrictions. -/
theorem exists_parameter_eq_zero
    (hbits : ∀ n, 0 < bits n)
    (hdecomp : ∀ n,
      parameter n = address n + 2 ^ bits n * parameter (n + 1)) :
    ∃ N, parameter N = 0 := by
  by_contra hzero
  have hzero' : ∀ n, parameter n ≠ 0 := by
    intro n hn
    exact hzero ⟨n, hn⟩
  have hdesc : ∀ n, parameter (n + 1) < parameter n := fun n ↦
    next_lt_of_ne_zero parameter address bits hbits hdecomp (hzero' (n + 1))
  have hbound : ∀ n, parameter n + n ≤ parameter 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hlt := hdesc n
        omega
  have hfinal := hbound (parameter 0 + 1)
  omega

private theorem zero_step
    (hdecomp : ∀ n,
      parameter n = address n + 2 ^ bits n * parameter (n + 1))
    (hn : parameter n = 0) :
    address n = 0 ∧ parameter (n + 1) = 0 := by
  have h := hdecomp n
  have hsum : address n + 2 ^ bits n * parameter (n + 1) = 0 := by omega
  have hparts := Nat.add_eq_zero_iff.mp hsum
  have hpow : 2 ^ bits n ≠ 0 := by positivity
  exact ⟨hparts.1, (mul_eq_zero.mp hparts.2).resolve_left hpow⟩

/-- QM42: after finitely many restrictions, both the quotient and every
subsequent cylinder address vanish. -/
theorem eventually_parameter_and_address_zero
    (hbits : ∀ n, 0 < bits n)
    (hdecomp : ∀ n,
      parameter n = address n + 2 ^ bits n * parameter (n + 1)) :
    ∃ N, ∀ n ≥ N, parameter n = 0 ∧ address n = 0 := by
  obtain ⟨N, hN⟩ := exists_parameter_eq_zero parameter address bits hbits hdecomp
  have htail : ∀ k, parameter (N + k) = 0 ∧ address (N + k) = 0 := by
    intro k
    induction k with
    | zero =>
        have hstep := zero_step parameter address bits hdecomp hN
        simpa using And.intro hN hstep.1
    | succ k ih =>
        have hstep := zero_step parameter address bits hdecomp ih.1
        have hnext : parameter (N + (k + 1)) = 0 := by
          simpa [Nat.add_assoc] using hstep.2
        have hnextstep := zero_step parameter address bits hdecomp hnext
        exact ⟨hnext, hnextstep.1⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hindex : N + (n - N) = n := by omega
  simpa [hindex] using htail (n - N)

theorem eventually_zero_of_properRestriction
    (h : ProperDyadicRestriction parameter address bits) :
    ∃ N, ∀ n ≥ N, parameter n = 0 ∧ address n = 0 :=
  eventually_parameter_and_address_zero parameter address bits h.1 h.2

/-- Equivalent operational form: positive chart addresses cannot occur
arbitrarily far down a pure restriction tower. -/
theorem not_frequently_positive_address
    (hbits : ∀ n, 0 < bits n)
    (hdecomp : ∀ n,
      parameter n = address n + 2 ^ bits n * parameter (n + 1)) :
    ¬ (∀ N, ∃ n ≥ N, 0 < address n) := by
  obtain ⟨N, htail⟩ :=
    eventually_parameter_and_address_zero parameter address bits hbits hdecomp
  intro hfrequent
  obtain ⟨n, hn, hpos⟩ := hfrequent N
  have := (htail n hn).2
  omega

end YahChartTowerNoGo
end KontoroC
