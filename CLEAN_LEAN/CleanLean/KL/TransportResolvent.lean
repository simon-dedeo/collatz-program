/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Exact elimination of the isometric transport term

If an eigen-equation is written `c x = p * c (U x) + b x`, repeated
substitution gives a finite renewal formula.  When `U` is periodic, the
transport term can be eliminated exactly.  For KL, `U` is multiplication by
`4`, a single cycle on each finite state section.
-/

namespace CleanLean.KL

open scoped BigOperators

theorem transport_unroll {X : Type} (U : X → X) (c b : X → ℝ) (p : ℝ)
    (h : ∀ x, c x = p * c (U x) + b x) (n : ℕ) (x : X) :
    c x = p ^ n * c (U^[n] x) + ∑ j ∈ Finset.range n, p ^ j * b (U^[j] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        c x = p ^ n * c (U^[n] x) +
            ∑ j ∈ Finset.range n, p ^ j * b (U^[j] x) := ih
        _ = p ^ n * (p * c (U (U^[n] x)) + b (U^[n] x)) +
            ∑ j ∈ Finset.range n, p ^ j * b (U^[j] x) := by rw [h]
        _ = p ^ (n + 1) * c (U^[n + 1] x) +
            ∑ j ∈ Finset.range (n + 1), p ^ j * b (U^[j] x) := by
              rw [Finset.sum_range_succ, Function.iterate_succ_apply']
              ring

/-- Exact cycle-resolvent identity.  It avoids any heuristic normalization of
the branch contribution. -/
theorem transport_cycle_resolvent {X : Type} (U : X → X) (c b : X → ℝ) (p : ℝ)
    (h : ∀ x, c x = p * c (U x) + b x) {N : ℕ} {x : X}
    (hperiod : U^[N] x = x) :
    (1 - p ^ N) * c x = ∑ j ∈ Finset.range N, p ^ j * b (U^[j] x) := by
  have hu := transport_unroll U c b p h N x
  rw [hperiod] at hu
  linarith

/-- If `0 ≤ p < 1` and the cycle is nonempty, the resolvent denominator is
strictly positive. -/
theorem transport_resolvent_denominator_pos {p : ℝ} {N : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hN : 0 < N) : 0 < 1 - p ^ N := by
  have hpow : p ^ N < 1 := pow_lt_one₀ hp0 hp1 hN.ne'
  linarith

end CleanLean.KL

