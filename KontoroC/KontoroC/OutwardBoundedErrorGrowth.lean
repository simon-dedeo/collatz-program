/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardLiteralMacroOrbit
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Exact bounded-error growth and the coercivity gate

A literal policy may expose a rational mixed coordinate satisfying

`u(next) >= lambda * u(current) - C`, with `lambda > 1`.

The fixed threshold is `C/(lambda-1)`.  Above it, the excess grows at least
by `lambda` each step.  This file proves the exact exponential lower bound and
unboundedness over the rationals.

Growth of an auxiliary coordinate is not automatically growth of the desired
execution counter.  The separate `CounterCoercive` hypothesis says that each
bounded counter window bounds the coordinate.  Only with that premise does
coordinate growth force counter growth.  In particular, an expanding address,
spectral superposition, or inert carry coordinate cannot silently stand in for
literal counter escape.

No policy, coordinate, or coercivity estimate is constructed here.
-/

namespace KontoroC
namespace OutwardBoundedErrorGrowth

variable {State : Type*}

/-- The rational mixed coordinate obeys one uniform affine lower-growth
inequality along the proposed orbit. -/
def HasBoundedErrorGrowth
    (orbit : ℕ → State) (height : State → ℚ) (lambda error : ℚ) : Prop :=
  ∀ n, lambda * height (orbit n) - error ≤ height (orbit (n + 1))

/-- Unboundedness of a rational coordinate along one distinguished orbit. -/
def HeightUnbounded
    (orbit : ℕ → State) (height : State → ℚ) : Prop :=
  ∀ bound, ∃ n, bound < height (orbit n)

/-- Coercivity in the direction needed for a counter proof: every bounded
counter window gives a uniform upper bound for the auxiliary coordinate. -/
def CounterCoercive
    (counter : State → ℕ) (height : State → ℚ) : Prop :=
  ∀ counterBound, ∃ heightBound,
    ∀ state, counter state ≤ counterBound → height state ≤ heightBound

/-- Exact solution comparison for the affine inequality.  The excess above
the fixed threshold grows by at least `lambda^n`. -/
theorem height_lower_bound
    (orbit : ℕ → State) (height : State → ℚ)
    (lambda error : ℚ)
    (hlambda : 1 < lambda)
    (hgrowth : HasBoundedErrorGrowth orbit height lambda error)
    (n : ℕ) :
    error / (lambda - 1) +
        lambda ^ n * (height (orbit 0) - error / (lambda - 1)) ≤
      height (orbit n) := by
  have hdenominator : lambda - 1 ≠ 0 := by linarith
  have hfixed : lambda * (error / (lambda - 1)) - error =
      error / (lambda - 1) := by
    field_simp [hdenominator]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        error / (lambda - 1) +
            lambda ^ (n + 1) *
              (height (orbit 0) - error / (lambda - 1)) =
            lambda *
                (error / (lambda - 1) +
                  lambda ^ n *
                    (height (orbit 0) - error / (lambda - 1))) -
              error := by
                rw [pow_succ]
                nlinarith [hfixed]
        _ ≤ lambda * height (orbit n) - error := by
          gcongr
        _ ≤ height (orbit (n + 1)) := hgrowth n

/-- Starting strictly above the affine fixed threshold makes the exact
rational mixed coordinate unbounded. -/
theorem height_unbounded_of_boundedErrorGrowth
    (orbit : ℕ → State) (height : State → ℚ)
    (lambda error : ℚ)
    (hlambda : 1 < lambda)
    (hstart : error / (lambda - 1) < height (orbit 0))
    (hgrowth : HasBoundedErrorGrowth orbit height lambda error) :
    HeightUnbounded orbit height := by
  intro bound
  let excess := height (orbit 0) - error / (lambda - 1)
  have hexcess : 0 < excess := by
    dsimp [excess]
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    ((bound - error / (lambda - 1)) / excess) hlambda
  have htarget : bound < error / (lambda - 1) + lambda ^ n * excess := by
    have hscaled := (div_lt_iff₀ hexcess).mp hn
    linarith
  refine ⟨n, htarget.trans_le ?_⟩
  simpa [excess] using
    height_lower_bound orbit height lambda error hlambda hgrowth n

/-- A coercive auxiliary coordinate cannot become unbounded while the actual
natural counter remains in one bounded window. -/
theorem counter_unbounded_of_heightUnbounded
    (orbit : ℕ → State) (height : State → ℚ) (counter : State → ℕ)
    (hunbounded : HeightUnbounded orbit height)
    (hcoercive : CounterCoercive counter height) :
    ∀ bound, ∃ n, bound < counter (orbit n) := by
  intro bound
  obtain ⟨heightBound, hheightBound⟩ := hcoercive bound
  obtain ⟨n, hn⟩ := hunbounded heightBound
  refine ⟨n, ?_⟩
  by_contra hnot
  have hcounter : counter (orbit n) ≤ bound := Nat.le_of_not_gt hnot
  exact (not_lt_of_ge (hheightBound (orbit n) hcounter)) hn

/-- Combined exact endpoint: bounded-error expansion above threshold plus
counter coercivity forces unbounded natural counter values. -/
theorem boundedErrorGrowth_gives_counter_unbounded
    (orbit : ℕ → State) (height : State → ℚ) (counter : State → ℕ)
    (lambda error : ℚ)
    (hlambda : 1 < lambda)
    (hstart : error / (lambda - 1) < height (orbit 0))
    (hgrowth : HasBoundedErrorGrowth orbit height lambda error)
    (hcoercive : CounterCoercive counter height) :
    ∀ bound, ∃ n, bound < counter (orbit n) := by
  exact counter_unbounded_of_heightUnbounded orbit height counter
    (height_unbounded_of_boundedErrorGrowth
      orbit height lambda error hlambda hstart hgrowth)
    hcoercive

end OutwardBoundedErrorGrowth
end KontoroC
