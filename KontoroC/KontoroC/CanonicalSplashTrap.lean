/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CanonicalSplashDynamics

/-!
# A closed thin trap is an infinite canonical splash orbit

This is the proof-carrying endpoint for a constructive exceptional language.
The structure does not assume an externally chosen infinite trace.  It gives
one public seed and a locally closed successor rule inside a predicate `L`.
Iteration of that rule produces the exact canonical partial-dynamics orbit.
-/

namespace KontoroC

/-- A locally closed, strictly outward sublanguage of the canonical splash
dynamics.  Constructing one of these is sufficient to refute the literal
Collatz conjecture. -/
structure CanonicalSplashTrap where
  L : CompleteSplashState → Prop
  seed : CompleteSplashState
  seed_mem : L seed
  seed_large : 4 < seed.start
  successor : (x : CompleteSplashState) → L x → CompleteSplashState
  successor_mem : ∀ x hx, L (successor x hx)
  successor_next : ∀ x hx, x.next = some (successor x hx)
  successor_outward : ∀ x hx, x.start < (successor x hx).start

namespace CanonicalSplashTrap

/-- The trap successor as an endomorphism of the proof-carrying trapped
state subtype. -/
def trappedNext (T : CanonicalSplashTrap) (x : {x // T.L x}) :
    {x // T.L x} :=
  ⟨T.successor x.val x.prop, T.successor_mem x.val x.prop⟩

/-- The canonical orbit obtained by iterating the local trap rule. -/
def trappedState (T : CanonicalSplashTrap) (n : ℕ) : {x // T.L x} :=
  (T.trappedNext^[n]) ⟨T.seed, T.seed_mem⟩

@[simp] theorem trappedState_zero (T : CanonicalSplashTrap) :
    T.trappedState 0 = ⟨T.seed, T.seed_mem⟩ := rfl

theorem trappedState_succ (T : CanonicalSplashTrap) (n : ℕ) :
    T.trappedState (n + 1) = T.trappedNext (T.trappedState n) := by
  simpa [trappedState] using
    Function.iterate_succ_apply' T.trappedNext n ⟨T.seed, T.seed_mem⟩

/-- A closed local trap supplies the infinite trace, exact `next` linkage,
and strict growth required by `InfiniteCanonicalSplashOrbit`. -/
noncomputable def toInfiniteCanonicalSplashOrbit (T : CanonicalSplashTrap) :
    InfiniteCanonicalSplashOrbit where
  state n := (T.trappedState n).val
  next_state n := by
    rw [show n + 1 = Nat.succ n by omega, T.trappedState_succ]
    exact T.successor_next _ _
  start_large := by simpa using T.seed_large
  outward n := by
    rw [show n + 1 = Nat.succ n by omega, T.trappedState_succ]
    exact T.successor_outward _ _

/-- Constructing a closed canonical splash trap refutes Collatz. -/
theorem not_conjecture (T : CanonicalSplashTrap) :
    ¬CleanLean.Collatz.Conjecture :=
  T.toInfiniteCanonicalSplashOrbit.not_conjecture

end CanonicalSplashTrap
end KontoroC
