/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.FiniteController
import KontoroC.AffineBreakoffDelay

/-!
# Ordinary-address obstruction for finite residual dispatchers

An ordinary natural realizing dyadic cylinders of unbounded precision has
eventually zero residual tail.  If a dispatcher has only finite internal
state after that residual vanishes, it becomes an autonomous finite-state
controller.  Such a controller cannot emit the genuinely aperiodic word
schedule of a growing Collatz macro-glider.

The finite-memory qualification is essential.  This file does not exclude a
dispatcher retaining another unbounded arithmetic register after address
stabilization.
-/

namespace KontoroC

/-- A deterministic word controller with no finiteness assumption on its
state type. -/
structure AutonomousController (g : MacroGlider) (σ : Type*) where
  phase : ℕ → σ
  next : σ → σ
  emit : σ → List ℕ
  phase_succ : ∀ t, phase (t + 1) = next (phase t)
  word_eq : ∀ t, g.word t = emit (phase t)

namespace AutonomousController

variable {g : MacroGlider} {σ : Type*}

theorem phase_future_eq (c : AutonomousController g σ)
    {i j : ℕ} (hij : c.phase i = c.phase j) (t : ℕ) :
    c.phase (i + t) = c.phase (j + t) := by
  induction t with
  | zero => simpa using hij
  | succ t ih =>
      calc
        c.phase (i + (t + 1)) = c.next (c.phase (i + t)) := by
          simpa [Nat.add_assoc] using c.phase_succ (i + t)
        _ = c.next (c.phase (j + t)) := congrArg c.next ih
        _ = c.phase (j + (t + 1)) := by
          simpa [Nat.add_assoc] using (c.phase_succ (j + t)).symm

/-- A deterministic controller for a growing macro-glider can never revisit
a state: a revisit would repeat the complete future word schedule. -/
theorem phase_injective (c : AutonomousController g σ) :
    Function.Injective c.phase := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply g.not_eventually_periodic_words i (p := j - i) (by omega)
    intro t
    rw [c.word_eq, c.word_eq]
    apply congrArg c.emit
    have hji : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
    calc
      c.phase (i + (t + (j - i))) = c.phase ((i + (j - i)) + t) := by
        congr 1
        ac_rfl
      _ = c.phase (j + t) := by rw [hji]
      _ = c.phase (i + t) := (c.phase_future_eq hij t).symm
  · apply g.not_eventually_periodic_words j (p := i - j) (by omega)
    intro t
    rw [c.word_eq, c.word_eq]
    apply congrArg c.emit
    have hij' : j + (i - j) = i := Nat.add_sub_of_le (Nat.le_of_lt hgt)
    calc
      c.phase (j + (t + (i - j))) = c.phase ((j + (i - j)) + t) := by
        congr 1
        ac_rfl
      _ = c.phase (i + t) := by rw [hij']
      _ = c.phase (j + t) := (c.phase_future_eq hij.symm t).symm

/-- Tightness witness: an unbounded natural clock can present every existing
macro-glider autonomously.  This represents a supplied glider; it does not
construct one or prove a Collatz counterexample. -/
def clock (g : MacroGlider) : AutonomousController g ℕ where
  phase t := t
  next t := t + 1
  emit t := g.word t
  phase_succ _ := rfl
  word_eq _ := rfl

end AutonomousController

/-- A controller whose only potentially unbounded input is a natural residual
which is eventually zero. -/
structure EventuallyZeroResidualController (g : MacroGlider)
    (σ : Type*) where
  phase : ℕ → σ
  residual : ℕ → ℕ
  next : σ → ℕ → σ
  emit : σ → ℕ → List ℕ
  residual_eventually_zero : ∃ K, ∀ t, K ≤ t → residual t = 0
  phase_succ : ∀ t, phase (t + 1) = next (phase t) (residual t)
  word_eq : ∀ t, g.word t = emit (phase t) (residual t)

namespace EventuallyZeroResidualController

variable {g : MacroGlider} {σ : Type*}

/-- After the residual vanishes, the tail schedule is autonomous, without
assuming that the remaining state type is finite. -/
noncomputable def toAutonomousTailCore
    (c : EventuallyZeroResidualController g σ) :
    AutonomousController (g.tail c.residual_eventually_zero.choose) σ := by
  let K := c.residual_eventually_zero.choose
  have hzero : ∀ t, K ≤ t → c.residual t = 0 :=
    c.residual_eventually_zero.choose_spec
  exact {
    phase := fun t => c.phase (K + t)
    next := fun s => c.next s 0
    emit := fun s => c.emit s 0
    phase_succ := fun t => by
      rw [show K + (t + 1) = (K + t) + 1 by omega,
        c.phase_succ (K + t), hzero (K + t) (by omega)]
    word_eq := fun t => by
      change g.word (K + t) = c.emit (c.phase (K + t)) 0
      rw [c.word_eq (K + t), hzero (K + t) (by omega)]
  }

/-- Necessary condition for any possible post-stabilization dispatcher: its
effective phase visits a new state at every subsequent time. -/
theorem tail_phase_injective (c : EventuallyZeroResidualController g σ) :
    Function.Injective
      (fun t => c.phase (c.residual_eventually_zero.choose + t)) :=
  c.toAutonomousTailCore.phase_injective

/-- After the residual vanishes, the tail schedule factors through an
autonomous finite-state controller. -/
noncomputable def toAutonomousTail [Finite σ]
    (c : EventuallyZeroResidualController g σ) :
    AutonomousFiniteController (g.tail c.residual_eventually_zero.choose) σ := by
  let core := c.toAutonomousTailCore
  exact {
    phase := core.phase
    next := core.next
    emit := core.emit
    phase_succ := core.phase_succ
    word_eq := core.word_eq
  }

/-- No growing Collatz macro-glider can be driven by finite state plus an
eventually zero residual. -/
theorem impossible [Finite σ]
    (c : EventuallyZeroResidualController g σ) : False :=
  c.toAutonomousTail.impossible

theorem no_controller [Finite σ] :
    ¬ Nonempty (EventuallyZeroResidualController g σ) := by
  rintro ⟨c⟩
  exact c.impossible

end EventuallyZeroResidualController

namespace DyadicBreakoffLinkSchedule

/-- Quotient left after removing the canonical low-bit address from an
ordinary candidate tail. -/
def addressResidual (S : DyadicBreakoffLinkSchedule) (n k : ℕ) : ℕ :=
  (n - (S.link k).firstTailBase) / 2 ^ S.bits k

/-- For an ordinary tail realizing every address cylinder, the residual is
eventually zero. -/
theorem addressResidual_eventually_zero (S : DyadicBreakoffLinkSchedule)
    {n : ℕ} (hn : S.RealizedBy n) :
    ∃ K, ∀ k, K ≤ k → S.addressResidual n k = 0 := by
  obtain ⟨K, hK⟩ := S.realized_eventually_constant hn
  refine ⟨K, fun k hk => ?_⟩
  simp [addressResidual, hK k hk]

/-- Elementary expanding-lift inequality used by recursive address
hierarchies. -/
theorem affineLift_gt (rho D K : ℕ) (hD : 1 < D) (hK : 0 < K) :
    K < rho + D * K := by
  have hmul : K < D * K := by
    have := (Nat.mul_lt_mul_right hK).2 hD
    simpa using this
  omega

/-- Any strictly growing canonical-address schedule is incompatible with one
ordinary realizing natural, because ordinary addresses must eventually be
constant. -/
theorem no_realization_of_strictly_growing_addresses
    (S : DyadicBreakoffLinkSchedule)
    (hgrows : ∀ k,
      (S.link k).firstTailBase < (S.link (k + 1)).firstTailBase) :
    ¬ ∃ n, S.RealizedBy n := by
  rintro ⟨n, hn⟩
  obtain ⟨K, hK⟩ := S.realized_eventually_constant hn
  have hg := hgrows K
  rw [hK K (by omega), hK (K + 1) (by omega)] at hg
  omega

/-- Concrete affine-lift form: if every deeper address is
`rho_k + D_k * address_k` with `D_k>1` and positive current address, no
ordinary natural realizes the hierarchy. -/
theorem no_realization_of_affine_address_lifts
    (S : DyadicBreakoffLinkSchedule) (rho D : ℕ → ℕ)
    (hpos : ∀ k, 0 < (S.link k).firstTailBase)
    (hD : ∀ k, 1 < D k)
    (hstep : ∀ k,
      (S.link (k + 1)).firstTailBase =
        rho k + D k * (S.link k).firstTailBase) :
    ¬ ∃ n, S.RealizedBy n := by
  apply S.no_realization_of_strictly_growing_addresses
  intro k
  rw [hstep k]
  exact affineLift_gt _ _ _ (hD k) (hpos k)

/-- Exact prefix-extension form used by affine macro composition.  If adding
one more block replaces the old canonical address `a_k` by
`a_k + 2^(bits k) * rho_k` with a positive source residue, then no ordinary
natural realizes every finite prefix. -/
theorem no_realization_of_positive_extension_lifts
    (S : DyadicBreakoffLinkSchedule) (rho : ℕ → ℕ)
    (hrho : ∀ k, 0 < rho k)
    (hstep : ∀ k,
      (S.link (k + 1)).firstTailBase =
        (S.link k).firstTailBase + 2 ^ S.bits k * rho k) :
    ¬ ∃ n, S.RealizedBy n := by
  apply S.no_realization_of_strictly_growing_addresses
  intro k
  rw [hstep k]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos (Nat.pow_pos (by omega)) (hrho k))

/-- Necessary form of the same obstruction: if the nested prefixes really do
come from one ordinary natural, then every sufficiently late extension must
use zero source residue.  Thus proving merely that nonzero lifts occur
infinitely often is enough to exclude an ordinary ray. -/
theorem extension_lifts_eventually_zero_of_realized
    (S : DyadicBreakoffLinkSchedule) (rho : ℕ → ℕ)
    (hstep : ∀ k,
      (S.link (k + 1)).firstTailBase =
        (S.link k).firstTailBase + 2 ^ S.bits k * rho k)
    {n : ℕ} (hn : S.RealizedBy n) :
    ∃ K, ∀ k, K ≤ k → rho k = 0 := by
  obtain ⟨K, hstable⟩ := S.realized_eventually_constant hn
  refine ⟨K, fun k hk ↦ ?_⟩
  have heq := hstep k
  rw [hstable k hk, hstable (k + 1) (by omega)] at heq
  have hpow : 0 < 2 ^ S.bits k := Nat.pow_pos (by omega)
  have hprod : 2 ^ S.bits k * rho k = 0 := by
    apply Nat.add_left_cancel (n := n)
    simpa using heq.symm
  rcases Nat.mul_eq_zero.mp hprod with hp | hr
  · exact (Nat.ne_of_gt hpow hp).elim
  · exact hr

/-- Operational no-ray criterion: arbitrarily late nonzero extension residues
exclude realization by one ordinary natural. -/
theorem no_realization_of_frequently_nonzero_extension_lifts
    (S : DyadicBreakoffLinkSchedule) (rho : ℕ → ℕ)
    (hstep : ∀ k,
      (S.link (k + 1)).firstTailBase =
        (S.link k).firstTailBase + 2 ^ S.bits k * rho k)
    (hfrequent : ∀ K, ∃ k, K ≤ k ∧ rho k ≠ 0) :
    ¬ ∃ n, S.RealizedBy n := by
  rintro ⟨n, hn⟩
  obtain ⟨K, hzero⟩ :=
    S.extension_lifts_eventually_zero_of_realized rho hstep hn
  obtain ⟨k, hk, hne⟩ := hfrequent K
  exact hne (hzero k hk)

end DyadicBreakoffLinkSchedule

/-- A dyadic affine-link dispatcher whose control consists of a finite phase
and the current residual of one ordinary realizing tail. -/
structure OrdinaryFiniteResidualDispatcher (g : MacroGlider)
    (σ : Type*) where
  schedule : DyadicBreakoffLinkSchedule
  ordinaryTail : ℕ
  realizes : schedule.RealizedBy ordinaryTail
  phase : ℕ → σ
  next : σ → ℕ → σ
  emit : σ → ℕ → List ℕ
  phase_succ : ∀ t,
    phase (t + 1) =
      next (phase t) (schedule.addressResidual ordinaryTail t)
  word_eq : ∀ t,
    g.word t = emit (phase t) (schedule.addressResidual ordinaryTail t)

namespace OrdinaryFiniteResidualDispatcher

variable {g : MacroGlider} {σ : Type*}

def toEventuallyZeroResidualController
    (d : OrdinaryFiniteResidualDispatcher g σ) :
    EventuallyZeroResidualController g σ where
  phase := d.phase
  residual := d.schedule.addressResidual d.ordinaryTail
  next := d.next
  emit := d.emit
  residual_eventually_zero :=
    d.schedule.addressResidual_eventually_zero d.realizes
  phase_succ := d.phase_succ
  word_eq := d.word_eq

/-- Impossibility theorem for the finite residual dispatcher architecture. -/
theorem impossible [Finite σ]
    (d : OrdinaryFiniteResidualDispatcher g σ) : False :=
  d.toEventuallyZeroResidualController.impossible

theorem no_dispatcher [Finite σ] :
    ¬ Nonempty (OrdinaryFiniteResidualDispatcher g σ) := by
  rintro ⟨d⟩
  exact d.impossible

end OrdinaryFiniteResidualDispatcher

end KontoroC
