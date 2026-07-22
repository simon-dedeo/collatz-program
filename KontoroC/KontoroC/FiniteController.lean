/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AperiodicGlider

/-!
# Autonomous finite-state controllers cannot drive growing Collatz gliders

This is the finite-memory consequence of `MacroGlider` aperiodicity.  If an
emitted valuation word depends only on a finite internal phase and that phase
updates autonomously, the pigeonhole principle repeats a phase.  Determinism
then repeats the complete future schedule, contradicting
`MacroGlider.not_eventually_periodic_words`.

The qualifier *autonomous* is essential.  A small controller may still read
an unbounded arithmetic tail or payload; in that case its effective state is
not the finite type appearing here.
-/

namespace KontoroC

/-- A factorization of a glider's word schedule through an autonomous finite
state machine. -/
structure AutonomousFiniteController (g : MacroGlider) (σ : Type*) [Finite σ] where
  phase : ℕ → σ
  next : σ → σ
  emit : σ → List ℕ
  phase_succ : ∀ t, phase (t + 1) = next (phase t)
  word_eq : ∀ t, g.word t = emit (phase t)

namespace AutonomousFiniteController

variable {g : MacroGlider} {σ : Type*} [Finite σ]

/-- Once two phases agree, determinism makes their entire future phase
sequences agree. -/
theorem phase_future_eq (c : AutonomousFiniteController g σ)
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

/-- An autonomous finite-state factorization of a growing exact Collatz
macro-glider is impossible. -/
theorem impossible (c : AutonomousFiniteController g σ) : False := by
  obtain ⟨i, j, hne, hij⟩ :=
    Finite.exists_ne_map_eq_of_infinite c.phase
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

/-- No autonomous controller over a finite type can generate the word
schedule of a macro-glider. -/
theorem no_controller : ¬ Nonempty (AutonomousFiniteController g σ) := by
  rintro ⟨c⟩
  exact c.impossible

end AutonomousFiniteController

end KontoroC
