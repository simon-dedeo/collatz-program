/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardLiteralMacroOrbit

/-!
# Literal first-passage recharge schedules are genuinely aperiodic

A fixed nonempty outward parity program cannot execute forever on positive
ordinary naturals.  This file lifts that obstruction to a sequence of exact
`RechargeMacro` witnesses.  A finite period of possibly different macros is
concatenated into one fixed outward super-macro, contradicting the repeated
outward-word theorem.

Consequently every proposed positive period is broken infinitely often in
the emitted macro schedule.  The ordinary boundary charge is allowed to grow
and is not attached to a finite symbolic state, so this is stronger than the
finite-state fixed-charge obstruction.  It does not rule out a genuinely
aperiodic schedule.
-/

namespace KontoroC
namespace OutwardRechargeAperiodic

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardCodeCounterexample OutwardInvariantBridge OutwardOddSlice

/-- Concatenate `n` successive block lists beginning at macro time `t`. -/
def segmentWords (words : ℕ → List (List Bool)) (t : ℕ) :
    ℕ → List (List Bool)
  | 0 => []
  | n + 1 => words t ++ segmentWords words (t + 1) n

@[simp] theorem segmentWords_zero
    (words : ℕ → List (List Bool)) (t : ℕ) :
    segmentWords words t 0 = [] := rfl

@[simp] theorem segmentWords_succ
    (words : ℕ → List (List Bool)) (t n : ℕ) :
    segmentWords words t (n + 1) =
      words t ++ segmentWords words (t + 1) n := rfl

/-- A positive-length segment of a literal recharge orbit is itself one
literal recharge macro, obtained by exact endpoint-sensitive composition. -/
theorem segment_rechargeMacro
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (t n : ℕ) (hn : 0 < n) :
    RechargeMacro (charge t) (charge (t + n))
      (segmentWords words t n) := by
  induction n generalizing t with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n ih =>
      cases n with
      | zero =>
          simpa using hmacro t
      | succ n =>
          have hhead := hmacro t
          have htail := ih (t + 1) (by omega)
          have happ := hhead.append htail
          have hend : t + 1 + (n + 1) = t + (n + 2) := by omega
          rw [hend] at happ
          simpa [segmentWords, Nat.add_assoc] using happ

/-- Periodicity by `p` propagates to every multiple of `p`. -/
theorem words_eq_of_periodic_mul
    (words : ℕ → List (List Bool)) {p : ℕ}
    (hperiod : ∀ t, words (t + p) = words t)
    (k t : ℕ) :
    words (k * p + t) = words t := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        words ((k + 1) * p + t) =
            words ((k * p + t) + p) := by
              congr 1
              simp [Nat.succ_mul, Nat.add_comm,
                Nat.add_left_comm]
        _ = words (k * p + t) := hperiod _
        _ = words t := ih

/-- Period-aligned finite segments are the same literal block list. -/
theorem segmentWords_eq_of_periodic_mul
    (words : ℕ → List (List Bool)) {p : ℕ}
    (hperiod : ∀ t, words (t + p) = words t)
    (k t n : ℕ) :
    segmentWords words (k * p + t) n = segmentWords words t n := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [segmentWords_succ, segmentWords_succ,
        words_eq_of_periodic_mul words hperiod k t]
      congr 1
      simpa [Nat.add_assoc] using ih (t + 1)

/-- One fixed first-passage block list cannot be the literal recharge macro
at every step of a positive ordinary charge orbit. -/
theorem no_constant_rechargeMacro_orbit
    (blocks : List (List Bool)) :
    ¬ ∃ charge : ℕ → ℕ,
      ∀ n, RechargeMacro (charge n) (charge (n + 1)) blocks := by
  rintro ⟨charge, hmacro⟩
  have hzero := hmacro 0
  have hout : WordOutward (flattenWords blocks) := by
    apply wordOutward_join hzero.words_ne_nil
    intro w hw
    exact (hzero.wordsIn w hw).1
  apply no_positive_repeated_outward_word
    (flattenWords blocks) (wordOutward_ne_nil hout) hout
  refine ⟨fun n ↦ 3 * charge n - 1, ?_, ?_⟩
  · intro n
    have hpos := (hmacro n).source_pos
    have hthree : 3 ≤ 3 * charge n :=
      Nat.mul_le_mul_left 3 hpos
    exact Nat.sub_pos_of_lt ((by norm_num : 1 < 3).trans_le hthree)
  · intro n
    exact executesBlocksTo_iff_flatten.mp (hmacro n).executesTo

/-- The block-list schedule of a literal recharge orbit cannot have a
positive period from its start.  A whole period is grouped into one fixed
outward super-macro. -/
theorem no_periodic_rechargeMacro_schedule
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    {p : ℕ} (hp : 0 < p)
    (hperiod : ∀ t, words (t + p) = words t) : False := by
  let cycle := segmentWords words 0 p
  let groupedCharge : ℕ → ℕ := fun k ↦ charge (k * p)
  apply no_constant_rechargeMacro_orbit cycle
  refine ⟨groupedCharge, fun k ↦ ?_⟩
  have hsegment := segment_rechargeMacro charge words hmacro (k * p) p hp
  have hcycle : segmentWords words (k * p) p = cycle := by
    simpa [cycle] using
      segmentWords_eq_of_periodic_mul words hperiod k 0 p
  dsimp only [groupedCharge]
  rw [hcycle] at hsegment
  simpa [Nat.succ_mul] using hsegment

/-- Removing any finite transient does not rescue periodicity. -/
theorem no_eventuallyPeriodic_rechargeMacro_schedule
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (t₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hperiod : ∀ t,
      words (t₀ + (t + p)) = words (t₀ + t)) : False := by
  let tailCharge : ℕ → ℕ := fun t ↦ charge (t₀ + t)
  let tailWords : ℕ → List (List Bool) := fun t ↦ words (t₀ + t)
  apply no_periodic_rechargeMacro_schedule tailCharge tailWords
    (p := p) (by
      intro n
      dsimp only [tailCharge, tailWords]
      simpa [Nat.add_assoc] using hmacro (t₀ + n)) hp
  intro t
  exact hperiod t

/-- Macro-times at which a proposed period fails. -/
def periodBreaks (words : ℕ → List (List Bool)) (p : ℕ) : Set ℕ :=
  {t | words (t + p) ≠ words t}

/-- Every positive proposed period is broken infinitely often along a
literal recharge orbit. -/
theorem periodBreaks_infinite
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    {p : ℕ} (hp : 0 < p) :
    (periodBreaks words p).Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  apply no_eventuallyPeriodic_rechargeMacro_schedule
    charge words hmacro (M + 1) hp
  intro t
  by_contra hne
  have hmem : M + 1 + t ∈ periodBreaks words p := by
    change words ((M + 1 + t) + p) ≠ words (M + 1 + t)
    intro heq
    exact hne (by simpa [Nat.add_assoc] using heq)
  have := hM (M + 1 + t) hmem
  omega

/-- Operational form: beyond every requested depth there is a later failure
of the proposed positive period. -/
theorem exists_periodBreak_after
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    {p : ℕ} (hp : 0 < p) (depth : ℕ) :
    ∃ t, depth < t ∧ words (t + p) ≠ words t := by
  obtain ⟨t, htmem, ht⟩ :=
    (periodBreaks_infinite charge words hmacro hp).exists_gt depth
  exact ⟨t, ht, htmem⟩

/-! ## Autonomous finite controllers -/

/-- A factorization of the emitted recharge block lists through an
autonomous finite state machine.  The ordinary charge is deliberately not a
field: it may be an independent unbounded lift supplied to the impossibility
theorem below. -/
structure AutonomousFiniteRechargeController
    (words : ℕ → List (List Bool)) (State : Type*) [Finite State] where
  phase : ℕ → State
  next : State → State
  emit : State → List (List Bool)
  phase_succ : ∀ t, phase (t + 1) = next (phase t)
  words_eq : ∀ t, words t = emit (phase t)

namespace AutonomousFiniteRechargeController

variable {State : Type*} [Finite State]
variable {words : ℕ → List (List Bool)}

/-- Once an autonomous phase repeats, determinism makes its complete future
phase trajectory repeat. -/
theorem phase_future_eq
    (controller : AutonomousFiniteRechargeController words State)
    {i j : ℕ} (hij : controller.phase i = controller.phase j) (t : ℕ) :
    controller.phase (i + t) = controller.phase (j + t) := by
  induction t with
  | zero => simpa using hij
  | succ t ih =>
      calc
        controller.phase (i + (t + 1)) =
            controller.next (controller.phase (i + t)) := by
              simpa [Nat.add_assoc] using controller.phase_succ (i + t)
        _ = controller.next (controller.phase (j + t)) :=
          congrArg controller.next ih
        _ = controller.phase (j + (t + 1)) := by
              simpa [Nat.add_assoc] using
                (controller.phase_succ (j + t)).symm

/-- No autonomous finite-state machine can emit the macro schedule of a
literal recharge orbit, even when the ordinary charge is retained as a
separate unbounded sequence. -/
theorem impossible
    (controller : AutonomousFiniteRechargeController words State)
    (charge : ℕ → ℕ)
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) : False := by
  obtain ⟨i, j, hne, hij⟩ :=
    Finite.exists_ne_map_eq_of_infinite controller.phase
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply no_eventuallyPeriodic_rechargeMacro_schedule
      charge words hmacro i (p := j - i) (by omega)
    intro t
    rw [controller.words_eq, controller.words_eq]
    apply congrArg controller.emit
    have hji : i + (j - i) = j :=
      Nat.add_sub_of_le (Nat.le_of_lt hlt)
    calc
      controller.phase (i + (t + (j - i))) =
          controller.phase ((i + (j - i)) + t) := by
            congr 1
            ac_rfl
      _ = controller.phase (j + t) := by rw [hji]
      _ = controller.phase (i + t) :=
        (controller.phase_future_eq hij t).symm
  · apply no_eventuallyPeriodic_rechargeMacro_schedule
      charge words hmacro j (p := i - j) (by omega)
    intro t
    rw [controller.words_eq, controller.words_eq]
    apply congrArg controller.emit
    have hij' : j + (i - j) = i :=
      Nat.add_sub_of_le (Nat.le_of_lt hgt)
    calc
      controller.phase (j + (t + (i - j))) =
          controller.phase ((j + (i - j)) + t) := by
            congr 1
            ac_rfl
      _ = controller.phase (i + t) := by rw [hij']
      _ = controller.phase (j + t) :=
        (controller.phase_future_eq hij.symm t).symm

/-- Negated-existence packaging for architecture audits. -/
theorem no_controller
    (charge : ℕ → ℕ)
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n)) :
    ¬ Nonempty (AutonomousFiniteRechargeController words State) := by
  rintro ⟨controller⟩
  exact controller.impossible charge hmacro

end AutonomousFiniteRechargeController

/-! ## Forced semantic aliases in every finite phase abstraction -/

/-- An autonomous finite phase abstraction with no assumption that the
emitted macro is determined by the phase. -/
structure AutonomousFinitePhase (State : Type*) [Finite State] where
  phase : ℕ → State
  next : State → State
  phase_succ : ∀ t, phase (t + 1) = next (phase t)

namespace AutonomousFinitePhase

variable {State : Type*} [Finite State]

theorem future_eq (phaseSystem : AutonomousFinitePhase State)
    {i j : ℕ} (hij : phaseSystem.phase i = phaseSystem.phase j) (t : ℕ) :
    phaseSystem.phase (i + t) = phaseSystem.phase (j + t) := by
  induction t with
  | zero => simpa using hij
  | succ t ih =>
      calc
        phaseSystem.phase (i + (t + 1)) =
            phaseSystem.next (phaseSystem.phase (i + t)) := by
              simpa [Nat.add_assoc] using phaseSystem.phase_succ (i + t)
        _ = phaseSystem.next (phaseSystem.phase (j + t)) :=
          congrArg phaseSystem.next ih
        _ = phaseSystem.phase (j + (t + 1)) := by
              simpa [Nat.add_assoc] using
                (phaseSystem.phase_succ (j + t)).symm

/-- Every autonomous finite phase abstraction aliases distinct literal
macros arbitrarily far out along a recharge orbit.  Thus any missing
information really must be carried by an unbounded payload which affects
macro selection inside the same finite phase. -/
theorem exists_semanticAlias_after
    (phaseSystem : AutonomousFinitePhase State)
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (depth : ℕ) :
    ∃ i j,
      depth < i ∧ depth < j ∧
      phaseSystem.phase i = phaseSystem.phase j ∧
      words i ≠ words j := by
  obtain ⟨a, b, habNe, habPhase⟩ :=
    Finite.exists_ne_map_eq_of_infinite phaseSystem.phase
  rcases lt_or_gt_of_ne habNe with hab | hba
  · let p := b - a
    have hp : 0 < p := by dsimp [p]; omega
    obtain ⟨t, htlarge, htbreak⟩ :=
      exists_periodBreak_after charge words hmacro hp (max depth a)
    have hat : a ≤ t := (Nat.le_max_right depth a).trans htlarge.le
    let s := t - a
    have has : a + s = t := by
      dsimp [s]
      exact Nat.add_sub_of_le hat
    have habp : a + p = b := by
      dsimp [p]
      exact Nat.add_sub_of_le hab.le
    have hphase : phaseSystem.phase t = phaseSystem.phase (t + p) := by
      calc
        phaseSystem.phase t = phaseSystem.phase (a + s) := by rw [has]
        _ = phaseSystem.phase (b + s) :=
          phaseSystem.future_eq habPhase s
        _ = phaseSystem.phase (t + p) := by
          congr 1
          omega
    exact ⟨t, t + p,
      (Nat.le_max_left depth a).trans_lt htlarge,
      ((Nat.le_max_left depth a).trans_lt htlarge).trans_le
        (Nat.le_add_right t p),
      hphase, Ne.symm htbreak⟩
  · let p := a - b
    have hp : 0 < p := by dsimp [p]; omega
    obtain ⟨t, htlarge, htbreak⟩ :=
      exists_periodBreak_after charge words hmacro hp (max depth b)
    have hbt : b ≤ t := (Nat.le_max_right depth b).trans htlarge.le
    let s := t - b
    have hbs : b + s = t := by
      dsimp [s]
      exact Nat.add_sub_of_le hbt
    have hbap : b + p = a := by
      dsimp [p]
      exact Nat.add_sub_of_le hba.le
    have hphase : phaseSystem.phase t = phaseSystem.phase (t + p) := by
      calc
        phaseSystem.phase t = phaseSystem.phase (b + s) := by rw [hbs]
        _ = phaseSystem.phase (a + s) :=
          phaseSystem.future_eq habPhase.symm s
        _ = phaseSystem.phase (t + p) := by
          congr 1
          omega
    exact ⟨t, t + p,
      (Nat.le_max_left depth b).trans_lt htlarge,
      ((Nat.le_max_left depth b).trans_lt htlarge).trans_le
        (Nat.le_add_right t p),
      hphase, Ne.symm htbreak⟩

end AutonomousFinitePhase

end OutwardRechargeAperiodic
end KontoroC
