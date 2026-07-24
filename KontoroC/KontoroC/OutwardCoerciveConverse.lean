/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLDyadicReset
import KontoroC.OutwardInvariantBridge

/-!
# A coercive converse gate for symbolic reset schedules

A compatible infinite reset schedule can describe only a `2`-adic initial
payload.  The existing `KLDyadicReset` theorem says that it comes from an
ordinary nonnegative integer exactly when its canonical initial residues are
bounded.  This module packages a theorem-friendly way to prove that bound:
an invariant sublevel set for a natural-valued potential which dominates the
canonical residue along the deterministic symbolic orbit.

This is deliberately not a Collatz counterexample theorem.  The reconstructed
integer reset chain need not have positive later entries, and the abstract
reset steps have not been identified with literal first-passage macros.
-/

namespace KontoroC
namespace OutwardCoerciveConverse

open KLDyadicReset OutwardCodeCompactness OutwardInvariantBridge

variable {State : Type*}

/-- Exact certificate that one invariant potential sublevel contains the
entire symbolic orbit and controls every canonical initial residue. -/
structure CoerciveSublevelCertificate
    (e : ℕ → ResetStep) (State : Type*) where
  next : State → State
  invariant : State → Prop
  potential : State → ℕ
  initial : State
  level : ℕ
  initial_mem : invariant initial
  initial_level : potential initial ≤ level
  closed : ∀ x, invariant x → potential x ≤ level →
    invariant (next x) ∧ potential (next x) ≤ level
  controls : ∀ n,
    initialResidue e n ≤ potential ((next^[n]) initial)

namespace CoerciveSublevelCertificate

/-- A conventional Lyapunov-style constructor: an invariant natural
potential which never increases stays in its initial sublevel. -/
def ofNonincreasing
    {e : ℕ → ResetStep}
    (next : State → State) (invariant : State → Prop)
    (potential : State → ℕ) (initial : State)
    (hinitial : invariant initial)
    (hclosed : ∀ x, invariant x → invariant (next x))
    (hnonincreasing : ∀ x, invariant x →
      potential (next x) ≤ potential x)
    (hcontrols : ∀ n,
      initialResidue e n ≤ potential ((next^[n]) initial)) :
    CoerciveSublevelCertificate e State where
  next := next
  invariant := invariant
  potential := potential
  initial := initial
  level := potential initial
  initial_mem := hinitial
  initial_level := le_rfl
  closed := by
    intro x hx hxlevel
    exact ⟨hclosed x hx, (hnonincreasing x hx).trans hxlevel⟩
  controls := hcontrols

/-- Closure really propagates both invariant membership and the potential
sublevel along every finite iterate. -/
theorem orbit_mem_and_level
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State) (n : ℕ) :
    cert.invariant ((cert.next^[n]) cert.initial) ∧
      cert.potential ((cert.next^[n]) cert.initial) ≤ cert.level := by
  induction n with
  | zero => simpa using And.intro cert.initial_mem cert.initial_level
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        cert.closed ((cert.next^[n]) cert.initial) ih.1 ih.2

/-- A coercive sublevel certificate supplies the exact bounded-residue
hypothesis in the ordinary-integer criterion. -/
theorem residuesBounded
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State) :
    ResiduesBounded e := by
  refine ⟨cert.level, fun n => ?_⟩
  exact (cert.controls n).trans (cert.orbit_mem_and_level n).2

/-- Coercivity forces eventual exact zero extension carry. -/
theorem eventuallyZeroCarry
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State) :
    EventuallyZeroCarry e := by
  exact (eventuallyConstantResidue_iff_eventuallyZeroCarry e).mp
    ((residuesBounded_iff_eventuallyConstant e).mp cert.residuesBounded)

/-- Coercivity reconstructs an ordinary nonnegative initial reset chain.
Later chain values are integers and are not asserted to be positive. -/
theorem exists_nonnegative_follows
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State) :
    ∃ m : ℕ → ℤ, Follows e m ∧ 0 ≤ m 0 :=
  (residuesBounded_iff_exists_nonnegative_follows e).mp cert.residuesBounded

/-- Adversarial form: a schedule whose canonical residues are unbounded
cannot admit any claimed coercive sublevel certificate. -/
theorem false_of_residuesUnbounded
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State)
    (hunbounded : ResiduesUnbounded e) : False := by
  obtain ⟨B, hB⟩ := cert.residuesBounded
  obtain ⟨n, hn⟩ := hunbounded B
  exact (not_lt_of_ge (hB n)) hn

/-! ## Conditional promotion to literal first-passage execution -/

/-- An integer reset chain is literally realized when every adjacent pair of
its natural values is connected by a positive nonempty first-passage macro.
This predicate is the semantic premise absent from abstract reset algebra. -/
def PositiveMacroRealization (m : ℕ → ℤ) : Prop :=
  ∀ n, ∃ words,
    RechargeMacro (m n).toNat (m (n + 1)).toNat words

/-- Coercivity plus a genuine semantic realization theorem produces an
ordinary infinite first-passage execution.  The `hpromote` hypothesis is
essential: reset equations alone do not prove positivity or literal parity
execution. -/
theorem infiniteExecution_of_semantic_promotion
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State)
    (hpromote : ∀ m : ℕ → ℤ, Follows e m → 0 ≤ m 0 →
      PositiveMacroRealization m) :
    ∃ H₀, 0 < H₀ ∧
      InfiniteExecution OutwardOddSlice.FirstPassageCode (3 * H₀ - 1) := by
  obtain ⟨m, hm, h0⟩ := cert.exists_nonnegative_follows
  have hmacro := hpromote m hm h0
  let I : ℕ → Prop := fun H => ∃ n, H = (m n).toNat
  let H₀ := (m 0).toNat
  obtain ⟨words₀, hfirst⟩ := hmacro 0
  have hH₀pos : 0 < H₀ := by
    simpa [H₀] using hfirst.source_pos
  have hI₀ : I H₀ := ⟨0, rfl⟩
  have hclosed : ∀ H, I H →
      ∃ H' words, RechargeMacro H H' words ∧ I H' := by
    intro H hH
    rcases hH with ⟨n, rfl⟩
    obtain ⟨words, hstep⟩ := hmacro n
    exact ⟨(m (n + 1)).toNat, words, hstep, n + 1, rfl⟩
  exact ⟨H₀, hH₀pos,
    invariant_gives_infiniteExecution I H₀ hH₀pos hI₀ hclosed⟩

/-- Fully conditional Collatz endpoint for the coercive architecture.  No
concrete certificate or semantic promotion is asserted here. -/
theorem not_collatz_of_semantic_promotion
    {e : ℕ → ResetStep}
    (cert : CoerciveSublevelCertificate e State)
    (hpromote : ∀ m : ℕ → ℤ, Follows e m → 0 ≤ m 0 →
      PositiveMacroRealization m) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨H₀, hH₀pos, hinfinite⟩ :=
    cert.infiniteExecution_of_semantic_promotion hpromote
  exact OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (fun _ hw => hw.1) hinfinite

end CoerciveSublevelCertificate

end OutwardCoerciveConverse
end KontoroC
