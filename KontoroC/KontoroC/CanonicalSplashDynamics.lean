/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CompleteSplashProgram

/-!
# The canonical partial splash dynamics

The total decoder induces a deterministic partial map on public sparse states.
A halt outcome maps to `none`; either splash branch maps to its uniquely
decoded output rail length and odd payload.  Thus endpoint linkage is no
longer an external certificate field.

An infinite outward orbit of this partial map is exactly the compressed object
needed to refute Collatz.  No such orbit is constructed here.
-/

namespace KontoroC

/-- Public data of a positive odd payload on a sparse `-1` rail. -/
structure CompleteSplashState where
  railLength : ℕ
  payload : ℕ
  payload_pos : 0 < payload
  payload_odd : Odd payload

namespace CompleteSplashState

def start (x : CompleteSplashState) : ℕ :=
  minusOneState x.payload (x.railLength + 1)

noncomputable def outcome (x : CompleteSplashState) :
    CompleteSplashOutcome x.railLength x.payload :=
  CompleteSplashOutcome.decoded x.railLength x.payload
    x.payload_pos x.payload_odd

noncomputable def word (x : CompleteSplashState) : List ℕ := x.outcome.word

noncomputable def endpoint (x : CompleteSplashState) : ℕ := x.outcome.endpoint

/-- The deterministic next public state, or `none` when the unique decoder
outcome is the explicit halt. -/
noncomputable def next (x : CompleteSplashState) : Option CompleteSplashState :=
  match x.outcome with
  | .halt _ => none
  | .even g _ _ => some {
      railLength := g.outputGap - 1
      payload := g.outputPayload
      payload_pos := g.outputPayload_pos
      payload_odd := g.outputPayload_odd
    }
  | .odd g _ _ => some {
      railLength := g.outputGap - 1
      payload := g.outputPayload
      payload_pos := g.outputPayload_pos
      payload_odd := g.outputPayload_odd
    }

@[simp] theorem outcome_start (x : CompleteSplashState) :
    x.outcome.start = x.start := by
  exact CompleteSplashOutcome.start_eq _

theorem legal_and_endpoint (x : CompleteSplashState) :
    WordLegal x.start x.word ∧ runWord x.start x.word = x.endpoint := by
  simpa [word, endpoint] using
    x.outcome.legal_and_endpoint x.payload_pos

theorem word_nonempty (x : CompleteSplashState) : x.word ≠ [] := by
  exact x.outcome.word_nonempty

/-- By construction, a nonhalting decoded endpoint is literally the next
public sparse state's start. -/
theorem endpoint_eq_next_start {x y : CompleteSplashState}
    (hnext : x.next = some y) : x.endpoint = y.start := by
  unfold next at hnext
  generalize hout : x.outcome = o at hnext
  cases o with
  | halt h => simp at hnext
  | even g hr hP =>
      have hgap : g.outputGap - 1 + 1 = g.outputGap := by
        have := g.outputGap_pos
        omega
      simp only [Option.some.injEq] at hnext
      subst y
      simp only [endpoint, hout, CompleteSplashOutcome.endpoint,
        EvenCleanupGate.endpoint, start, hgap]
  | odd g hr hP =>
      have hgap : g.outputGap - 1 + 1 = g.outputGap := by
        have := g.outputGap_pos
        omega
      simp only [Option.some.injEq] at hnext
      subst y
      simp only [endpoint, hout, CompleteSplashOutcome.endpoint,
        OddCatcherGate.endpoint, start, hgap]

end CompleteSplashState

/-- An infinite surviving outward orbit of the canonical partial decoder. -/
structure InfiniteCanonicalSplashOrbit where
  state : ℕ → CompleteSplashState
  next_state : ∀ t, (state t).next = some (state (t + 1))
  start_large : 4 < (state 0).start
  outward : ∀ t, (state t).start < (state (t + 1)).start

namespace InfiniteCanonicalSplashOrbit

/-- The partial-dynamics orbit expands to an exact ordinary Collatz glider. -/
noncomputable def toMacroGlider (g : InfiniteCanonicalSplashOrbit) :
    MacroGlider where
  state t := (g.state t).start
  word t := (g.state t).word
  start_large := g.start_large
  word_nonempty t := (g.state t).word_nonempty
  legal t := (g.state t).legal_and_endpoint.1
  transition t := (g.state t).legal_and_endpoint.2.trans
    ((g.state t).endpoint_eq_next_start (g.next_state t))
  grows t := g.outward t

theorem not_conjecture (g : InfiniteCanonicalSplashOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end InfiniteCanonicalSplashOrbit

end KontoroC
