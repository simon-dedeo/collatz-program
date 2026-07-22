/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ExecutableBreakoff

/-!
# Finite literal semantics for the executable break-off counter

`breakoffRun` is an arithmetic evaluator on the intermediate break-off
coordinate.  This file proves the missing finite semantic bridge: once the
source coordinate is supplied with its exact ternary factorization, every
successful finite run expands to a legal word for the ordinary accelerated
Collatz map.

The initial factorization is deliberately explicit.  Thus this theorem does
not identify the break-off coordinate with an ordinary Collatz state, and it
does not assume that the final router decoding is affine or monotone.
-/

namespace KontoroC

/-- Literal semantic data reconstructed from a successful finite break-off
run.  The source ordinary state is
`2^(r+1) * (3*H) - 1`; the result supplies the corresponding canonical
factorization and ordinary state at the endpoint. -/
structure BreakoffRunSemantics (n k k' r H : ℕ) where
  run : breakoffRun n k = some k'
  outputRail : ℕ
  outputPayload : ℕ
  outputPayload_pos : 0 < outputPayload
  outputPayload_odd : Odd outputPayload
  output_factor :
    8 * k' = 3 ^ (outputRail + 2) * outputPayload + 1
  word : List ℕ
  word_nonempty : 0 < n → word ≠ []
  legal : WordLegal (minusOneState (3 * H) (r + 1)) word
  endpoint :
    runWord (minusOneState (3 * H) (r + 1)) word =
      minusOneState (3 * outputPayload) (outputRail + 1)

/-- One executable break-off step is exactly one canonical ordinary Collatz
router word. -/
noncomputable def breakoffStep_literal_semantics {k k' r H : ℕ}
    (hk : 0 < k) (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor : 8 * k = 3 ^ (r + 2) * H + 1)
    (hstep : breakoffNext k = some k') :
    BreakoffRunSemantics 1 k k' r H := by
  let u := breakoffPayload k
  let j := breakoffOpcode k
  have hu_pos : 0 < u := breakoffPayload_pos hk
  have hu_odd : Odd u := breakoffPayload_odd hk
  have hout_factor : 8 * k' = 3 ^ (j + 2) * u + 1 := by
    simpa [j, u] using
      (breakoffNext_eq_some_iff_equation k k').mp hstep
  let x : CompleteSplashState := {
    railLength := r
    payload := 3 * H
    payload_pos := Nat.mul_pos (by omega) hHpos
    payload_odd := (by norm_num : Odd 3).mul hHodd
  }
  let y : CompleteSplashState := {
    railLength := j
    payload := 3 * u
    payload_pos := Nat.mul_pos (by omega) hu_pos
    payload_odd := (by norm_num : Odd 3).mul hu_odd
  }
  have hrec :
      2 ^ (y.railLength + 3) * y.payload =
        3 ^ (x.railLength + 2) * x.payload + 3 := by
    dsimp [x, y]
    calc
      2 ^ (j + 3) * (3 * u) = 24 * (2 ^ j * u) := by
        rw [show j + 3 = 3 + j by omega, pow_add]
        norm_num
        ring
      _ = 24 * k := by rw [breakoff_binary_factor k]
      _ = 3 * (8 * k) := by ring
      _ = 3 * (3 ^ (r + 2) * H + 1) := by rw [hfactor]
      _ = 3 ^ (r + 2) * (3 * H) + 3 := by ring
  have hnext : x.next = some y :=
    completeSplashState_next_of_router_recurrence x y hrec
  have hsem := x.legal_and_endpoint
  refine {
    run := by simp [breakoffRun, hstep]
    outputRail := j
    outputPayload := u
    outputPayload_pos := hu_pos
    outputPayload_odd := hu_odd
    output_factor := hout_factor
    word := x.word
    word_nonempty := ?_
    legal := ?_
    endpoint := ?_
  }
  · intro _
    exact x.word_nonempty
  · simpa [x, CompleteSplashState.start] using hsem.1
  · calc
      runWord (minusOneState (3 * H) (r + 1)) x.word = x.endpoint := by
        simpa [x, CompleteSplashState.start] using hsem.2
      _ = y.start := x.endpoint_eq_next_start hnext
      _ = minusOneState (3 * u) (j + 1) := rfl

/-- Every successful finite execution of the one-register break-off map has
an exact literal accelerated-Collatz interpretation. -/
noncomputable def breakoffRun_literal_semantics {n k k' r H : ℕ}
    (hk : 0 < k) (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor : 8 * k = 3 ^ (r + 2) * H + 1)
    (hrun : breakoffRun n k = some k') :
    BreakoffRunSemantics n k k' r H := by
  induction n generalizing k k' r H with
  | zero =>
      have hkk' : k = k' := by simpa [breakoffRun] using hrun
      subst k'
      exact {
        run := hrun
        outputRail := r
        outputPayload := H
        outputPayload_pos := hHpos
        outputPayload_odd := hHodd
        output_factor := hfactor
        word := []
        word_nonempty := by omega
        legal := by simp [WordLegal]
        endpoint := by simp
      }
  | succ n ih =>
      simp only [breakoffRun] at hrun
      cases hstep : breakoffNext k with
      | none => simp [hstep] at hrun
      | some y =>
          rw [hstep] at hrun
          have hky : k < y := breakoffNext_strictly_grows hk hstep
          have hy : 0 < y := lt_trans hk hky
          let first := breakoffStep_literal_semantics hk hHpos hHodd hfactor hstep
          let rest := ih hy first.outputPayload_pos first.outputPayload_odd
            first.output_factor hrun
          refine {
            run := by
              simp only [breakoffRun]
              rw [hstep]
              exact hrun
            outputRail := rest.outputRail
            outputPayload := rest.outputPayload
            outputPayload_pos := rest.outputPayload_pos
            outputPayload_odd := rest.outputPayload_odd
            output_factor := rest.output_factor
            word := first.word ++ rest.word
            word_nonempty := ?_
            legal := ?_
            endpoint := ?_
          }
          · intro _
            exact List.append_ne_nil_of_left_ne_nil
              (first.word_nonempty (by omega)) rest.word
          · rw [wordLegal_append_iff]
            exact ⟨first.legal, by simpa [first.endpoint] using rest.legal⟩
          · rw [runWord_append, first.endpoint, rest.endpoint]

/-- A proof-carrying regenerative gate inherits literal Collatz semantics as
soon as its source break-off coordinate is supplied with the canonical
ternary factorization used by the incoming link. -/
noncomputable def BreakoffDelayGate.literal_semantics (g : BreakoffDelayGate)
    {r H : ℕ} (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor : 8 * g.start = 3 ^ (r + 2) * H + 1) :
    BreakoffRunSemantics (g.delay + 1) g.start g.endpoint r H := by
  have hstart_base : 1 < 9 * 2 ^ (3 * g.delay) * g.coefficient := by
    have htail : 0 < 2 ^ (3 * g.delay) * g.coefficient :=
      Nat.mul_pos (Nat.pow_pos (by omega)) g.coefficient_pos
    nlinarith
  have hstart : 0 < g.start := by
    dsimp [BreakoffDelayGate.start]
    omega
  exact breakoffRun_literal_semantics hstart hHpos hHodd hfactor g.run

/-- Proposition-valued interface to the finite compiler, convenient when a
consumer needs only existence and does not choose the reconstructed word. -/
theorem breakoffRun_has_literal_semantics {n k k' r H : ℕ}
    (hk : 0 < k) (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor : 8 * k = 3 ^ (r + 2) * H + 1)
    (hrun : breakoffRun n k = some k') :
    Nonempty (BreakoffRunSemantics n k k' r H) :=
  ⟨breakoffRun_literal_semantics hk hHpos hHodd hfactor hrun⟩

/-- Proposition-valued literal endpoint for a regenerative delay gate. -/
theorem BreakoffDelayGate.has_literal_semantics (g : BreakoffDelayGate)
    {r H : ℕ} (hHpos : 0 < H) (hHodd : Odd H)
    (hfactor : 8 * g.start = 3 ^ (r + 2) * H + 1) :
    Nonempty (BreakoffRunSemantics (g.delay + 1) g.start g.endpoint r H) :=
  ⟨g.literal_semantics hHpos hHodd hfactor⟩

end KontoroC
